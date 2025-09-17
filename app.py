from flask import Flask, request, render_template, jsonify, Response, send_from_directory
import os
import re
import time
from datetime import datetime
import yt_dlp
import shutil
import subprocess
import unicodedata
from urllib.parse import quote as _urlquote
import threading
import uuid
from urllib.parse import urlparse


app = Flask(__name__)
# Secrets and basic config via environment variables for production readiness
app.config['SECRET_KEY'] = os.getenv('SECRET_KEY', 'change-me-in-production')

# Honor reverse proxy headers on Render (X-Forwarded-For / X-Forwarded-Proto)
try:
    from werkzeug.middleware.proxy_fix import ProxyFix
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1)
except Exception:
    pass


# Directories (prefer ephemeral /tmp on Render; fallback to project dir locally)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
TEMP_DOWNLOAD_DIR = os.getenv('TEMP_DIR') or os.path.join('/tmp', 'temp_downloads') if os.name != 'nt' else os.path.join('.', 'temp_downloads')
os.makedirs(TEMP_DOWNLOAD_DIR, exist_ok=True)


def _cookies_file_path() -> str | None:
    """Return path to a cookies file if present or provided via env.

    Supports:
    - File at repo root: cookies.txt / cookies.sqlite / cookies
    - Env var COOKIES_TEXT: raw Netscape cookie text
    - Env var COOKIES_B64: base64-encoded Netscape cookie text
    """
    # 1) Repo files
    for cand in ('cookies.txt', 'cookies.sqlite', 'cookies'):
        path = os.path.join(BASE_DIR, cand)
        if os.path.exists(path):
            return path
    # 2) Env-provided cookies → write to /tmp
    cookies_text = os.getenv('COOKIES_TEXT')
    cookies_b64 = os.getenv('COOKIES_B64')
    if not cookies_text and cookies_b64:
        try:
            import base64 as _b64
            cookies_text = _b64.b64decode(cookies_b64).decode('utf-8', 'ignore')
        except Exception:
            cookies_text = None
    if cookies_text:
        try:
            tmp_path = os.path.join('/tmp' if os.name != 'nt' else '.', 'cookies.txt')
            with open(tmp_path, 'w', encoding='utf-8') as f:
                f.write(cookies_text)
            return tmp_path
        except Exception:
            return None
    return None


def _build_ydl_opts(extra: dict | None = None) -> dict:
    """Centralized yt-dlp options with robust defaults for YouTube.

    - geo_bypass: True, retries, and sane networking defaults
    - prefer Android player client to avoid some restrictions
    - optional cookies support if a cookies file exists in repo root
    - consistent user-agent and referer
    """
    opts = {
        'format': 'best',
        'ignoreerrors': True,
        'no_warnings': True,
        'extract_flat': False,
        'noplaylist': True,
        'geo_bypass': True,
        'retries': 3,
        'fragment_retries': 3,
        'concurrent_fragment_downloads': 1,
        'user_agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36',
        'referer': 'https://www.youtube.com/',
        'http_headers': {
            'Accept-Language': os.getenv('ACCEPT_LANGUAGE', 'en-US,en;q=0.9'),
        },
        'extractor_args': {
            'youtube': {
                # Try multiple clients; some are less restricted than others
                'player_client': ['android', 'ios', 'tv', 'web'],
            }
        },
    }
    cfile = _cookies_file_path()
    if cfile:
        opts['cookiefile'] = cfile
        try:
            app.logger.info(f"yt-dlp: using cookie file at {cfile}")
        except Exception:
            pass
    if extra:
        opts.update(extra)
    return opts


def _create_safe_filename(filename: str, max_length: int = 100) -> str:
    """Create filesystem- and header-safe ASCII filename.

    - Normalizes Unicode to NFKD and strips non-ASCII
    - Replaces reserved characters with underscores
    - Trims whitespace and length
    - Ensures there is at least a default name
    """
    try:
        # Normalize and strip non-ascii
        filename = unicodedata.normalize('NFKD', filename)
        filename = filename.encode('ascii', 'ignore').decode('ascii')
    except Exception:
        pass
    filename = re.sub(r'[<>:"/\\|?*]', '_', filename).strip()
    if not filename:
        filename = 'download'
    # Avoid trailing dots/spaces on Windows
    filename = filename.rstrip(' .')
    return filename[:max_length] if len(filename) > max_length else filename


def _is_youtube_url(url: str) -> bool:
    try:
        u = urlparse(url)
        host = (u.hostname or '').lower()
        return 'youtube.com' in host or 'youtu.be' in host
    except Exception:
        return False


def _cleanup_old_temp():
    try:
        if os.path.exists(TEMP_DOWNLOAD_DIR):
            for item in os.listdir(TEMP_DOWNLOAD_DIR):
                item_path = os.path.join(TEMP_DOWNLOAD_DIR, item)
                if os.path.isdir(item_path):
                    shutil.rmtree(item_path, ignore_errors=True)
    except Exception:
        pass


_cleanup_old_temp()


class YouTubeDownloader:
    def __init__(self) -> None:
        pass

    @staticmethod
    def _score_audio_format(fmt: dict, original_lang: str | None) -> tuple:
        """Return a tuple used to sort audio formats preferring original, English and good containers/bitrates.

        Lower tuple sorts first (more preferred).
        """
        # Track source preference: original < unknown < dubbed
        source_rank = 1
        try:
            at = fmt.get('audio_track') or {}
            source = (at.get('source') or fmt.get('source') or '').lower()
            at_id = (at.get('id') or '').lower()
            at_name = (at.get('name') or '').lower()
            if 'dub' in source or 'dub' in at_id or 'dub' in at_name:
                source_rank = 2
            if 'orig' in source or 'orig' in at_id or 'orig' in at_name:
                source_rank = 0
        except Exception:
            pass

        # Language preference: original language or English variants first
        preferred_langs = ['en', 'en-us', 'en-gb']
        lang = (fmt.get('language') or '').lower()
        if original_lang:
            ol = str(original_lang).lower()
            lang_rank = 0 if (lang and lang == ol) else (0 if not lang and ol in preferred_langs else (1 if (lang and lang in preferred_langs) else 2))
        else:
            lang_rank = 0 if (lang and lang in preferred_langs) else 1

        # Container preference
        container_rank = 0 if fmt.get('ext') in ('m4a', 'mp4') else 1

        # Higher bitrate preferred (we invert by negating)
        abr = fmt.get('abr') or fmt.get('tbr') or 0
        bitrate_sort = -(int(abr) if isinstance(abr, (int, float)) else 0)

        return (source_rank, lang_rank, container_rank, bitrate_sort)

    @staticmethod
    def _normalize_lang(lang: str | None) -> str:
        try:
            if not lang:
                return ''
            return str(lang).strip().lower()
        except Exception:
            return ''

    @staticmethod
    def _is_dubbed(fmt: dict) -> bool:
        try:
            at = fmt.get('audio_track') or {}
            source = (at.get('source') or fmt.get('source') or '').lower()
            at_id = (at.get('id') or '').lower()
            at_name = (at.get('name') or '').lower()
            return ('dub' in source) or ('dub' in at_id) or ('dub' in at_name)
        except Exception:
            return False

    def _determine_preferred_language(self, info: dict, audio_formats: list[dict]) -> str | None:
        # Prefer explicitly provided original_language, else English variants if present
        orig = self._normalize_lang(info.get('original_language') or info.get('language'))
        if orig:
            return orig
        langs = {self._normalize_lang(f.get('language')) for f in (audio_formats or []) if f}
        for cand in ('en', 'en-us', 'en-gb'):
            if cand in langs:
                return cand
        return None

    def _pick_audio_format(self, info: dict, audio_formats: list[dict], requested_abr: int | None = None) -> dict | None:
        if not audio_formats:
            return None
        # Remove clearly dubbed tracks first
        non_dubbed = [f for f in audio_formats if not self._is_dubbed(f)] or audio_formats
        preferred_lang = self._determine_preferred_language(info, non_dubbed)
        ranked = sorted(non_dubbed, key=lambda f: self._score_audio_format(f, preferred_lang))
        if requested_abr:
            try:
                abr_int = int(requested_abr)
                for f in ranked:
                    br = f.get('abr') or f.get('tbr') or 0
                    try:
                        if int(br) <= abr_int:
                            return f
                    except Exception:
                        continue
            except Exception:
                pass
        return ranked[0]

    def create_temp_download_folder(self, timestamp: str) -> str:
        temp_folder = os.path.join(TEMP_DOWNLOAD_DIR, f"youtube_{timestamp}")
        os.makedirs(temp_folder, exist_ok=True)
        return temp_folder

    def clean_youtube_url(self, url: str) -> str:
        try:
            if 'youtube.com/watch' in url:
                if any(x in url for x in ['&list=', '&playlist=', '&start_radio=', '&pp=']):
                    video_id = url.split('v=')[1].split('&')[0]
                    return f"https://www.youtube.com/watch?v={video_id}"
            elif 'youtu.be/' in url:
                video_id = url.split('youtu.be/')[1].split('?')[0]
                return f"https://www.youtube.com/watch?v={video_id}"
            elif '/shorts/' in url:
                # Normalize Shorts URLs to standard watch URL
                try:
                    parts = url.split('/shorts/')[1]
                    video_id = parts.split('?')[0].split('/')[0]
                    if video_id:
                        return f"https://www.youtube.com/watch?v={video_id}"
                except Exception:
                    pass
            return url
        except Exception:
            return url

    def verify_and_fix_video_file(self, video_file: str, temp_folder: str) -> str:
        try:
            check_cmd = ['ffprobe', '-v', 'quiet', '-print_format', 'json', '-show_streams', video_file]
            result = subprocess.run(check_cmd, capture_output=True, text=True, timeout=30)
            if result.returncode == 0:
                import json as _json
                streams = _json.loads(result.stdout).get('streams', [])
                has_video = any(s.get('codec_type') == 'video' for s in streams)
                has_audio = any(s.get('codec_type') == 'audio' for s in streams)
                if has_video and has_audio:
                    return video_file
            fixed = os.path.join(temp_folder, 'fixed_video.mp4')
            fix_cmd = ['ffmpeg', '-i', video_file, '-c:v', 'libx264', '-c:a', 'aac', '-b:a', '192k', '-movflags', '+faststart', '-y', fixed]
            result = subprocess.run(fix_cmd, capture_output=True, text=True, timeout=120)
            if result.returncode == 0 and os.path.exists(fixed) and os.path.getsize(fixed) > 0:
                return fixed
            return video_file
        except Exception:
            return video_file

    def get_video_info(self, url: str):
        try:
            url = self.clean_youtube_url(url)
            ydl_opts = _build_ydl_opts()
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(url, download=False)
            if not info or 'entries' in info:
                return {'status': 'error', 'message': 'No single-video information found'}

            title = info.get('title') or 'Unknown'
            uploader = info.get('uploader') or info.get('channel') or 'Unknown'
            duration = info.get('duration') or 0
            thumbnail = info.get('thumbnail') or (info.get('thumbnails') or [{}])[-1].get('url')
            video_id = info.get('id')
            embed_url = f"https://www.youtube.com/embed/{video_id}" if video_id else None
            # Build a robust thumbnail list with fallbacks
            thumb_candidates = []
            # Provided thumbnails from yt-dlp
            for t in (info.get('thumbnails') or []):
                u = t.get('url')
                if u:
                    thumb_candidates.append(u)
            # Construct standard YouTube thumbnail URLs
            if video_id:
                bases = [
                    f"https://i.ytimg.com/vi/{video_id}/maxresdefault.jpg",
                    f"https://i.ytimg.com/vi/{video_id}/sddefault.jpg",
                    f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg",
                    f"https://i.ytimg.com/vi/{video_id}/mqdefault.jpg",
                    f"https://i.ytimg.com/vi/{video_id}/default.jpg",
                ]
                thumb_candidates.extend(bases)
            # Ensure https and unique order
            seen = set()
            thumbnails_list = []
            for u in thumb_candidates:
                if not u:
                    continue
                if u.startswith('//'):
                    u = 'https:' + u
                if u.startswith('http:'):
                    u = u.replace('http:', 'https:')
                if u not in seen:
                    seen.add(u)
                    thumbnails_list.append(u)

            formats = info.get('formats', []) or []
            # Separate formats
            video_formats = [f for f in formats if f.get('vcodec') not in (None, 'none') and (f.get('height') or 0) > 0]
            audio_formats = [f for f in formats if f.get('acodec') not in (None, 'none') and f.get('vcodec') in (None, 'none')]

            # Prefer original-language/English audio tracks and avoid dubbed tracks
            original_lang = info.get('original_language') or info.get('language')
            preferred_audio_formats = sorted(audio_formats, key=lambda f: self._score_audio_format(f, original_lang))

            # Choose best audio-only format (prefer m4a/mp4)
            def audio_key(f):
                return (0 if f.get('ext') in ('m4a', 'mp4') else 1, -(f.get('abr') or 0), -(f.get('tbr') or 0))
            preferred_audio_formats.sort(key=audio_key)
            chosen_audio = preferred_audio_formats[0] if preferred_audio_formats else None

            # Helper to estimate size in bytes
            def estimate_size_bytes(fmt, dur):
                if not fmt:
                    return 0
                size = fmt.get('filesize') or fmt.get('filesize_approx')
                if size:
                    return int(size)
                tbr = fmt.get('tbr') or fmt.get('abr')
                if tbr and dur:
                    try:
                        # tbr is in Kbps
                        return int((tbr * 1000 / 8) * dur)
                    except Exception:
                        return 0
                return 0

            # For each distinct height, pick a good video-only format and compute merged size with chosen_audio
            height_to_best_video = {}
            def video_key(f):
                return (0 if f.get('ext') == 'mp4' else 1, -(f.get('height') or 0), -(f.get('tbr') or 0))
            video_formats.sort(key=video_key)
            for f in video_formats:
                h = f.get('height')
                if not h:
                    continue
                if h not in height_to_best_video:
                    height_to_best_video[h] = f

            qualities = []
            for h, vf in height_to_best_video.items():
                v_size = estimate_size_bytes(vf, duration)
                a_size = estimate_size_bytes(chosen_audio, duration)
                total = (v_size or 0) + (a_size or 0)
                qualities.append({
                    'label': f"{h}p.mp4",
                    'height': h,
                    'size_bytes': total if total > 0 else None,
                    'fps': vf.get('fps') or vf.get('framerate')
                })

            # Sort by height desc and return explicit resolutions only
            qualities.sort(key=lambda x: x.get('height') or 0, reverse=True)

            # Build audio qualities list (MP3 target)
            audio_qualities = []
            seen_abr = set()
            for af in preferred_audio_formats:
                abr = af.get('abr') or af.get('tbr')
                if not abr:
                    continue
                abr_int = int(round(abr))
                if abr_int in seen_abr:
                    continue
                seen_abr.add(abr_int)
                # Estimate size for MP3 transcode at the same bitrate
                size_a = int((abr_int * 1000 / 8) * duration) if duration and abr_int else 0
                audio_qualities.append({
                    'label': f"{abr_int} kbps MP3",
                    'abr': abr_int,
                    'ext': 'mp3',
                    'size_bytes': size_a if size_a > 0 else None
                })
            audio_qualities.sort(key=lambda x: x.get('abr') or 0, reverse=True)

            return {
                'status': 'success',
                'title': title,
                'uploader': uploader,
                'duration': duration,
                'thumbnail': thumbnail,
                'thumbnails': thumbnails_list,
                'embed_url': embed_url,
                'qualities': qualities,
                'audio_qualities': audio_qualities,
            }
        except Exception as e:
            msg = str(e)
            if 'Precondition check failed' in msg or 'HTTP Error 400' in msg:
                return {'status': 'error', 'message': 'YouTube is blocking requests. Try again later.'}
            return {'status': 'error', 'message': f'YouTube error: {msg}'}

    def download_youtube_with_quality(self, url: str, quality: str, download_type: str = 'video', requested_abr: int | None = None):
        try:
            url = self.clean_youtube_url(url)
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            temp_folder = self.create_temp_download_folder(timestamp)

            requested_height = None
            try:
                if isinstance(quality, str) and quality.endswith('p'):
                    requested_height = int(quality.rstrip('p'))
            except Exception:
                requested_height = None

            info_opts = _build_ydl_opts()
            with yt_dlp.YoutubeDL(info_opts) as ydl:
                info = ydl.extract_info(url, download=False)
                if not info or 'entries' in info:
                    shutil.rmtree(temp_folder, ignore_errors=True)
                    return {'status': 'error', 'message': 'No single-video information found'}

                formats = info.get('formats', []) or []
                video_formats = [f for f in formats if f.get('vcodec') != 'none' and f.get('acodec') == 'none']
                audio_formats = [f for f in formats if f.get('acodec') != 'none' and f.get('vcodec') == 'none']

                # Pick audio by enumerating tracks and preferring original/English and non-dubbed
                chosen_audio = self._pick_audio_format(info, audio_formats, requested_abr=requested_abr)
                preferred_audio_formats = [chosen_audio] if chosen_audio else audio_formats

                def sort_video_key(f):
                    return (0 if f.get('ext') == 'mp4' else 1, -(f.get('height') or 0), -(f.get('tbr') or 0))

                if download_type == 'audio':
                    # Prefer best audio, then transcode to MP3 if needed
                    def audio_key(f):
                        return (0 if f.get('ext') in ('m4a', 'mp4') else 1, -(f.get('abr') or 0), -(f.get('tbr') or 0))
                    preferred_audio_formats.sort(key=audio_key)
                    if not chosen_audio:
                        chosen_audio = preferred_audio_formats[0] if preferred_audio_formats else None
                    if not chosen_audio:
                        shutil.rmtree(temp_folder, ignore_errors=True)
                        return {'status': 'error', 'message': 'No suitable audio format'}
                    # Download best audio and transcode to MP3 using ffmpeg
                    ydl_opts = _build_ydl_opts({
                        'format': chosen_audio['format_id'],
                        'outtmpl': os.path.join(temp_folder, '%(title)s.%(ext)s'),
                        'prefer_ffmpeg': True,
                        'ffmpeg_location': None,
                        'postprocessors': [{
                            'key': 'FFmpegExtractAudio',
                            'preferredcodec': 'mp3',
                            'preferredquality': str(int(requested_abr) if requested_abr else 192)
                        }],
                    })
                else:
                    chosen_video = None
                    if requested_height:
                        candidates = [f for f in video_formats if (f.get('height') or 0) <= requested_height]
                        if candidates:
                            candidates.sort(key=sort_video_key)
                            chosen_video = candidates[0]
                    if not chosen_video:
                        video_formats.sort(key=sort_video_key)
                        chosen_video = video_formats[0] if video_formats else None

                    # Prefer original-language/English for video merge
                    chosen_audio = self._pick_audio_format(info, audio_formats)
                    if not chosen_audio:
                        audio_formats.sort(key=lambda f: (0 if f.get('ext') in ('m4a', 'mp4') else 1, -(f.get('abr') or 0), -(f.get('tbr') or 0)))
                        chosen_audio = audio_formats[0] if audio_formats else None

                    if not chosen_video or not chosen_audio:
                        shutil.rmtree(temp_folder, ignore_errors=True)
                        return {'status': 'error', 'message': 'Could not select suitable video/audio formats'}

                    format_id = f"{chosen_video['format_id']}+{chosen_audio['format_id']}"
                    ydl_opts = _build_ydl_opts({
                        'format': format_id,
                        'outtmpl': os.path.join(temp_folder, '%(title)s.%(ext)s'),
                        'merge_output_format': 'mp4',
                        'prefer_ffmpeg': True,
                        'ffmpeg_location': None,
                    })

                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info2 = ydl.extract_info(url, download=True)
                    if not info2:
                        shutil.rmtree(temp_folder, ignore_errors=True)
                        return {'status': 'error', 'message': 'No video information found'}

                downloaded_files = [os.path.join(temp_folder, f) for f in os.listdir(temp_folder) if f.endswith(('.mp4', '.webm', '.mkv', '.m4a', '.mp3', '.opus'))]
                if not downloaded_files:
                    shutil.rmtree(temp_folder, ignore_errors=True)
                    return {'status': 'error', 'message': 'No video file was downloaded'}

                chosen_path = downloaded_files[0]
                if download_type != 'audio':
                    chosen_path = self.verify_and_fix_video_file(chosen_path, temp_folder)
                with open(chosen_path, 'rb') as f:
                    video_data = f.read()

                title = (info.get('title') or 'Unknown')
                uploader = (info.get('uploader') or 'Unknown')
                if download_type == 'audio':
                    ext = 'mp3'
                    # If yt-dlp created an mp3 file with a different name, find it
                    mp3_files = [p for p in downloaded_files if p.lower().endswith('.mp3')]
                    if mp3_files:
                        chosen_path = mp3_files[0]
                        with open(chosen_path, 'rb') as f:
                            video_data = f.read()
                    filename = _create_safe_filename(f"{title[:50]}.mp3")
                    content_type = 'audio/mpeg'
                else:
                    final_height = chosen_video.get('height') or 'unknown'
                    filename = _create_safe_filename(f"{title[:50]}_{final_height}p.mp4")
                    content_type = 'video/mp4'

                shutil.rmtree(temp_folder, ignore_errors=True)

                return {
                    'status': 'success',
                    'data': video_data,
                    'filename': filename,
                    'content_type': content_type,
                    'title': title,
                    'uploader': uploader,
                    'type': 'audio' if download_type == 'audio' else 'video'
                }
        except Exception as e:
            if 'temp_folder' in locals():
                shutil.rmtree(temp_folder, ignore_errors=True)
            msg = str(e)
            if 'Precondition check failed' in msg or 'HTTP Error 400' in msg:
                return {'status': 'error', 'message': 'YouTube is blocking requests. Try again later.'}
            return {'status': 'error', 'message': f'YouTube error: {msg}'}


downloader = YouTubeDownloader()

# Simple in-memory job store for progress reporting
JOBS: dict[str, dict] = {}

def _new_job() -> str:
    job_id = uuid.uuid4().hex
    JOBS[job_id] = {
        'status': 'queued',
        'progress': 0,
        'message': 'Queued',
        'filename': None,
        'content_type': None,
        'path': None,
        'type': None,
        'error': None,
    }
    return job_id

def _set_job(job_id: str, **kwargs):
    job = JOBS.get(job_id)
    if not job:
        return
    job.update(kwargs)


@app.route('/')
def index():
    return render_template('index.html')


@app.get('/healthz')
def healthz():
    # Lightweight health endpoint for Render
    return jsonify({'status': 'ok'}), 200


@app.route('/info', methods=['POST'])
def info():
    try:
        data = request.get_json(silent=True) or {}
        url = (data.get('url') or '').strip()
        if not url:
            return jsonify({'status': 'error', 'message': 'URL is required'})
        if not _is_youtube_url(url):
            return jsonify({'status': 'error', 'message': 'Link not supported'}), 400
        result = downloader.get_video_info(url)
        return jsonify(result)
    except Exception as e:
        return jsonify({'status': 'error', 'message': f'Server error: {str(e)}'})

@app.route('/download', methods=['POST'])
def download():
    try:
        data = request.get_json(silent=True) or {}
        url = (data.get('url') or '').strip()
        quality = data.get('quality') or data.get('height') or 'best'
        download_type = (data.get('type') or 'video').lower()
        requested_abr = data.get('abr')
        if not url:
            return jsonify({'status': 'error', 'message': 'URL is required'})
        if not _is_youtube_url(url):
            return jsonify({'status': 'error', 'message': 'Link not supported'}), 400

        result = downloader.download_youtube_with_quality(url, quality, download_type=download_type, requested_abr=requested_abr)
        if result and result.get('status') == 'success':
            resp = Response(
                result['data'],
                mimetype=result.get('content_type', 'application/octet-stream'),
                headers={
                    'Content-Disposition': f"attachment; filename=\"{result['filename']}\"",
                    'Content-Length': str(len(result['data'])),
                    'Content-Type': result.get('content_type', 'application/octet-stream'),
                    'Cache-Control': 'no-cache'
                }
            )
            return resp
        return jsonify(result or {'status': 'error', 'message': 'Unknown error'})
    except Exception as e:
        return jsonify({'status': 'error', 'message': f'Server error: {str(e)}'})


@app.route('/start-download', methods=['POST'])
def start_download():
    try:
        data = request.get_json(silent=True) or {}
        url = (data.get('url') or '').strip()
        quality = data.get('quality') or data.get('height') or 'best'
        download_type = (data.get('type') or 'video').lower()
        requested_abr = data.get('abr')
        title_hint = (data.get('title') or '').strip() or 'download'
        if not url:
            return jsonify({'status': 'error', 'message': 'URL is required'})
        if not _is_youtube_url(url):
            return jsonify({'status': 'error', 'message': 'Link not supported'}), 400

        job_id = _new_job()
        _set_job(job_id, status='processing', message='Starting', type=download_type)

        def run_job():
            try:
                timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                temp_folder = downloader.create_temp_download_folder(timestamp)

                # Prepare info to choose formats
                info_opts = _build_ydl_opts()
                with yt_dlp.YoutubeDL(info_opts) as ydl:
                    info = ydl.extract_info(downloader.clean_youtube_url(url), download=False)
                if not info or 'entries' in info:
                    shutil.rmtree(temp_folder, ignore_errors=True)
                    _set_job(job_id, status='error', error='No single-video information found')
                    return

                formats = info.get('formats', []) or []
                video_formats = [f for f in formats if f.get('vcodec') != 'none' and f.get('acodec') == 'none']
                audio_formats = [f for f in formats if f.get('acodec') != 'none' and f.get('vcodec') == 'none']

                def sort_video_key(f):
                    return (0 if f.get('ext') == 'mp4' else 1, -(f.get('height') or 0), -(f.get('tbr') or 0))

                ydl_opts = _build_ydl_opts({
                    'outtmpl': os.path.join(temp_folder, '%(title)s.%(ext)s'),
                    'prefer_ffmpeg': True,
                    'ffmpeg_location': None,
                })

                # progress hook to update job
                def hook(d):
                    try:
                        if d.get('status') == 'downloading':
                            total = d.get('total_bytes') or d.get('total_bytes_estimate') or 0
                            downloaded = d.get('downloaded_bytes') or 0
                            pct = int(downloaded * 100 / total) if total else 0
                            _set_job(job_id, progress=max(0, min(99, pct)), message='Downloading')
                        elif d.get('status') == 'finished':
                            _set_job(job_id, progress=99, message='Post-processing')
                        elif d.get('status') == 'error':
                            _set_job(job_id, status='error', error=d.get('errmsg') or 'Download error')
                    except Exception:
                        pass

                ydl_opts['progress_hooks'] = [hook]

                if download_type == 'audio':
                    def audio_key(f):
                        return (0 if f.get('ext') in ('m4a', 'mp4') else 1, -(f.get('abr') or 0), -(f.get('tbr') or 0))
                    # Enumerate audio tracks and choose original-language when possible
                    chosen_audio = downloader._pick_audio_format(info, audio_formats, requested_abr=requested_abr)
                    if not chosen_audio:
                        audio_formats.sort(key=audio_key)
                        chosen_audio = audio_formats[0] if audio_formats else None
                    if not chosen_audio:
                        shutil.rmtree(temp_folder, ignore_errors=True)
                        _set_job(job_id, status='error', error='No suitable audio format')
                        return
                    # Precompute filename early and expose to job status
                    vid_title = info.get('title') or title_hint
                    filename = _create_safe_filename(f"{vid_title[:50]}.mp3")
                    _set_job(job_id, filename=filename, content_type='audio/mpeg', message='Starting download')
                    ydl_opts.update({
                        'format': chosen_audio['format_id'],
                        'postprocessors': [{
                            'key': 'FFmpegExtractAudio',
                            'preferredcodec': 'mp3',
                            'preferredquality': str(int(requested_abr) if requested_abr else 192)
                        }],
                    })
                else:
                    chosen_video = None
                    requested_height = None
                    try:
                        if isinstance(quality, str) and quality.endswith('p'):
                            requested_height = int(quality.rstrip('p'))
                    except Exception:
                        requested_height = None
                    if requested_height:
                        candidates = [f for f in video_formats if (f.get('height') or 0) <= requested_height]
                        if candidates:
                            candidates.sort(key=sort_video_key)
                            chosen_video = candidates[0]
                    if not chosen_video:
                        video_formats.sort(key=sort_video_key)
                        chosen_video = video_formats[0] if video_formats else None
                    # Prefer original-language audio track for video downloads too
                    chosen_audio = downloader._pick_audio_format(info, audio_formats)
                    if not chosen_audio:
                        audio_formats.sort(key=lambda f: (0 if f.get('ext') in ('m4a', 'mp4') else 1, -(f.get('abr') or 0), -(f.get('tbr') or 0)))
                        chosen_audio = audio_formats[0] if audio_formats else None
                    if not chosen_video or not chosen_audio:
                        shutil.rmtree(temp_folder, ignore_errors=True)
                        _set_job(job_id, status='error', error='Could not select suitable video/audio formats')
                        return
                    format_id = f"{chosen_video['format_id']}+{chosen_audio['format_id']}"
                    # Precompute filename early and expose to job status
                    vid_title = info.get('title') or title_hint
                    final_height = (chosen_video.get('height') or requested_height or 'best')
                    filename = _create_safe_filename(f"{vid_title[:50]}_{final_height}p.mp4")
                    _set_job(job_id, filename=filename, content_type='video/mp4', message='Starting download')
                    ydl_opts.update({
                        'format': format_id,
                        'merge_output_format': 'mp4',
                    })

                with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                    info2 = ydl.extract_info(url, download=True)
                # Determine output file
                downloaded_files = [os.path.join(temp_folder, f) for f in os.listdir(temp_folder) if f.endswith(('.mp4', '.webm', '.mkv', '.m4a', '.mp3', '.opus'))]
                if not downloaded_files:
                    shutil.rmtree(temp_folder, ignore_errors=True)
                    _set_job(job_id, status='error', error='No file was downloaded')
                    return
                chosen_path = downloaded_files[0]
                if download_type != 'audio':
                    chosen_path = downloader.verify_and_fix_video_file(chosen_path, temp_folder)

                # Finalize job metadata
                content_type = 'audio/mpeg' if download_type == 'audio' else 'video/mp4'
                _set_job(job_id, status='ready', progress=100, message='Ready', content_type=content_type, path=chosen_path)
            except Exception as e:
                _set_job(job_id, status='error', error=str(e))

        threading.Thread(target=run_job, daemon=True).start()
        return jsonify({'status': 'success', 'job_id': job_id})
    except Exception as e:
        return jsonify({'status': 'error', 'message': f'Server error: {str(e)}'})


@app.route('/job-status')
def job_status():
    job_id = request.args.get('id', '')
    job = JOBS.get(job_id)
    if not job:
        return jsonify({'status': 'error', 'message': 'Invalid job id'}), 404
    return jsonify({'status': job.get('status'), 'progress': job.get('progress'), 'message': job.get('message'), 'filename': job.get('filename'), 'type': job.get('type')})


@app.route('/fetch-file')
def fetch_file():
    job_id = request.args.get('id', '')
    job = JOBS.get(job_id)
    if not job or job.get('status') != 'ready' or not job.get('path'):
        return jsonify({'status': 'error', 'message': 'File not ready'}), 400
    path = job['path']
    try:
        with open(path, 'rb') as f:
            data = f.read()
        resp = Response(
            data,
            mimetype=job.get('content_type', 'application/octet-stream'),
            headers={
                'Content-Disposition': f"attachment; filename=\"{job.get('filename')}\"",
                'Content-Length': str(len(data)),
                'Cache-Control': 'no-cache'
            }
        )
        # Cleanup folder on success
        try:
            folder = os.path.dirname(path)
            shutil.rmtree(folder, ignore_errors=True)
        except Exception:
            pass
        # Mark job as completed
        _set_job(job_id, status='completed')
        return resp
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)}), 500


@app.route('/get-progressive', methods=['POST'])
def get_progressive():
    # Optional helper for clients wanting a single progressive MP4 stream up to a max height
    try:
        data = request.get_json(silent=True) or {}
        url = (data.get('url') or '').strip()
        max_height = (data.get('max_height') or '').strip() or None
        if not url:
            return jsonify({'status': 'error', 'message': 'URL is required'})

        url = downloader.clean_youtube_url(url)
        ydl_opts = _build_ydl_opts()
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
        if not info or 'entries' in info:
            return jsonify({'status': 'error', 'message': 'No single-video information found'})

        formats = info.get('formats', []) or []
        progressive = [f for f in formats if f.get('vcodec') != 'none' and f.get('acodec') != 'none' and f.get('ext') == 'mp4']
        if not progressive:
            return jsonify({'status': 'error', 'message': 'No progressive MP4 stream available'})

        def choose(formats_list, mh):
            if mh:
                try:
                    mh_val = int(mh)
                except Exception:
                    mh_val = None
            else:
                mh_val = None
            if mh_val:
                candidates = [f for f in formats_list if (f.get('height') or 0) <= mh_val]
                if candidates:
                    candidates.sort(key=lambda f: (-(f.get('height') or 0), -(f.get('tbr') or 0)))
                    return candidates[0]
            formats_list.sort(key=lambda f: (-(f.get('height') or 0), -(f.get('tbr') or 0)))
            return formats_list[0]

        chosen = choose(progressive, max_height)
        return jsonify({
            'status': 'success',
            'stream_url': chosen['url'],
            'height': chosen.get('height'),
            'title': info.get('title', 'Video'),
        })
    except Exception as e:
        return jsonify({'status': 'error', 'message': f'Failed to get progressive stream: {str(e)}'})


@app.route('/assets/<path:filename>')
def assets(filename: str):
    try:
        # Serve from project-relative Icons directory
        icons_dir = os.path.join('.', 'Icons')
        return send_from_directory(icons_dir, filename)
    except Exception:
        return jsonify({'status': 'error', 'message': 'File not found'}), 404


if __name__ == '__main__':
    port = int(os.environ.get('PORT', '5001'))
    debug = os.getenv('FLASK_DEBUG', '0') in ('1', 'true', 'True')
    app.run(host='0.0.0.0', port=port, debug=debug)


