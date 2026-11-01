"""
Rename Bot PRO (Pyrogram / Pyrofork)

Install:
    pip install pyrofork tgcrypto        # (or: pip install pyrogram tgcrypto)
    sudo apt install ffmpeg              # ffmpeg + ffprobe required

Required env vars:
    API_ID, API_HASH, BOT_TOKEN
Optional env vars:
    ADMINS            comma separated admin user ids  (e.g. 12345,67890)
    DEFAULT_TAG       default audio tag               (default @RvN_Aniplix)
    SETTINGS_PIC      image URL / file_id for /settings panel
    DONATE_TEXT       text shown by /donate
    PREMIUM_TEXT      text shown by /premium
    FREE_MODE         1 = no limits for anyone
    FREE_DAILY_LIMIT  renames/day for free users      (default 5)
    SHORTENER_URL     shortener domain for /task      (e.g. gplinks.in)
    SHORTENER_API     shortener API key
    SPLIT_LIMIT_GB    split files above this size     (default 1.9)
    MAX_CONCURRENT    parallel tasks                  (default 2)
    DB_PATH           sqlite file path                (default rename_bot.db)

Run:
    python rename_bot_pro.py
"""
import os
import re
import sys
import json
import math
import html
import time
import random
import shutil
import asyncio
import sqlite3
import secrets
import tempfile
import urllib.parse
import urllib.request

from pyrogram import Client, filters, idle, enums, StopTransmission
from pyrogram.errors import FloodWait
from pyrogram.types import (
    Message,
    CallbackQuery,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
    BotCommand,
    ForceReply,
    InputMediaPhoto,
)

# ───────────────────────────── CONFIG ─────────────────────────────
API_ID = int(os.environ.get("API_ID", "0"))
API_HASH = os.environ.get("API_HASH", "")
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")

ADMINS = {int(x) for x in os.environ.get("ADMINS", "").replace(" ", "").split(",") if x.isdigit()}
DEFAULT_TAG = os.environ.get("DEFAULT_TAG", "@RvN_Aniplix")
SETTINGS_PIC = os.environ.get("SETTINGS_PIC", "")
DONATE_TEXT = os.environ.get("DONATE_TEXT", "💖 Thanks for supporting! Contact the owner to donate.")
PREMIUM_TEXT = os.environ.get("PREMIUM_TEXT", "💎 Premium = unlimited renames.\nContact the owner to upgrade.")
FREE_MODE = os.environ.get("FREE_MODE", "0") == "1"
FREE_DAILY_LIMIT = int(os.environ.get("FREE_DAILY_LIMIT", "5"))
SHORTENER_URL = os.environ.get("SHORTENER_URL", "")
SHORTENER_API = os.environ.get("SHORTENER_API", "")
TASK_HOURS = 24
MIN_TASK_SECONDS = 15

SPLIT_LIMIT = int(float(os.environ.get("SPLIT_LIMIT_GB", "1.9")) * 1024 ** 3)
MAX_TOTAL_BYTES = 20 * 1024 ** 3
MAX_CONCURRENT = int(os.environ.get("MAX_CONCURRENT", "2"))
DB_PATH = os.environ.get("DB_PATH", "rename_bot.db")

DOWNLOAD_DIR = os.path.join(os.path.expanduser("~"), "bot_downloads")
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

VIDEO_EXTS = (".mkv", ".mp4", ".mov", ".webm")

# "Encoded by" text burned into the first seconds of the video (needs re-encode)
ENCODE_TEXT = os.environ.get("ENCODE_TEXT", "Encoded by RvN_Aniplix")
ENC_SECONDS = float(os.environ.get("ENC_SECONDS", "2"))
ENC_CRF = int(os.environ.get("ENC_CRF", "20"))
ENC_PRESET = os.environ.get("ENC_PRESET", "veryfast")
ENC_FONT = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"

app = Client(
    "rename_bot",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN,
    max_concurrent_transmissions=8,
)

BOT_START_TIME = time.time()
BOT_USERNAME = ""

pending_file = {}   # uid -> Message waiting for new name
awaiting = {}       # uid -> {"kind": ...} waiting for a text input
cancel_flags = {}   # uid -> True
active_tasks = set()
task_state = {}     # uid -> progress throttling state
task_tokens = {}    # token -> {"uid", "t"}
junk = {}           # uid -> messages to delete after a successful rename
task_sem = asyncio.Semaphore(MAX_CONCURRENT)


class DownloadCancelled(Exception):
    pass


# ───────────────────────────── DATABASE ─────────────────────────────
db = sqlite3.connect(DB_PATH, check_same_thread=False)
db.row_factory = sqlite3.Row
db.execute(
    """CREATE TABLE IF NOT EXISTS users(
        id INTEGER PRIMARY KEY,
        name TEXT DEFAULT '', username TEXT DEFAULT '', joined INTEGER DEFAULT 0,
        thumb TEXT, caption TEXT, upload_type TEXT DEFAULT 'document',
        sample INTEGER DEFAULT 0, screenshot INTEGER DEFAULT 0,
        dump_mode INTEGER DEFAULT 0, dump_channel TEXT,
        random_thumb INTEGER DEFAULT 0, meta_on INTEGER DEFAULT 1,
        audio_tag TEXT, sub_tag TEXT DEFAULT '',
        premium_until INTEGER DEFAULT 0, verified_until INTEGER DEFAULT 0,
        renames INTEGER DEFAULT 0, day TEXT DEFAULT '', day_count INTEGER DEFAULT 0,
        banned INTEGER DEFAULT 0, enc_tag INTEGER DEFAULT 0, auto_del INTEGER DEFAULT 1
    )"""
)
for _col in ("enc_tag INTEGER DEFAULT 0", "auto_del INTEGER DEFAULT 1"):  # migrate older databases
    try:
        db.execute(f"ALTER TABLE users ADD COLUMN {_col}")
    except sqlite3.OperationalError:
        pass
db.commit()

USER_COLS = {
    "name", "username", "thumb", "caption", "upload_type", "sample", "screenshot",
    "dump_mode", "dump_channel", "random_thumb", "meta_on", "audio_tag", "sub_tag",
    "premium_until", "verified_until", "renames", "day", "day_count", "banned", "enc_tag", "auto_del",
}


def get_user(uid):
    row = db.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    if row is None:
        db.execute("INSERT INTO users(id, joined) VALUES(?, ?)", (uid, int(time.time())))
        db.commit()
        row = db.execute("SELECT * FROM users WHERE id=?", (uid,)).fetchone()
    return dict(row)


def set_user(uid, **kw):
    bad = [k for k in kw if k not in USER_COLS]
    if bad:
        raise ValueError(f"bad columns: {bad}")
    get_user(uid)
    sets = ", ".join(f"{k}=?" for k in kw)
    db.execute(f"UPDATE users SET {sets} WHERE id=?", (*kw.values(), uid))
    db.commit()


def touch(tg_user):
    u = get_user(tg_user.id)
    name = tg_user.first_name or ""
    uname = tg_user.username or ""
    if u["name"] != name or u["username"] != uname:
        set_user(tg_user.id, name=name, username=uname)
        u["name"], u["username"] = name, uname
    return u


async def guard(message: Message):
    """Return user dict, or None if banned / no user."""
    if not message.from_user:
        return None
    u = touch(message.from_user)
    if u["banned"]:
        await message.reply_text("🚫 You are banned from using this bot.")
        return None
    return u


# ───────────────────────────── PLANS ─────────────────────────────
def today():
    return time.strftime("%Y-%m-%d", time.gmtime())


def fmt_date(ts):
    return time.strftime("%d %b %Y, %H:%M UTC", time.gmtime(ts))


def has_unlimited(u):
    now = time.time()
    return FREE_MODE or u["id"] in ADMINS or u["premium_until"] > now or u["verified_until"] > now


def used_today(u):
    return u["day_count"] if u["day"] == today() else 0


def limit_reached(u):
    return not has_unlimited(u) and used_today(u) >= FREE_DAILY_LIMIT


def plan_name(u):
    now = time.time()
    if u["id"] in ADMINS:
        return "👑 Admin"
    if u["premium_until"] > now:
        return f"💎 Premium (until {fmt_date(u['premium_until'])})"
    if u["verified_until"] > now:
        return f"✨ Task verified (until {fmt_date(u['verified_until'])})"
    if FREE_MODE:
        return "🆓 Free (unlimited)"
    return f"🆓 Free ({FREE_DAILY_LIMIT} renames/day)"


def count_rename(uid):
    u = get_user(uid)
    t = today()
    dc = u["day_count"] + 1 if u["day"] == t else 1
    set_user(uid, renames=u["renames"] + 1, day=t, day_count=dc)


LIMIT_MSG = (
    f"⚠️ Daily limit reached ({FREE_DAILY_LIMIT} renames).\n\n"
    "• /task - complete a simple task for 24h free access\n"
    "• /premium - upgrade for unlimited use"
)

# ───────────────────────────── CONSTANTS ─────────────────────────────
LANG_NAMES = {
    "tam": "Tamil", "eng": "English", "hin": "Hindi", "tel": "Telugu",
    "mal": "Malayalam", "kan": "Kannada", "mar": "Marathi", "ben": "Bengali",
    "guj": "Gujarati", "pan": "Punjabi", "urd": "Urdu", "ori": "Odia",
    "asm": "Assamese", "san": "Sanskrit", "nep": "Nepali", "sin": "Sinhala",
    "jpn": "Japanese", "kor": "Korean", "chi": "Chinese", "zho": "Chinese",
    "tha": "Thai", "vie": "Vietnamese", "ind": "Indonesian", "may": "Malay",
    "msa": "Malay", "fil": "Filipino", "tgl": "Filipino", "khm": "Khmer",
    "lao": "Lao", "bur": "Burmese", "mya": "Burmese",
    "spa": "Spanish", "fre": "French", "fra": "French", "ger": "German",
    "deu": "German", "ita": "Italian", "por": "Portuguese", "rus": "Russian",
    "dut": "Dutch", "nld": "Dutch", "gre": "Greek", "ell": "Greek",
    "pol": "Polish", "swe": "Swedish", "nor": "Norwegian", "dan": "Danish",
    "fin": "Finnish", "cze": "Czech", "ces": "Czech", "hun": "Hungarian",
    "rom": "Romanian", "ron": "Romanian", "ukr": "Ukrainian", "bul": "Bulgarian",
    "ara": "Arabic", "heb": "Hebrew", "per": "Persian", "fas": "Persian",
    "tur": "Turkish", "und": "Unknown",
}
CODEC_NAMES = {
    "ac3": "DD", "eac3": "DDP", "dts": "DTS", "truehd": "TrueHD",
    "aac": "AAC", "mp3": "MP3", "flac": "FLAC", "opus": "OPUS",
    "vorbis": "VORBIS", "pcm_s16le": "PCM", "pcm_s24le": "PCM",
}
CHANNEL_LAYOUTS = {1: "1.0", 2: "2.0", 3: "2.1", 6: "5.1", 7: "6.1", 8: "7.1"}
MP4_INCOMPATIBLE_AUDIO = {"truehd", "dts", "vorbis", "flac"}
MP4_INCOMPATIBLE_SUBTITLE = {"ass", "ssa", "hdmv_pgs_subtitle", "dvd_subtitle", "dvb_subtitle"}


# ───────────────────────────── HELPERS ─────────────────────────────
def human_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{int(n)} B" if unit == "B" else f"{n:.2f} {unit}"
        n /= 1024


def format_time(seconds):
    seconds = int(seconds)
    if seconds < 60:
        return f"{seconds}s"
    m, s = divmod(seconds, 60)
    if m < 60:
        return f"{m}m {s}s"
    h, m = divmod(m, 60)
    return f"{h}h {m}m {s}s"


def make_progress_bar(pct, length=20):
    filled = int(pct / 100 * length)
    return "■" * filled + "□" * (length - filled)


def sanitize_filename(name):
    name = os.path.basename(name.replace("\\", "/").strip())
    name = re.sub(r'[<>:"|?*\x00-\x1f]', "_", name).strip(" .")
    base, ext = os.path.splitext(name)
    if len(name.encode()) > 200:
        keep = 200 - len(ext.encode())
        base = base.encode()[:keep].decode(errors="ignore")
        name = base + ext
    return name or "file"


def get_media(msg: Message):
    return msg.document or msg.video or msg.audio


def get_original_filename(msg: Message):
    media = get_media(msg)
    if msg.document:
        return media.file_name or "file"
    if msg.video:
        return media.file_name or "video.mp4"
    if msg.audio:
        return media.file_name or "audio.mp3"
    return "file"


def audio_label(stream):
    codec = (stream.get("codec_name") or "").lower()
    codec_label = CODEC_NAMES.get(codec, codec.upper() if codec else "")
    ch = stream.get("channels")
    ch_label = CHANNEL_LAYOUTS.get(ch, f"{ch}ch" if ch else "")
    return " ".join(p for p in (codec_label, ch_label) if p)


def build_caption(u, name, size):
    tpl = u.get("caption")
    if tpl:
        ext = os.path.splitext(name)[1].lstrip(".")
        text = (
            tpl.replace("{filename}", html.escape(name))
            .replace("{size}", human_size(size))
            .replace("{ext}", html.escape(ext))
        )
        return text, enums.ParseMode.HTML
    return f"<b>{html.escape(name)}</b>", enums.ParseMode.HTML


def dump_target(u):
    ch = (u.get("dump_channel") or "").strip()
    if not ch:
        return None
    return int(ch) if ch.lstrip("-").isdigit() else ch


def join_hint(name, n):
    win = "+".join(f'"{name}.{i:03d}"' for i in range(1, n + 1))
    return (
        f"Join parts:\nLinux/Mac: cat \"{name}\".* > \"{name}\"\n"
        f"Windows: copy /b {win} \"{name}\""
    )


# ───────────────────────────── PROGRESS UI ─────────────────────────────
def task_markup(uid):
    return InlineKeyboardMarkup(
        [[
            InlineKeyboardButton("✖️ Cancel", callback_data=f"cancel_{uid}"),
            InlineKeyboardButton("🔄 Refresh", callback_data=f"refresh_{uid}"),
        ]]
    )


async def progress(current, total, status_msg, label, start_time, state, user_id):
    if cancel_flags.get(user_id):
        raise StopTransmission
    total = total or 1
    now = time.time()
    if not state.get("force") and now - state.get("last_update", 0) < 3 and current != total:
        return
    state["force"] = False
    state["last_update"] = now

    pct = current * 100 / total
    elapsed = now - start_time
    speed = current / (elapsed + 0.001)
    eta = (total - current) / speed if speed > 0 else 0

    text = (
        f"{label}\n\n"
        f"{make_progress_bar(pct)}\n\n"
        f"🔗 Size : {human_size(current)} | {human_size(total)}\n"
        f"⏳ Done : {pct:.2f}%\n"
        f"🚀 Speed : {human_size(speed)}/s\n"
        f"⏰ ETA : {format_time(eta)}"
    )
    try:
        await status_msg.edit_text(text, reply_markup=task_markup(user_id))
    except Exception:
        pass


# ───────────────────────────── FFMPEG ─────────────────────────────
async def run_cmd(cmd):
    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    out, err = await proc.communicate()
    return proc.returncode, out, err


async def run_ffmpeg(cmd, uid=None):
    """Run ffmpeg; kills the process if the user presses Cancel."""
    cmd = [cmd[0], "-hide_banner", "-loglevel", "error"] + cmd[1:]
    proc = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE
    )
    comm = asyncio.ensure_future(proc.communicate())
    while True:
        done, _ = await asyncio.wait({comm}, timeout=1)
        if done:
            break
        if uid is not None and cancel_flags.get(uid):
            proc.kill()
            await comm
            raise DownloadCancelled()
    _, stderr = comm.result()
    if proc.returncode != 0:
        raise RuntimeError(stderr.decode(errors="ignore")[-800:])


async def probe_json(path, *args):
    _, out, _ = await run_cmd(
        ["ffprobe", "-v", "quiet", "-print_format", "json", *args, path]
    )
    try:
        return json.loads(out or b"{}")
    except ValueError:
        return {}


async def probe_streams(path):
    return (await probe_json(path, "-show_streams")).get("streams", [])


async def probe_duration(path):
    data = await probe_json(path, "-show_format")
    try:
        return float(data.get("format", {}).get("duration", 0) or 0)
    except ValueError:
        return 0.0


async def video_info(path):
    """(duration, width, height) for send_video."""
    dur = int(await probe_duration(path))
    w = h = 0
    for s in await probe_streams(path):
        if s.get("codec_type") == "video" and not (s.get("disposition") or {}).get("attached_pic"):
            w, h = s.get("width", 0) or 0, s.get("height", 0) or 0
            break
    return dur, w, h


def titles_for_streams(streams, tag, sub_tag):
    audio_titles, sub_titles = [], []
    for s in streams:
        ct = s.get("codec_type")
        lang_code = ((s.get("tags") or {}).get("language") or "und").lower()
        lang = LANG_NAMES.get(lang_code, lang_code.title())
        if ct == "audio":
            audio_titles.append(" ".join(p for p in (tag, lang, audio_label(s)) if p))
        elif ct == "subtitle":
            sub_titles.append(f"{sub_tag} {lang}".strip() if sub_tag else "")
    return audio_titles, sub_titles


def meta_args(streams, u):
    """-metadata args. Empty subtitle title is forced so old branding is cleared."""
    if not u["meta_on"]:
        return []
    tag = u["audio_tag"] or DEFAULT_TAG
    sub_tag = u["sub_tag"] or ""
    a_titles, s_titles = titles_for_streams(streams, tag, sub_tag)
    args = []
    for i, t in enumerate(a_titles):
        args += [f"-metadata:s:a:{i}", f"title={t}"]
    for i, t in enumerate(s_titles):
        args += [f"-metadata:s:s:{i}", f"title={t}"]
    return args


def build_fast_cmd(inp, out, streams, u):
    return ["ffmpeg", "-y", "-i", inp, "-map", "0", "-c", "copy", *meta_args(streams, u), out]


def enc_filter():
    text = re.sub(r"[\\':%]", "", ENCODE_TEXT)
    return (
        f"drawtext=fontfile={ENC_FONT}:text='{text}':fontcolor=white:fontsize=h/18:"
        "box=1:boxcolor=black@0.55:boxborderw=12:x=(w-text_w)/2:y=h-text_h-h/10:"
        f"enable='between(t,0,{ENC_SECONDS})'"
    )


def build_safe_cmd(inp, out, streams, u, target_ext, enc=False):
    to_mp4 = target_ext == ".mp4"
    cmd = ["ffmpeg", "-y", "-i", inp]
    if enc:
        # re-encode video with the "Encoded by" text, copy everything else
        cmd += ["-map", "0:v:0", "-map", "0:a?", "-map", "0:s?"]
        if not to_mp4:
            cmd += ["-map", "0:t?"]
        cmd += ["-vf", enc_filter(), "-c:v", "libx264", "-preset", ENC_PRESET,
                "-crf", str(ENC_CRF), "-pix_fmt", "yuv420p"]
    else:
        if to_mp4:
            cmd += ["-map", "0:v", "-map", "0:a?", "-map", "0:s?"]
        else:
            cmd += ["-map", "0"]
        cmd += ["-c:v", "copy"]

    a_idx = s_idx = 0
    for s in streams:
        ct = s.get("codec_type")
        cn = (s.get("codec_name") or "").lower()
        if ct == "audio":
            if to_mp4 and cn in MP4_INCOMPATIBLE_AUDIO:
                cmd += [f"-c:a:{a_idx}", "aac", f"-b:a:{a_idx}", "192k"]
            else:
                cmd += [f"-c:a:{a_idx}", "copy"]
            a_idx += 1
        elif ct == "subtitle":
            if to_mp4 and cn in MP4_INCOMPATIBLE_SUBTITLE:
                cmd += [f"-c:s:{s_idx}", "mov_text"]
            else:
                cmd += [f"-c:s:{s_idx}", "copy"]
            s_idx += 1
    cmd += meta_args(streams, u)
    cmd.append(out)
    return cmd


async def convert_and_rename(inp, out, u, uid):
    streams = await probe_streams(inp)
    target_ext = os.path.splitext(out)[1].lower()
    if u["enc_tag"] and target_ext != ".webm":
        await run_ffmpeg(build_safe_cmd(inp, out, streams, u, target_ext, enc=True), uid)
        return
    try:
        await run_ffmpeg(build_fast_cmd(inp, out, streams, u), uid)
        return
    except RuntimeError:
        if os.path.exists(out):
            os.remove(out)
    await run_ffmpeg(build_safe_cmd(inp, out, streams, u, target_ext), uid)


async def extract_frame(video, ts, out, vf, uid=None):
    await run_ffmpeg(
        ["ffmpeg", "-y", "-ss", f"{ts:.2f}", "-i", video, "-frames:v", "1", "-vf", vf, "-q:v", "3", out],
        uid,
    )


async def make_thumb(src, out, square, uid=None):
    if square:
        vf = ("scale=320:320:force_original_aspect_ratio=decrease,"
              "pad=320:320:(ow-iw)/2:(oh-ih)/2:color=black")
    else:
        vf = "scale=320:-2"
    await run_ffmpeg(["ffmpeg", "-y", "-i", src, "-vf", vf, "-q:v", "5", out], uid)
    return out


async def generate_screenshots(video, outdir, dur, uid, count=5):
    paths = []
    if dur <= 0:
        return paths
    for i in range(count):
        ts = dur * (i + 1) / (count + 1)
        out = os.path.join(outdir, f"shot_{i + 1}.jpg")
        try:
            await extract_frame(video, ts, out, "scale=1280:-2", uid)
            paths.append(out)
        except DownloadCancelled:
            raise
        except RuntimeError:
            continue
    return paths


async def generate_sample_video(video, out, dur, uid, length=30):
    start = max(0, min(dur * 0.1, dur - length)) if dur > length else 0
    await run_ffmpeg(
        ["ffmpeg", "-y", "-ss", f"{start:.2f}", "-i", video, "-t", str(length),
         "-map", "0:v:0", "-map", "0:a:0?", "-c:v", "copy", "-c:a", "aac", "-b:a", "128k",
         "-sn", "-movflags", "+faststart", out],
        uid,
    )
    return out


# ───────────────────────────── SPLITTING ─────────────────────────────
def make_part_filename(name, n):
    base, ext = os.path.splitext(name)
    return f"{base} - Part {n}{ext}"


async def split_video(path, n, uid):
    dur = await probe_duration(path)
    if dur <= 0:
        return None
    base, ext = os.path.splitext(path)
    seg = dur / n
    parts = []
    for i in range(n):
        out = f"{base}.part{i + 1}{ext}"
        cmd = ["ffmpeg", "-y", "-ss", f"{seg * i:.3f}", "-i", path]
        if i < n - 1:
            cmd += ["-t", f"{seg:.3f}"]
        cmd += ["-map", "0", "-c", "copy", "-avoid_negative_ts", "make_zero", out]
        await run_ffmpeg(cmd, uid)
        parts.append(out)
    return parts


async def split_video_by_size(path, limit, uid):
    """Playable parts, each guaranteed <= limit (retries with more parts)."""
    size = os.path.getsize(path)
    n = max(2, math.ceil(size / limit * 1.08))
    for _ in range(6):
        parts = await split_video(path, n, uid)
        if parts is None:
            return None
        if all(os.path.getsize(p) <= limit for p in parts):
            return parts
        for p in parts:
            if os.path.exists(p):
                os.remove(p)
        n += 1
    return None


def _split_file_sync(path, part_size, buf=8 * 1024 * 1024):
    parts, num, written, out = [], 1, 0, None
    try:
        with open(path, "rb") as f:
            while True:
                if out is None:
                    p = f"{path}.{num:03d}"
                    out = open(p, "wb")
                    parts.append(p)
                    written = 0
                data = f.read(min(buf, part_size - written))
                if not data:
                    break
                out.write(data)
                written += len(data)
                if written >= part_size:
                    out.close()
                    out = None
                    num += 1
    finally:
        if out:
            out.close()
    return parts


async def split_file(path, part_size):
    return await asyncio.get_running_loop().run_in_executor(None, _split_file_sync, path, part_size)


# ───────────────────────────── MAIN PROCESS ─────────────────────────────
async def process_file(client, message: Message, file_msg: Message, target_name: str, extra=None):
    uid = message.from_user.id
    chat_id = message.chat.id
    u = get_user(uid)

    if uid in active_tasks:
        pending_file[uid] = file_msg
        junk[uid] = list(extra or [])
        await message.reply_text("⏳ You already have a task running. Wait or cancel it, then send the name again.")
        return

    active_tasks.add(uid)
    cancel_flags.pop(uid, None)
    state = task_state[uid] = {"last_update": 0, "force": False}
    status = await message.reply_text(
        "⏳ Queued..." if task_sem.locked() else "🚀 Preparing...",
        reply_markup=task_markup(uid),
    )
    workdir = None

    try:
        async with task_sem:
            workdir = tempfile.mkdtemp(prefix=f"{uid}_", dir=DOWNLOAD_DIR)
            media = get_media(file_msg)
            src_size = media.file_size or 0

            if shutil.disk_usage(DOWNLOAD_DIR).free < src_size * 2.3:
                raise RuntimeError("Not enough free disk space on the server.")

            orig_ext = os.path.splitext(get_original_filename(file_msg))[1]
            raw_path = os.path.join(workdir, "__source__" + orig_ext)
            final_path = os.path.join(workdir, target_name)

            # ── download ──
            t0 = time.time()
            try:
                dl = await file_msg.download(
                    file_name=raw_path,
                    progress=progress,
                    progress_args=(status, "🚀 Downloading Media... ⚡", t0, state, uid),
                )
            except StopTransmission:
                raise DownloadCancelled()
            if cancel_flags.get(uid):
                raise DownloadCancelled()
            if not dl or not os.path.exists(str(dl)):
                raise RuntimeError("Download failed.")
            raw_path = str(dl)

            # ── convert / rename ──
            ext = os.path.splitext(target_name)[1].lower()
            is_video = ext in VIDEO_EXTS
            if is_video and (u["meta_on"] or u["enc_tag"] or ext != orig_ext.lower()):
                msg_txt = (
                    "🏷 Adding 'Encoded by' tag & encoding...\n(this takes longer than a normal rename)"
                    if u["enc_tag"] and ext != ".webm"
                    else "⚙️ Converting / renaming tracks..."
                )
                await status.edit_text(msg_txt, reply_markup=task_markup(uid))
                await convert_and_rename(raw_path, final_path, u, uid)
            else:
                os.rename(raw_path, final_path)
            if os.path.exists(raw_path):
                os.remove(raw_path)

            final_size = os.path.getsize(final_path)
            if final_size > MAX_TOTAL_BYTES:
                raise RuntimeError(f"File is {human_size(final_size)}, over the {human_size(MAX_TOTAL_BYTES)} limit.")

            # ── extras: sample / screenshots / thumbnail ──
            sample_path, shot_paths, thumb_path = None, [], None
            square = u["upload_type"] != "video"
            dur = await probe_duration(final_path) if is_video else 0

            if is_video and (u["sample"] or u["screenshot"] or u["random_thumb"]):
                await status.edit_text("🖼 Generating previews...", reply_markup=task_markup(uid))
            try:
                if is_video and u["sample"] and dur > 0:
                    sample_path = await generate_sample_video(
                        final_path, os.path.join(workdir, "sample.mp4"), dur, uid
                    )
                if is_video and u["screenshot"]:
                    shot_paths = await generate_screenshots(final_path, workdir, dur, uid)
                if is_video and u["random_thumb"] and dur > 0:
                    frame = os.path.join(workdir, "rand_frame.jpg")
                    await extract_frame(final_path, random.uniform(dur * 0.1, dur * 0.9), frame, "scale=640:-2", uid)
                    thumb_path = await make_thumb(frame, os.path.join(workdir, "thumb.jpg"), square, uid)
            except DownloadCancelled:
                raise
            except Exception:
                pass  # previews are optional

            if thumb_path is None and u["thumb"]:
                try:
                    src = await client.download_media(u["thumb"], file_name=os.path.join(workdir, "thumb_src.jpg"))
                    thumb_path = await make_thumb(str(src), os.path.join(workdir, "thumb.jpg"), square, uid)
                except DownloadCancelled:
                    raise
                except Exception:
                    thumb_path = None

            # ── split if too big ──
            raw_split = False
            if final_size > SPLIT_LIMIT:
                await status.edit_text("✂️ File is large, splitting into parts...", reply_markup=task_markup(uid))
                parts = await split_video_by_size(final_path, SPLIT_LIMIT, uid) if is_video else None
                if parts:
                    jobs = [(p, make_part_filename(target_name, i + 1)) for i, p in enumerate(parts)]
                else:
                    parts = await split_file(final_path, SPLIT_LIMIT)
                    jobs = [(p, f"{target_name}.{i + 1:03d}") for i, p in enumerate(parts)]
                    raw_split = True
                os.remove(final_path)
            else:
                jobs = [(final_path, target_name)]

            # ── upload ──
            total = len(jobs)
            dump = dump_target(u) if u["dump_mode"] else None
            dump_warned = False

            for idx, (path, name) in enumerate(jobs, start=1):
                note = f" (part {idx}/{total})" if total > 1 else ""
                size_p = os.path.getsize(path)
                caption, pm = build_caption(u, name, size_p)
                if raw_split and idx == total:
                    caption += "\n\n<code>" + html.escape(join_hint(target_name, total)) + "</code>"

                state["last_update"] = 0
                t1 = time.time()
                common = dict(
                    chat_id=chat_id,
                    caption=caption,
                    parse_mode=pm,
                    thumb=thumb_path,
                    file_name=name,
                    progress=progress,
                    progress_args=(status, f"📤 Uploading Media...{note} ⚡", t1, state, uid),
                )
                try:
                    if u["upload_type"] == "video" and is_video and not raw_split:
                        d, w, h = await video_info(path)
                        sent = await client.send_video(
                            video=path, duration=d, width=w, height=h, supports_streaming=True, **common
                        )
                    else:
                        sent = await client.send_document(document=path, **common)
                except StopTransmission:
                    raise DownloadCancelled()
                if sent is None:
                    if cancel_flags.get(uid):
                        raise DownloadCancelled()
                    raise RuntimeError("Upload failed.")

                if dump:
                    try:
                        await sent.copy(dump)
                    except Exception as e:
                        if not dump_warned:
                            dump_warned = True
                            await message.reply_text(f"⚠️ Couldn't copy to dump channel: {e}")

                os.remove(path)

            # ── sample + screenshots ──
            try:
                if sample_path and os.path.exists(sample_path):
                    sd, sw, sh = await video_info(sample_path)
                    await client.send_video(
                        chat_id, sample_path, caption="🎞 Sample Video",
                        duration=sd, width=sw, height=sh, supports_streaming=True,
                    )
                if len(shot_paths) == 1:
                    await client.send_photo(chat_id, shot_paths[0], caption="📸 Screenshot")
                elif len(shot_paths) > 1:
                    media_group = [InputMediaPhoto(p) for p in shot_paths]
                    media_group[0] = InputMediaPhoto(shot_paths[0], caption="📸 Screenshots")
                    await client.send_media_group(chat_id, media_group)
            except Exception:
                pass

            count_rename(uid)
            if u["auto_del"]:
                # keep only the renamed file: remove original, info card, prompts, name text, status
                ids = [file_msg.id, status.id] + [m.id for m in (extra or [])]
                try:
                    await client.delete_messages(chat_id, ids)
                except Exception:
                    pass
            else:
                await status.edit_text(f"✅ Done! Finished in {format_time(time.time() - t0)}.")

    except DownloadCancelled:
        await status.edit_text("❌ Cancelled by user.")
    except Exception as e:
        await status.edit_text(f"❌ Error: {e}")
    finally:
        active_tasks.discard(uid)
        cancel_flags.pop(uid, None)
        task_state.pop(uid, None)
        if workdir:
            shutil.rmtree(workdir, ignore_errors=True)


# ───────────────────────────── BASIC COMMANDS ─────────────────────────────
WELCOME = (
    "👋 Hey {name}!\n\n"
    "I rename files up to 4GB, edit audio/subtitle track names, add thumbnails & captions.\n\n"
    "1️⃣ Send me any file (document / video / audio)\n"
    "2️⃣ Send the new file name (add .mkv / .mp4 to convert container)\n"
    "3️⃣ Done ✅\n\n"
    "Use /settings, /metadata, /myplan or the menu for more."
)


async def verify_task(message: Message, u, token):
    info = task_tokens.pop(token, None)
    if not info or info["uid"] != u["id"]:
        await message.reply_text("❌ Invalid or expired task link. Use /task again.")
        return
    elapsed = time.time() - info["t"]
    if elapsed < MIN_TASK_SECONDS or elapsed > 3600:
        await message.reply_text("❌ Task not completed properly. Use /task and finish the steps.")
        return
    until = int(time.time() + TASK_HOURS * 3600)
    set_user(u["id"], verified_until=max(until, u["verified_until"]))
    await message.reply_text(f"✅ Task verified! Unlimited renames until {fmt_date(until)}.")


@app.on_message(filters.private & filters.command("start"))
async def start_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if len(message.command) > 1 and message.command[1].startswith("verify_"):
        await verify_task(message, u, message.command[1][7:])
        return
    await message.reply_text(WELCOME.format(name=message.from_user.first_name or "there"))


@app.on_message(filters.private & filters.command("ping"))
async def ping_cmd(client, message: Message):
    if not await guard(message):
        return
    t = time.time()
    m = await message.reply_text("🏓 Pinging...")
    await m.edit_text(f"🔥 Pong! `{(time.time() - t) * 1000:.0f} ms`\n⏱ Uptime: {format_time(time.time() - BOT_START_TIME)}")


@app.on_message(filters.private & filters.command("donate"))
async def donate_cmd(client, message: Message):
    if await guard(message):
        await message.reply_text(DONATE_TEXT)


@app.on_message(filters.private & filters.command("premium"))
async def premium_cmd(client, message: Message):
    if await guard(message):
        await message.reply_text(PREMIUM_TEXT)


@app.on_message(filters.private & filters.command("myplan"))
async def myplan_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    lim = "∞" if has_unlimited(u) else str(FREE_DAILY_LIMIT)
    await message.reply_text(
        "❄️ My Plan\n\n"
        f"👤 Plan: {plan_name(u)}\n"
        f"📊 Today: {used_today(u)}/{lim}\n"
        f"🏆 Total renames: {u['renames']}\n"
        f"🆔 ID: {u['id']}",
        parse_mode=enums.ParseMode.DISABLED,
    )


@app.on_message(filters.private & filters.command("task"))
async def task_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if not (SHORTENER_URL and SHORTENER_API):
        await message.reply_text("ℹ️ The task system is not enabled. Use /premium instead.")
        return
    token = secrets.token_urlsafe(8)
    task_tokens[token] = {"uid": u["id"], "t": time.time()}
    deep = f"https://t.me/{BOT_USERNAME}?start=verify_{token}"
    try:
        short = await shorten(deep)
    except Exception as e:
        await message.reply_text(f"❌ Couldn't create task link: {e}")
        return
    await message.reply_text(
        f"✨ Open the link, finish the steps, and come back to the bot.\nYou get {TASK_HOURS}h unlimited access.",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔗 Complete Task", url=short)]]),
    )


def _shorten_sync(url):
    api = f"https://{SHORTENER_URL}/api?api={SHORTENER_API}&url={urllib.parse.quote(url, safe='')}"
    with urllib.request.urlopen(api, timeout=15) as r:
        data = json.loads(r.read().decode())
    short = data.get("shortenedUrl") or data.get("short_url")
    if not short:
        raise RuntimeError("shortener returned no link")
    return short


async def shorten(url):
    return await asyncio.get_running_loop().run_in_executor(None, _shorten_sync, url)


@app.on_message(filters.private & filters.command("leaderboard"))
async def leaderboard_cmd(client, message: Message):
    if not await guard(message):
        return
    rows = db.execute(
        "SELECT name, renames FROM users WHERE renames>0 ORDER BY renames DESC LIMIT 10"
    ).fetchall()
    if not rows:
        await message.reply_text("🏆 No renames yet. Be the first!")
        return
    medals = ["🥇", "🥈", "🥉"] + ["🔹"] * 7
    lines = [f"{medals[i]} {r['name'] or 'User'} — {r['renames']}" for i, r in enumerate(rows)]
    await message.reply_text("🏆 Top Renamers\n\n" + "\n".join(lines), parse_mode=enums.ParseMode.DISABLED)


@app.on_message(filters.private & filters.command("cancel"))
async def cancel_cmd(client, message: Message):
    uid = message.from_user.id
    a = awaiting.pop(uid, None)
    p = pending_file.pop(uid, None)
    junk.pop(uid, None)
    if uid in active_tasks:
        cancel_flags[uid] = True
        await message.reply_text("Cancelling your running task...")
    elif a or p:
        await message.reply_text("✅ Cancelled.")
    else:
        await message.reply_text("Nothing to cancel.")


# ───────────────────────────── THUMB / CAPTION ─────────────────────────────
@app.on_message(filters.private & filters.photo)
async def save_thumb(client, message: Message):
    u = await guard(message)
    if not u:
        return
    set_user(u["id"], thumb=message.photo.file_id)
    await message.reply_text("🖼 Thumbnail saved! Now send your file.")


@app.on_message(filters.private & filters.command("viewthumb"))
async def viewthumb_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if u["thumb"]:
        await message.reply_photo(u["thumb"], caption="👀 This is your current thumbnail")
    else:
        await message.reply_text("You haven't set a thumbnail yet. Send me a photo to set one.")


@app.on_message(filters.private & filters.command("delthumb"))
async def delthumb_cmd(client, message: Message):
    u = await guard(message)
    if u:
        set_user(u["id"], thumb=None)
        await message.reply_text("🗑 Thumbnail removed.")


CAPTION_HELP = (
    "✏️ Send your custom caption now.\n\n"
    "Placeholders: {filename}  {size}  {ext}\n"
    "HTML allowed: <b>bold</b> <i>italic</i> <code>mono</code>\n\n"
    "/cancel to abort."
)


@app.on_message(filters.private & filters.command("set_caption"))
async def set_caption_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    parts = (message.text or "").split(None, 1)
    if len(parts) > 1:
        set_user(u["id"], caption=parts[1])
        await message.reply_text("✅ Caption saved.")
    else:
        awaiting[u["id"]] = {"kind": "caption"}
        await message.reply_text(CAPTION_HELP, parse_mode=enums.ParseMode.DISABLED)


@app.on_message(filters.private & filters.command("see_caption"))
async def see_caption_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if u["caption"]:
        await message.reply_text("👀 Your caption:\n\n" + u["caption"], parse_mode=enums.ParseMode.DISABLED)
    else:
        await message.reply_text("No custom caption set. Default = file name.")


@app.on_message(filters.private & filters.command("del_caption"))
async def del_caption_cmd(client, message: Message):
    u = await guard(message)
    if u:
        set_user(u["id"], caption=None)
        await message.reply_text("🗑 Custom caption deleted.")


# ───────────────────────────── SETTINGS ─────────────────────────────
def onoff(v):
    return "✅" if v else "❌"


SETTING_INFO = {
    "sample": "📹 Sample Video: sends a 30 sec sample clip after the upload.",
    "shot": "📸 Screenshot: sends 5 screenshots from the video.",
    "dump": "🎀 Dump Mode: also copies every uploaded file to your dump channel.",
    "rthumb": "🖼 Random Thumbnail: uses a random frame from the video as the thumbnail.",
    "utype": "📁 Upload Type: send as Document or as streamable Video.",
    "autodel": "🧹 Auto Delete: after a successful rename, deletes your original file, the info card and your name message. Only the renamed file stays.",
    "enc": f"🏷 Encoded Tag: shows '{ENCODE_TEXT}' on screen for the first {ENC_SECONDS:g} sec. Re-encodes the video, so it is slower.",
}


def settings_markup(u):
    B = InlineKeyboardButton
    return InlineKeyboardMarkup([
        [B("🎯 Set Dump Channel 🎯", callback_data="st_dump")],
        [B("📹 Sample Video", callback_data="noop_sample"), B(onoff(u["sample"]), callback_data="st_sample")],
        [B("📸 Screenshot", callback_data="noop_shot"), B(onoff(u["screenshot"]), callback_data="st_shot")],
        [B("🎀 Dump Mode", callback_data="noop_dump"), B(onoff(u["dump_mode"]), callback_data="st_dumpmode")],
        [B("🖼 Random Thumbnail", callback_data="noop_rthumb"), B(onoff(u["random_thumb"]), callback_data="st_rthumb")],
        [B("🏷 Encoded Tag", callback_data="noop_enc"), B(onoff(u["enc_tag"]), callback_data="st_enc")],
        [B("🧹 Auto Delete", callback_data="noop_autodel"), B(onoff(u["auto_del"]), callback_data="st_autodel")],
        [B("📁 Upload Type", callback_data="noop_utype"),
         B("🎞 Video" if u["upload_type"] == "video" else "📁 Document", callback_data="st_utype")],
        [B("✖️ Close ✖️", callback_data="close")],
    ])


def settings_text(u):
    return (
        f"Hey {u['name'] or 'there'}\n\n"
        "Here You Can Change Or Configure Your Settings\n\n"
        f"🎯 Dump Channel: {u['dump_channel'] or 'Not set'}"
    )


async def edit_panel(msg: Message, text, markup):
    try:
        if msg.photo:
            await msg.edit_caption(text, reply_markup=markup, parse_mode=enums.ParseMode.DISABLED)
        else:
            await msg.edit_text(text, reply_markup=markup, parse_mode=enums.ParseMode.DISABLED)
    except Exception:
        pass


@app.on_message(filters.private & filters.command("settings"))
async def settings_cmd(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if SETTINGS_PIC:
        try:
            await message.reply_photo(
                SETTINGS_PIC, caption=settings_text(u), reply_markup=settings_markup(u),
                parse_mode=enums.ParseMode.DISABLED,
            )
            return
        except Exception:
            pass
    await message.reply_text(settings_text(u), reply_markup=settings_markup(u), parse_mode=enums.ParseMode.DISABLED)


@app.on_callback_query(filters.regex(r"^noop_"))
async def noop_cb(client, cq: CallbackQuery):
    await cq.answer(SETTING_INFO.get(cq.data[5:], ""), show_alert=True)


@app.on_callback_query(filters.regex(r"^st_"))
async def settings_cb(client, cq: CallbackQuery):
    uid = cq.from_user.id
    u = get_user(uid)
    if u["banned"]:
        await cq.answer("Banned.", show_alert=True)
        return
    d = cq.data

    if d == "st_dump":
        awaiting[uid] = {"kind": "dump"}
        await cq.message.reply_text(
            "🎯 Send your dump channel ID (like -100123456789) or @username.\n"
            "Add me to that channel as admin first.\n\n/cancel to abort."
        )
        await cq.answer()
        return
    if d == "st_sample":
        set_user(uid, sample=int(not u["sample"]))
    elif d == "st_shot":
        set_user(uid, screenshot=int(not u["screenshot"]))
    elif d == "st_rthumb":
        set_user(uid, random_thumb=int(not u["random_thumb"]))
    elif d == "st_autodel":
        set_user(uid, auto_del=int(not u["auto_del"]))
    elif d == "st_enc":
        set_user(uid, enc_tag=int(not u["enc_tag"]))
    elif d == "st_utype":
        set_user(uid, upload_type="document" if u["upload_type"] == "video" else "video")
    elif d == "st_dumpmode":
        if not u["dump_mode"] and not u["dump_channel"]:
            await cq.answer("Set a dump channel first!", show_alert=True)
            return
        set_user(uid, dump_mode=int(not u["dump_mode"]))

    u = get_user(uid)
    await edit_panel(cq.message, settings_text(u), settings_markup(u))
    await cq.answer("Updated ✅")


# ───────────────────────────── METADATA ─────────────────────────────
def metadata_text(u):
    tag = u["audio_tag"] or DEFAULT_TAG
    sub = u["sub_tag"] or "(none - subtitle names cleared)"
    return (
        "⚡ Metadata Settings\n\n"
        f"Status: {onoff(u['meta_on'])} {'ON' if u['meta_on'] else 'OFF'}\n"
        f"🔊 Audio Tag: {tag}\n"
        f"💬 Subtitle Tag: {sub}\n\n"
        f"Audio track title example:\n{tag} Tamil DD 5.1"
    )


def metadata_markup(u):
    B = InlineKeyboardButton
    return InlineKeyboardMarkup([
        [B(f"{onoff(u['meta_on'])} Metadata {'ON' if u['meta_on'] else 'OFF'}", callback_data="md_toggle")],
        [B("🔊 Set Audio Tag", callback_data="md_audio"), B("💬 Set Subtitle Tag", callback_data="md_sub")],
        [B("♻️ Reset", callback_data="md_reset")],
        [B("✖️ Close ✖️", callback_data="close")],
    ])


@app.on_message(filters.private & filters.command("metadata"))
async def metadata_cmd(client, message: Message):
    u = await guard(message)
    if u:
        await message.reply_text(metadata_text(u), reply_markup=metadata_markup(u), parse_mode=enums.ParseMode.DISABLED)


@app.on_callback_query(filters.regex(r"^md_"))
async def metadata_cb(client, cq: CallbackQuery):
    uid = cq.from_user.id
    u = get_user(uid)
    d = cq.data
    if d == "md_audio":
        awaiting[uid] = {"kind": "audio_tag"}
        await cq.message.reply_text("🔊 Send the new audio tag (e.g. @MyChannel). Send - to reset to default.")
        await cq.answer()
        return
    if d == "md_sub":
        awaiting[uid] = {"kind": "sub_tag"}
        await cq.message.reply_text("💬 Send the subtitle tag. Send - to leave subtitle names blank.")
        await cq.answer()
        return
    if d == "md_toggle":
        set_user(uid, meta_on=int(not u["meta_on"]))
    elif d == "md_reset":
        set_user(uid, audio_tag=None, sub_tag="", meta_on=1)
    u = get_user(uid)
    await edit_panel(cq.message, metadata_text(u), metadata_markup(u))
    await cq.answer("Updated ✅")


# ───────────────────────────── FILE FLOW ─────────────────────────────
@app.on_message(filters.private & (filters.document | filters.video | filters.audio))
async def file_received(client, message: Message):
    u = await guard(message)
    if not u:
        return
    if limit_reached(u):
        await message.reply_text(LIMIT_MSG)
        return
    media = get_media(message)
    size = media.file_size or 0
    if size > MAX_TOTAL_BYTES:
        await message.reply_text(f"❌ File too big ({human_size(size)}). Max {human_size(MAX_TOTAL_BYTES)}.")
        return

    pending_file[u["id"]] = message
    awaiting.pop(u["id"], None)
    name = get_original_filename(message)
    ext = os.path.splitext(name)[1].lstrip(".") or "-"
    B = InlineKeyboardButton
    info = await message.reply_text(
        "🗂️ Media Info :\n\n"
        f"◈ File Name : {name}\n"
        f"◈ File Size : {human_size(size)}\n"
        f"◈ File Extension : {ext}\n"
        f"◈ Mime Type : {getattr(media, 'mime_type', None) or '-'}\n"
        f"◈ DC ID : {getattr(media, 'dc_id', None) or '-'}\n\n"
        "Please Enter The New Filename.",
        reply_markup=InlineKeyboardMarkup([[
            B("📝 Rename", callback_data="rename_btn"),
            B("✖️ Close", callback_data="close_media"),
        ]]),
        quote=True,
        parse_mode=enums.ParseMode.DISABLED,
    )
    junk[u["id"]] = [info]


@app.on_callback_query(filters.regex(r"^rename_btn$"))
async def rename_btn_cb(client, cq: CallbackQuery):
    uid = cq.from_user.id
    if uid not in pending_file:
        await cq.answer("No file pending. Send a file first.", show_alert=True)
        return
    prompt = await cq.message.reply_text(
        "📝 Send the new file name (with extension, e.g. movie.mkv):",
        reply_markup=ForceReply(selective=True),
    )
    junk.setdefault(uid, []).append(prompt)
    await cq.answer()


@app.on_callback_query(filters.regex(r"^close"))
async def close_cb(client, cq: CallbackQuery):
    if cq.data == "close_media":
        pending_file.pop(cq.from_user.id, None)
        junk.pop(cq.from_user.id, None)
    try:
        await cq.message.delete()
    except Exception:
        pass
    await cq.answer()


@app.on_callback_query(filters.regex(r"^(cancel|refresh)_"))
async def task_cb(client, cq: CallbackQuery):
    action, owner = cq.data.split("_", 1)
    if cq.from_user.id != int(owner):
        await cq.answer("This isn't your task.", show_alert=True)
        return
    if action == "cancel":
        cancel_flags[int(owner)] = True
        await cq.answer("Cancelling...")
    else:
        st = task_state.get(int(owner))
        if st is not None:
            st["force"] = True
        await cq.answer("🔄 Refreshing...")


async def handle_awaiting(client, message: Message, u, aw):
    uid, txt, kind = u["id"], message.text.strip(), aw["kind"]

    if kind == "caption":
        set_user(uid, caption=txt)
        await message.reply_text("✅ Custom caption saved.")
    elif kind == "audio_tag":
        set_user(uid, audio_tag=None if txt == "-" else txt)
        await message.reply_text("✅ Audio tag saved. Check /metadata")
    elif kind == "sub_tag":
        set_user(uid, sub_tag="" if txt == "-" else txt)
        await message.reply_text("✅ Subtitle tag saved. Check /metadata")
    elif kind == "dump":
        target = txt if txt.startswith("@") else None
        if target is None:
            try:
                target = int(txt)
            except ValueError:
                awaiting[uid] = aw
                await message.reply_text("❌ Send a numeric ID (-100...) or @username. /cancel to abort.")
                return
        try:
            chat = await client.get_chat(target)
            await client.send_message(chat.id, "✅ Dump channel connected.")
        except Exception as e:
            await message.reply_text(f"❌ Couldn't access that channel. Make me admin there and try again.\n{e}")
            return
        set_user(uid, dump_channel=str(chat.id))
        await message.reply_text(f"✅ Dump channel set: {chat.title or chat.id}")


@app.on_message(filters.private & filters.text & ~filters.regex(r"^/"))
async def text_handler(client, message: Message):
    u = await guard(message)
    if not u:
        return
    uid = u["id"]

    aw = awaiting.pop(uid, None)
    if aw:
        await handle_awaiting(client, message, u, aw)
        return

    file_msg = pending_file.pop(uid, None)
    if not file_msg:
        return  # ignore random text

    if limit_reached(u):
        await message.reply_text(LIMIT_MSG)
        return

    target = sanitize_filename(message.text)
    if not os.path.splitext(target)[1]:
        target += os.path.splitext(get_original_filename(file_msg))[1]

    extra = junk.pop(uid, []) + [message]
    await process_file(client, message, file_msg, target, extra)


# ───────────────────────────── ADMIN ─────────────────────────────
async def _is_admin(_, __, m):
    return bool(m.from_user and m.from_user.id in ADMINS)


admin_only = filters.create(_is_admin)


@app.on_message(filters.private & filters.command("admin_cmd") & admin_only)
async def admin_cmd(client, message: Message):
    await message.reply_text(
        "🛠 Admin Commands\n\n"
        "/stats - bot stats\n"
        "/addpremium <id> <days>\n"
        "/delpremium <id>\n"
        "/ban <id>\n"
        "/unban <id>\n"
        "/broadcast - reply to a message to send it to all users"
    )


@app.on_message(filters.private & filters.command("stats") & admin_only)
async def stats_cmd(client, message: Message):
    now = int(time.time())
    total = db.execute("SELECT COUNT(*) c FROM users").fetchone()["c"]
    prem = db.execute("SELECT COUNT(*) c FROM users WHERE premium_until>?", (now,)).fetchone()["c"]
    banned = db.execute("SELECT COUNT(*) c FROM users WHERE banned=1").fetchone()["c"]
    ren = db.execute("SELECT COALESCE(SUM(renames),0) c FROM users").fetchone()["c"]
    disk = shutil.disk_usage(DOWNLOAD_DIR)
    await message.reply_text(
        "📊 Bot Stats\n\n"
        f"👥 Users: {total}\n💎 Premium: {prem}\n🚫 Banned: {banned}\n"
        f"🔁 Total renames: {ren}\n⚙️ Active tasks: {len(active_tasks)}\n"
        f"💾 Disk free: {human_size(disk.free)} / {human_size(disk.total)}\n"
        f"⏱ Uptime: {format_time(time.time() - BOT_START_TIME)}"
    )


def _arg_id(message):
    try:
        return int(message.command[1])
    except (IndexError, ValueError):
        return None


@app.on_message(filters.private & filters.command("addpremium") & admin_only)
async def addpremium_cmd(client, message: Message):
    uid = _arg_id(message)
    try:
        days = int(message.command[2])
    except (IndexError, ValueError):
        days = 0
    if uid is None or days <= 0:
        await message.reply_text("Usage: /addpremium <user_id> <days>")
        return
    u = get_user(uid)
    base = max(time.time(), u["premium_until"])
    until = int(base + days * 86400)
    set_user(uid, premium_until=until)
    await message.reply_text(f"✅ Premium for {uid} until {fmt_date(until)}")
    try:
        await client.send_message(uid, f"💎 You got Premium for {days} days! Enjoy unlimited renames.")
    except Exception:
        pass


@app.on_message(filters.private & filters.command("delpremium") & admin_only)
async def delpremium_cmd(client, message: Message):
    uid = _arg_id(message)
    if uid is None:
        await message.reply_text("Usage: /delpremium <user_id>")
        return
    set_user(uid, premium_until=0)
    await message.reply_text(f"✅ Premium removed for {uid}")


@app.on_message(filters.private & filters.command(["ban", "unban"]) & admin_only)
async def ban_cmd(client, message: Message):
    uid = _arg_id(message)
    if uid is None:
        await message.reply_text(f"Usage: /{message.command[0]} <user_id>")
        return
    banned = 1 if message.command[0] == "ban" else 0
    set_user(uid, banned=banned)
    await message.reply_text(f"✅ User {uid} {'banned' if banned else 'unbanned'}.")


@app.on_message(filters.private & filters.command("broadcast") & admin_only)
async def broadcast_cmd(client, message: Message):
    src = message.reply_to_message
    if not src:
        await message.reply_text("Reply to a message with /broadcast")
        return
    ids = [r["id"] for r in db.execute("SELECT id FROM users WHERE banned=0").fetchall()]
    status = await message.reply_text(f"📢 Broadcasting to {len(ids)} users...")
    ok = fail = 0
    for i, uid in enumerate(ids, start=1):
        try:
            await src.copy(uid)
            ok += 1
        except FloodWait as e:
            await asyncio.sleep(e.value)
            try:
                await src.copy(uid)
                ok += 1
            except Exception:
                fail += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.05)
        if i % 50 == 0:
            try:
                await status.edit_text(f"📢 {i}/{len(ids)} ... ✅ {ok} ❌ {fail}")
            except Exception:
                pass
    await status.edit_text(f"📢 Broadcast done.\n✅ Sent: {ok}\n❌ Failed: {fail}")


# ───────────────────────────── STARTUP ─────────────────────────────
async def main():
    global BOT_USERNAME
    await app.start()
    BOT_USERNAME = (await app.get_me()).username
    try:
        await app.set_bot_commands([
            BotCommand("start", "Bot alive checking"),
            BotCommand("premium", "Upgrade your plan"),
            BotCommand("myplan", "Check your current plan info"),
            BotCommand("metadata", "Configure your metadata tags"),
            BotCommand("settings", "Configure your settings"),
            BotCommand("viewthumb", "View your thumbnail"),
            BotCommand("delthumb", "Delete your thumbnail"),
            BotCommand("set_caption", "Set a custom caption"),
            BotCommand("see_caption", "See your custom caption"),
            BotCommand("del_caption", "Delete custom caption"),
            BotCommand("ping", "Check bot ping"),
            BotCommand("donate", "Support the developer"),
            BotCommand("task", "Complete a simple task & use me for free"),
            BotCommand("leaderboard", "Top renamers"),
            BotCommand("admin_cmd", "Admin commands (admin only)"),
        ])
    except Exception as e:
        print("set_bot_commands failed:", e)
    print(f"Bot started as @{BOT_USERNAME}")
    await idle()
    await app.stop()


if __name__ == "__main__":
    if not (API_ID and API_HASH and BOT_TOKEN):
        sys.exit("Set API_ID, API_HASH and BOT_TOKEN environment variables first.")
    app.run(main())
