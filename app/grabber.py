#!/usr/bin/env python3
"""Раз в минуту сохраняет кадр с каждой камеры Frigate (список берётся из Frigate).

Папки: SAVE_ROOT/<сервер>_<камера>/YYYY-MM-DD/YYYY-MM-DD_HH-MM-SS.jpg
Кадр берётся из go2rtc (frame.jpeg, полное разрешение основного потока),
если go2rtc недоступен - из Frigate latest.jpg (разрешение detect-потока).
Раз в сутки (CLEAN_HOUR) в старых днях оставляются только снимки кратные 5 минутам.

Работает от root, поэтому ему не мешают права на папке; владельца и права
выставляет явно (как у samba force user), чтобы samba могла читать и удалять.
Внешних процессов (ffmpeg) нет - все запросы с жёсткими таймаутами.
"""
import html
import io
import json
import os
import queue
import re
import shutil
import struct
import sys
import threading
import time
import urllib.request
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta
from urllib.parse import urlparse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.environ.get("SAVE_ROOT", "/timelapse")
SERVERS_FILE = os.environ.get("SERVERS_FILE", "/app/servers.json")      # начальные настройки из репозитория
SETTINGS_FILE = os.environ.get("SETTINGS_FILE", "/state/servers.json")  # сохранённые с админ-страницы, главнее
UID = int(os.environ.get("OWNER_UID", "1000"))
GID = int(os.environ.get("OWNER_GID", "1000"))
KEEP_FULL_DAYS = int(os.environ.get("KEEP_FULL_DAYS", "28"))
CLEAN_HOUR = int(os.environ.get("CLEAN_HOUR", "3"))
CLEAN_DRY_RUN = os.environ.get("CLEAN_DRY_RUN", "0") == "1"
CLEAN_LOOKBACK_DAYS = int(os.environ.get("CLEAN_LOOKBACK_DAYS", "90"))
FETCH_TIMEOUT = 10
MIN_JPEG = 5 * 1024
DISCOVERY_TTL = 300
WATCHDOG_SECONDS = 900
HEARTBEAT = "/tmp/last_ok"
STATE_FILE = os.environ.get("STATE_FILE", "/state/stats.json")
HTTP_PORT = int(os.environ.get("HTTP_PORT", "8080"))
STALE_SECONDS = 180
SETTINGS = {"interval": 1, "keep_days": KEEP_FULL_DAYS, "thin_every": 5}
# interval: снимок раз в N минут; keep_days: сколько дней хранить все снимки (0 - вечно);
# thin_every: дальше оставляется снимок раз в M минут (кратно interval)
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
THIN_MARK = ".thinned"

os.umask(0)
_last_err = {}
SIZES = {}
LOCK = threading.Lock()
STATE = {"cams": {}, "scan": {}, "clean": {}}
SERVERS = []


def cam_state(folder):
    return STATE["cams"].setdefault(folder, {
        "server": None, "cam": None, "live": False, "last_ok": None, "via": None,
        "last_err": None, "last_err_at": None, "bytes": 0, "files": 0, "days": 0, "oldest": None})


def load_state():
    try:
        with open(STATE_FILE) as f:
            STATE.update(json.load(f))
    except Exception:
        pass
    prune_state()


def prune_state():
    """Убирает из статистики папки, которых больше нет на диске (переименованные, слитые)."""
    with LOCK:
        for folder in [f for f in STATE["cams"] if not os.path.isdir(os.path.join(ROOT, f))]:
            del STATE["cams"][folder]


def save_state():
    try:
        os.makedirs(os.path.dirname(STATE_FILE), exist_ok=True)
        tmp = STATE_FILE + ".tmp"
        with LOCK, open(tmp, "w") as f:
            json.dump(STATE, f)
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        note("state", f"cant save state: {e}")


def load_config():
    for path in (SETTINGS_FILE, SERVERS_FILE):
        try:
            with open(path) as f:
                return json.load(f)
        except FileNotFoundError:
            continue
    return {"servers": []}


def apply_loaded(cfg):
    """Берёт частоту и сроки из файла настроек (понимает и старый формат с minute_shots)."""
    interval = cfg.get("interval") or (1 if cfg.get("minute_shots", True) else 5)
    SETTINGS["interval"] = int(interval)
    SETTINGS["keep_days"] = int(cfg.get("keep_days", KEEP_FULL_DAYS))
    SETTINGS["thin_every"] = int(cfg.get("thin_every") or max(5, SETTINGS["interval"]))


def load_servers_config():
    return load_config()["servers"]


def log(msg):
    print(datetime.now().strftime("%Y-%m-%d %H:%M:%S"), msg, flush=True)


def fetch(url, timeout=FETCH_TIMEOUT, deadline=20):
    end = time.monotonic() + deadline
    with urllib.request.urlopen(url, timeout=timeout) as r:
        chunks = []
        while True:
            if time.monotonic() > end:
                raise TimeoutError("deadline exceeded")
            c = r.read(65536)
            if not c:
                break
            chunks.append(c)
    return b"".join(chunks)


def safe(name):
    return re.sub(r"[^a-z0-9_-]", "_", name.lower())


class Server:
    def __init__(self, cfg):
        self.name = cfg["name"]
        self.frigate = cfg["frigate"].rstrip("/")
        self.go2rtc = (cfg.get("go2rtc") or "").rstrip("/")
        self.aliases = cfg.get("aliases", {})
        self.cams = []          # [(frigate_name, folder)]
        self.streams = {}       # lower(name) -> real go2rtc stream name
        self.found_at = 0

    def cfg(self):
        return {"name": self.name, "frigate": self.frigate, "go2rtc": self.go2rtc, "aliases": self.aliases}

    def refresh(self):
        fresh = bool(self.cams) and time.time() - self.found_at < DISCOVERY_TTL
        if not fresh:
            try:
                cfg = json.loads(fetch(self.frigate + "/api/config"))
                self.cams = [
                    (n, f"{self.name}_{safe(self.aliases.get(n, n))}")
                    for n, c in cfg["cameras"].items() if c.get("enabled", True)
                ]
                self.found_at = time.time()
            except Exception as e:
                note(self.name + ":config", f"{self.name}: cant read Frigate config ({e}), using last known list")
        # список потоков go2rtc обновляем вместе с камерами, а пока он пуст - каждую минуту
        if self.go2rtc and (not fresh or not self.streams):
            try:
                s = json.loads(fetch(self.go2rtc + "/api/streams"))
                self.streams = {k.lower(): k for k in s}
            except Exception as e:
                self.streams = {}
                note(self.name + ":go2rtc", f"{self.name}: go2rtc unavailable ({e}), fallback to latest.jpg")

    def grab(self, cam):
        errs = []
        if self.streams:
            for cand in (cam.lower() + "_live", cam.lower()):
                real = self.streams.get(cand)
                if not real:
                    continue
                try:
                    return check(fetch(f"{self.go2rtc}/api/frame.jpeg?src={real}")), "go2rtc"
                except Exception as e:
                    errs.append(f"go2rtc:{e}")
        try:
            return check(fetch(f"{self.frigate}/api/{cam}/latest.jpg")), "latest"
        except Exception as e:
            errs.append(f"latest:{e}")
        raise RuntimeError("; ".join(errs))


def check(data):
    if len(data) < MIN_JPEG or data[:2] != b"\xff\xd8":
        raise ValueError(f"not a valid jpeg ({len(data)} bytes)")
    return data


def note(key, msg):
    """Пишет ошибку при смене состояния и не чаще раза в 30 минут."""
    now = time.time()
    if now - _last_err.get(key, 0) > 1800:
        _last_err[key] = now
        log("WARN " + msg)


def mkdir_owned(path):
    if not os.path.isdir(path):
        os.makedirs(path, mode=0o775, exist_ok=True)
    st = os.stat(path)
    if (st.st_uid, st.st_gid) != (UID, GID):
        os.chown(path, UID, GID)
    if st.st_mode & 0o777 != 0o775:
        os.chmod(path, 0o775)


def save(folder, data, now):
    cam_dir = os.path.join(ROOT, folder)
    day_dir = os.path.join(cam_dir, now.strftime("%Y-%m-%d"))
    mkdir_owned(cam_dir)
    mkdir_owned(day_dir)
    final = os.path.join(day_dir, now.strftime("%Y-%m-%d_%H-%M-%S") + ".jpg")
    tmp = os.path.join(day_dir, ".tmp_" + os.path.basename(final))
    with open(tmp, "wb") as f:
        f.write(data)
    os.chown(tmp, UID, GID)
    os.chmod(tmp, 0o664)
    os.rename(tmp, final)


def cycle(servers, pool):
    started = datetime.now()
    jobs = []
    for s in servers:
        s.refresh()
        jobs += [(s, c, f) for c, f in s.cams]

    def one(job):
        s, cam, folder = job
        for attempt in (1, 2):
            try:
                data, via = s.grab(cam)
                save(folder, data, started)
                SIZES[folder] = len(data)
                return folder, via, None
            except Exception as e:
                err = e
                time.sleep(1.5)
        return folder, None, err

    results = list(pool.map(one, jobs))
    with LOCK:
        for c in STATE["cams"].values():
            c["live"] = False
        for (s, cam, folder), (_, via, err) in zip(jobs, results):
            c = cam_state(folder)
            c.update(server=s.name, cam=cam, live=True)
            if err is None:
                c.update(last_ok=started.timestamp(), via=via, last_err=None)
                c["bytes"] += SIZES.pop(folder, 0)
                c["files"] += 1
            else:
                c.update(last_err=str(err)[:200], last_err_at=started.timestamp())
    save_state()
    ok = [r for r in results if r[2] is None]
    bad = [r for r in results if r[2] is not None]
    fallback = [r[0] for r in ok if r[1] == "latest"]
    for folder, _, err in bad:
        note(folder, f"{folder}: {err}")
    log(f"done {len(ok)}/{len(results)}" + (f" FAIL {[b[0] for b in bad]}" if bad else "")
        + (f" low-res fallback {fallback}" if fallback else ""))
    if ok:
        with open(HEARTBEAT, "w") as f:
            f.write(str(time.time()))


def thin_day(path, every):
    """Удаляет в папке дня снимки, время которых (минуты от полуночи) не кратно every. Возвращает (удалено, оставлено, байт)."""
    removed = kept = freed = 0
    with os.scandir(path) as it:
        entries = list(it)
    for e in entries:
        fn = e.name
        if fn.startswith(".tmp_"):
            if time.time() - e.stat().st_mtime > 3600 and not CLEAN_DRY_RUN:
                try:
                    os.unlink(e.path)
                except FileNotFoundError:
                    pass
            continue
        if not fn.endswith(".jpg"):
            continue
        try:
            hh, mm = fn.split("_")[1].split("-")[:2]
            minute = int(hh) * 60 + int(mm)
        except (IndexError, ValueError):
            continue
        if minute % every == 0:
            kept += 1
            continue
        removed += 1
        try:
            freed += e.stat().st_size
            if not CLEAN_DRY_RUN:
                os.unlink(e.path)
        except FileNotFoundError:  # параллельный проход уже удалил
            pass
    return removed, kept, freed


def clean():
    today = datetime.now().date()
    keep = SETTINGS["keep_days"]
    if keep <= 0:
        log("clean skipped: minute shots are kept without limit")
        return
    every = SETTINGS["thin_every"]
    newest = today - timedelta(days=keep)
    oldest = newest - timedelta(days=CLEAN_LOOKBACK_DAYS)
    log(f"clean start (keep all {keep} d, then every {every} min, dry_run={CLEAN_DRY_RUN})")
    total = total_bytes = 0
    for cam in sorted(os.listdir(ROOT)):
        cam_dir = os.path.join(ROOT, cam)
        if cam.startswith(".") or not os.path.isdir(cam_dir):
            continue
        cam_removed = cam_freed = 0
        for day in sorted(os.listdir(cam_dir)):
            if not DATE_RE.match(day):
                continue
            d = datetime.strptime(day, "%Y-%m-%d").date()
            if not (oldest <= d < newest):
                continue
            path = os.path.join(cam_dir, day)
            mark = os.path.join(path, THIN_MARK)
            if os.path.exists(mark):
                try:  # в метке записана частота, до которой день уже прорежен (пустая метка - 5 минут)
                    done_every = int(open(mark).read().strip() or 5)
                except ValueError:
                    done_every = 5
                if done_every % every == 0:
                    continue
            try:
                removed, _, freed = thin_day(path, every)
                cam_removed += removed
                cam_freed += freed
                if not CLEAN_DRY_RUN:
                    with open(mark, "w") as f:
                        f.write(str(every))
            except Exception as e:
                log(f"WARN clean {path}: {e}")
        if cam_removed:
            log(f"clean {cam}: {'would delete' if CLEAN_DRY_RUN else 'deleted'} {cam_removed} files, {cam_freed / 2**30:.1f} GB")
        total += cam_removed
        total_bytes += cam_freed
    with LOCK:
        STATE["clean"] = {"at": time.time(), "dry_run": CLEAN_DRY_RUN, "removed": total}
    save_state()
    log(f"clean done, total {total} files, {total_bytes / 2**30:.1f} GB")


def scan():
    """Считает размер, число файлов и дней по каждой папке камеры. Медленно и с паузами, чтобы не грузить диск."""
    t0 = time.time()
    with LOCK:
        STATE["scan"] = {"running": True, "started": t0, "finished": STATE["scan"].get("finished"), "seconds": STATE["scan"].get("seconds")}
    for cam in sorted(os.listdir(ROOT)):
        cam_dir = os.path.join(ROOT, cam)
        if cam.startswith(".") or not os.path.isdir(cam_dir):
            continue
        size = files = days = 0
        oldest = None
        try:
            with os.scandir(cam_dir) as it:
                day_dirs = [e for e in it if e.is_dir(follow_symlinks=False)]
            for d in day_dirs:
                days += 1
                if DATE_RE.match(d.name) and (oldest is None or d.name < oldest):
                    oldest = d.name
                with os.scandir(d.path) as it:
                    for e in it:
                        if e.name.endswith(".jpg"):
                            size += e.stat(follow_symlinks=False).st_size
                            files += 1
                time.sleep(0.03)
        except Exception as e:
            log(f"WARN scan {cam}: {e}")
            continue
        with LOCK:
            c = cam_state(cam)
            c.update(bytes=size, files=files, days=days, oldest=oldest)
    prune_state()
    with LOCK:
        STATE["scan"] = {"running": False, "started": t0, "finished": time.time(), "seconds": round(time.time() - t0)}
    save_state()
    log(f"scan done in {round(time.time() - t0)} s")


def fmt_size(n):
    for unit in ("Б", "КБ", "МБ", "ГБ", "ТБ"):
        if n < 1024 or unit == "ТБ":
            return f"{n:.0f} {unit}" if unit == "Б" else f"{n:.1f} {unit}"
        n /= 1024


def fmt_ago(sec):
    if sec < 90:
        return f"{int(sec)} с назад"
    if sec < 5400:
        return f"{int(sec / 60)} мин назад"
    if sec < 172800:
        return f"{sec / 3600:.1f} ч назад"
    return f"{int(sec / 86400)} дн назад"


def page():
    now = time.time()
    st = os.statvfs(ROOT)
    total, free = st.f_blocks * st.f_frsize, st.f_bavail * st.f_frsize
    used_pct = round(100 * (total - free) / total)
    with LOCK:
        cams = sorted(STATE["cams"].items(), key=lambda kv: (not kv[1]["live"], kv[0]))
        scan_info, clean_info = dict(STATE["scan"]), dict(STATE["clean"])
    e = html.escape
    stale = SETTINGS["interval"] * 60 + 120
    known = [s.name for s in SERVERS]
    groups = {}
    for folder, c in cams:
        srv = c["server"] if c["live"] else None
        if not srv:
            srv = next((n for n in known if folder.startswith(n + "_")), None)
        groups.setdefault(srv, []).append((folder, c))
    order = [n for n in known if n in groups] + sorted(n for n in groups if n and n not in known) + ([None] if None in groups else [])
    total_bytes, sections = 0, []
    for srv in order:
        rows, gbytes = [], 0
        for folder, c in groups[srv]:
            gbytes += c["bytes"]
            age = now - c["last_ok"] if c["last_ok"] else None
            if c["live"]:
                cls = "bad" if age is None or age > stale else "ok"
                last = (f"{datetime.fromtimestamp(c['last_ok']):%d.%m}<br><small>{fmt_ago(age)}</small>"
                        if age is not None else "нет данных")
                thumb = f'<img loading="lazy" src="/thumb/{e(folder)}?t={int(now // 60)}" alt="">'
                mode = {"go2rtc": "полное", "latest": "<b>низкое</b>"}.get(c["via"], "-")
            else:
                cls, thumb, mode = "arch", "", "-"
                last = (f"{datetime.fromtimestamp(c['last_ok']):%d.%m}" if c["last_ok"] else "архив")
            err = f"<small class=err>{e(c['last_err'])}</small>" if c["last_err"] and c["live"] else ""
            rows.append(
                f"<tr class={cls}><td class=th>{thumb}</td><td><a href=/cam/{e(folder)}><b>{e(folder)}</b></a>"
                f"{'' if c['live'] else '<br><small>сейчас не снимается</small>'}</td><td>{last}</td><td>{mode}</td>"
                f"<td>{c['days']}</td><td>{e(c['oldest'] or '-')}</td><td>{c['files']:,}</td>"
                f"<td>{fmt_size(c['bytes'])}</td><td>{err}</td></tr>".replace(",", " "))
        total_bytes += gbytes
        url = next((s.frigate for s in SERVERS if s.name == srv), "")
        title = e(srv) if srv else "Прочий архив"
        sections.append(
            f"<h2>{title} <small>{e(url)}{' · ' if url else ''}{len(rows)} шт., {fmt_size(gbytes)}</small></h2>"
            f'<div class="card wrap"><table><tr><th></th><th>Камера</th><th>Последний снимок</th><th title="полное: кадр основного потока камеры (2560x1440 или 1920x1080); низкое: запасной кадр потока детекции Frigate (1280x720 или 640x360), берётся, если go2rtc недоступен">Качество кадра</th>'
            f"<th>Дней</th><th>С даты</th><th>Файлов</th><th>Размер</th><th>Ошибка</th></tr>{''.join(rows)}</table></div>")
    scan_txt = ("идёт подсчёт размеров..." if scan_info.get("running") else
                f"размеры посчитаны {datetime.fromtimestamp(scan_info['finished']):%d.%m %H:%M} за {scan_info['seconds']} с"
                if scan_info.get("finished") else "размеры ещё не посчитаны")
    if clean_info.get("at"):
        clean_txt = (f"чистка {datetime.fromtimestamp(clean_info['at']):%d.%m %H:%M}: "
                     f"{'удалила бы' if clean_info['dry_run'] else 'удалила'} {clean_info['removed']:,} файлов").replace(",", " ")
    else:
        clean_txt = "чистка ещё не запускалась"
    mode_txt = "<b class=warn>тестовый режим, файлы не удаляются</b>" if CLEAN_DRY_RUN else "боевой режим"
    n, keep, m = SETTINGS["interval"], SETTINGS["keep_days"], SETTINGS["thin_every"]
    keep_txt = "кадр " + ("каждую минуту" if n == 1 else f"раз в {n} мин")
    if keep > 0 and m > n:
        keep_txt += f", через {keep} дн. остаётся кадр раз в {m} мин"
    else:
        keep_txt += ", ничего не удаляется"
    return f"""<!doctype html><html lang=ru><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>Camgrabber</title><style>
:root{{--bg:#fff;--fg:#1d2330;--mut:#667;--line:#dde1e8;--ok:#1a7f37;--bad:#c62828;--bar:#e8ebf0;--fill:#3d6fd9}}
@media(prefers-color-scheme:dark){{:root{{--bg:#15181f;--fg:#e6e9ef;--mut:#99a;--line:#2b303b;--ok:#4cc26a;--bad:#ff6b6b;--bar:#2b303b;--fill:#6c97f2}}}}
body{{font:14px system-ui,sans-serif;background:var(--bg);color:var(--fg);margin:0;padding:16px}}
header{{display:flex;align-items:baseline;gap:16px;margin-bottom:12px}}h1{{font-size:20px;margin:0}}h2{{font-size:16px;margin:18px 0 6px}}
.card{{border:1px solid var(--line);border-radius:8px;padding:12px;margin-bottom:14px}}
.bar{{height:10px;background:var(--bar);border-radius:5px;overflow:hidden;margin:8px 0}}.bar i{{display:block;height:100%;background:var(--fill)}}
.wrap{{overflow-x:auto}}table{{border-collapse:collapse;width:100%}}th,td{{text-align:left;padding:6px 8px;border-bottom:1px solid var(--line);vertical-align:middle;white-space:nowrap}}
a{{color:inherit}}th{{color:var(--mut);font-weight:600;font-size:12px}}small{{color:var(--mut);font-weight:400}}.err{{color:var(--bad);white-space:normal;display:block;max-width:260px}}
tr.ok td:nth-child(3){{color:var(--ok)}}tr.bad td:nth-child(3){{color:var(--bad);font-weight:700}}tr.arch{{opacity:.7}}
.th img{{width:128px;height:72px;object-fit:cover;border-radius:4px;display:block}}.warn{{color:#d98200}}
</style></head><body><header><h1>Camgrabber</h1><a href="/settings">&#9881; Настройки</a></header>
<div class=card><b>Диск NAS:</b> занято {fmt_size(total - free)} из {fmt_size(total)} ({used_pct}%), свободно {fmt_size(free)}
<div class=bar><i style="width:{used_pct}%"></i></div>
<small>Архив снимков: {fmt_size(total_bytes)} · {scan_txt}<br>{clean_txt} · {mode_txt} · {keep_txt}</small></div>
{''.join(sections)}<small>Обновлено {datetime.now():%d.%m.%Y %H:%M:%S}</small></body></html>"""


try:
    from PIL import Image
except ImportError:  # без Pillow отдаём оригиналы
    Image = None

FOLDER_RE = re.compile(r"^[a-z0-9_-]{1,64}$")
TIME_RE = re.compile(r"^\d{2}-\d{2}-\d{2}$")
CACHE_MAX = 300 * 1024 * 1024
_cache = OrderedDict()
_cache_size = 0
_cache_lock = threading.Lock()
_resize_slots = threading.Semaphore(3)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "cam_page.html"), encoding="utf-8") as _f:
    CAM_PAGE = _f.read()
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "settings.html"), encoding="utf-8") as _f:
    SETTINGS_PAGE = _f.read()


def cam_dir(folder):
    if not FOLDER_RE.match(folder):
        raise FileNotFoundError(folder)
    path = os.path.join(ROOT, folder)
    if not os.path.isdir(path):
        raise FileNotFoundError(folder)
    return path


def list_days(folder):
    with os.scandir(cam_dir(folder)) as it:
        return sorted(e.name for e in it if DATE_RE.match(e.name) and e.is_dir(follow_symlinks=False))


def list_day(folder, date):
    if not DATE_RE.match(date):
        raise FileNotFoundError(date)
    path = os.path.join(cam_dir(folder), date)
    return sorted(n[11:19] for n in os.listdir(path)
                  if len(n) == 23 and n.endswith(".jpg") and n[:10] == date)


def image_bytes(folder, date, t, w):
    if not (DATE_RE.match(date) and TIME_RE.match(t)):
        raise FileNotFoundError(t)
    path = os.path.join(cam_dir(folder), date, f"{date}_{t}.jpg")
    if w <= 0 or Image is None:
        with open(path, "rb") as f:
            return f.read()
    global _cache_size
    key = (path, w)
    with _cache_lock:
        if key in _cache:
            _cache.move_to_end(key)
            return _cache[key]
    with _resize_slots:
        im = Image.open(path)
        im.draft("RGB", (w, w))
        im = im.convert("RGB")
        im.thumbnail((w, w))
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=70, optimize=True)
        data = buf.getvalue()
    with _cache_lock:
        _cache[key] = data
        _cache_size += len(data)
        while _cache_size > CACHE_MAX and _cache:
            _cache_size -= len(_cache.popitem(last=False)[1])
    return data


PREV_DIR = os.path.join(ROOT, ".previews")
BUNDLE_W = 800
_build_q = queue.Queue()
_queued = set()
_cancel_at = {}
_wanted = {}
_progress = {}
CANCEL_GRACE = 8


class BuildCancelled(Exception):
    pass
_queued_lock = threading.Lock()


def bundle_path(folder, date):
    return os.path.join(PREV_DIR, folder, date + ".bin")


def bundle_header(path):
    try:
        with open(path, "rb") as f:
            (n,) = struct.unpack(">I", f.read(4))
            return json.loads(f.read(n))
    except Exception:
        return None


def resize_jpeg(path, w):
    with _resize_slots:
        im = Image.open(path)
        im.draft("RGB", (w, w))
        im = im.convert("RGB")
        im.thumbnail((w, w))
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=70, optimize=True)
        return buf.getvalue()


def is_cancelled(key):
    """Отмена действует, только если после неё никто не просил этот день (F5 не должен терять сборку)."""
    ca = _cancel_at.get(key)
    return ca is not None and ca > _wanted.get(key, 0) and time.time() - ca > CANCEL_GRACE


def build_bundle(folder, date):
    key = (folder, date)
    names = list_day(folder, date)
    _progress[key] = [0, len(names)]

    def one(t):
        if is_cancelled(key):
            raise BuildCancelled()
        try:
            data = resize_jpeg(os.path.join(ROOT, folder, date, f"{date}_{t}.jpg"), BUNDLE_W)
        except Exception:
            data = None
        _progress[key][0] += 1
        return t, data

    with ThreadPoolExecutor(max_workers=3) as ex:
        results = list(ex.map(one, names))
    parts, items, off = [], [], 0
    for t, data in results:
        if data is None:
            continue
        items.append([t, off, len(data)])
        parts.append(data)
        off += len(data)
    head = json.dumps({"w": BUNDLE_W, "n": len(names), "items": items}).encode()
    path = bundle_path(folder, date)
    os.makedirs(os.path.dirname(path), mode=0o775, exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(struct.pack(">I", len(head)) + head)
        for d in parts:
            f.write(d)
    os.chown(tmp, UID, GID)
    os.chmod(tmp, 0o664)
    os.replace(tmp, path)
    for d in (PREV_DIR, os.path.dirname(path)):
        os.chown(d, UID, GID)
    return len(names), off


def enqueue_bundle(folder, date):
    key = (folder, date)
    with _queued_lock:
        _wanted[key] = time.time()
        if key in _queued:
            return
        _queued.add(key)
    _build_q.put(key)


def cancel_bundle(folder, date):
    """Остановить сборку (или убрать из очереди), если её никто больше не ждёт."""
    key = (folder, date)
    with _queued_lock:
        if key in _queued:
            _cancel_at[key] = time.time()


def bundle_worker():
    while True:
        folder, date = _build_q.get()
        t0 = time.time()
        try:
            if is_cancelled((folder, date)):
                raise BuildCancelled()
            n, size = build_bundle(folder, date)
            log(f"bundle {folder} {date}: {n} frames, {size // 1024 // 1024} MB, {round(time.time() - t0)} s")
        except BuildCancelled:
            log(f"bundle {folder} {date}: cancelled after {round(time.time() - t0)} s")
        except Exception as e:
            log(f"WARN bundle {folder} {date}: {e!r}")
        finally:
            with _queued_lock:
                _queued.discard((folder, date))
                for d in (_cancel_at, _wanted, _progress):
                    d.pop((folder, date), None)


def bundle_state(folder, date):
    names = list_day(folder, date)
    if date >= datetime.now().strftime("%Y-%m-%d") or not names or Image is None:
        return {"state": "live"}
    path = bundle_path(folder, date)
    h = bundle_header(path)
    if h and h.get("n") == len(names):
        return {"state": "ready", "v": int(os.stat(path).st_mtime), "size": os.path.getsize(path)}
    enqueue_bundle(folder, date)
    p = _progress.get((folder, date))
    return {"state": "building", "queued": p is None, "done": p[0] if p else 0, "total": p[1] if p else len(names)}


def enqueue_yesterday():
    day = (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
    with LOCK:
        folders = [f for f, c in STATE["cams"].items() if c["live"]]
    for folder in folders:
        try:
            bundle_state(folder, day)
        except Exception:
            pass


NAME_RE = re.compile(r"^[a-z0-9_-]{1,32}$")


def clean_servers(data):
    items = data.get("servers") if isinstance(data, dict) else None
    if not isinstance(items, list) or not items:
        raise ValueError("нужен хотя бы один сервер")
    out, names = [], set()
    for n, s in enumerate(items, 1):
        name = str(s.get("name", "")).strip().lower()
        if not NAME_RE.match(name):
            raise ValueError(f"сервер {n}: имя только из латинских букв, цифр, - и _ (до 32 символов)")
        if name in names:
            raise ValueError(f"имя {name} повторяется")
        names.add(name)
        urls = {}
        for key, required in (("frigate", True), ("go2rtc", False)):
            url = str(s.get(key, "")).strip().rstrip("/")
            if not url and not required:
                urls[key] = ""
                continue
            parts = urlparse(url)
            if parts.scheme not in ("http", "https") or not parts.netloc:
                raise ValueError(f"{name}: адрес {key} должен быть вида http://адрес:порт")
            urls[key] = url
        aliases = {}
        for k, v in (s.get("aliases") or {}).items():
            k, v = str(k).strip(), str(v).strip().lower()
            if not k or len(k) > 64 or not NAME_RE.match(v):
                raise ValueError(f"{name}: неверная замена имени {k}={v}")
            aliases[k] = v
        out.append({"name": name, "frigate": urls["frigate"], "go2rtc": urls["go2rtc"], "aliases": aliases})
    return out


def _int(data, key, default, lo, hi, what):
    raw = str(data.get(key) if data.get(key) is not None else "").strip()
    try:
        v = int(raw) if raw else default
    except ValueError:
        raise ValueError(f"{what}: нужно целое число")
    if not lo <= v <= hi:
        raise ValueError(f"{what}: от {lo} до {hi}")
    return v


def clean_settings(data):
    out = {"servers": clean_servers(data)}
    out["interval"] = _int(data, "interval", 1, 1, 60, "частота снимков, минут")
    out["keep_days"] = _int(data, "keep_days", 0, 0, 36500, "срок хранения всех снимков, дней")
    out["thin_every"] = _int(data, "thin_every", 5, 1, 1440, "частота оставляемых снимков, минут")
    if out["keep_days"] > 0 and out["thin_every"] % out["interval"] != 0:
        raise ValueError(f"оставляемые снимки раз в {out['thin_every']} мин: число должно делиться на частоту съёмки ({out['interval']} мин)")
    return out


def apply_settings(cfg):
    os.makedirs(os.path.dirname(SETTINGS_FILE), exist_ok=True)
    tmp = SETTINGS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)
    os.replace(tmp, SETTINGS_FILE)
    SERVERS[:] = [Server(c) for c in cfg["servers"]]
    apply_loaded(cfg)
    log(f"settings saved: servers={', '.join(c['name'] for c in cfg['servers'])}, "
        f"interval={cfg['interval']}, keep_days={cfg['keep_days']}, thin_every={cfg['thin_every']}")


def test_server(frigate, go2rtc):
    parts = urlparse(frigate)
    if parts.scheme not in ("http", "https") or not parts.netloc:
        raise ValueError("адрес Frigate должен быть вида http://адрес:порт")
    frigate = frigate.rstrip("/")
    version = fetch(frigate + "/api/version", timeout=5, deadline=8).decode(errors="replace").strip()[:40]
    cfg = json.loads(fetch(frigate + "/api/config", timeout=8, deadline=15))
    cams = [n for n, c in cfg["cameras"].items() if c.get("enabled", True)]
    streams = None
    if go2rtc:
        streams = len(json.loads(fetch(go2rtc.rstrip("/") + "/api/streams", timeout=5, deadline=8)))
    return {"version": version, "cameras": cams, "go2rtc": streams}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype, cache="no-store"):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", cache)
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        path = self.path.split("?")[0]
        try:
            if path.startswith("/api/bundle-cancel/"):
                folder, date = path[19:].split("/")
                cam_dir(folder)
                if not DATE_RE.match(date):
                    raise ValueError(date)
                cancel_bundle(folder, date)
                self.send(200, b"{}", "application/json")
            elif path in ("/api/settings", "/api/settings/test"):
                if not self.same_origin_json():
                    return self.send(403, b'{"error": "forbidden"}', "application/json")
                body = json.loads(self.rfile.read(min(int(self.headers.get("Content-Length", 0)), 65536)) or b"{}")
                try:
                    if path == "/api/settings":
                        apply_settings(clean_settings(body))
                        result = {"ok": True}
                    else:
                        result = test_server(str(body.get("frigate", "")).strip(), str(body.get("go2rtc", "")).strip())
                    self.send(200, json.dumps(result, ensure_ascii=False).encode(), "application/json")
                except Exception as e:
                    self.send(400, json.dumps({"error": str(e)[:200]}, ensure_ascii=False).encode(), "application/json")
            else:
                self.send(404, b"not found", "text/plain")
        except (FileNotFoundError, ValueError):
            self.send(404, b"not found", "text/plain")

    def same_origin_json(self):
        """Защита от чужих сайтов: только JSON и только со страницы с того же адреса."""
        if "application/json" not in self.headers.get("Content-Type", ""):
            return False
        origin = self.headers.get("Origin")
        return origin is None or urlparse(origin).netloc == self.headers.get("Host")

    def do_GET(self):
        path = self.path.split("?")[0]
        try:
            if path == "/":
                self.send(200, page().encode(), "text/html; charset=utf-8")
            elif path == "/settings":
                self.send(200, SETTINGS_PAGE.encode(), "text/html; charset=utf-8")
            elif path == "/api/settings":
                self.send(200, json.dumps({"servers": [x.cfg() for x in SERVERS], **SETTINGS}, ensure_ascii=False).encode(), "application/json")
            elif path == "/api/status":
                with LOCK:
                    body = json.dumps(STATE, ensure_ascii=False).encode()
                self.send(200, body, "application/json; charset=utf-8")
            elif path.startswith("/cam/"):
                cam_dir(path[5:])
                self.send(200, CAM_PAGE.replace("__FOLDER__", path[5:]).encode(), "text/html; charset=utf-8")
            elif path.startswith("/api/days/"):
                self.send(200, json.dumps({"days": list_days(path[10:])}).encode(), "application/json")
            elif path.startswith("/api/bundle/"):
                folder, date = path[12:].split("/")
                self.send(200, json.dumps(bundle_state(folder, date)).encode(), "application/json")
            elif path.startswith("/bundle/"):
                folder, date = path[8:].split("/")
                cam_dir(folder)
                if not DATE_RE.match(date):
                    raise FileNotFoundError(date)
                with open(bundle_path(folder, date), "rb") as f:
                    size = os.fstat(f.fileno()).st_size
                    self.send_response(200)
                    self.send_header("Content-Type", "application/octet-stream")
                    self.send_header("Content-Length", str(size))
                    self.send_header("Cache-Control", "public, max-age=86400")
                    self.end_headers()
                    shutil.copyfileobj(f, self.wfile, 1 << 20)
            elif path.startswith("/api/day/"):
                folder, date = path[9:].split("/")
                self.send(200, json.dumps({"files": list_day(folder, date)}).encode(), "application/json")
            elif path.startswith("/img/"):
                folder, date, t = path[5:].split("/")
                q = self.path.partition("?")[2]
                w = int(q.split("w=")[1].split("&")[0]) if "w=" in q else 0
                w = min(max(w, 0), 2560)
                self.send(200, image_bytes(folder, date, t, w), "image/jpeg", "public, max-age=86400")
            elif path.startswith("/thumb/"):
                with LOCK:
                    c = STATE["cams"].get(path[7:])
                srv = next((x for x in SERVERS if c and x.name == c["server"]), None)
                if not srv:
                    return self.send(404, b"no such camera", "text/plain")
                data = fetch(f"{srv.frigate}/api/{c['cam']}/latest.jpg?h=144", timeout=6, deadline=10)
                self.send(200, data, "image/jpeg", "max-age=30")
            else:
                self.send(404, b"not found", "text/plain")
        except (FileNotFoundError, ValueError):
            try:
                self.send(404, b"not found", "text/plain")
            except Exception:
                pass
        except Exception as e:
            try:
                self.send(502, str(e).encode(), "text/plain")
            except Exception:
                pass


def run():
    cfg = load_config()
    SERVERS.extend(Server(c) for c in cfg["servers"])
    apply_loaded(cfg)
    os.makedirs(ROOT, exist_ok=True)
    load_state()
    threading.Thread(target=ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), Handler).serve_forever, daemon=True).start()
    threading.Thread(target=lambda: (time.sleep(20), _safe_scan()), daemon=True).start()
    threading.Thread(target=bundle_worker, daemon=True).start()
    last_clean_day = last_bundle_day = None
    pool = ThreadPoolExecutor(max_workers=8)
    boot = time.time()

    def watchdog():
        while True:
            time.sleep(60)
            try:
                last = float(open(HEARTBEAT).read())
            except Exception:
                last = boot
            if time.time() - last > max(WATCHDOG_SECONDS, SETTINGS["interval"] * 120 + 300):
                log("FATAL no successful cycle for 15 min, exiting for restart")
                os._exit(1)

    threading.Thread(target=watchdog, daemon=True).start()
    log(f"started, root={ROOT}, servers={[s.name for s in SERVERS]}")
    while True:
        nxt = (int(time.time() // 60) + 1) * 60
        time.sleep(max(0, nxt - time.time()))
        try:
            now_ = datetime.now()
            if (now_.hour * 60 + now_.minute) % SETTINGS["interval"] == 0:
                cycle(list(SERVERS), pool)
        except Exception as e:
            log(f"ERROR cycle: {e!r}")
        now = datetime.now()
        if now.hour == 0 and now.minute >= 10 and last_bundle_day != now.date():
            last_bundle_day = now.date()
            threading.Thread(target=enqueue_yesterday, daemon=True).start()
        if now.hour == CLEAN_HOUR and last_clean_day != now.date():
            last_clean_day = now.date()
            threading.Thread(target=lambda: _safe_clean(), daemon=True).start()


def _safe_clean():
    try:
        clean()
    except Exception as e:
        log(f"ERROR clean: {e!r}")
    _safe_scan()


def _safe_scan():
    try:
        scan()
    except Exception as e:
        log(f"ERROR scan: {e!r}")


def backfill(dry=False):
    """Достаёт кадры раз в 5 минут из записей Frigate туда, где снимков нет (повторный запуск безопасен)."""
    cfg = load_config()
    apply_loaded(cfg)
    servers = [Server(c) for c in cfg["servers"]]
    every = SETTINGS["thin_every"] if SETTINGS["thin_every"] % SETTINGS["interval"] == 0 else SETTINGS["interval"]
    step = every * 60
    off = int(datetime.now().astimezone().utcoffset().total_seconds())
    now = time.time()
    listed = {}

    def exists(folder, t):
        d = datetime.fromtimestamp(t)
        key = (folder, d.strftime("%Y-%m-%d"))
        if key not in listed:
            path = os.path.join(ROOT, folder, key[1])
            listed[key] = {n[:16] for n in os.listdir(path)} if os.path.isdir(path) else set()
        return d.strftime("%Y-%m-%d_%H-%M") in listed[key]

    jobs = []
    for s in servers:
        s.refresh()
        for cam, folder in s.cams:
            try:
                segs = json.loads(fetch(f"{s.frigate}/api/{cam}/recordings?after={int(now - 30 * 86400)}&before={int(now)}",
                                        timeout=120, deadline=300))
            except Exception as e:
                log(f"backfill {folder}: cant list recordings ({e})")
                continue
            iv = sorted((x["start_time"], x["end_time"]) for x in segs)
            if not iv:
                continue
            t, i, n = ((int(iv[0][0]) + off) // step + 1) * step - off, 0, 0
            while t < now:
                while i < len(iv) and iv[i][1] <= t:
                    i += 1
                if i < len(iv) and iv[i][0] <= t and not exists(folder, t):
                    jobs.append((s, cam, folder, t))
                    n += 1
                t += step
            log(f"backfill {folder}: {n} frames missing since {datetime.fromtimestamp(iv[0][0]):%Y-%m-%d %H:%M}")
    log(f"backfill total {len(jobs)} frames" + (" (dry run)" if dry else ""))
    if dry:
        return

    def one(job):
        s, cam, folder, t = job
        for attempt in (1, 2, 3):
            try:
                data = check(fetch(f"{s.frigate}/api/{cam}/recordings/{t + 1}/snapshot.jpg", timeout=30))
                save(folder, data, datetime.fromtimestamp(t))
                return True
            except Exception as e:
                err = e
                time.sleep(2)
        log(f"WARN backfill {folder} {datetime.fromtimestamp(t):%Y-%m-%d %H:%M}: {err}")
        return False

    done = failed = 0
    with ThreadPoolExecutor(max_workers=2) as pool:
        for ok in pool.map(one, jobs):
            done += ok
            failed += not ok
            if (done + failed) % 500 == 0:
                log(f"backfill progress {done + failed}/{len(jobs)} (failed {failed})")
    log(f"backfill finished: saved {done}, failed {failed}")


def health():
    try:
        age = time.time() - float(open(HEARTBEAT).read())
    except Exception:
        age = 1e9
    try:
        apply_loaded(load_config())
    except Exception:
        pass
    sys.exit(0 if age < max(420, SETTINGS["interval"] * 120 + 120) else 1)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "run"
    if cmd == "backfill":
        backfill("--dry" in sys.argv)
    else:
        {"run": run, "clean": clean, "health": health}[cmd]()
