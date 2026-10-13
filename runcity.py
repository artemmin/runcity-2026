#!/usr/bin/env python3
"""
Runcity (Бегущий Город) 2026 — сбор прохождения КП и визуализация на карте
===========================================================================

Источники:
  /ru/events/2026/result/                  — список категорий
  /ru/events/2026/routes/{cat}/            — КП с координатами, этапами, бонусами (статика)
  /ru/events/2026/result/{cat}/            — команды, места, НЕвзятые КП/бонусы (статика)
  /ru/events/2026/result/{cat}/?view_gpx=ID  — GPS-трек + время на КП (inline JSON)

Команды:
  python runcity.py probe "URL_ТРЕКА"         # что лежит в inline JSON страницы трека
  python runcity.py scrape                    # маршруты + результаты
  python runcity.py scrape --tracks           # + GPS-треки и время на КП
  python runcity.py scrape --cats atlant-pro,lion-pro --tracks --tracks-limit 20
  python runcity.py map                       # HTML-карты + CSV статистики
  python runcity.py all                       # scrape --tracks + map

pip install requests beautifulsoup4 lxml folium

В zsh URL с «?» берите в кавычки.
"""

import argparse
import csv
import hashlib
import html as htmllib
import json
import logging
import math
import random
import re
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from statistics import mean
from typing import Optional
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup, NavigableString, Tag

# ─────────────────────────── Настройки ─────────────────────────────

YEAR         = 2026
BASE         = "https://www.runcity.org"
RESULT_INDEX = f"{BASE}/ru/events/{YEAR}/result/"
ROUTE_URL    = f"{BASE}/ru/events/{YEAR}/routes/{{cat}}/"
RESULT_URL   = f"{BASE}/ru/events/{YEAR}/result/{{cat}}/"

DATA_DIR  = Path("runcity_data")
CACHE_DIR = DATA_DIR / "cache"     # сырые HTML — повторный запуск не ходит в сеть
DEBUG_DIR = DATA_DIR / "debug"
MAPS_DIR  = Path("runcity_maps")

ONLINE_CATS = {"gonka1", "progulka1"}   # онлайн-категории — без реальных координат
DELAY       = (0.7, 1.8)
GPS_MIN_STEP_M = 15      # прореживание GPS: ~7000 точек → ~1500
MSK_OFFSET  = 3 * 3600   # ts на сайте — unix UTC
TRACK_HOURS = (8, 23)     # GPS на картах и в повторе — только с 08:00 до 23:00 МСК
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("runcity")

CP_HREF   = re.compile(r"/routes/cp(\d+)/?$")
OSM_RE    = re.compile(r"mlat=([\d.]+)&(?:amp;)?mlon=([\d.]+)")
BONUS_RE  = re.compile(r"Дает бонус\s+(\d+)\s*мин")


def norm_cp(s) -> str:
    """'06' и '6' — один и тот же КП."""
    return str(int(s))


# ─────────────────────────── Модели ────────────────────────────────

@dataclass
class ControlPoint:
    cp:        str             # нормализованный номер ("6")
    label:     str             # как на сайте ("06")
    stage:     str
    stage_idx: int
    kind:      str = "cp"      # start | cp | bonus | finish
    address:   str = ""
    lat:       Optional[float] = None
    lon:       Optional[float] = None
    bonus_min: Optional[int] = None
    desc:      str = ""             # где искать: «Памятник рядом с фонтаном»
    quest:     str = ""             # текст задания
    answer:    str = ""             # правильный ответ
    history:   str = ""             # историческая справка
    history_images: list = field(default_factory=list)


@dataclass
class Team:
    team_id:        str
    number:         str
    name:           str
    category:       str
    place:          str = ""
    start:          str = ""
    finish:         str = ""
    time_on_course: str = ""
    taken:          Optional[int] = None
    penalty:        str = ""
    total:          str = ""
    members:        int = 0
    missed_cps:     list = field(default_factory=list)
    missed_bonuses: list = field(default_factory=list)
    track_type:     Optional[str] = None   # passing | gpx
    track_url:      Optional[str] = None
    track_fetched:  bool = False
    passing:        list = field(default_factory=list)   # [{"cp","time","src"}]
    gps_track:      list = field(default_factory=list)   # [[lat, lon, unix_ts], ...]


# ─────────────────────────── HTTP ──────────────────────────────────

_session = requests.Session()
_session.headers.update({"User-Agent": UA, "Accept-Language": "ru-RU,ru;q=0.9"})


def get_html(url: str, refresh: bool = False, cache: bool = True) -> str:
    path = CACHE_DIR / f"{hashlib.md5(url.encode()).hexdigest()}.html"
    if cache and path.exists() and not refresh:
        return path.read_text("utf-8")
    for attempt in range(1, 4):
        try:
            r = _session.get(url, timeout=30)
            r.raise_for_status()
            r.encoding = r.encoding or "utf-8"
            if cache:
                CACHE_DIR.mkdir(parents=True, exist_ok=True)
                path.write_text(r.text, "utf-8")
            time.sleep(random.uniform(*DELAY))
            return r.text
        except requests.RequestException as e:
            log.warning(f"{url} (попытка {attempt}): {e}")
            time.sleep(3 * attempt)
    raise RuntimeError(f"Не удалось загрузить {url}")


# ─────────────────────── Парсинг: категории ────────────────────────

def parse_categories(html: str) -> dict[str, str]:
    soup = BeautifulSoup(html, "lxml")
    pat = re.compile(rf"/events/{YEAR}/result/([\w-]+)/?$")
    cats: dict[str, str] = {}
    for a in soup.find_all("a", href=True):
        u = urlparse(a["href"])
        m = pat.search(u.path)
        if m and not u.query:
            cats.setdefault(m.group(1), a.get_text(strip=True))
    return cats


# ─────────────────────── Парсинг: маршрут ──────────────────────────

IMG_HREF   = re.compile(r"img\.runcity\.org/storage/")
FIGURE_CAP = re.compile(r"^Рисунок к КП\s*\d+$")


def _clean_text(parts: list[str]) -> str:
    text = "".join(parts)
    text = re.sub(r"[ \t\r\f\v]+", " ", text)
    text = re.sub(r" *\n *", "\n", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def parse_route(html: str) -> list[ControlPoint]:
    """
    Идём по документу последовательно:
      h2/h3                          → этап (Старт / Этап N / Бонусные КП / Финиш)
      <a href=/routes/cpNN/>         → новый КП, текст после ссылки — адрес
      первая ссылка на OSM           → координаты
      первая <a href="#"> после них  → текст задания (фолбэк, точнее — cpData)
      первый <b>/<strong> после него → правильный ответ (фолбэк)
      «Дает бонус N минут»           → бонус
      h4 «Историческая справка»      → всё до следующего КП/этапа — справка и картинки
    """
    soup = BeautifulSoup(html, "lxml")
    cps: dict[str, ControlPoint] = {}
    stage, stage_idx, kind = "", 0, "cp"
    cur: Optional[ControlPoint] = None
    in_history = False
    history_parts: list[str] = []

    def close_history():
        nonlocal in_history, history_parts
        if cur is not None and in_history:
            cur.history = _clean_text(history_parts)
        in_history, history_parts = False, []

    for node in soup.descendants:
        if isinstance(node, Tag):
            if node.name in ("h2", "h3"):
                close_history()
                title = node.get_text(" ", strip=True)
                if title.startswith("Старт"):
                    stage, stage_idx, kind = "Старт", 0, "start"
                elif title.startswith("Финиш"):
                    stage, stage_idx, kind = "Финиш", 99, "finish"
                elif title.startswith("Этап"):
                    m = re.search(r"\d+", title)
                    stage_idx = int(m.group()) if m else stage_idx + 1
                    stage, kind = title, "cp"
                elif title.startswith("Бонус"):
                    stage, kind = "Бонусные КП", "bonus"
                elif stage:                       # любой другой заголовок — конец маршрута
                    stage, cur = "", None
                continue

            if node.name == "h4" and cur and "Историческая справка" in node.get_text():
                close_history()
                in_history = True
                continue

            if in_history:
                if node.name in ("br", "p", "div"):
                    history_parts.append("\n")
                if node.name == "img" and node.parent is not None and node.parent.name == "a" \
                        and IMG_HREF.search(node.parent.get("href", "")):
                    src_url = None            # миниатюра внутри ссылки на полную картинку
                else:
                    src_url = node.get("src") if node.name == "img" else node.get("href") if node.name == "a" else None
                if src_url and IMG_HREF.search(src_url):
                    full = urljoin(BASE, src_url)
                    if full not in cur.history_images:
                        cur.history_images.append(full)

            if node.name == "a" and node.has_attr("href"):
                href = node["href"]
                m = CP_HREF.search(urlparse(href).path)
                if m and stage:
                    close_history()
                    label = node.get_text(strip=True) or m.group(1)
                    key = norm_cp(label)
                    if key in cps:
                        cur = cps[key]
                        continue
                    sib = node.next_sibling
                    addr = sib.strip() if isinstance(sib, NavigableString) else ""
                    cur = ControlPoint(cp=key, label=label, stage=stage,
                                       stage_idx=stage_idx, kind=kind, address=addr)
                    cps[key] = cur
                    continue
                if cur and cur.lat is None and "openstreetmap" in href:
                    mm = OSM_RE.search(href)
                    if mm:
                        cur.lat, cur.lon = float(mm.group(1)), float(mm.group(2))
                    continue
                if (cur and cur.lat is not None and not in_history and not cur.quest
                        and href.startswith("#") and node.get_text(strip=True)):
                    cur.quest = node.get_text(" ", strip=True)
                    continue

            if (node.name in ("b", "strong") and cur and cur.quest and not cur.answer
                    and not in_history and not node.find("a")):
                cur.answer = node.get_text(" ", strip=True)

        elif isinstance(node, NavigableString) and cur:
            if in_history:
                if node.find_parent("h4") is None and not FIGURE_CAP.match(node.strip()):
                    history_parts.append(str(node))
                continue
            mb = BONUS_RE.search(node)
            if mb:
                cur.bonus_min = int(mb.group(1))

    close_history()
    return list(cps.values())


def enrich_from_cpdata(cps: list[ControlPoint], cp_data: dict):
    """Точные desc/quest/answer из cpData страницы прохождения поверх разбора маршрута."""
    by_key = {c.cp: c for c in cps}
    for v in (cp_data.values() if isinstance(cp_data, dict) else cp_data):
        num = str(v.get("number", "")).strip()
        c = by_key.get(norm_cp(num)) if num.isdigit() else None
        if not c:
            continue
        for fld in ("desc", "quest", "answer"):
            val = (v.get(fld) or "").strip()
            if val:
                setattr(c, fld, BeautifulSoup(val, "lxml").get_text(" ", strip=True))
        if not c.address and v.get("address"):
            c.address = v["address"].strip()


# ─────────────────────── Парсинг: результаты ───────────────────────

HEADER_MAP = {
    "Место": "place", "Номер команды": "number", "Название команды": "name",
    "Старт": "start", "Финиш": "finish", "Время на трассе": "time_on_course",
    "Взято КП": "taken", "Штраф и/или бонус": "penalty", "Итоговое время": "total",
}


def _parse_detail_row(tr: Tag, team: Team):
    """Строка-подвал команды: участники + «Невзятые КП» / «Невзятые бонусы»."""
    people = {a["href"] for a in tr.find_all("a", href=re.compile(r"/people/\d+"))}
    team.members = max(team.members, len(people))

    mode = None
    for node in tr.descendants:
        if isinstance(node, NavigableString):
            t = node.strip()
            if t.startswith("Невзятые КП"):
                mode = "cp"
            elif t.startswith("Невзятые бонус"):
                mode = "bonus"
        elif isinstance(node, Tag) and node.name == "a" and node.has_attr("href") and mode:
            m = CP_HREF.search(urlparse(node["href"]).path)
            if m:
                cp = norm_cp(node.get_text(strip=True) or m.group(1))
                lst = team.missed_cps if mode == "cp" else team.missed_bonuses
                if cp not in lst:
                    lst.append(cp)


def parse_results(html: str, cat: str) -> list[Team]:
    soup = BeautifulSoup(html, "lxml")
    teams: dict[str, Team] = {}

    for table in soup.find_all("table"):
        headers = [th.get_text(" ", strip=True) for th in table.find_all("th")]
        if "Номер команды" not in headers:
            continue
        col = {HEADER_MAP[h]: i for i, h in enumerate(headers) if h in HEADER_MAP}
        cur: Optional[Team] = None

        for tr in table.find_all("tr"):
            tds = tr.find_all("td", recursive=False)
            if not tds:
                continue
            id_link = tr.find("a", title=re.compile(r"^\d+$"))

            if id_link and len(tds) >= len(col):            # основная строка команды
                def cell(k):
                    i = col.get(k)
                    return tds[i].get_text(" ", strip=True) if i is not None and i < len(tds) else ""

                tid = id_link["title"]
                if tid not in teams:
                    taken = cell("taken")
                    t = Team(
                        team_id=tid, number=id_link.get_text(strip=True),
                        name=cell("name"), category=cat, place=cell("place"),
                        start=cell("start"), finish=cell("finish"),
                        time_on_course=cell("time_on_course"),
                        taken=int(taken) if taken.isdigit() else None,
                        penalty=cell("penalty"), total=cell("total"),
                    )
                    track = tr.find("a", href=re.compile(r"view_(passing|gpx)="))
                    if track:
                        t.track_type = "passing" if "view_passing" in track["href"] else "gpx"
                        t.track_url = urljoin(BASE, track["href"])
                    teams[tid] = t
                cur = teams[tid]
            elif cur:                                           # подвал команды
                _parse_detail_row(tr, cur)

    return list(teams.values())


# ─────────────────────── Треки (inline JSON) ───────────────────────
#
# Страница ?view_gpx=ID (и ?view_passing=ID) содержит в inline-скрипте:
#   var points_raw = JSON.parse('[{"lat","lon","ts","ts_fmt"}, ...]')        — GPS-трек
#   var cpData     = JSON.parse('{"<id>": {"number","lat","lng","ts_fmt"}}')   — отметки на КП
# Браузер не нужен: строки — экранированный JSON внутри JS-литерала.

JS_JSON_RE = re.compile(
    r"var\s+(\w+)\s*=\s*(?:\w+\()?JSON\.parse\('((?:[^'\\]|\\.)*)'\)", re.S)


def extract_js_json(html: str) -> dict:
    """Все `var X = JSON.parse('...')` со страницы → {X: python-объект}."""
    out = {}
    for m in JS_JSON_RE.finditer(html):
        lit = m.group(2).replace("\\'", "'")
        for candidate in (lit, re.sub(r'(?<!\\)"', r'\\"', lit)):   # 2-я попытка: неэкранированные "
            try:
                out[m.group(1)] = json.loads(json.loads(f'"{candidate}"'))
                break
            except json.JSONDecodeError:
                continue
        else:
            log.debug(f"Не разобран JSON в переменной {m.group(1)}")
    return out


def haversine_m(a_lat, a_lon, b_lat, b_lon) -> float:
    r = 6_371_000
    p1, p2 = math.radians(a_lat), math.radians(b_lat)
    dp, dl = p2 - p1, math.radians(b_lon - a_lon)
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(h))


def to_minutes(t: Optional[str]) -> Optional[float]:
    if not t:
        return None
    parts = [int(x) for x in t.split(":")]
    return parts[0] * 60 + parts[1] + (parts[2] / 60 if len(parts) > 2 else 0)


def thin_track(points: list, min_m: float = GPS_MIN_STEP_M) -> list:
    """Прореживание: точка сохраняется, если ушли от предыдущей на ≥ min_m."""
    if not points:
        return []
    out = [points[0]]
    for p in points[1:]:
        if haversine_m(out[-1][0], out[-1][1], p[0], p[1]) >= min_m:
            out.append(p)
    if out[-1] is not points[-1]:
        out.append(points[-1])
    return out


def parse_track_html(html: str, start: str = "") -> tuple[list, list]:
    """→ (passing [{"cp","time"}] по порядку взятия, gps [[lat, lon, unix_ts], ...])."""
    data = extract_js_json(html)

    passing = []
    cp_data = data.get("cpData") or {}
    for v in (cp_data.values() if isinstance(cp_data, dict) else cp_data):
        num = str(v.get("number", "")).strip()
        t = v.get("ts_fmt") or v.get("tsFmt")
        if num.isdigit() and t:
            passing.append({"cp": norm_cp(num), "time": t})

    # сортировка по времени с учётом перехода через полночь
    start_min = to_minutes(start) or 0
    passing.sort(key=lambda p: to_minutes(p["time"]) + (1440 if to_minutes(p["time"]) < start_min - 60 else 0))

    gps = []
    for p in data.get("points_raw") or []:
        try:
            gps.append([round(float(p["lat"]), 6), round(float(p["lon"]), 6), int(p["ts"])])
        except (KeyError, TypeError, ValueError):
            continue
    gps.sort(key=lambda p: p[2])
    return passing, thin_track(gps)


def track_urls(team: dict) -> list[str]:
    base = RESULT_URL.format(cat=team["category"])
    tid = team["team_id"]
    # view_gpx отдаёт и GPS, и отметки; view_passing — только отметки (запасной вариант)
    return [f"{base}?view_gpx={tid}", f"{base}?view_passing={tid}"]


def probe(url: str):
    """Что лежит в inline JSON страницы трека."""
    html = get_html(url, refresh=True, cache=False)
    DEBUG_DIR.mkdir(parents=True, exist_ok=True)
    (DEBUG_DIR / "track.html").write_text(html, "utf-8")
    for name, obj in extract_js_json(html).items():
        sample = next(iter(obj.values())) if isinstance(obj, dict) and obj else (obj[0] if obj else None)
        log.info(f"var {name}: {type(obj).__name__}[{len(obj)}], пример: {str(sample)[:200]}")
    passing, gps = parse_track_html(html)
    log.info(f"Итого: отметок на КП {len(passing)}, GPS-точек после прореживания {len(gps)}")


# ─────────────────────────── Scrape ────────────────────────────────

def cat_path(cat: str) -> Path:
    return DATA_DIR / f"{cat}.json"


def save_json(path: Path, data: dict):
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")), "utf-8")


def scrape_static(only: Optional[set], with_online: bool, refresh: bool) -> list[Path]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    cats = parse_categories(get_html(RESULT_INDEX, refresh))
    log.info(f"Категорий на сайте: {len(cats)}")
    paths = []
    for cat, title in cats.items():
        if only and cat not in only:
            continue
        if cat in ONLINE_CATS and not with_online:
            continue
        cps = parse_route(get_html(ROUTE_URL.format(cat=cat), refresh))
        teams = parse_results(get_html(RESULT_URL.format(cat=cat), refresh), cat)

        # задания и ответы: cpData со страницы прохождения любой стартовавшей команды
        sample = next((t for t in teams if t.start), None)
        if sample and cps:
            try:
                url = f"{RESULT_URL.format(cat=cat)}?view_passing={sample.team_id}"
                enrich_from_cpdata(cps, extract_js_json(get_html(url, refresh)).get("cpData") or {})
            except RuntimeError as e:
                log.warning(f"[{cat}] cpData не получен: {e}")

        # не затираем уже скачанные треки
        old = json.loads(cat_path(cat).read_text("utf-8")) if cat_path(cat).exists() else {}
        old_tracks = {t["team_id"]: t for t in old.get("teams", []) if t.get("track_fetched")}
        team_dicts = []
        for t in teams:
            d = asdict(t)
            if t.team_id in old_tracks:
                for k in ("passing", "gps_track", "track_fetched"):
                    d[k] = old_tracks[t.team_id][k]
            team_dicts.append(d)

        save_json(cat_path(cat), {"category": cat, "title": title,
                                  "cps": [asdict(c) for c in cps], "teams": team_dicts})
        with_coords = sum(c.lat is not None for c in cps)
        with_quest = sum(bool(c.quest) for c in cps)
        with_hist = sum(bool(c.history) for c in cps)
        log.info(f"[{cat}] {title}: КП {len(cps)} (коорд. {with_coords}, заданий {with_quest}, "
                 f"справок {with_hist}), команд {len(teams)}")
        paths.append(cat_path(cat))
    return paths


def scrape_tracks(paths: list[Path], limit: int, refresh: bool):
    done = 0
    for path in paths:
        data = json.loads(path.read_text("utf-8"))
        todo = [t for t in data["teams"] if t["start"] and (refresh or not t["track_fetched"])]
        log.info(f"[{data['category']}] треков к загрузке: {len(todo)}")
        for t in todo:
            if limit and done >= limit:
                break
            passing, gps = [], []
            for url in track_urls(t):
                try:
                    html = get_html(url, refresh=refresh, cache=False)   # страницы по ~700 КБ — не кешируем
                except RuntimeError as e:
                    log.warning(f"  {t['number']}: {e}")
                    continue
                p, g = parse_track_html(html, t["start"])
                passing = passing or p
                # на view_passing points_raw — это координаты КП, а не GPS
                if "view_gpx" in url:
                    gps = gps or g
                if passing and gps:
                    break
            t["passing"], t["gps_track"], t["track_fetched"] = passing, gps, True
            log.info(f"  {t['number']}: отметок {len(passing)}, GPS-точек {len(gps)}")
            done += 1
            if done % 10 == 0:                     # чекпоинт
                save_json(path, data)
        save_json(path, data)


# ─────────────────────────── Аналитика ─────────────────────────────

def active_teams(data: dict) -> list[dict]:
    return [t for t in data["teams"] if t.get("taken") is not None and t.get("start")]


def compute_cp_stats(data: dict) -> dict[str, dict]:
    teams = active_teams(data)
    stats = {}
    for c in data["cps"]:
        if c["kind"] in ("start", "finish"):
            stats[c["cp"]] = {"teams": len(teams), "taken": None, "rate": None, "missed_by": []}
            continue
        key = "missed_bonuses" if c["kind"] == "bonus" else "missed_cps"
        missed = [t["number"] for t in teams if c["cp"] in t[key]]
        n = len(teams)
        stats[c["cp"]] = {"teams": n, "taken": n - len(missed),
                          "rate": (n - len(missed)) / n if n else None, "missed_by": missed}
    return stats


def place_key(t: dict) -> int:
    return int(t["place"]) if str(t.get("place", "")).isdigit() else 10_000


def export_csv(all_data: list[dict]):
    MAPS_DIR.mkdir(exist_ok=True)
    with open(MAPS_DIR / "cp_stats.csv", "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["category", "cp", "stage", "kind", "address", "lat", "lon",
                    "bonus_min", "teams", "taken", "rate",
                    "desc", "quest", "answer", "history", "history_images"])
        for d in all_data:
            st = compute_cp_stats(d)
            for c in d["cps"]:
                s = st[c["cp"]]
                w.writerow([d["category"], c["label"], c["stage"], c["kind"], c["address"],
                            c["lat"], c["lon"], c["bonus_min"], s["teams"], s["taken"],
                            round(s["rate"], 3) if s["rate"] is not None else "",
                            c.get("desc", ""), c.get("quest", ""), c.get("answer", ""),
                            c.get("history", ""), " ".join(c.get("history_images", []))])
    with open(MAPS_DIR / "teams.csv", "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["category", "place", "number", "name", "members", "start", "finish",
                    "time_on_course", "taken", "penalty", "total",
                    "missed_cps", "missed_bonuses", "track_type", "track_cps", "gps_points", "gps_km"])
        for d in all_data:
            for t in sorted(d["teams"], key=place_key):
                w.writerow([d["category"], t["place"], t["number"], t["name"], t["members"],
                            t["start"], t["finish"], t["time_on_course"], t["taken"],
                            t["penalty"], t["total"], " ".join(t["missed_cps"]),
                            " ".join(t["missed_bonuses"]), t["track_type"],
                            len(t["passing"]), len(t["gps_track"]), round(gps_km(t["gps_track"]), 2)])

    # Сплиты: время и расстояние между последовательными отметками на КП
    with open(MAPS_DIR / "splits.csv", "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["category", "place", "number", "name", "order", "cp", "stage", "time",
                    "min_from_start", "leg_min", "leg_km_straight"])
        for d in all_data:
            cps = {c["cp"]: c for c in d["cps"]}
            for t in sorted(d["teams"], key=place_key):
                start = to_minutes(t["start"])
                prev_min, prev_cp = start, next((c for c in cps.values() if c["kind"] == "start"), None)
                marks = [p for p in t["passing"]
                         if cps.get(p["cp"], {}).get("kind") not in ("start", "finish")]
                for n, p in enumerate(marks, 1):
                    c, m = cps.get(p["cp"]), to_minutes(p["time"])
                    if m is not None and start is not None and m < start - 60:
                        m += 1440                                     # после полуночи
                    leg_km = (haversine_m(prev_cp["lat"], prev_cp["lon"], c["lat"], c["lon"]) / 1000
                              if c and prev_cp and c["lat"] and prev_cp["lat"] else None)
                    w.writerow([d["category"], t["place"], t["number"], t["name"], n,
                                c["label"] if c else p["cp"], c["stage"] if c else "", p["time"],
                                round(m - start) if m is not None and start is not None else "",
                                round(m - prev_min) if m is not None and prev_min is not None else "",
                                round(leg_km, 2) if leg_km is not None else ""])
                    prev_min, prev_cp = m, c or prev_cp


def clip_track(track: list, hours: tuple = TRACK_HOURS) -> list:
    """Оставляет GPS-точки с hours[0]:00 до hours[1]:00 по Москве (включительно)."""
    lo, hi = hours[0] * 3600, hours[1] * 3600
    return [p for p in track if lo <= (p[2] + MSK_OFFSET) % 86400 <= hi]


def with_clipped_gps(team: dict) -> dict:
    return {**team, "gps_track": clip_track(team["gps_track"])}


def gps_km(track: list) -> float:
    return sum(haversine_m(a[0], a[1], b[0], b[1]) for a, b in zip(track, track[1:])) / 1000


# ─────────────────────────── Карты ─────────────────────────────────

PALETTE = ["#e41a1c", "#377eb8", "#4daf4a", "#984ea3", "#ff7f00", "#a65628",
           "#f781bf", "#17becf", "#bcbd22", "#1f78b4", "#6a3d9a", "#b15928"]


def team_path(team: dict, cps: dict) -> tuple[list, str]:
    """
    Возвращает (координаты, тип): exact — по треку с сайта,
    approx — взятые КП по порядку этапов, внутри этапа жадный ближайший сосед.
    """
    start = next((c for c in cps.values() if c["kind"] == "start" and c["lat"]), None)
    finish = next((c for c in cps.values() if c["kind"] == "finish" and c["lat"]), None)
    ends = lambda seq: ([[start["lat"], start["lon"]]] if start else []) + seq + \
                       ([[finish["lat"], finish["lon"]]] if finish else [])

    if team["passing"]:
        seq = [[cps[p["cp"]]["lat"], cps[p["cp"]]["lon"]] for p in team["passing"]
               if cps.get(p["cp"], {}).get("lat") and cps[p["cp"]]["kind"] not in ("start", "finish")]
        return ends(seq), "exact"

    missed = set(team["missed_cps"]) | set(team["missed_bonuses"])
    taken = [c for c in cps.values()
             if c["lat"] and c["kind"] in ("cp", "bonus") and c["cp"] not in missed]
    seq, pos = [], (start["lat"], start["lon"]) if start else None
    for idx in sorted({c["stage_idx"] for c in taken}):
        left = [c for c in taken if c["stage_idx"] == idx]
        while left:
            nxt = min(left, key=lambda c: haversine_m(*pos, c["lat"], c["lon"])) if pos else left[0]
            seq.append([nxt["lat"], nxt["lon"]])
            pos = (nxt["lat"], nxt["lon"])
            left.remove(nxt)
    return ends(seq), "approx"


# Подложки без требований к Referer: карты открываются прямо с диска (file://).
# tile.openstreetmap.org для локальных файлов отдаёт 403, CartoDB теперь требует ключ.
BASEMAPS = [
    ("Esri.WorldGrayCanvas", "Светлая"),
    ("Esri.WorldStreetMap",  "Улицы"),
    ("Esri.WorldImagery",    "Спутник"),
]


def base_map(location, zoom: int):
    import folium
    fmap = folium.Map(location=location, zoom_start=zoom, tiles=None, control_scale=True)
    for i, (tiles, name) in enumerate(BASEMAPS):
        folium.TileLayer(tiles, name=name, overlay=False, control=True, show=i == 0).add_to(fmap)
    return fmap


def _cp_popup(c: dict, s: dict) -> str:
    e = htmllib.escape
    rows = [f"<b>КП {e(c['label'])}</b> · {e(c['stage'])}", e(c["address"])]
    if c.get("desc"):
        rows.append(f"<i>{e(c['desc'])}</i>")
    if c.get("quest"):
        rows.append(f"<b>Задание:</b> {e(c['quest'])}")
    if c.get("answer"):
        rows.append(f"<details><summary>Правильный ответ</summary><b>{e(c['answer'])}</b></details>")
    if c["bonus_min"]:
        rows.append(f"Бонус: {c['bonus_min']} мин")
    if s["rate"] is not None:
        rows.append(f"Взяли: <b>{s['taken']}/{s['teams']}</b> ({s['rate']:.0%})")
        if s["missed_by"]:
            more = f" … +{len(s['missed_by']) - 20}" if len(s["missed_by"]) > 20 else ""
            rows.append("Не взяли: " + ", ".join(map(e, s["missed_by"][:20])) + more)
    if c.get("history"):
        imgs = "".join(f'<img src="{e(u)}" style="max-width:100%;margin-top:6px">'
                       for u in c.get("history_images", []))
        text = e(c["history"]).replace("\n", "<br>")
        rows.append(f'<details><summary>Историческая справка</summary>'
                    f'<div style="max-height:260px;overflow:auto;font-size:12px">{text}{imgs}</div></details>')
    return "<br>".join(r for r in rows if r)


def add_cp_layer(fmap, data: dict, name: str, show: bool, cmap):
    import folium
    from folium.features import DivIcon
    stats = compute_cp_stats(data)
    fg = folium.FeatureGroup(name=name, show=show)
    for c in data["cps"]:
        if c["lat"] is None:
            continue
        s = stats[c["cp"]]
        popup = folium.Popup(_cp_popup(c, s), max_width=360)
        if c["kind"] in ("start", "finish"):
            folium.Marker([c["lat"], c["lon"]], popup=popup,
                          tooltip=f"{'Старт' if c['kind'] == 'start' else 'Финиш'} · КП {c['label']}",
                          icon=folium.Icon(color="green" if c["kind"] == "start" else "black",
                                           icon="flag")).add_to(fg)
            continue
        bonus = c["kind"] == "bonus"
        pct = f"{s['rate']:.0%}" if s["rate"] is not None else "—"
        folium.CircleMarker(
            [c["lat"], c["lon"]], radius=10 if bonus else 8,
            color="#6a3d9a" if bonus else "#333", weight=3 if bonus else 1,
            fill=True, fill_color=cmap(s["rate"]) if s["rate"] is not None else "#999",
            fill_opacity=0.9, popup=popup,
            tooltip=f"КП {c['label']}{' (бонус)' if bonus else ''}: {pct}",
        ).add_to(fg)
        folium.Marker([c["lat"], c["lon"]], icon=DivIcon(
            icon_size=(30, 12), icon_anchor=(-9, 6),
            html=f'<div style="font:600 10px sans-serif;color:#222;'
                 f'text-shadow:0 0 2px #fff">{htmllib.escape(c["label"])}</div>')).add_to(fg)
    fg.add_to(fmap)


def _title_box(fmap, title: str, subtitle: str):
    import folium
    fmap.get_root().html.add_child(folium.Element(
        f'<div style="position:fixed;top:12px;left:60px;z-index:9999;background:#fff;'
        f'padding:8px 14px;border-radius:8px;box-shadow:0 2px 8px rgba(0,0,0,.25);'
        f'font-family:sans-serif"><b style="font-size:15px">{htmllib.escape(title)}</b>'
        f'<div style="font-size:12px;color:#555">{subtitle}</div></div>'))


def build_category_map(data: dict, top_tracks_shown: int = 3) -> Optional[Path]:
    import branca.colormap as bcm
    import folium
    from folium.plugins import AntPath, Fullscreen

    cps_list = [c for c in data["cps"] if c["lat"] is not None]
    if not cps_list:
        log.info(f"[{data['category']}] нет координат — карта пропущена")
        return None
    cps = {c["cp"]: c for c in data["cps"]}
    cmap = bcm.LinearColormap(["#d73027", "#fee08b", "#1a9850"], vmin=0, vmax=1,
                              caption="Доля команд, взявших КП")

    fmap = base_map([mean(c["lat"] for c in cps_list), mean(c["lon"] for c in cps_list)], 12)
    add_cp_layer(fmap, data, "Контрольные пункты", True, cmap)

    teams = sorted(active_teams(data), key=place_key)
    for i, t in enumerate(teams):
        t = with_clipped_gps(t)
        coords, kind = team_path(t, cps)
        if len(coords) < 2 and not t["gps_track"]:
            continue
        color = PALETTE[i % len(PALETTE)]
        mark = "GPS" if t["gps_track"] else {"exact": "отметки", "approx": "≈ порядок этапов"}[kind]
        fg = folium.FeatureGroup(
            name=f'<span style="color:{color}">■</span> {t["place"] or "—"}. '
                 f'{htmllib.escape(t["number"])} {htmllib.escape(t["name"])} ({mark})',
            show=i < top_tracks_shown)
        tip = (f'<b>{htmllib.escape(t["name"])}</b><br>'
               f'{t["place"] or "—"} место · {htmllib.escape(t["number"])} · '
               f'{t["time_on_course"]} на трассе · КП {t["taken"]}')
        if t["gps_track"]:
            tip += f' · GPS {gps_km(t["gps_track"]):.1f} км'
            AntPath([p[:2] for p in t["gps_track"]], color=color, weight=3, opacity=0.8,
                    delay=1200, dash_array=[12, 30], tooltip=tip).add_to(fg)
        elif kind == "exact":
            AntPath(coords, color=color, weight=4, delay=900, tooltip=tip).add_to(fg)
        if kind == "exact":
            for n, p in enumerate(t["passing"], 1):
                c = cps.get(p["cp"])
                if c and c["lat"]:
                    folium.CircleMarker([c["lat"], c["lon"]], radius=4, color=color, fill=True,
                                        tooltip=f'<b>{htmllib.escape(t["name"])}</b><br>'
                                                f'#{n} · КП {c["label"]} · {p["time"] or ""}').add_to(fg)
        elif not t["gps_track"]:
            folium.PolyLine(coords, color=color, weight=3, opacity=0.75,
                            dash_array="6 8", tooltip=tip).add_to(fg)
        fg.add_to(fmap)

    cmap.add_to(fmap)
    Fullscreen().add_to(fmap)
    folium.LayerControl(collapsed=True).add_to(fmap)
    n_cp = sum(c["kind"] in ("cp", "bonus") for c in data["cps"])
    _title_box(fmap, f"Бегущий Город {YEAR} — {data['title']}",
               f"КП: {n_cp} · команд: {len(teams)} · цвет точки = доля взявших")

    MAPS_DIR.mkdir(exist_ok=True)
    out = MAPS_DIR / f"{data['category']}.html"
    fmap.save(str(out))
    return out


def build_replay(data: dict, step_min: int = 2) -> Optional[Path]:
    """Анимация: точки всех команд категории по GPS, шаг step_min минут, хвост 20 минут."""
    import folium
    import branca.colormap as bcm
    from datetime import datetime, timezone
    from folium.plugins import TimestampedGeoJson

    teams = [t for t in (with_clipped_gps(t) for t in sorted(active_teams(data), key=place_key))
             if len(t["gps_track"]) > 1]
    if not teams:
        return None
    cmap = bcm.LinearColormap(["#d73027", "#fee08b", "#1a9850"], vmin=0, vmax=1,
                              caption="Доля команд, взявших КП")
    pts = [p for t in teams for p in t["gps_track"]]
    fmap = base_map([mean(p[0] for p in pts), mean(p[1] for p in pts)], 12)
    add_cp_layer(fmap, data, "Контрольные пункты", True, cmap)

    features, step = [], step_min * 60
    iso = lambda ts: datetime.fromtimestamp(ts + MSK_OFFSET, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
    for i, t in enumerate(teams):
        color, track = PALETTE[i % len(PALETTE)], t["gps_track"]
        j = 0
        for ts in range(track[0][2] - track[0][2] % step, track[-1][2] + step, step):
            while j + 1 < len(track) and track[j + 1][2] <= ts:     # последняя известная позиция
                j += 1
            features.append({
                "type": "Feature",
                "geometry": {"type": "Point", "coordinates": [track[j][1], track[j][0]]},
                "properties": {
                    "time": iso(ts),
                    "popup": f'{htmllib.escape(t["number"])} {htmllib.escape(t["name"])} (место {t["place"] or "—"})',
                    "icon": "circle",
                    "iconstyle": {"fillColor": color, "fillOpacity": 0.9, "stroke": True,
                                  "color": "#fff", "weight": 1, "radius": 6},
                },
            })
    TimestampedGeoJson({"type": "FeatureCollection", "features": features},
                       period=f"PT{step_min}M", duration="PT20M", transition_time=150,
                       add_last_point=False, auto_play=False, loop=False, max_speed=20,
                       date_options="HH:mm", time_slider_drag_update=True).add_to(fmap)
    _title_box(fmap, f"Бегущий Город {YEAR} — {data['title']}: повтор гонки",
               f"{len(teams)} команд с GPS · время московское · ▶ внизу слева")
    out = MAPS_DIR / f"{data['category']}_replay.html"
    fmap.save(str(out))
    return out


# ─────────────────── Граф переходов между КП ───────────────────────

def team_sequence(team: dict, cps: dict) -> list[tuple[str, Optional[float]]]:
    """
    Порядок КП команды по отметкам: [(cp, минуты от полуночи), ...],
    обрамлённый стартом и финишем категории (время — старт/финиш команды).
    """
    start = next((c["cp"] for c in cps.values() if c["kind"] == "start"), None)
    finish = next((c["cp"] for c in cps.values() if c["kind"] == "finish"), None)
    t0 = to_minutes(team["start"])

    def fix(m):                                    # переход через полночь
        return m + 1440 if m is not None and t0 is not None and m < t0 - 60 else m

    seq = [(start, t0)] if start else []
    for p in team["passing"]:
        c = cps.get(p["cp"])
        if c and c["kind"] not in ("start", "finish"):
            seq.append((p["cp"], fix(to_minutes(p["time"]))))
    if finish and team.get("finish"):
        seq.append((finish, fix(to_minutes(team["finish"]))))
    return seq


def compute_edges(data: dict) -> tuple[dict, int]:
    """{(from, to): {"teams": [...номера], "legs": [минуты]}}, число команд с отметками."""
    cps = {c["cp"]: c for c in data["cps"]}
    edges: dict[tuple, dict] = {}
    n_teams = 0
    for t in active_teams(data):
        if not t["passing"]:
            continue
        n_teams += 1
        seq = team_sequence(t, cps)
        for (a, ta), (b, tb) in zip(seq, seq[1:]):
            if a == b:
                continue
            e = edges.setdefault((a, b), {"teams": [], "legs": []})
            e["teams"].append(t["number"])
            if ta is not None and tb is not None and tb >= ta:
                e["legs"].append(tb - ta)
    return edges, n_teams


def _median(xs: list) -> Optional[float]:
    if not xs:
        return None
    s = sorted(xs)
    m = len(s) // 2
    return s[m] if len(s) % 2 else (s[m - 1] + s[m]) / 2


def _curved_edge(a: tuple, b: tuple, bend: float = 0.12, n: int = 24):
    """
    Дуга a→b (квадратичная Безье), выгнутая вправо по ходу движения:
    рёбра A→B и B→A расходятся в разные стороны и не сливаются.
    Возвращает (точки дуги, наконечник стрелки — треугольник).
    """
    lat0 = (a[0] + b[0]) / 2
    kx, ky = 111_320 * math.cos(math.radians(lat0)), 110_540      # м на градус
    ax, ay = a[1] * kx, a[0] * ky
    bx, by = b[1] * kx, b[0] * ky
    dx, dy = bx - ax, by - ay
    length = math.hypot(dx, dy) or 1.0
    nx, ny = dy / length, -dx / length                              # нормаль вправо
    cx, cy = (ax + bx) / 2 + nx * length * bend, (ay + by) / 2 + ny * length * bend

    def at(t):
        x = (1 - t) ** 2 * ax + 2 * (1 - t) * t * cx + t ** 2 * bx
        y = (1 - t) ** 2 * ay + 2 * (1 - t) * t * cy + t ** 2 * by
        return x, y

    pts = [at(i / n) for i in range(n + 1)]
    # стрелка в 60 % пути, по касательной
    t = 0.6
    px, py = at(t)
    tx = 2 * (1 - t) * (cx - ax) + 2 * t * (bx - cx)
    ty = 2 * (1 - t) * (cy - ay) + 2 * t * (by - cy)
    tl = math.hypot(tx, ty) or 1.0
    ux, uy = tx / tl, ty / tl
    size = min(length * 0.08, 140)
    head = [(px + ux * size, py + uy * size),
            (px - ux * size * 0.6 + uy * size * 0.55, py - uy * size * 0.6 - ux * size * 0.55),
            (px - ux * size * 0.6 - uy * size * 0.55, py - uy * size * 0.6 + ux * size * 0.55)]
    to_ll = lambda x, y: [y / ky, x / kx]
    return [to_ll(x, y) for x, y in pts], [to_ll(x, y) for x, y in head]


def build_flow_map(data: dict, min_teams: int = 1) -> Optional[Path]:
    """
    Общий трек категории: направленный граф переходов КП→КП.
    Толщина и цвет ребра — число команд, прошедших этот переход подряд.
    """
    import branca.colormap as bcm
    import folium

    cps = {c["cp"]: c for c in data["cps"] if c["lat"] is not None}
    edges, n_teams = compute_edges(data)
    edges = {k: v for k, v in edges.items()
             if k[0] in cps and k[1] in cps and len(v["teams"]) >= min_teams}
    if not edges:
        log.info(f"[{data['category']}] нет отметок команд — граф переходов пропущен")
        return None

    max_n = max(len(v["teams"]) for v in edges.values())
    flow_cmap = bcm.LinearColormap(["#c6dbef", "#4292c6", "#08306b"], vmin=1, vmax=max(max_n, 2),
                                   caption="Команд прошло переход")
    rate_cmap = bcm.LinearColormap(["#d73027", "#fee08b", "#1a9850"], vmin=0, vmax=1,
                                   caption="Доля команд, взявших КП")
    pts = [(c["lat"], c["lon"]) for c in cps.values()]
    fmap = base_map([mean(p[0] for p in pts), mean(p[1] for p in pts)], 12)

    fg_main = folium.FeatureGroup(name="Переходы (≥ 2 команд)", show=True)
    fg_rare = folium.FeatureGroup(name="Единичные переходы (1 команда)", show=max_n <= 3)
    for (a, b), e in sorted(edges.items(), key=lambda kv: len(kv[1]["teams"])):   # толстые сверху
        n = len(e["teams"])
        ca, cb = cps[a], cps[b]
        line, head = _curved_edge((ca["lat"], ca["lon"]), (cb["lat"], cb["lon"]))
        weight = 1.5 + 12 * math.sqrt(n / max_n)
        color = flow_cmap(n)
        med = _median(e["legs"])
        more = f" … +{n - 15}" if n > 15 else ""
        tip = (f"<b>КП {htmllib.escape(ca['label'])} → КП {htmllib.escape(cb['label'])}</b><br>"
               f"{n} из {n_teams} команд ({n / n_teams:.0%})"
               + (f"<br>медиана перегона: {med:.0f} мин" if med is not None else "")
               + f"<br><span style='font-size:11px;color:#555'>{', '.join(map(htmllib.escape, e['teams'][:15]))}{more}</span>")
        target = fg_main if n >= 2 else fg_rare
        folium.PolyLine(line, color=color, weight=weight, opacity=0.85, tooltip=tip).add_to(target)
        folium.Polygon(head, color=color, weight=1, fill=True, fill_color=color,
                       fill_opacity=0.95, tooltip=tip).add_to(target)
    fg_rare.add_to(fmap)
    fg_main.add_to(fmap)
    add_cp_layer(fmap, data, "Контрольные пункты", True, rate_cmap)

    flow_cmap.add_to(fmap)
    folium.LayerControl(collapsed=False).add_to(fmap)
    _title_box(fmap, f"Бегущий Город {YEAR} — {data['title']}: общий трек",
               f"{n_teams} команд с отметками · толщина ребра = сколько команд прошли переход подряд")
    out = MAPS_DIR / f"{data['category']}_flow.html"
    fmap.save(str(out))
    return out


def export_edges(all_data: list[dict]):
    with open(MAPS_DIR / "edges.csv", "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f)
        w.writerow(["category", "from_cp", "to_cp", "teams", "share", "median_leg_min",
                    "straight_km", "team_numbers"])
        for d in all_data:
            cps = {c["cp"]: c for c in d["cps"]}
            edges, n_teams = compute_edges(d)
            for (a, b), e in sorted(edges.items(), key=lambda kv: -len(kv[1]["teams"])):
                ca, cb = cps.get(a), cps.get(b)
                km = (haversine_m(ca["lat"], ca["lon"], cb["lat"], cb["lon"]) / 1000
                      if ca and cb and ca["lat"] and cb["lat"] else None)
                med = _median(e["legs"])
                w.writerow([d["category"], ca["label"] if ca else a, cb["label"] if cb else b,
                            len(e["teams"]), round(len(e["teams"]) / n_teams, 3) if n_teams else "",
                            round(med) if med is not None else "",
                            round(km, 2) if km is not None else "", " ".join(e["teams"])])


def build_overview(all_data: list[dict]) -> Optional[Path]:
    import branca.colormap as bcm
    import folium
    from folium.plugins import Fullscreen

    with_coords = [d for d in all_data if any(c["lat"] for c in d["cps"])]
    if not with_coords:
        return None
    pts = [(c["lat"], c["lon"]) for d in with_coords for c in d["cps"] if c["lat"]]
    cmap = bcm.LinearColormap(["#d73027", "#fee08b", "#1a9850"], vmin=0, vmax=1,
                              caption="Доля команд, взявших КП")
    fmap = base_map([mean(p[0] for p in pts), mean(p[1] for p in pts)], 11)
    for i, d in enumerate(with_coords):
        add_cp_layer(fmap, d, f"{d['title']} ({len(active_teams(d))} ком.)", i == 0, cmap)
    cmap.add_to(fmap)
    Fullscreen().add_to(fmap)
    folium.LayerControl(collapsed=False).add_to(fmap)
    _title_box(fmap, f"Бегущий Город {YEAR} — все категории", "переключайте категории справа")
    out = MAPS_DIR / "overview.html"
    fmap.save(str(out))
    return out


def build_index(all_data: list[dict], maps: dict[str, Path]):
    rows = []
    for d in sorted(all_data, key=lambda x: x["title"]):
        st = [s for s in compute_cp_stats(d).values() if s["rate"] is not None]
        avg = mean(s["rate"] for s in st) if st else None
        hardest = min(((s["rate"], c["label"]) for c in d["cps"]
                       for s in [compute_cp_stats(d)[c["cp"]]] if s["rate"] is not None),
                      default=None)
        link = (f'<a href="{maps[d["category"]].name}">{htmllib.escape(d["title"])}</a>'
                if d["category"] in maps else htmllib.escape(d["title"]))
        tracks = sum(1 for t in d["teams"] if t["passing"] or t["gps_track"])
        if (MAPS_DIR / f'{d["category"]}_replay.html').exists():
            link += f' · <a href="{d["category"]}_replay.html">▶ повтор</a>'
        if (MAPS_DIR / f'{d["category"]}_flow.html').exists():
            link += f' · <a href="{d["category"]}_flow.html">⇄ общий трек</a>'
        rows.append(
            f"<tr><td>{link}</td><td>{len(active_teams(d))}</td>"
            f"<td>{sum(c['kind'] in ('cp', 'bonus') for c in d['cps'])}</td>"
            f"<td>{f'{avg:.0%}' if avg is not None else '—'}</td>"
            f"<td>{f'КП {hardest[1]} ({hardest[0]:.0%})' if hardest else '—'}</td>"
            f"<td>{tracks}</td></tr>")
    (MAPS_DIR / "index.html").write_text(f"""<!doctype html><html lang="ru"><head>
<meta charset="utf-8"><title>Бегущий Город {YEAR}</title>
<style>body{{font-family:system-ui,sans-serif;max-width:900px;margin:40px auto;padding:0 16px}}
table{{border-collapse:collapse;width:100%}}td,th{{padding:6px 10px;border-bottom:1px solid #ddd;text-align:left}}
th{{background:#f4f4f4}}a{{color:#1f78b4}}</style></head><body>
<h1>Бегущий Город {YEAR}</h1>
<p><a href="overview.html">Общая карта всех КП</a> · <a href="cp_stats.csv">cp_stats.csv</a> · <a href="teams.csv">teams.csv</a> · <a href="splits.csv">splits.csv</a> · <a href="edges.csv">edges.csv</a></p>
<table><tr><th>Категория</th><th>Команд</th><th>КП</th><th>Средняя взятость</th><th>Самый сложный КП</th><th>Треков</th></tr>
{''.join(rows)}</table></body></html>""", "utf-8")


def build_maps():
    all_data = [json.loads(p.read_text("utf-8")) for p in sorted(DATA_DIR.glob("*.json"))]
    if not all_data:
        log.error("Нет данных — сначала запустите scrape")
        return
    export_csv(all_data)
    export_edges(all_data)
    maps = {}
    for d in all_data:
        out = build_category_map(d)
        if out:
            maps[d["category"]] = out
            log.info(f"🗺  {out}")
        replay = build_replay(d)
        if replay:
            log.info(f"▶  {replay}")
        flow = build_flow_map(d)
        if flow:
            log.info(f"⇄  {flow}")
    build_overview(all_data)
    build_index(all_data, maps)
    log.info(f"Готово: откройте {MAPS_DIR / 'index.html'}")


# ─────────────────────────── CLI ───────────────────────────────────

def main():
    ap = argparse.ArgumentParser(description="Runcity 2026: сбор и карты")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("probe", help="дамп страницы трека для отладки парсера")
    p.add_argument("url")

    for name in ("scrape", "all"):
        s = sub.add_parser(name)
        s.add_argument("--cats", help="категории через запятую (slug из URL)")
        s.add_argument("--with-online", action="store_true")
        s.add_argument("--refresh", action="store_true", help="игнорировать HTML-кеш")
        s.add_argument("--tracks-limit", type=int, default=0)
        if name == "scrape":
            s.add_argument("--tracks", action="store_true", help="скачать GPS-треки и время на КП")

    sub.add_parser("map")
    a = ap.parse_args()

    if a.cmd == "probe":
        probe(a.url)
    elif a.cmd in ("scrape", "all"):
        only = set(a.cats.split(",")) if a.cats else None
        paths = scrape_static(only, a.with_online, a.refresh)
        if a.cmd == "all" or a.tracks:
            scrape_tracks(paths, a.tracks_limit, a.refresh)
        if a.cmd == "all":
            build_maps()
    elif a.cmd == "map":
        build_maps()


if __name__ == "__main__":
    main()
