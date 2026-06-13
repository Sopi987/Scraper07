# ================== Anti-freeze (inactivity timeout) ==================
# Objectif: ne PAS imposer un délai fixe par message.
# Timeout déclenché uniquement s'il n'y a AUCUN "progrès" pendant N secondes.
INACTIVITY_TIMEOUT_SEC = 180  # 3 minutes sans progrès

class InactivityTimeout(Exception):
    pass

# Gestion ré-entrante: évite que des timeouts imbriqués s'annulent entre eux.
_INACT_ALARM_DEPTH = 0
_INACT_ALARM_SECONDS = INACTIVITY_TIMEOUT_SEC
_INACT_ALARM_OLD_HANDLER = None
_INACT_ALARM_ENABLED = False

def _inact_alarm_supported():
    import sys, signal
    return hasattr(signal, "SIGALRM") and (not sys.platform.startswith("win"))

def _inact_alarm_install(seconds: int):
    global _INACT_ALARM_DEPTH, _INACT_ALARM_SECONDS, _INACT_ALARM_OLD_HANDLER, _INACT_ALARM_ENABLED
    import signal
    _INACT_ALARM_SECONDS = int(max(1, seconds))
    if not _inact_alarm_supported():
        _INACT_ALARM_ENABLED = False
        return

    _INACT_ALARM_ENABLED = True
    if _INACT_ALARM_DEPTH == 0:
        _INACT_ALARM_OLD_HANDLER = signal.getsignal(signal.SIGALRM)

        def _handler(signum, frame):
            raise InactivityTimeout(f"No progress for {_INACT_ALARM_SECONDS}s")

        signal.signal(signal.SIGALRM, _handler)

    _INACT_ALARM_DEPTH += 1
    _inact_alarm_touch()

def _inact_alarm_touch():
    if not _INACT_ALARM_ENABLED:
        return
    import signal
    sec = int(max(1, _INACT_ALARM_SECONDS))
    if hasattr(signal, "setitimer"):
        try:
            signal.setitimer(signal.ITIMER_REAL, sec)
            return
        except Exception:
            pass
    try:
        signal.alarm(sec)
    except Exception:
        pass

def _inact_alarm_remove():
    global _INACT_ALARM_DEPTH, _INACT_ALARM_OLD_HANDLER, _INACT_ALARM_ENABLED
    if not _INACT_ALARM_ENABLED:
        return
    import signal
    _INACT_ALARM_DEPTH = max(0, _INACT_ALARM_DEPTH - 1)
    if _INACT_ALARM_DEPTH == 0:
        try:
            if hasattr(signal, "setitimer"):
                signal.setitimer(signal.ITIMER_REAL, 0)
            else:
                signal.alarm(0)
        except Exception:
            pass
        try:
            signal.signal(signal.SIGALRM, _INACT_ALARM_OLD_HANDLER)
        except Exception:
            pass

class InactivityGuard:
    def __init__(self, seconds: int = INACTIVITY_TIMEOUT_SEC):
        self.seconds = int(max(1, seconds))

    def __enter__(self):
        _inact_alarm_install(self.seconds)
        return self

    def touch(self):
        _inact_alarm_touch()

    def __exit__(self, exc_type, exc, tb):
        _inact_alarm_remove()
        return False
# =======================================================================

import sys
import os
import platform
import re
import time
import datetime
import threading
import random
import requests
import json
import ipaddress
from concurrent.futures import ThreadPoolExecutor, as_completed



# ------------------ UI sizing (global) ------------------
# Some UI helpers expect BANNER_WIDTH at module scope.
# QPython may not report terminal size reliably, so we fall back safely.
try:
    _TERM_COLS = os.get_terminal_size().columns
except Exception:
    _TERM_COLS = 60
# Keep a reasonable width for boxed panels
BANNER_WIDTH = max(42, min(int(_TERM_COLS), 120))

def _is_ipv6_host(host: str) -> bool:
    """Retourne True si 'host' est une adresse IPv6."""
    try:
        return isinstance(ipaddress.ip_address(str(host)), ipaddress.IPv6Address)
    except Exception:
        return False

from urllib.parse import urlparse, parse_qs


# --- urlparse sécurisé: ignore les URLs IPv6 mal formées (évite ValueError: Invalid IPv6 URL) ---
_real_urlparse = urlparse
def urlparse(url, scheme="", allow_fragments=True):
    try:
        return _real_urlparse(url, scheme=scheme, allow_fragments=allow_fragments)
    except ValueError:
        # On retourne un ParseResult "vide" => hostname=None => la cible sera ignorée.
        return _real_urlparse("", scheme=scheme, allow_fragments=allow_fragments)



def _safe_urlparse(u: str):
    """Parse une URL sans jamais lever d'exception.
    - Utilise le wrapper urlparse (ci-dessus) qui ignore les IPv6 mal formées.
    - Retourne None si l'entrée est vide.
    """
    if not u:
        return None
    try:
        p = urlparse(u)
        return p
    except Exception:
        return None

import urllib3
from telethon.sync import TelegramClient
from telethon.sessions import StringSession
from datetime import timezone
import colorama
from colorama import Fore, Back, Style
from collections import Counter, OrderedDict, defaultdict
import socket  # ⇦ ajouté
import itertools
import os, re

# -------------------------------------------
# 1) En haut du fichier (imports)
from collections import deque
import time
from collections import deque
import time

TXT_EVENTS = deque(maxlen=5)
TXT_EVENT_TTL = 20  # secondes d'affichage max d'un événement
SAVED_M3U = set()
_display_lock = threading.Lock()
MIRROR_FLAG_RENAME = True
# Barre de progression actuelle pour l'analyse des .txt
CURRENT_TXT_PROGRESS = ""
# 2) Historique des 5 derniers événements (cascade)
LAST_EVENTS = deque(maxlen=5)

# Flag global pour arrêter la recherche de M3U sources dès qu'on en a assez
_STOP_M3U_SOURCE_SCAN = threading.Event()
def push_m3u_event(is_active: bool, label: str):
    """
    Ajoute une ligne dans la cascade (affichée sous le cadre).
    - is_active=True  -> ligne verte   ✅
    - is_active=False -> ligne rouge   ❌
    label = url M3U (ou nom) affiché
    """
    ts = time.strftime("%H:%M:%S")
    if is_active:
        line = f"{Fore.GREEN}✅ ACTIVE{Fore.RESET}  {Fore.LIGHTYELLOW_EX}{label}{Fore.RESET}   {Fore.BLACK}{Style.DIM}{ts}{Style.NORMAL}{Fore.RESET}"
    else:
        line = f"{Fore.RED}❌ INACTIVE{Fore.RESET} {Fore.LIGHTBLACK_EX}{label}{Fore.RESET}   {Fore.BLACK}{Style.DIM}{ts}{Style.NORMAL}{Fore.RESET}"
    LAST_EVENTS.append(line)

# Historique des 5 derniers domaines testés (cascade ACTIVE DOMAINS)
ACTIVE_EVENTS = deque(maxlen=5)

def push_txt_event(label: str):
    """
    Ajoute une ligne dans la cascade TXT (analyse de fichiers .txt)
    avec un timestamp pour pouvoir l'expirer après quelques secondes.
    """
    TXT_EVENTS.append({
        "ts": time.time(),   # timestamp en secondes
        "label": label,
    })
def push_active_event(is_active: bool, label: str):
    """
    Ajoute une ligne dans la cascade de filtrage domaines actifs.
    - is_active=True  -> ligne verte   ✅
    - is_active=False -> ligne rouge   ❌
    label = domaine:port + info (code HTTP, timeout...)
    """
    ts = time.strftime("%H:%M:%S")
    if is_active:
        line = (
            f"{Fore.GREEN}✅ ACTIVE{Fore.RESET}  "
            f"{Fore.LIGHTYELLOW_EX}{label}{Fore.RESET}   "
            f"{Fore.BLACK}{Style.DIM}{ts}{Style.RESET_ALL}"
        )
    else:
        line = (
            f"{Fore.RED}❌ INACTIVE{Fore.RESET} "
            f"{Fore.LIGHTBLACK_EX}{label}{Fore.RESET}   "
            f"{Fore.BLACK}{Style.DIM}{ts}{Style.RESET_ALL}"
        )
    ACTIVE_EVENTS.append(line)
    
_thread_local = threading.local()
def _get_thread_session(stealth=True):
    s = getattr(_thread_local, "session", None)
    if s is None:
        s = requests.Session()
        _thread_local.session = s
    headers, cookies = get_stealth_headers(stealth=stealth)
    s.headers.clear(); s.cookies.clear()
    s.headers.update(headers); s.cookies.update(cookies)
    return s    
# -------------------------------------------
# Initialize colorama
colorama.init(autoreset=True)

# Global configuration
NAME = 'SUPER-SCRAPER-SOPI987 v9'
if sys.platform.startswith('win'):
    try:
        import ctypes
        ctypes.windll.kernel32.SetConsoleTitleW(NAME)
    except Exception:
        pass
else:
    try:
        sys.stdout.write(f"\033]2;{NAME}\a")
    except Exception:
        pass

# Disable SSL warnings
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# HTTP checker configuration
user_agents = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/122.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 12_6_1) AppleWebKit/605.1.15 Version/16.1 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; WOW64; rv:45.0) Gecko/20100101 Firefox/45.0",
    "Mozilla/5.0 (Linux; Android 10; SM-G960F) AppleWebKit/537.36 Chrome/111.0.5563.116 Mobile Safari/537.36"
]
NB_THREADS = 30
TIMEOUT = 15
socket.setdefaulttimeout(TIMEOUT)  # ⇦ garde-fou global contre les blocages

def rand_ua():
    return random.choice(user_agents)

def get_session_path():
    """
    Session Telethon stockée dans:
    - Android : /sdcard/Hits/SUPER-SCRAPER/
    - Windows : ./Hits/SUPER-SCRAPER/
    """
    import os, platform

    base_path = "." if platform.system() == "Windows" else "/sdcard"
    base_dir  = os.path.join(base_path, "Hits", "SUPER-SCRAPER")
    os.makedirs(base_dir, exist_ok=True)

    return os.path.join(base_dir, "Super_scraper_SOPI987.txt")


# ─── Dossiers de travail SUPER-SCRAPER ───
import os, platform

base_path  = "." if platform.system() == "Windows" else "/sdcard"
SUPER_BASE = os.path.join(base_path, "Hits", "SUPER-SCRAPER")
os.makedirs(SUPER_BASE, exist_ok=True)

# 📂 Hits Telegram → Hits/SUPER-SCRAPER/telegram
hits_dir = os.path.join(SUPER_BASE, "telegram")
os.makedirs(hits_dir, exist_ok=True)

# 📂 Mirror domains → Hits/SUPER-SCRAPER/mirror
MIRROR_DIR = os.path.join(SUPER_BASE, "mirror")
os.makedirs(MIRROR_DIR, exist_ok=True)

# 📂 Fichiers temporaires / résiduels → Hits/SUPER-SCRAPER/residual
RESIDUAL_DIR = os.path.join(SUPER_BASE, "residual")
os.makedirs(RESIDUAL_DIR, exist_ok=True)


# 📂 Geolocation → Hits/SUPER-SCRAPER/geoloc
GEOLOC_DIR = os.path.join(SUPER_BASE, "geoloc")
os.makedirs(GEOLOC_DIR, exist_ok=True)
DOMAINS_FILE     = os.path.join(MIRROR_DIR, "domains.txt")
ALL_RESULTS_FILE = os.path.join(MIRROR_DIR, "all_results.txt")

# ====== Fichier JSON de progression (même dossier que la session) ======
PROGRESS_FILE = os.path.join(
    os.path.dirname(get_session_path()),
    "Super_scraper_SOPI987_progress.json"
)

BLOCKED_DOMAINS = [
    "mhd122.iptv2022.com", "tv.dimaiptv.com", "dgbstb.top", "xc.adultiptv.net", "tvpremiumhd.club",
    "server.iptvxxx.net", "adultiptv.net", "edutvweb.online"
]

api_id = 25858399
api_hash = "0dd8d6ebcc59700e02583adca08cbecb"

IGNORED_BOT_USERNAMES = ["SayanGoku_bot"]

# --- Language global (en = English, es = Español)
LANG = "en"
# --- Globals / config ---
global_counts = {"http": 0, "m3u": 0, "combo": 0}
# Tous les HTTP déjà enregistrés dans filename_http.txt
SAVED_HTTP_BASES = set()

def clear_screen():
    import os
    import platform
    if platform.system().lower().startswith("win"):
        os.system("cls")
    else:
        os.system("clear")
        
def list_http_files():
    lang = globals().get("LANG", "en")   # ← détecte anglais / espagnol

    if not os.path.exists(hits_dir):
        if lang == "es":
            print(f"\n{Fore.RED}❌ ¡El directorio {hits_dir} no existe!{Fore.RESET}")
        else:
            print(f"\n{Fore.RED}❌ The directory {hits_dir} doesn't exist!{Fore.RESET}")
        return None
    
    http_files = [f for f in os.listdir(hits_dir) if f.endswith('_http.txt')]
    if not http_files:
        if lang == "es":
            print(f"\n{Fore.RED}❌ No se han encontrado archivos _http.txt en {hits_dir}!{Fore.RESET}")
        else:
            print(f"\n{Fore.RED}❌ No _http.txt files found in {hits_dir}!{Fore.RESET}")
        return None

    # --- LISTA DE ARCHIVOS / FILE LIST ---
    if lang == "es":
        print(f"\n{Fore.YELLOW}📁 Archivos HTTP disponibles:{Fore.RESET}")
    else:
        print(f"\n{Fore.YELLOW}📁 Available HTTP files:{Fore.RESET}")

    for i, file in enumerate(http_files, 1):
        print(f"{Fore.RED}{i}.{Fore.RESET} {Fore.YELLOW}{file}{Fore.RESET}")
    
    # --- SELECCIÓN / SELECTION LOOP ---
    while True:
        try:
            if lang == "es":
                choice = input(
                    f"\n{Fore.YELLOW}Introduce el número del archivo a filtrar (0 para cancelar): {Fore.RESET}"
                ).strip()
            else:
                choice = input(
                    f"\n{Fore.YELLOW}Enter the file number to filter (0 to cancel): {Fore.RESET}"
                ).strip()

            if choice == "0":
                return None
            
            index = int(choice) - 1
            if 0 <= index < len(http_files):
                return os.path.join(hits_dir, http_files[index])

            if lang == "es":
                print(f"{Fore.RED}❌ ¡Número inválido!{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ Invalid number!{Fore.RESET}")

        except ValueError:
            if lang == "es":
                print(f"{Fore.RED}❌ ¡Introduce un número válido!{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ Please enter a number!{Fore.RESET}")
                
# =========================
# Option 3: Geolocalización HTTP (scan TCP + GEO)
# - Input: un fichier *_http.txt (dossier SUPER-SCRAPER/telegram)
# - IPv6: ignoré (préférence utilisateur)
# - Output: /sdcard/Hits/SUPER-SCRAPER/geoloc/
# =========================

_GEO_DNS_CACHE = {}   # hostname -> ipv4
_GEO_IP_CACHE  = {}   # ipv4 -> location str
_GEO_LOCK = threading.Lock()

def _geoloc_unique_path(base_name: str, suffix: str, out_dir: str) -> str:
    base = f"{base_name}{suffix}"
    path = os.path.join(out_dir, base)
    if not os.path.exists(path):
        return path
    i = 1
    while True:
        path = os.path.join(out_dir, f"{base_name}_{i}{suffix}")
        if not os.path.exists(path):
            return path
        i += 1

def _country_code_to_flag(country_code: str) -> str:
    try:
        if not country_code or len(country_code) != 2:
            return "🌍"
        offset = 127397
        return chr(ord(country_code[0].upper()) + offset) + chr(ord(country_code[1].upper()) + offset)
    except Exception:
        return "🌍"

def _geoloc_extract_hosts_from_http_file(filepath: str):
    # Extrait des bases "http://host:port" depuis les lignes d'un *_http.txt
    # - Force https:// -> http:// (géoloc HTTP)
    # - Ignore IPv6 littérales et URLs IPv6 invalides
    hosts = set()
    try:
        with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                s = (line or "").strip()
                if not s:
                    continue
                m = re.match(r"(https?://[^/\s]+)", s, re.IGNORECASE)
                if not m:
                    continue
                u = m.group(1).strip()
                p = _safe_urlparse(u)
                if not p or (not p.hostname):
                    continue
                if _is_ipv6_host(p.hostname):
                    continue
                host = (p.hostname or "").strip().lower()
                port = p.port or (80 if (p.scheme or "http").lower() == "http" else 443)
                hosts.add(f"http://{host}:{port}")
    except FileNotFoundError:
        return []
    except Exception:
        return []
    return sorted(hosts)

def _geoloc_tcp_online(host_url: str) -> bool:
    # Test TCP brut (port ouvert/fermé) sur host:port
    try:
        p = _safe_urlparse(host_url)
        if not p or (not p.hostname):
            return False
        if _is_ipv6_host(p.hostname):
            return False
        host = p.hostname
        port = p.port or 80
        with socket.create_connection((host, int(port)), timeout=10):
            return True
    except Exception:
        return False

def _geoloc_get_location(host_url: str) -> str:
    # Résout host -> IPv4 (socket.gethostbyname), puis GEO via APIs en cascade
    # Priorité: ip-api -> ipwhois -> ipapi
    try:
        p = _safe_urlparse(host_url)
        if not p or (not p.hostname):
            return "🌍 Localización desconocida" if LANG == "es" else ("🌍 Localizzazione sconosciuta" if LANG == "it" else "🌍 Unknown location")
        if _is_ipv6_host(p.hostname):
            return "⛔ IPv6 (omitido)" if LANG == "es" else ("⛔ IPv6 (saltato)" if LANG == "it" else "⛔ IPv6 (skipped)")

        hostname = p.hostname.strip().lower()

        with _GEO_LOCK:
            ip = _GEO_DNS_CACHE.get(hostname)

        if not ip:
            ip = socket.gethostbyname(hostname)
            with _GEO_LOCK:
                _GEO_DNS_CACHE[hostname] = ip

        with _GEO_LOCK:
            cached = _GEO_IP_CACHE.get(ip)
        if cached:
            return cached

        GEO_APIS = [
            {
                "name": "ip-api",
                "url": "http://ip-api.com/json/{ip}?fields=status,country,countryCode,city",
                "parser": lambda data: (
                    data.get("countryCode"),
                    data.get("country"),
                    data.get("city"),
                ) if data.get("status") == "success" else None,
            },
            {
                "name": "ipwhois",
                "url": "https://ipwhois.io/json/{ip}",
                "parser": lambda data: (
                    data.get("country_code"),
                    data.get("country"),
                    data.get("city"),
                ) if data.get("country") else None,
            },
            {
                "name": "ipapi",
                "url": "https://ipapi.co/{ip}/json/",
                "parser": lambda data: (
                    data.get("country_code"),
                    data.get("country_name"),
                    data.get("city"),
                ) if data.get("country_code") else None,
            },
        ]

        TIMEOUT_SECONDS = 30
        ERROR_WAIT_SECONDS = 5
        RETRIES_PER_API = 1
        RETRIES_ON_429 = 1

        def _headers():
            return {
                "User-Agent": rand_ua() if callable(globals().get("rand_ua")) else "Mozilla/5.0",
                "Accept": "application/json,text/plain,*/*",
                "Accept-Language": "es-ES,es;q=0.9,fr-FR;q=0.8,en-US;q=0.7,en;q=0.6",
                "Connection": "close",
            }

        for api in GEO_APIS:
            url = api["url"].format(ip=ip)
            normal_left = RETRIES_PER_API + 1
            ratelimit_left = RETRIES_ON_429 + 1

            while normal_left > 0:
                try:
                    r = requests.get(url, timeout=TIMEOUT_SECONDS, headers=_headers())
                    if r.status_code == 429:
                        ratelimit_left -= 1
                        if ratelimit_left > 0:
                            time.sleep(ERROR_WAIT_SECONDS)
                            continue
                        break
                    if r.status_code != 200:
                        normal_left -= 1
                        if normal_left > 0:
                            time.sleep(ERROR_WAIT_SECONDS)
                            continue
                        break

                    try:
                        data = r.json()
                    except Exception:
                        normal_left -= 1
                        if normal_left > 0:
                            time.sleep(ERROR_WAIT_SECONDS)
                            continue
                        break

                    res = api["parser"](data)
                    if res:
                        cc, country, city = res
                        flag = _country_code_to_flag(cc)
                        parts = [flag, (country or "").strip()]
                        if cc and country and cc != country:
                            parts.append(f"({cc})")
                        if city and str(city).strip() and str(city).strip().upper() != "N/A":
                            parts.append(f"- {str(city).strip()}")
                        loc = " ".join([x for x in parts if x])

                        with _GEO_LOCK:
                            _GEO_IP_CACHE[ip] = loc
                        return loc

                    normal_left -= 1
                    if normal_left > 0:
                        time.sleep(ERROR_WAIT_SECONDS)
                        continue
                    break

                except Exception:
                    normal_left -= 1
                    if normal_left > 0:
                        time.sleep(ERROR_WAIT_SECONDS)
                        continue
                    break

        loc = "🌍 Localización desconocida" if LANG == "es" else ("🌍 Localizzazione sconosciuta" if LANG == "it" else "🌍 Unknown location")
        with _GEO_LOCK:
            _GEO_IP_CACHE[ip] = loc
        return loc

    except Exception as e:
        return f"🚫 Error: {type(e).__name__}"

def geolocalizacion_http():
    # 1) Choisir un fichier *_http.txt (déjà dans Hits/SUPER-SCRAPER/telegram)
    input_file = list_http_files()
    if not input_file:
        return

    hosts = _geoloc_extract_hosts_from_http_file(input_file)
    if not hosts:
        if LANG == "es":
            print(f"{Fore.RED}❌ No se han encontrado hosts válidos en este archivo.{Fore.RESET}")
        elif LANG == "it":
            print(f"{Fore.RED}❌ Nessun host valido trovato in questo file.{Fore.RESET}")
        else:
            print(f"{Fore.RED}❌ No valid hosts found in this file.{Fore.RESET}")
        return

    # Titre en 3 langues (comme demandé)
    TITLES = {"es": "GEOLOCALIZACIÓN HTTP", "en": "HTTP GEOLOCATION", "it": "GEOLOCALIZZAZIONE HTTP"}
    TITLE_3 = TITLES.get(LANG, TITLES["en"])
    total = len(hosts)

    # 2) Pipeline TCP -> GEO (même logique, mais affichage "panel" propre)
    tcp_workers = 30
    geo_workers = 2

    done_tcp = 0
    geo_completed = 0  # pour l'affichage (dès qu'une GEO se termine)
    results = []

    # Output file name
    base_name = os.path.splitext(os.path.basename(input_file))[0]
    out_path = _geoloc_unique_path(base_name, "_geoloc.txt", GEOLOC_DIR)

    start = time.time()
    last_paint = 0.0
    _geo_lock = threading.Lock()
    _paint_lock = threading.Lock()

    def _ansi_clear():
        # Plus "propre" et plus rapide que os.system('clear') si supporté.
        try:
            sys.stdout.write("\033[H\033[J")
            sys.stdout.flush()
            return True
        except Exception:
            return False

    def _bar(done, tot, length=28, fill_color=Fore.CYAN):
        if tot <= 0:
            tot = 1
        done = max(0, min(int(done), int(tot)))
        filled = int(length * done // tot)
        return f"{fill_color}{'█'*filled}{Fore.WHITE}{'░'*(length-filled)}{Fore.RESET}"

    def _tcp_color(pct: float):
        # Couleur progress TCP : vert -> jaune -> rouge
        if pct < 35:
            return Fore.GREEN
        if pct < 75:
            return Fore.YELLOW
        return Fore.RED

    def _paint(force=False):
        nonlocal last_paint
        now = time.time()
        if (not force) and (now - last_paint < 0.7):
            return
        last_paint = now

        with _paint_lock:
            # Clear "one-page" (pas de cascade)
            if not _ansi_clear():
                clear_screen()

            elapsed = max(0.1, now - start)
            tcp_pct = (done_tcp / total) * 100 if total else 0.0
            geo_pct = (geo_completed / total) * 100 if total else 0.0

            col_tcp = _tcp_color(tcp_pct)
            bar_tcp = _bar(done_tcp, total, length=30, fill_color=col_tcp)
            bar_geo = _bar(geo_completed, total, length=30, fill_color=Fore.CYAN)

            # Header
            print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
            print(f"{Fore.YELLOW}{TITLE_3.center(BANNER_WIDTH)}{Fore.RESET}")
            print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}\n")

            # Infos fichier / volume
            if LANG == "es":
                print(f"{Fore.LIGHTBLACK_EX}📄 Archivo: {Fore.WHITE}{base_name}_http.txt{Fore.RESET}")
                print(f"{Fore.LIGHTBLACK_EX}🌐 Hosts únicos a geolocalizar: {Fore.CYAN}{total}{Fore.RESET}\n")
                tcp_label = "DOMINIOS (activos/inactivos)"
                tcp_short_label = "DOMINIOS"
                geo_label = "GEO "
            elif LANG == "it":
                print(f"{Fore.LIGHTBLACK_EX}📄 File: {Fore.WHITE}{base_name}_http.txt{Fore.RESET}")
                print(f"{Fore.LIGHTBLACK_EX}🌐 Host unici da geolocalizzare: {Fore.CYAN}{total}{Fore.RESET}\n")
                tcp_label = "DOMINI (online/offline)"
                tcp_short_label = "DOMINI"
                geo_label = "GEO "
            else:
                print(f"{Fore.LIGHTBLACK_EX}📄 File: {Fore.WHITE}{base_name}_http.txt{Fore.RESET}")
                print(f"{Fore.LIGHTBLACK_EX}🌐 Unique hosts to geolocate: {Fore.CYAN}{total}{Fore.RESET}\n")
                tcp_label = "DOMAINS (online/offline)"
                tcp_short_label = "DOMAINS"
                geo_label = "GEO "

            # Bloc TCP
            print(f"{Fore.LIGHTBLACK_EX}► {tcp_label}{Fore.RESET}")
            print(f"   {Fore.LIGHTBLACK_EX}Progress: {col_tcp}{tcp_pct:6.2f}%{Fore.RESET}   "
                  f"{Fore.LIGHTBLACK_EX}Done: {Fore.WHITE}{done_tcp}{Fore.RESET}{Fore.LIGHTBLACK_EX}/{Fore.WHITE}{total}{Fore.RESET}   "
                  f"{Fore.LIGHTBLACK_EX}Time: {Fore.WHITE}{elapsed:,.1f}s{Fore.RESET}")
            print(f"   {bar_tcp}  {col_tcp}{tcp_pct:6.2f}%{Fore.RESET}\n")

            # Bloc GEO
            print(f"{Fore.LIGHTBLACK_EX}► {geo_label}{Fore.RESET}")
            print(f"   {Fore.LIGHTBLACK_EX}Progress: {Fore.CYAN}{geo_pct:6.2f}%{Fore.RESET}   "
                  f"{Fore.LIGHTBLACK_EX}Done: {Fore.WHITE}{geo_completed}{Fore.RESET}{Fore.LIGHTBLACK_EX}/{Fore.WHITE}{total}{Fore.RESET}")
            print(f"   {bar_geo}  {Fore.CYAN}{geo_pct:6.2f}%{Fore.RESET}\n")

            # Ligne courte type "status"
            print(f"{Fore.LIGHTBLACK_EX}{tcp_short_label} {Fore.WHITE}{done_tcp}{Fore.RESET}{Fore.LIGHTBLACK_EX}/{Fore.WHITE}{total}{Fore.RESET}"
                  f"{Fore.LIGHTBLACK_EX}  •  GEO {Fore.WHITE}{geo_completed}{Fore.RESET}{Fore.LIGHTBLACK_EX}/{Fore.WHITE}{total}{Fore.RESET}")

    # Premier rendu "propre" dès le choix du fichier
    _paint(force=True)

    with ThreadPoolExecutor(max_workers=min(tcp_workers, max(1, total))) as ex_tcp, \
         ThreadPoolExecutor(max_workers=min(geo_workers, max(1, total))) as ex_geo:

        tcp_futs = {ex_tcp.submit(_geoloc_tcp_online, h): h for h in hosts}
        geo_futs = []

        # callback : incrémente geo_completed dès qu'une GEO se termine (affichage en "temps réel")
        def _geo_done_cb(_fut):
            nonlocal geo_completed
            with _geo_lock:
                geo_completed += 1

        for fut in as_completed(tcp_futs):
            host = tcp_futs[fut]
            try:
                online = bool(fut.result())
            except Exception:
                online = False

            status = "ONLINE 🟢" if online else "OFFLINE 🔴"

            gf = ex_geo.submit(_geoloc_get_location, host)
            gf._host_status = (host, status)
            gf.add_done_callback(_geo_done_cb)
            geo_futs.append(gf)

            done_tcp += 1
            _paint()

        # Collecte des résultats (ordre indifférent)
        for gf in as_completed(geo_futs):
            host, status = getattr(gf, "_host_status", ("", ""))
            try:
                loc = gf.result()
            except Exception:
                loc = "🌍 Localización desconocida" if LANG == "es" else ("🌍 Localizzazione sconosciuta" if LANG == "it" else "🌍 Unknown location")
            results.append((host, status, loc))
            _paint()

    _paint(force=True)

    # 3) Sauvegarde regroupée par pays
    def _country_from_loc(loc: str) -> str:
        try:
            parts = (loc or "").split()
            if len(parts) >= 2:
                return parts[1]
        except Exception:
            pass
        return "Desconocido" if LANG == "es" else ("Sconosciuto" if LANG == "it" else "Unknown")

    groups = {}
    for host, status, loc in results:
        key = _country_from_loc(loc)
        groups.setdefault(key, []).append((host, status, loc))

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("⚡ SOPI987 TV ⚡ - GEOLOC HTTP\n")
        f.write("by IGOR\n")
        f.write("📅 " + datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n")
        f.write("════════════════════\n\n")
        for country in sorted(groups.keys()):
            f.write(f"\n=== {country} ===\n")
            for host, status, loc in sorted(groups[country], key=lambda x: x[0]):
                f.write(f"{host} - {status} - {loc}\n")

    elapsed = time.time() - start
    if LANG == "es":
        print(f"{Fore.GREEN}✅ Geolocalización terminada.{Fore.RESET} {Fore.CYAN}Archivo:{Fore.RESET} {out_path}")
        print(f"{Fore.GREEN}⏱ Tiempo total: {elapsed:.2f}s{Fore.RESET}")
    elif LANG == "it":
        print(f"{Fore.GREEN}✅ Geolocalizzazione completata.{Fore.RESET} {Fore.CYAN}File:{Fore.RESET} {out_path}")
        print(f"{Fore.GREEN}⏱ Tempo totale: {elapsed:.2f}s{Fore.RESET}")
    else:
        print(f"{Fore.GREEN}✅ HTTP geolocation finished.{Fore.RESET} {Fore.CYAN}File:{Fore.RESET} {out_path}")
        print(f"{Fore.GREEN}⏱ Total time: {elapsed:.2f}s{Fore.RESET}")



def choose_language():
    global LANG
    BANNER_WIDTH = 42

    print(f"\n{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
    print(f"{Fore.YELLOW}    SUPER SCRAPER SOPI987 v9{Fore.RESET}".center(BANNER_WIDTH+8))
    print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
    print(f"{Fore.CYAN}Select language / Seleccionar idioma / Seleziona lingua:{Fore.RESET}")
    print(f"{Fore.YELLOW}[ENTER]{Fore.RESET} English 🇺🇸 (default)")
    print(f"{Fore.YELLOW}[1]{Fore.RESET} Español 🇪🇸")
    print(f"{Fore.YELLOW}[2]{Fore.RESET} Italiano 🇮🇹")
    print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")

    choice = input(f"{Fore.YELLOW}➤ Choice: {Fore.RESET}").strip()

    if choice == "1":
        LANG = "es"
        print(f"\n{Fore.GREEN}✅ Idioma seleccionado: Español{Fore.RESET}")
    elif choice == "2":
        LANG = "it"
        print(f"\n{Fore.GREEN}✅ Lingua selezionata: Italiano{Fore.RESET}")
    else:
        LANG = "en"
        print(f"\n{Fore.GREEN}✅ Language selected: English{Fore.RESET}")

    time.sleep(0.7)
    clear_screen()
        
def get_stealth_headers(stealth=True):
    ua = rand_ua()
    base = {
        "User-Agent": ua,
        "Accept": "*/*",
        "Connection": "keep-alive",
        "Accept-Encoding": "gzip, deflate",
    }
    if stealth:
        ip = ".".join(str(random.randint(1, 254)) for _ in range(4))
        base["X-Forwarded-For"] = ip
        base["X-Real-IP"] = ip
    cookies = {"session": ''.join(random.choices("abcdefghijklmnopqrstuvwxyz0123456789", k=16))}
    return base, cookies

SESSION = requests.Session()

def get_stealth_session(stealth=True):
    headers, cookies = get_stealth_headers(stealth=stealth)
    s = SESSION
    s.headers.clear()
    s.cookies.clear()
    s.headers.update(headers)
    s.cookies.update(cookies)
    return s   
     
def check_active_domains(input_file, output_file=None):
    from concurrent.futures import ThreadPoolExecutor, as_completed
    import time
    import os
    import re
    import threading
    import requests
    # urlparse: utilise la version globale sécurisée
    # 🌐 Langue globale (par défaut anglais)
    lang = globals().get("LANG", "en")

    # ⛔ Durée max tolérée pour un worker (garde-fou anti-zombie)
    MAX_WORKER_LIFETIME = max(30, TIMEOUT + 10)

    def choose_output_format():
        if lang == "es":
            print(f"\n{Fore.YELLOW}📝 Formato del archivo de salida:{Fore.RESET}")
            print(f"{Fore.RED}1.{Fore.RESET} {Fore.YELLOW}Dominio completo con http:// y puerto{Fore.RESET}")
            print(f"{Fore.CYAN}(ej: http://example.com:8080){Fore.RESET}")
            print(f"{Fore.RED}2.{Fore.RESET} {Fore.YELLOW}Solo dominio sin http:// ni puerto{Fore.RESET}")
            print(f"{Fore.CYAN}(ej: example.com){Fore.RESET}")
            print(f"{Fore.RED}3.{Fore.RESET} {Fore.YELLOW}Dominio con puerto pero sin http://{Fore.RESET}")
            print(f"{Fore.CYAN}(ej: example.com:8080){Fore.RESET}")

            while True:
                choice = input(f"{Fore.YELLOW}Tu elección (1-3): {Fore.RESET}").strip()
                if choice in {"1", "2", "3"}:
                    return choice
                print(f"{Fore.RED}❌ Opción inválida. Introduce 1, 2 o 3{Fore.RESET}")

        elif lang == "it":
            print(f"\n{Fore.YELLOW}📝 Formato del file di output:{Fore.RESET}")
            print(f"{Fore.RED}1.{Fore.RESET} {Fore.YELLOW}Dominio completo con http:// e porta{Fore.RESET}")
            print(f"{Fore.CYAN}(es: http://example.com:8080){Fore.RESET}")
            print(f"{Fore.RED}2.{Fore.RESET} {Fore.YELLOW}Solo dominio senza http:// né porta{Fore.RESET}")
            print(f"{Fore.CYAN}(es: example.com){Fore.RESET}")
            print(f"{Fore.RED}3.{Fore.RESET} {Fore.YELLOW}Dominio con porta ma senza http://{Fore.RESET}")
            print(f"{Fore.CYAN}(es: example.com:8080){Fore.RESET}")

            while True:
                choice = input(f"{Fore.YELLOW}La tua scelta (1-3): {Fore.RESET}").strip()
                if choice in {"1", "2", "3"}:
                    return choice
                print(f"{Fore.RED}❌ Scelta non valida. Inserisci 1, 2 o 3{Fore.RESET}")

        else:
            print(f"\n{Fore.YELLOW}📝 Output file format:{Fore.RESET}")
            print(f"{Fore.RED}1.{Fore.RESET} {Fore.YELLOW}Full domain with http:// and port{Fore.RESET}")
            print(f"{Fore.CYAN}(ex: http://example.com:8080){Fore.RESET}")
            print(f"{Fore.RED}2.{Fore.RESET} {Fore.YELLOW}Domain only without http:// or port{Fore.RESET}")
            print(f"{Fore.CYAN}(ex: example.com){Fore.RESET}")
            print(f"{Fore.RED}3.{Fore.RESET} {Fore.YELLOW}Domain with port but without http://{Fore.RESET}")
            print(f"{Fore.CYAN}(ex: example.com:8080){Fore.RESET}")

            while True:
                choice = input(f"{Fore.YELLOW}Your choice (1-3): {Fore.RESET}").strip()
                if choice in {"1", "2", "3"}:
                    return choice
                print(f"{Fore.RED}❌ Invalid choice! Please enter 1, 2 or 3{Fore.RESET}")

    def animate_cleaning_slow_threads(stop_event):
        import time
        if lang == "es":
            frames = [
                f"{Fore.YELLOW}⏳ Limpiando hilos lentos.  {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Limpiando hilos lentos.. {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Limpiando hilos lentos...{Fore.RESET}",
            ]
        elif lang == "it":
            frames = [
                f"{Fore.YELLOW}⏳ Pulizia dei thread lenti.  {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Pulizia dei thread lenti.. {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Pulizia dei thread lenti...{Fore.RESET}",
            ]
        else:
            frames = [
                f"{Fore.YELLOW}⏳ Cleaning slow threads.  {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Cleaning slow threads.. {Fore.RESET}",
                f"{Fore.YELLOW}⏳ Cleaning slow threads...{Fore.RESET}",
            ]
        i = 0
        while not stop_event.is_set():
            frame = frames[i % len(frames)]
            print("\r" + frame, end="", flush=True)
            time.sleep(0.4)
            i += 1
        print("\r" + " " * 60 + "\r", end="", flush=True)

    # 🧾 Choix du format de sortie
    format_choice = choose_output_format()
    if output_file is None:
        base_name = os.path.splitext(os.path.basename(input_file))[0]
        output_file = os.path.join(hits_dir, f"{base_name}_active.txt")

    with open(output_file, "w", encoding="utf-8") as out_file:
        out_file.write("")

    def extract_domains(file):
        with open(file, "r", encoding="utf-8") as f:
            content = f.read()
        urls = re.findall(r"http://[^\s\",]+", content)
        return list(set(urls))

    def is_active(url):
        """
        🔌 VERSION TCP ONLY
        - pas de requête HTTP (pas de GET/HEAD)
        - on teste juste si le port est ouvert (connexion TCP)
        """
        parsed = urlparse(url)
        domain_with_port = parsed.netloc or parsed.path.split("/")[0]

        host_part = domain_with_port
        if ":" in host_part:
            host, port_str = host_part.split(":", 1)
            try:
                port = int(port_str)
            except ValueError:
                port = 80
        else:
            host = host_part
            port = 80

        try:
            with socket.create_connection((host, port), timeout=TIMEOUT):
                info = f"TCP OPEN:{port}"
                return (url, domain_with_port, True, info)
        except socket.timeout:
            info = f"TCP TIMEOUT>{TIMEOUT}s"
            return (None, domain_with_port, False, info)
        except Exception as e:
            info = f"TCP {type(e).__name__}"
            return (None, domain_with_port, False, info)

    urls = extract_domains(input_file)
    total = len(urls)

    if total == 0:
        if lang == "es":
            print(f"\n{Fore.RED}❌ No se ha encontrado ningún http://dominio:puerto en este archivo.{Fore.RESET}")
        elif lang == "it":
            print(f"\n{Fore.RED}❌ Nessun http://dominio:porta trovato in questo file.{Fore.RESET}")
        else:
            print(f"\n{Fore.RED}❌ No http://domain:port found in this file.{Fore.RESET}")
        return

    if lang == "es":
        print(f"\n{Fore.YELLOW}🔍 Analizando {total} dominio(s)...{Fore.RESET}\n")
    elif lang == "it":
        print(f"\n{Fore.YELLOW}🔍 Analisi di {total} dominio/i...{Fore.RESET}\n")
    else:
        print(f"\n{Fore.YELLOW}🔍 Analyzing {total} domain(s)...{Fore.RESET}\n")

    done_count = 0
    active_count = 0
    inactive_count = 0
    panel_lock = threading.Lock()
    file_lock = threading.Lock()

    _render_active_domains_panel(total, done_count, active_count, inactive_count, current="")

    def task(url):
        start = time.time()
        url_res, domain, success, info = is_active(url)
        elapsed = time.time() - start
        if elapsed > MAX_WORKER_LIFETIME:
            domain_label = domain or url
            if lang == "es":
                return (None, domain_label, False, f"Hilo > {MAX_WORKER_LIFETIME}s")
            elif lang == "it":
                return (None, domain_label, False, f"Thread > {MAX_WORKER_LIFETIME}s")
            else:
                return (None, domain_label, False, f"Worker timeout > {MAX_WORKER_LIFETIME}s")
        return (url_res, domain, success, info)

    with ThreadPoolExecutor(max_workers=NB_THREADS) as executor:
        future_to_url = {executor.submit(task, u): u for u in urls}
        for fut in as_completed(future_to_url):
            url = future_to_url[fut]
            try:
                url_res, domain, success, info = fut.result()
            except Exception as e:
                url_res, domain, success, info = (None, url, False, f"error:{type(e).__name__}")

            if success and url_res and domain:
                if format_choice == "1":
                    line = url_res
                elif format_choice == "2":
                    line = domain.split(':')[0]
                else:
                    line = domain
                with file_lock:
                    with open(output_file, "a", encoding="utf-8") as out_file:
                        out_file.write(line + "\n")

            with panel_lock:
                done_count += 1
                if success:
                    active_count += 1
                else:
                    inactive_count += 1
                label = (domain or url) + f" • {info}"
                push_active_event(success, label)
                _render_active_domains_panel(
                    total, done_count, active_count, inactive_count, current=(domain or url)
                )

    if lang == "es":
        print(
            f"\n{Fore.GREEN}✅ ¡Filtrado completado!{Fore.RESET} "
            f"{Fore.CYAN}{done_count}{Fore.RESET}/{Fore.CYAN}{total}{Fore.RESET} comprobados."
        )
        print(f"{Fore.GREEN}📁 Resultados guardados en:{Fore.RESET} {output_file}")
    elif lang == "it":
        print(
            f"\n{Fore.GREEN}✅ Filtraggio completato!{Fore.RESET} "
            f"{Fore.CYAN}{done_count}{Fore.RESET}/{Fore.CYAN}{total}{Fore.RESET} verificati."
        )
        print(f"{Fore.GREEN}📁 Risultati salvati in:{Fore.RESET} {output_file}")
    else:
        print(
            f"\n{Fore.GREEN}✅ Filtering complete!{Fore.RESET} "
            f"{Fore.CYAN}{done_count}{Fore.RESET}/{Fore.CYAN}{total}{Fore.RESET} checked."
        )
        print(f"{Fore.GREEN}📁 Results saved to:{Fore.RESET} {output_file}")
                
def get_or_create_session():
    session_path = get_session_path()
    if os.path.exists(session_path):
        with open(session_path, "r") as f:
            return f.read().strip()
    print("\n\033[33mNo StringSession found. Creating automatically...\033[0m")
    with TelegramClient(StringSession(), api_id, api_hash) as client:
        client.start()
        session_str = client.session.save()
        with open(session_path, "w") as f:
            f.write(session_str)
        print(f"\033[32m✅ Session created and saved to: {session_path}\033[0m")
        return session_str
                 
def load_progress():
    """
    Charge la progression du scraper (JSON).
    Retourne un dict ou None si pas de fichier / erreur.
    """
    try:
        if not os.path.exists(PROGRESS_FILE):
            return None
        with open(PROGRESS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def save_progress(data):
    """
    Sauvegarde la progression actuelle dans PROGRESS_FILE.
    """
    try:
        with open(PROGRESS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def clear_progress():
    """
    Supprime le fichier de progression (fin d'analyse complète).
    """
    try:
        if os.path.exists(PROGRESS_FILE):
            os.remove(PROGRESS_FILE)
    except Exception:
        pass
        
def clean_residual_files(directory=None):
    """
    Nettoie une fois les fichiers .txt résiduels dans:
    Hits/SUPER-SCRAPER/residual
    (appelée à la fin du scraper)
    """
    import os

    # Par défaut → dossier RESIDUAL
    if directory is None:
        directory = RESIDUAL_DIR

    try:
        os.makedirs(directory, exist_ok=True)
    except Exception:
        return

    try:
        for file in os.listdir(directory):
            if file.endswith(".txt"):
                file_path = os.path.join(directory, file)
                try:
                    os.remove(file_path)
                    print(f"\033[31m🧹 Residual file deleted: {file_path}\033[0m")
                except Exception:
                    pass
    except Exception:
        pass
                        
def _http_base(url):
    """
    Compat QPython : renvoie scheme://host:port
    (sans annotation moderne str | None)
    """
    s = (url or "").strip()
    if not s:
        return None

    if not s.startswith(("http://", "https://")):
        s = "http://" + s

    try:
        p = urlparse(s)
        host = p.hostname
        if not host:
            return None


        # ⛔ Ignorer IPv6 (préférence utilisateur)
        if _is_ipv6_host(host):
            return None
        port = p.port or (443 if p.scheme == "https" else 80)
        return "%s://%s:%s" % (p.scheme, _fmt_host(host), port)

    except Exception:
        return None
# ─────────────────────────────────────────────

def save_hit_http(hitdata: str):
    """
    Enregistre un lien HTTP normalisé (scheme://host:port) dans filename_http.txt
    sans doublons :
      - normalisation via _http_base()
      - déduplication grâce à SAVED_HTTP_BASES
    """
    global SAVED_HTTP_BASES, global_counts

    try:
        base = _http_base(hitdata)
        if not base:
            return

        # ⛔ Déjà enregistré ? → on ne réécrit pas
        if base in SAVED_HTTP_BASES:
            return

        # 📝 Nouveau serveur → on ajoute dans le fichier et dans le set
        with open(f"{hits_dir}/{filename}_http.txt", 'a+', encoding="utf-8") as f:
            f.write(base.strip() + '\n')

        SAVED_HTTP_BASES.add(base)
        global_counts["http"] += 1

    except Exception:
        # on ne casse jamais le scraper pour un problème d'IO
        pass

def save_hit_m3u(hitdata: str):
    """
    Enregistre un lien M3U complet normalisé dans filename_m3u.txt
    sans doublons en mémoire session.
    """
    global SAVED_M3U, global_counts
    try:
        h = hitdata.strip()
        if not h or h in SAVED_M3U:
            return
        with open(f"{hits_dir}/{filename}_m3u.txt", 'a+', encoding="utf-8") as f:
            f.write(h + '\n')
        SAVED_M3U.add(h)
        global_counts["m3u"] += 1
    except Exception:
        pass
        
def clean_raw_combo(user, password):
    """
    Nettoie les combos extraits depuis Telegram :
    - supprime tout après '&password'
    - supprime les 'type:m3u_plus'
    - garde uniquement USER:PASSWORD propre
    """

    # USER : couper avant &password ou &type
    user = re.split(r"&password|&type", user)[0]

    # PASSWORD : couper avant &type ou tout doublon
    password = re.split(r"&type", password)[0]

    return user.strip(), password.strip()

def save_hit_combo(user: str, password: str):
    """
    Enregistre un combo user:pass dans filename_combo.txt
    et incrémente global_counts["combo"].
    """
    try:
        with open(f"{hits_dir}/{filename}_combo.txt", 'a+', encoding="utf-8") as f:
            f.write(f"{user}:{password}\n")
        global_counts["combo"] += 1
    except Exception:
        pass


# 🔥 MAC brutes (ex: 00:1A:79:A3:2B:C1)
def save_hit_mac(mac_str: str):
    """
    Enregistre une MAC brute dans filename_mac.txt
    (compteur affiché via len(found_mac)).
    """
    try:
        with open(f"{hits_dir}/{filename}_mac.txt", 'a+', encoding="utf-8") as f:
            f.write(mac_str.strip() + "\n")
    except Exception:
        pass


# 🔥 Portails MAG/STB (ex: http://host:8080/c/)
def save_hit_http_mac(url: str):
    """
    Enregistre un portail MAG /c/ dans filename_http_mac.txt
    (compteur affiché via len(found_http_mac)).
    """
    try:
        with open(f"{hits_dir}/{filename}_http_mac.txt", 'a+', encoding="utf-8") as f:
            f.write(url.strip() + "\n")
    except Exception:
        pass


def _seed_counts_from_files():
    """
    Recharge les compteurs globaux (Total HTTP / Total M3U / COMBOS)
    à partir des fichiers *_http.txt, *_m3u.txt, *_combo.txt si ils existent.
    + pour HTTP : recharge aussi le set SAVED_HTTP_BASES pour éviter les doublons.
    """
    global SAVED_HTTP_BASES, global_counts

    try:
        for kind in ("http", "m3u", "combo"):
            path = f"{hits_dir}/{filename}_{kind}.txt"
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    lines = {l.strip() for l in f if l.strip()}

                global_counts[kind] = len(lines)

                # Pour HTTP : on garde aussi les lignes en mémoire
                if kind == "http":
                    SAVED_HTTP_BASES = set(lines)
    except Exception:
        # en cas de souci : on laisse les compteurs à 0, mais on ne plante pas
        pass
        


ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")

def strip_ansi(text: str) -> str:
    """Supprime les codes de couleur ANSI d'une chaîne."""
    return ANSI_RE.sub("", text)
def remove_ansi(text: str) -> str:
    """Alias compatible : ancien nom utilisé dans le script."""
    return strip_ansi(text)
        
def is_valid_combo(user, password):
    import re

    u = user.strip().lower()
    p = password.strip().lower()

    # ❌ Exclure MAC ou formats dérivés
    if u.startswith("play:live.php?mac=") or p.startswith("play:live.php?mac="):
        return False
    if "mac=" in u or "mac=" in p:
        return False

    # ❌ Adresses MAC directes
    mac_pattern = r"(?:[0-9a-f]{2}[:-]){5}[0-9a-f]{2}"
    if re.fullmatch(mac_pattern, u, re.IGNORECASE) or re.fullmatch(mac_pattern, p, re.IGNORECASE):
        return False

    # ❌ Valeurs vides, N/A, null
    if not u or not p or u in {"n/a", "na", "null"} or p in {"n/a", "na", "null"}:
        return False

    # ❌ Placeholders
    if any(tag in (u + p) for tag in (
        "<user>", "<pass>", "<username>", "<password>",
        ":user:", ":pass:", "user::", "pass::"
    )):
        return False

    # ❌ Liens vidéo
    video_ext = [".ts", ".m3u8", ".mp4", ".avi", ".mov", "?ext=.ts"]
    if any(ext in u for ext in video_ext) or any(ext in p for ext in video_ext):
        return False

    # ❌ Combos pollués (&password / &type / %26)
    if any(tag in u for tag in ("&password", "&type", "?type", "%26")):
        return False
    if any(tag in p for tag in ("&password", "&type", "?type", "%26")):
        return False

    # ❌ Fragments JSON / API web
    if any(token in (u + p) for token in (
        "captcha", "rememberme", "prefillusername",
        "fingerprint", "csrf", "json", "{", "}", "[", "]"
    )):
        return False

    # ❌ Caractères et symboles indésirables
    if re.search(r"[<>\|\"]", u) or re.search(r"[<>\|\"]", p):
        return False
    if "\\" in u or "\\" in p:
        return False
    if "::" in u or "::" in p:
        return False
    if "\r" in u or "\n" in u or "\r" in p or "\n" in p:
        return False

    # ⚠️ ICI : on laisse maintenant passer user == password (comme tu veux)
    return True
                
MAC_PATTERN = re.compile(r"([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})", re.IGNORECASE)
PORTAL_MAC_PATTERN = re.compile(r"https?://[^\s\"]+/c/", re.IGNORECASE)    
REGEX_M3U = re.compile(
    r"""https?://[^\s'"]+get\.php\?(?:username|user)=([^\s&]+)&(?:password|pass)=([^\s&]+)(?![^"']*mac=)[^"'\s]*""",
    re.IGNORECASE
)
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse


# ─────────────────────────────────────────────
# IPv6 helpers (évite "Invalid IPv6 URL" sur requests/urlparse)
import re as _re_ipv6

def _fmt_host(host: str) -> str:
    """Ajoute des crochets autour d'une IPv6 littérale pour former une URL valide."""
    h = (host or "").strip()
    if not h:
        return h
    if h.startswith("[") and h.endswith("]"):
        return h
    # heuristique: IPv6 littérale (seulement hex + :)
    if ":" in h and _re_ipv6.fullmatch(r"[0-9A-Fa-f:]+", h):
        return f"[{h}]"
    return h

def _fix_ipv6_url(url: str) -> str:
    """Répare http(s)://IPv6:port (sans crochets) → http(s)://[IPv6]:port"""
    s = (url or "").strip()
    if not s:
        return s
    if not s.lower().startswith(("http://", "https://")):
        return s
    m = _re_ipv6.match(r"^(https?://)([^/]+)(.*)$", s, _re_ipv6.IGNORECASE)
    if not m:
        return s
    prefix, netloc, rest = m.group(1), m.group(2), m.group(3)

    # preserve éventuel userinfo "user:pass@"
    userinfo = ""
    hostport = netloc
    if "@" in netloc:
        userinfo, hostport = netloc.rsplit("@", 1)
        userinfo += "@"

    # déjà bracketé → ok
    if "[" in hostport:
        return s

    # IPv6 probable si >= 2 ':'
    if hostport.count(":") >= 2:
        host_part = hostport
        port_part = ""
        mp = _re_ipv6.match(r"^(.+):(\d+)$", hostport)
        if mp:
            host_part, port_part = mp.group(1), mp.group(2)
        if _re_ipv6.fullmatch(r"[0-9A-Fa-f:]+", host_part):
            hostport = f"[{host_part}]" + (f":{port_part}" if port_part else "")
            return prefix + userinfo + hostport + rest

    return s
# ─────────────────────────────────────────────

def normalize_m3u_url(url: str):
    """
    Normalise un M3U Xtream Codes:
    - force type=m3u_plus
    - force output=m3u8
    - supprime autres params inutiles
    - renvoie l'URL normalisée
    """
    try:
        u = _fix_ipv6_url(url.strip())
        p = urlparse(u)
        q = parse_qs(p.query)

        # username/password obligatoires
        user = (q.get("username") or q.get("user") or [None])[0]
        pwd  = (q.get("password") or q.get("pass") or [None])[0]
        if not user or not pwd:
            return None

        # params standard
        new_q = {
            "username": user,
            "password": pwd,
            "type": "m3u_plus",
            "output": "m3u8"
        }

        new_query = urlencode(new_q, doseq=False)

        new_p = p._replace(query=new_query)
        return urlunparse(new_p)

    except Exception:
        return None
        
# === Préfixes MAC des STB les plus connus (MAG, STB asiatiques, Raspberry Pi, etc.) ===
stb_mac_prefixes = [
    "00:1A:79",  # MAG Devices (très courant)
    "00:1B:7A",  # STB diverses
    "00:1C:7B",  # STB diverses
    "00:1D:7C",  # STB diverses
    "00:1E:7D",  # STB diverses
    "00:1F:7E",  # STB diverses
    "54:9F:35",  # STB asiatiques
    "D4:11:AE",  # STB chinoises
    "A4:17:31",  # STB diverses
    "B8:27:EB",  # Raspberry Pi (souvent utilisés comme STB IPTV)
]

def _http_from_m3u_base(url):
    try:
        p = urlparse(url.strip())
        host = p.hostname
        if not host:
            return None
        scheme = (p.scheme or "").lower()
        port = p.port or (80 if scheme == "http" else 443)

        # ✅ Amélioration : si c’est vraiment HTTPS:443 → on garde https://
        if scheme == "https" and port == 443:
            return f"https://{_fmt_host(host)}:{port}"
        # Sinon on force en HTTP comme avant
        return f"http://{_fmt_host(host)}:{port}"
    except Exception:
        return None
        
            
# urlparse: utilise la version globale sécurisée
def _portal_from_mac_url(url):
    """
    À partir d'un lien complet avec mac=..., reconstruit un portail MAG:
      http://host:port/c/

    Si host ou port manquent, renvoie None.
    """
    try:
        p = urlparse(url.strip())
        scheme = p.scheme or "http"
        host = p.hostname
        if not host:
            return None
        port = p.port or (80 if scheme == "http" else 443)
        return f"{scheme}://{_fmt_host(host)}:{port}/c/"
    except Exception:
        return None                                    
# --- Helper: extrait http://host:port à partir d'un lien M3U ---
def _normalize_labels(s: str) -> str:
    """Normalise le texte avant extraction (accents, décorations, small-caps, etc.)."""
    import unicodedata, re

    # 1) Forme canonique + suppression des diacritiques
    s = unicodedata.normalize("NFKD", s)
    s = "".join(ch for ch in s if not unicodedata.combining(ch))

    # 2) Convertit les 'small caps' Unicode (ex: ʜᴏsᴛ, ᴜsᴇʀɴᴀᴍᴇ, ᴘᴀssᴡᴏʀᴅ) vers ASCII
    _SMALLCAPS = {
        "ᴀ": "a", "ʙ": "b", "ᴄ": "c", "ᴅ": "d", "ᴇ": "e", "ꜰ": "f", "ғ": "f",
        "ɢ": "g", "ʜ": "h", "ɪ": "i", "ᴊ": "j", "ᴋ": "k", "ʟ": "l", "ᴌ": "l",
        "ᴍ": "m", "ɴ": "n", "ᴏ": "o", "ᴘ": "p", "ꞯ": "q", "ʀ": "r",
        "ꜱ": "s", "s": "s", "ᴛ": "t", "ᴜ": "u", "ᴠ": "v", "ᴡ": "w",
        "x": "x", "ʏ": "y", "ᴢ": "z",
    }
    # translate() attend une table ord->str
    s = s.translate({ord(k): v for k, v in _SMALLCAPS.items()})

    # 3) Supprime les tags décoratifs fréquents du type "❪...❫" (ex: ❪웃❫)
    s = re.sub(r"❪[^❫]{0,20}❫", " ", s)

    # 4) Nettoyage de quelques décorations connues
    s = re.sub(r"[╔╗║╚╝═🚧]+", " ", s)

    return s


def _iter_labeled_creds(text: str):
    """
    Détection multi-langue (EN / ES / PT) de blocs Host / User / Pass.
    Version stable + améliorée :
      - support des flèches (➺, ➤, →, ➜, ➡, etc.)
      - support de 'username'
      - NETTOYAGE des paramètres supplémentaires (&password, &type, etc.)
      - 'Real Url' et 'Portal' acceptés comme synonymes de Host
      - FIX: évite les valeurs qui commencent par '=' (ex: '=madalina')
    """
    import re

    norm = _normalize_labels(text)
    blocks = re.split(r"\n\s*\n", norm)

    for block in blocks:
        low = block.lower()

        # Déclencheurs de bloc (Host/User/Pass)
        if not any(k in low for k in (
            "host", "server", "servidor", "dominio",
            "real url", "portal",
            "user", "username", "usuario", "login",
            "senha", "password", "contrase", "clave"
        )):
            continue

        host = user = pwd = None

        for raw_line in block.splitlines():
            line = _normalize_labels(raw_line).strip()
            if not line:
                continue
            l = line

            # Normalise uniquement le séparateur entre le label et la valeur (sans casser les URLs)
            # Ajout real url + portal dans les labels
            l = re.sub(
                r"^(\s*(?:host|server|servidor|dominio|real\s*url?|portal|"
                r"user|username|usuario|login|pass(?:word)?|senha|contrase[nñ]a|clave)\s*)"
                r"[➺➤»▶→➡➞➟➠➜➝➙➛➚➘➥➦➧➨➩➮➯➱➲➳➵➸➻➼➽➾＝=><\-–—•·]+\s*",
                r"\1: ",
                l,
                flags=re.I
            )

            # Host = host/server/servidor/dominio/real url/portal
            m = re.search(
                r"\b(host|server|servidor|dominio|portal|real\s*url?)\b"
                r"\s*(?:\s*[:=\-–]\s*)?(\S+)",
                l,
                flags=re.I
            )
            if m and not host:
                host = m.group(2).strip()
                host = host.lstrip("=＝")  # ✅ FIX

            # User : accepte ":" "-" "–" ET "=" comme séparateur (évite que "=" rentre dans la valeur)
            m = re.search(
                r"\b(user|username|usuario|login)\b\s*(?:\s*[:=\-–]\s*)?([^\s]+)",
                l,
                flags=re.I
            )
            if m and not user:
                user = m.group(2).strip()
                # NETTOYAGE: supprime tout après &password ou &type
                user = re.split(r"&password|&type|\?password|\?type", user)[0]
                user = user.strip().lstrip("=＝")  # ✅ FIX

            # Password : accepte ":" "-" "–" ET "=" comme séparateur
            m = re.search(
                r"\b(pass(word)?|senha|contrase[nñ]a|clave)\b\s*(?:\s*[:=\-–]\s*)?([^\s]+)",
                l,
                flags=re.I
            )
            if m and not pwd:
                pwd = m.group(3).strip()
                # NETTOYAGE: supprime tout après &type
                pwd = re.split(r"&type|\?type", pwd)[0]
                pwd = pwd.strip().lstrip("=＝")  # ✅ FIX

        if host and user and pwd:
            if not host.startswith("http://") and not host.startswith("https://"):
                host = "http://" + host

            yield {"host": host, "user": user, "password": pwd}
                        
# Améliorer la détection des MAC dans la fonction extract_http_and_m3u
def extract_http_and_m3u(text, results_http, results_m3u,
                         current_msg_id=None, live_status=None,
                         keep_pred=None, enable_mac_portal_detection=True, heartbeat=None):
    import re
    from urllib.parse import urlparse, parse_qs, urlencode, urlunparse

    if keep_pred is None:
        keep_pred = lambda kind, url: True

    if heartbeat:
        heartbeat()

    # ✅ Normalisation interne M3U : garde uniquement type=m3u_plus&output=m3u8
    def normalize_m3u_url(url: str):
        try:
            u = (url or "").strip()
            if not u:
                return None
            p = urlparse(u)
            q = parse_qs(p.query)

            user = (q.get("username") or q.get("user") or [None])[0]
            pwd  = (q.get("password") or q.get("pass") or [None])[0]
            if not user or not pwd:
                return None

            new_q = {
                "username": user,
                "password": pwd,
                "type": "m3u_plus",
                "output": "m3u8"
            }

            new_query = urlencode(new_q, doseq=False)
            new_p = p._replace(query=new_query)
            return urlunparse(new_p)
        except Exception:
            return None

    # 0-bis) BLOCS Host / User / Pass (EN / ES / PT), SANS EXPIRES
    _hb_i = 0
    for cred in _iter_labeled_creds(text):
        _hb_i += 1
        if heartbeat and (_hb_i % 200 == 0):
            heartbeat()

        host = cred["host"]
        user = cred["user"]
        pwd  = cred["password"]

        # 🔥 FILTRE MAC : si désactivé, rejeter les user/password avec mac=
        if not enable_mac_portal_detection and ("mac=" in user.lower() or "mac=" in pwd.lower()):
            continue

        combo = f"{user}:{pwd}"

        # 🛑 Bloquer les faux combos MAC
        if user.lower().startswith("play:live.php?mac=") or pwd.lower().startswith("play:live.php?mac="):
            continue

        # 🛡️ On ignore les combos sans host clair
        if not host or not re.match(r"^https?://[a-z0-9\-\.]+(:\d+)?", host, re.IGNORECASE):
            continue  # Pas de host HTTP valide → on ignore

        # ✅ Si combo complet et valide → on enregistre
        if is_valid_combo(user, pwd) and combo not in found_combo:
            found_combo.add(combo)
            save_hit_combo(user, pwd)
            if live_status:
                live_status(None, None, combo, None)
            if heartbeat:
                heartbeat()

            # 🧩 NOUVEAU : générer automatiquement le M3U à partir de host + user + pass
            try:
                m3u_candidates = _m3u_from_host_creds(host, user, pwd)
            except Exception:
                m3u_candidates = []

            for raw_m3u in m3u_candidates:
                url = normalize_m3u_url(raw_m3u) or (raw_m3u.strip() if raw_m3u else "")
                if not url:
                    continue
                if not keep_pred("m3u", url):
                    continue
                if url not in found_m3u:
                    found_m3u.add(url)
                    results_m3u.append(url)
                    save_hit_m3u(url)
                    if live_status:
                        live_status(None, url, None, None)
                    if heartbeat:
                        heartbeat()

        # ✅ Host ajouté à la liste HTTP si non présent
        if keep_pred("http", host) and host not in found_http:
            found_http.add(host)
            results_http.append(host)
            save_hit_http(host)
            if live_status:
                live_status(host, None, None, None)

    # 0-ter) 🔥 Détection MAC + portails MAG/STB - CONDITIONNELLE
    if enable_mac_portal_detection:
        try:
            raw_candidates = set()

            # MAC "classiques" 00:11:22:33:44:55 ou 00-11-22-33-44-55
            for m in re.finditer(r"(?:[0-9A-Fa-f]{2}[:-]){5}[0-9A-Fa-f]{2}", text, re.IGNORECASE):
                raw_candidates.add(m.group(0))
            # MAC dans mac=XX:XX...
            for m in re.finditer(r"mac=([0-9A-Fa-f:\-]{11,23})", text, re.IGNORECASE):
                raw_candidates.add(m.group(1))
            # MAC compactes 001122334455
            for m in re.finditer(r"(?<![0-9A-Fa-f])[0-9A-Fa-f]{12}(?![0-9A-Fa-f])", text, re.IGNORECASE):
                raw_candidates.add(m.group(0))

            all_macs = set()
            for raw in raw_candidates:
                mac = raw.strip()
                if "mac=" in mac.lower():
                    mac = mac.split("=", 1)[1].strip()
                mac = mac.replace("-", ":").upper()
                compact = re.sub(r"[^0-9A-F]", "", mac)
                if ":" not in mac and len(compact) == 12:
                    mac = ":".join(compact[i:i+2] for i in range(0, 12, 2))
                if not re.fullmatch(r"(?:[0-9A-F]{2}:){5}[0-9A-F]{2}", mac):
                    continue
                all_macs.add(mac)

            for mac in all_macs:
                if not any(mac.startswith(prefix) for prefix in stb_mac_prefixes):
                    continue
                if mac in found_mac:
                    continue
                found_mac.add(mac)
                save_hit_mac(mac)
                if live_status:
                    live_status(None, None, None, None, new_portal=None, new_mac=mac)

            portal_patterns = [
                r"https?://[^\s\"]+/c/",
                r"https?://[^\s\"]+:8080/c/",
                r"https?://[^\s\"]+:80/c/",
                r"http[^\s\"]*?/c/",
            ]

            all_portals = set()
            for pattern in portal_patterns:
                for m in re.finditer(pattern, text, re.IGNORECASE):
                    all_portals.add(m.group(0))

            for url in all_portals:
                if url not in found_http_mac:
                    found_http_mac.add(url)
                    save_hit_http_mac(url)
                    if keep_pred("http", url) and url not in found_http:
                        found_http.add(url)
                        results_http.append(url)
                        save_hit_http(url)
                    if live_status:
                        live_status(None, None, None, None, new_portal=url, new_mac=None)

        except Exception as e:
            print(f"⚠️ Erreur détection MAC/Portail: {e}")

    # 1️⃣ Liens HTTP(S) bruts trouvés — ❌ DÉSACTIVÉ (pas de host seul)
    pass  # <-- cette ligne neutralise toute la détection brute

    # 2️⃣ Liens M3U + conversion host:port (✅ corrigé)
    _hb_m = 0
    for match in re.finditer(REGEX_M3U, text):
        _hb_m += 1
        if heartbeat and (_hb_m % 200 == 0):
            heartbeat()
        raw_url = match.group(0)
        username = match.group(1)
        password = match.group(2)

        if not enable_mac_portal_detection and "mac=" in raw_url.lower():
            continue

        # -- Garder la logique MAC/MAG EXACTEMENT comme avant --
        if enable_mac_portal_detection and re.search(
            r"mac=([0-9A-Fa-f]{2}[:-]){5}([0-9A-Fa-f]{2})", raw_url, re.IGNORECASE
        ):
            portal = _portal_from_mac_url(raw_url)
            if portal and portal not in found_http_mac:
                found_http_mac.add(portal)
                save_hit_http_mac(portal)
                if live_status:
                    live_status(None, None, None, None, new_portal=portal, new_mac=None)
            try:
                parsed = urlparse(raw_url)
                base_domain = f"{parsed.scheme}://{parsed.netloc}"
                if base_domain not in found_http:
                    found_http.add(base_domain)
                    results_http.append(base_domain)
                    save_hit_http(base_domain)
                    if live_status:
                        live_status(base_domain, None, None, None)
            except Exception:
                pass
            continue

        # ✅ Normaliser → si c'était une version brute ou incomplète, elle devient complète
        url = normalize_m3u_url(raw_url)
        if not url:
            continue  # brute / cassé → ignoré

        if not keep_pred("m3u", url):
            continue

        # ✅ Dedup sur URL normalisée
        if url not in found_m3u:
            found_m3u.add(url)
            results_m3u.append(url)
            if heartbeat:
                heartbeat()
            save_hit_m3u(url)
            if live_status:
                live_status(None, url, None, None)

        base_http = _http_from_m3u_base(url)
        if base_http and keep_pred("http", base_http):
            m2 = re.search(r"https?://([^:/]+)", base_http)
            if m2:
                domain_txt = m2.group(1).lower()
                if ('www.' not in domain_txt) and ('cpanel' not in domain_txt):
                    if base_http not in found_http:
                        found_http.add(base_http)
                        results_http.append(base_http)
                        save_hit_http(base_http)
                        if live_status:
                            live_status(base_http, None, None, None)

        if is_valid_combo(username, password):
            combo = f"{username}:{password}"
            if combo not in found_combo:
                found_combo.add(combo)
                save_hit_combo(username, password)
                if live_status:
                    live_status(None, None, combo, None)
                                                                                                                                                                                                                                                                                
def _m3u_from_host_creds(host: str, user: str, pwd: str):
    """
    Génère un lien M3U Xtream Codes au format :
      http://host:port/get.php?username=USER&password=PASS&type=m3u_plus&output=m3u8

    - host : http://domaine:port
    - user : login
    - pwd  : mot de passe

    Si le host contient déjà get.php ou .m3u, on le renvoie tel quel.
    """
    host = host.strip()

    low = host.lower()
    # Si c'est déjà un M3U complet ou un lien get.php, on ne le modifie pas
    if "get.php" in low or ".m3u" in low:
        return [host]

    # On enlève "/" final pour éviter //get.php
    base = host.rstrip("/")

    # Format demandé par toi :
    # type=m3u_plus  +  output=m3u8
    m3u_url = (
        f"{base}/get.php?"
        f"username={user}&password={pwd}"
        f"&type=m3u_plus&output=m3u8"
    )
    return [m3u_url]

from telethon.tl.types import MessageEntityTextUrl

def _extract_hidden_urls(message):

    import re
    urls = []


    text = message.message or ""
    urls.extend(re.findall(r"https?://[^\s'\"<>]+", text))


    try:
        entities = getattr(message, "entities", None)
        if entities:
            for ent in entities:
                if hasattr(ent, "url") and ent.url:
                    urls.append(ent.url)
    except Exception:
        pass


    try:
        btn_rows = getattr(message, "buttons", None)
        if btn_rows:
            for row in btn_rows:
                for btn in row:
                    # Bouton normal
                    url = getattr(btn, "url", None)
                    if url:
                        urls.append(url)

                
                    if hasattr(btn, "web_app") and btn.web_app:
                        wa = getattr(btn.web_app, "url", None)
                        if wa:
                            urls.append(wa)
    except Exception:
        pass

    return urls
                                                                                                          
def analyze_message(message, client, results_http, results_m3u, live_status=None, keep_pred=None):

    try:
        # Timeout "inactivité": se déclenche seulement si rien n'avance pendant INACTIVITY_TIMEOUT_SEC.
        with InactivityGuard(INACTIVITY_TIMEOUT_SEC) as guard:
            guard.touch()

            if message.sender and hasattr(message.sender, 'username') and message.sender.username in IGNORED_BOT_USERNAMES:
                return
            current_id = str(message.id)
            if message.message:
                if live_status:
                    def ls_wrapper(url, m3u, combo, _msg_date=None, new_portal=None, new_mac=None):
                        msg_dt = message.date.astimezone() if hasattr(message.date, "astimezone") else message.date
                        return live_status(url, m3u, combo, msg_dt, new_portal=new_portal, new_mac=new_mac)
                else:
                    ls_wrapper = None

                payload = message.message or ""
                extra_urls = _extract_hidden_urls(message)
                if extra_urls:
                    payload = payload + "\n" + "\n".join(extra_urls)

                guard.touch()

                extract_http_and_m3u(
                    payload,
                    results_http,
                    results_m3u,
                    current_id,
                    ls_wrapper,
                    keep_pred=keep_pred,
                    enable_mac_portal_detection=DETECT_MACS,
                    heartbeat=guard.touch
                )

    except InactivityTimeout:
        raise
    except Exception as e:
        print(f"❌ Error in message {str(getattr(message, 'id', '?'))}: {e}")

def analyze_txt(message, client, results_http, results_m3u, live_status=None, keep_pred=None):

    import os, re

    file_path = None
    try:
        with InactivityGuard(INACTIVITY_TIMEOUT_SEC) as guard:
            guard.touch()

            if message.sender and hasattr(message.sender, 'username') and message.sender.username in IGNORED_BOT_USERNAMES:
                return

            current_id = str(message.id)

            if message.document and message.document.mime_type == 'text/plain':
                file_name = getattr(message.document, 'file_name', f"document_{current_id}.txt")
                label = f"{file_name}  (ID {current_id})"
                push_txt_event(label)

                safe_name = re.sub(r"[^a-zA-Z0-9_\-\.]", "_", file_name)
                target_path = os.path.join(RESIDUAL_DIR, f"{current_id}_{safe_name}")

                file_path = client.download_media(message.document, file=target_path)
                guard.touch()

                try:
                    total_size = int(getattr(message.document, "size", 0) or 0)
                except Exception:
                    total_size = 0

                msg_dt = message.date.astimezone() if hasattr(message.date, "astimezone") else message.date

                file_idx = globals().get("CURRENT_TXT_FILE_INDEX", 0)
                file_tot = globals().get("CURRENT_TXT_FILE_TOTAL", 0)

                if live_status and total_size > 0:
                    bar = "·" * 10
                    globals()["CURRENT_TXT_PROGRESS"] = f"📄 TXT {file_idx}/{file_tot} 0% [{bar}]"
                    live_status(None, None, None, msg_dt)

                chunks = []
                read_bytes = 0

                try:
                    with open(file_path, "rb") as f:
                        while True:
                            data = f.read(4096)
                            if not data:
                                break
                            chunks.append(data)
                            read_bytes += len(data)
                            guard.touch()

                            if live_status and total_size > 0:
                                pct = int(read_bytes * 100 / total_size)
                                if pct > 100:
                                    pct = 100
                                TOTAL_BLOCKS = 15
                                filled = max(0, min(TOTAL_BLOCKS, int(pct * TOTAL_BLOCKS / 100)))
                                bar = "█" * filled + "·" * (TOTAL_BLOCKS - filled)
                                globals()["CURRENT_TXT_PROGRESS"] = f"📄 TXT {file_idx}/{file_tot} {pct}% [{bar}]"
                                live_status(None, None, None, msg_dt)

                    try:
                        content = b"".join(chunks).decode("utf-8", errors="ignore")
                    except Exception:
                        try:
                            content = b"".join(chunks).decode("latin-1", errors="ignore")
                        except Exception:
                            content = ""

                    if not content:
                        with open(file_path, "r", encoding="latin-1", errors="ignore") as f:
                            content = f.read()

                except Exception:
                    with open(file_path, "r", encoding="latin-1", errors="ignore") as f:
                        content = f.read()

                guard.touch()

                if live_status:
                    def ls_wrapper(url, m3u, combo, _msg_date=None, new_portal=None, new_mac=None):
                        msg_dt2 = message.date
                        if hasattr(msg_dt2, "astimezone"):
                            msg_dt2 = msg_dt2.astimezone()
                        return live_status(url, m3u, combo, msg_dt2, new_portal=new_portal, new_mac=new_mac)
                else:
                    ls_wrapper = None

                extract_http_and_m3u(
                    content,
                    results_http,
                    results_m3u,
                    current_id,
                    ls_wrapper,
                    keep_pred=keep_pred,
                    enable_mac_portal_detection=DETECT_MACS,
                    heartbeat=guard.touch
                )

    except InactivityTimeout:
        raise
    except Exception as e:
        print(f"❌ Error in TXT message {getattr(message, 'id', '?')}: {e}")
    finally:
        try:
            if file_path and os.path.exists(file_path):
                os.remove(file_path)
        except Exception as ex:
            print(f"⚠️ Could not delete file {file_path}: {ex}")

def _parse_base(base_str: str):
    """
    Normalise une entrée utilisateur du type:
      - dctv.pro:8080
      - http://dctv.pro:8080
      - https://dctv.pro (→ port 443 par défaut)
      - dctv.pro (→ port 80 par défaut)
    → retourne (host_lower, port_int)
    """
    s = (base_str or "").strip().lower()
    if not s:
        return None, None
    if not s.startswith(("http://", "https://")):
        # si l'utilisateur n'a pas mis de schéma, supposer http://
        s = "http://" + s
    p = urlparse(s)
    host = (p.hostname or "").lower()
    port = p.port or (443 if p.scheme == "https" else 80)
    return host, port

def _m3u_belongs_to_base(m3u_url: str, base_host: str, base_port: int) -> bool:
    """
    Vérifie si le lien M3U appartient au host:port donnés.
    """
    try:
        p = urlparse(m3u_url.strip())
        host = (p.hostname or "").lower()
        port = p.port or (443 if p.scheme == "https" else 80)
        return (host == base_host) and (port == base_port)
    except Exception:
        return False

def _http_belongs_to_base(http_url: str, base_host: str, base_port: int) -> bool:
    """
    Vérifie si un http(s)://host:port correspond à la base.
    """
    try:
        p = urlparse(http_url.strip())
        host = (p.hostname or "").lower()
        port = p.port or (443 if p.scheme == "https" else 80)
        return (host == base_host) and (port == base_port)
    except Exception:
        return False

def make_keep_pred(base_choice: str):
    """
    Construit un prédicat keep_pred(kind, url) qui retourne True/False.
      - kind ∈ {"m3u","http"} (les combos viennent des M3U conservés)
    Si base_choice est vide → garde tout.
    """
    base_host, base_port = _parse_base(base_choice)
    if not base_host or not base_port:
        # pas de filtre → on garde tout
        return lambda kind, url: True

    def _pred(kind: str, url: str) -> bool:
        if kind == "m3u":
            return _m3u_belongs_to_base(url, base_host, base_port)
        if kind == "http":
            return _http_belongs_to_base(url, base_host, base_port)
        # pour "combo": il n'est appelé que quand on a accepté un M3U,
        # donc on ne filtre pas ici
        return True

    return _pred

from colorama import Fore, Style

def run_scraper():
    global filename, found_http, found_m3u, found_combo, found_mac, found_http_mac, LANG

    resume_mode = False
    prev = load_progress()
    last_dates_map = {}

    # ====== SYSTÈME REPRISE ======
    if prev:
        if LANG == "es":
            print(f"\n{Fore.YELLOW}⚠️  Se ha detectado un análisis anterior{Fore.RESET}")
        elif LANG == "it":
            print(f"\n{Fore.YELLOW}⚠️  È stata rilevata un'analisi precedente{Fore.RESET}")
        else:
            print(f"\n{Fore.YELLOW}⚠️  A previous analysis was detected{Fore.RESET}")

        # Display filename + ".txt"
        fname = prev.get("filename", "?")
        if LANG == "es":
            print(
                f"   {Fore.YELLOW}💾Archivo:{Fore.RESET} "
                f"{Fore.CYAN}{fname}.txt{Fore.RESET}"
            )
        elif LANG == "it":
            print(
                f"   {Fore.YELLOW}💾File:{Fore.RESET} "
                f"{Fore.CYAN}{fname}.txt{Fore.RESET}"
            )
        else:
            print(
                f"   {Fore.YELLOW}💾File:{Fore.RESET} "
                f"{Fore.CYAN}{fname}.txt{Fore.RESET}"
            )

        # Servers analyzed (current index / total)
        gi = prev.get("group_ids", [])
        total_groups = len(gi)
        current_index = prev.get("next_index", 0)
        if current_index < 0:
            current_index = 0
        if current_index > total_groups:
            current_index = total_groups

        if LANG == "es":
            print(
                f"   {Fore.YELLOW}Servidores analizados:{Fore.RESET} "
                f"{Fore.GREEN}{current_index}{Fore.RESET}"
                f"{Fore.WHITE}/{Fore.RESET}"
                f"{Fore.CYAN}{total_groups}{Fore.RESET}"
            )
        elif LANG == "it":
            print(
                f"   {Fore.YELLOW}Server analizzati:{Fore.RESET} "
                f"{Fore.GREEN}{current_index}{Fore.RESET}"
                f"{Fore.WHITE}/{Fore.RESET}"
                f"{Fore.CYAN}{total_groups}{Fore.RESET}"
            )
        else:
            print(
                f"   {Fore.YELLOW}Servers analyzed:{Fore.RESET} "
                f"{Fore.GREEN}{current_index}{Fore.RESET}"
                f"{Fore.WHITE}/{Fore.RESET}"
                f"{Fore.CYAN}{total_groups}{Fore.RESET}"
            )

        print()  # Empty line for spacing

        # Choices
        if LANG == "es":
            print(
                f"{Fore.GREEN}[1]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Empezar un nuevo análisis{Fore.RESET} "
                f"{Fore.LIGHTBLACK_EX}(borrar el anterior){Fore.RESET}"
            )
            print(
                f"{Fore.GREEN}[2]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Continuar con mi análisis guardado{Fore.RESET}"
            )
            choice = input(f"{Fore.YELLOW}➤ Elección: {Fore.RESET}").strip()
        elif LANG == "it":
            print(
                f"{Fore.GREEN}[1]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Iniziare una nuova analisi{Fore.RESET} "
                f"{Fore.LIGHTBLACK_EX}(cancellare la precedente){Fore.RESET}"
            )
            print(
                f"{Fore.GREEN}[2]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Continuare con l'analisi salvata{Fore.RESET}"
            )
            choice = input(f"{Fore.YELLOW}➤ Scelta: {Fore.RESET}").strip()
        else:
            print(
                f"{Fore.GREEN}[1]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Start a new analysis{Fore.RESET} "
                f"{Fore.LIGHTBLACK_EX}(discard previous){Fore.RESET}"
            )
            print(
                f"{Fore.GREEN}[2]{Fore.RESET} "
                f"{Fore.LIGHTYELLOW_EX}Continue my saved analysis{Fore.RESET}"
            )
            choice = input(f"{Fore.YELLOW}➤ Choice: {Fore.RESET}").strip()

        if choice == "2":
            resume_mode = True
            last_dates_map = prev.get("last_dates", {}) or {}
        else:
            clear_progress()
            prev = None
            last_dates_map = {}
    else:
        last_dates_map = {}
    # ====== FIN SYSTÈME REPRISE ======

    BANNER_WIDTH = 42

    if LANG == "es":
        intro = f"""
\033[33m{'='*BANNER_WIDTH}\033[0m
     {Fore.YELLOW}SUPER SCRAPER{Fore.RESET}        {Fore.CYAN}SOPI987 EDITION{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m

{Fore.YELLOW}Este script extrae enlaces {Fore.GREEN}http://dominio:puerto{Fore.YELLOW}
y {Fore.MAGENTA}enlaces M3U IPTV completos{Fore.YELLOW}
y se detiene cuando los mensajes son más antiguos que el período seleccionado.

{Fore.LIGHTGREEN_EX}Creado por: IGOR  |  Potenciado por SOPI987{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m
"""
    elif LANG == "it":
        intro = f"""
\033[33m{'='*BANNER_WIDTH}\033[0m
     {Fore.YELLOW}SUPER SCRAPER{Fore.RESET}        {Fore.CYAN}SOPI987 EDITION{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m

{Fore.YELLOW}Questo script estrae link {Fore.GREEN}http://dominio:porta{Fore.YELLOW}
e {Fore.MAGENTA}link M3U IPTV completi{Fore.YELLOW}
e si ferma quando i messaggi sono più vecchi del periodo selezionato.

{Fore.LIGHTGREEN_EX}Creato da: IGOR  |  Potenziato da SOPI987{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m
"""
    else:
        intro = f"""
\033[33m{'='*BANNER_WIDTH}\033[0m
     {Fore.YELLOW}SUPER SCRAPER{Fore.RESET}        {Fore.CYAN}SOPI987 EDITION{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m

{Fore.YELLOW}This script extracts {Fore.GREEN}http://domain:port{Fore.YELLOW} links
and {Fore.MAGENTA}complete M3U IPTV links{Fore.YELLOW}
and stops analysis when messages are older than the selected period.

{Fore.LIGHTGREEN_EX}Created by: IGOR  |  Powered by SOPI987{Fore.RESET}
\033[33m{'='*BANNER_WIDTH}\033[0m
"""
    print(intro)

    # --- FILENAME + COMPTEURS ---
    if resume_mode and prev:
        filename = prev.get("filename", "").strip()
        if filename:
            if LANG == "es":
                print(f"{Fore.YELLOW}📁 Usando archivo existente:{Fore.RESET} {Fore.LIGHTYELLOW_EX}{filename}{Fore.RESET}")
            elif LANG == "it":
                print(f"{Fore.YELLOW}📁 Uso file esistente:{Fore.RESET} {Fore.LIGHTYELLOW_EX}{filename}{Fore.RESET}")
            else:
                print(f"{Fore.YELLOW}📁 Using existing file:{Fore.RESET} {Fore.LIGHTYELLOW_EX}{filename}{Fore.RESET}")
        else:
            if LANG == "es":
                filename = input(Fore.YELLOW + "📁 Nombre del archivo para guardar: " + Fore.RESET).strip()
            elif LANG == "it":
                filename = input(Fore.YELLOW + "📁 Nome del file da salvare: " + Fore.RESET).strip()
            else:
                filename = input(Fore.YELLOW + "📁 Save filename: " + Fore.RESET).strip()
    else:
        if LANG == "es":
            filename = input(Fore.YELLOW + "📁 Nombre del archivo para guardar: " + Fore.RESET).strip()
        elif LANG == "it":
            filename = input(Fore.YELLOW + "📁 Nome del file da salvare: " + Fore.RESET).strip()
        else:
            filename = input(Fore.YELLOW + "📁 Save filename: " + Fore.RESET).strip()

    # Sets globaux utilisés par extract_http_and_m3u / analyse
    found_http = set()
    found_m3u = set()
    found_combo = set()
    found_mac = set()
    found_http_mac = set()

    # on recharge les compteurs globaux à partir des fichiers existants
    _seed_counts_from_files()

    # ===== Fenêtre temporelle =====
    date_ranges = {
        "1": datetime.timedelta(days=1),
        "2": datetime.timedelta(days=3),
        "3": datetime.timedelta(weeks=1),
        "4": datetime.timedelta(weeks=4),
        "5": datetime.timedelta(weeks=520)
    }

    if resume_mode and prev and "config" in prev:
        cfg = prev.get("config", {})
        days_back_choice = cfg.get("days_back_choice", "5")
    else:
        if LANG == "es":
            days_back_choice = input("""\033[33m
📆 ¿Hasta qué fecha quieres recuperar mensajes?\033[32m
 1: últimas 24 horas
 2: últimos 3 días
 3: última semana
 4: último mes
 5: todo
 Respuesta: \033[0m""").strip()
        elif LANG == "it":
            days_back_choice = input("""\033[33m
📆 Fino a quando vuoi recuperare i messaggi?\033[32m
 1: ultime 24 ore
 2: ultimi 3 giorni
 3: ultima settimana
 4: ultimo mese
 5: tutto
 Risposta: \033[0m""").strip()
        else:
            days_back_choice = input("""\033[33m
📆 How far back should we retrieve messages?\033[32m
 1: last 24 hours
 2: last 3 days
 3: last week
 4: last month
 5: all
 Answer: \033[0m""").strip()

    date_limit = datetime.datetime.now(timezone.utc) - date_ranges.get(
        days_back_choice, datetime.timedelta()
    )

    # ---- Search mode: ALL vs. specific server ----
    if resume_mode and prev and "config" in prev:
        cfg = prev.get("config", {})
        mode = cfg.get("mode", "1")
        base_choice = cfg.get("base_choice", "")
    else:
        if LANG == "es":
            print(f"\n{Fore.YELLOW}🔎 Modo de búsqueda:{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} Escanear TODOS los mensajes de Telegram")
            print(f" {Fore.YELLOW}2:{Fore.RESET} SOLO un servidor específico")
            mode = input(f"{Fore.CYAN}Tu elección (1/2): {Fore.RESET}").strip()
            base_choice = ""
            if mode == "2":
                base_choice = input(
                    f"{Fore.YELLOW}Introduce el servidor {Fore.RESET}"
                    f"{Fore.CYAN}( ejemplo.com:8080 o http://ejemplo.com:8080){Fore.RESET}: "
                ).strip()
        elif LANG == "it":
            print(f"\n{Fore.YELLOW}🔎 Modalità di ricerca:{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} Scansiona TUTTI i messaggi di Telegram")
            print(f" {Fore.YELLOW}2:{Fore.RESET} SOLO un server specifico")
            mode = input(f"{Fore.CYAN}La tua scelta (1/2): {Fore.RESET}").strip()
            base_choice = ""
            if mode == "2":
                base_choice = input(
                    f"{Fore.YELLOW}Inserisci il server {Fore.RESET}"
                    f"{Fore.CYAN}( esempio.com:8080 o http://esempio.com:8080){Fore.RESET}: "
                ).strip()
        else:
            print(f"\n{Fore.YELLOW}🔎 Search mode:{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} Scan ALL Telegram messages")
            print(f" {Fore.YELLOW}2:{Fore.RESET} ONLY a specific server")
            mode = input(f"{Fore.CYAN}Your choice (1/2): {Fore.RESET}").strip()
            base_choice = ""
            if mode == "2":
                base_choice = input(
                    f"{Fore.YELLOW}Enter server {Fore.RESET}"
                    f"{Fore.CYAN}( example.com:8080 or http://example.com:8080){Fore.RESET}: "
                ).strip()

    keep_pred = make_keep_pred(base_choice)

    # 🔥 Option MAC / Portals
    global DETECT_MACS
    if resume_mode and prev and "config" in prev:
        cfg = prev.get("config", {})
        detect_macs = cfg.get("detect_macs", False)
    else:
        if LANG == "es":
            print(f"\n{Fore.YELLOW}🖥️ ¿Quieres detectar MACs y portales MAG (/c/)?{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} No (modo clásico)")
            print(f" {Fore.GREEN}2:{Fore.RESET} Sí (modo MAC + MAG)")
            mac_choice = input(f"{Fore.CYAN}Tu elección (1/2): {Fore.RESET}").strip()
        elif LANG == "it":
            print(f"\n{Fore.YELLOW}🖥️ Vuoi rilevare MAC e portali MAG (/c/)?{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} No (modalità classica)")
            print(f" {Fore.GREEN}2:{Fore.RESET} Sì (modalità MAC + MAG)")
            mac_choice = input(f"{Fore.CYAN}La tua scelta (1/2): {Fore.RESET}").strip()
        else:
            print(f"\n{Fore.YELLOW}🖥️ Do you want to detect MACs and MAG portals (/c/)?{Fore.RESET}")
            print(f" {Fore.GREEN}1:{Fore.RESET} No (classic mode)")
            print(f" {Fore.GREEN}2:{Fore.RESET} Yes (MAC + MAG mode)")
            mac_choice = input(f"{Fore.CYAN}Your choice (1/2): {Fore.RESET}").strip()
        detect_macs = (mac_choice == "2")
    DETECT_MACS = detect_macs

    # Connexion Telegram (device personnalisé)
    custom_device = {
        "device_model": "SOPI987-SCRAPER",
        "system_version": "Android 13",
        "app_version": "6.5",
        "lang_code": "en",
        "system_lang_code": "en",
    }

    client = TelegramClient(
        StringSession(get_or_create_session()),
        api_id,
        api_hash,
        device_model=custom_device["device_model"],
        system_version=custom_device["system_version"],
        app_version=custom_device["app_version"],
        lang_code=custom_device["lang_code"],
        system_lang_code=custom_device["system_lang_code"],
    )

    with client:
        client.start()

        # 🔍 Récupérer TOUS les dialogs (pas seulement les récents)
        raw_dialogs = client.get_dialogs(limit=None)

        # 👥 Garder groupes + supergroups + chaînes (pas les MP)
        dialogs = [
            d for d in raw_dialogs
            if getattr(d, "is_group", False) or getattr(d, "is_channel", False)
        ]

        # ——— Choix / reconstruction des groupes ———
        if resume_mode and prev:
            prev_ids = prev.get("group_ids", [])
            id_to_dialog = {}
            for d in dialogs:
                try:
                    gid = d.entity.id
                except Exception:
                    gid = getattr(d, "id", None)
                id_to_dialog[gid] = d

            groups_to_process = []
            for gid in prev_ids:
                if gid in id_to_dialog:
                    groups_to_process.append(id_to_dialog[gid])

            if not groups_to_process:
                # fallback si les IDs ne correspondent plus
                groups_to_process = dialogs

        else:
            # 1 = tous les groupes
            # 2 = choisir 1 ou plusieurs groupes (ex: 1 ou 1,3,5)

            if LANG == "es":
                print(f"\n{Fore.YELLOW}🎯 Selecciona el grupo a analizar:{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} Todos los grupos")
                print(f" {Fore.GREEN}2:{Fore.RESET} Elegir uno o varios grupos (ej: 1 o 1,3,5)")
                group_choice = input(f"{Fore.YELLOW}Tu elección: {Fore.RESET}").strip()

            elif LANG == "it":
                print(f"\n{Fore.YELLOW}🎯 Seleziona il gruppo da analizzare:{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} Tutti i gruppi")
                print(f" {Fore.GREEN}2:{Fore.RESET} Scegli uno o più gruppi (es: 1 o 1,3,5)")
                group_choice = input(f"{Fore.YELLOW}La tua scelta: {Fore.RESET}").strip()

            else:
                print(f"\n{Fore.YELLOW}🎯 Select group to analyze:{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} All groups")
                print(f" {Fore.GREEN}2:{Fore.RESET} Choose one or multiple groups (ex: 1 or 1,3,5)")
                group_choice = input(f"{Fore.YELLOW}Your choice: {Fore.RESET}").strip()

            groups_to_process = []

            if group_choice == "2":
                # ✅ Affichage indexé à partir de 1 (pour pouvoir taper 1,3,5)
                for i, d in enumerate(dialogs, 1):
                    print(f"{Fore.GREEN}[{i}]{Fore.RESET} {Fore.CYAN}{d.name}{Fore.RESET}")

                try:
                    if LANG == "es":
                        raw = input(f"{Fore.YELLOW}Introduce número(s) (ej: 1 o 1,3,5): {Fore.RESET}").strip()
                    elif LANG == "it":
                        raw = input(f"{Fore.YELLOW}Inserisci numero(i) (es: 1 o 1,3,5): {Fore.RESET}").strip()
                    else:
                        raw = input(f"{Fore.YELLOW}Enter number(s) (ex: 1 or 1,3,5): {Fore.RESET}").strip()

                    # Tolère "1,3,5" et aussi "1 3 5" ou "1;3;5"
                    raw = raw.replace(";", ",").replace(" ", ",")
                    parts = [p.strip() for p in raw.split(",") if p.strip()]
                    idxs = sorted(set(int(p) for p in parts))

                    if not idxs:
                        raise ValueError("empty")
                    if any(i < 1 or i > len(dialogs) for i in idxs):
                        raise ValueError("out of range")

                    groups_to_process = [dialogs[i - 1] for i in idxs]

                except Exception:
                    if LANG == "es":
                        print(f"{Fore.RED}❌ Error de selección.{Fore.RESET}")
                    elif LANG == "it":
                        print(f"{Fore.RED}❌ Errore di selezione.{Fore.RESET}")
                    else:
                        print(f"{Fore.RED}❌ Selection error.{Fore.RESET}")
                    sys.exit(1)

            else:
                # ✅ Tous les groupes (choix 1 ou défaut)
                groups_to_process = dialogs

        total_groups = len(groups_to_process)
        if total_groups == 0:
            if LANG == "es":
                print(f"{Fore.RED}❌ Ningún grupo para analizar.{Fore.RESET}")
            elif LANG == "it":
                print(f"{Fore.RED}❌ Nessun gruppo da analizzare.{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ No group to analyze.{Fore.RESET}")
            return

        # ====== REPRISE : start_index ======
        if resume_mode and prev:
            start_index = prev.get("next_index", 0)
            if not isinstance(start_index, int) or start_index < 0 or start_index >= total_groups:
                start_index = 0
        else:
            start_index = 0

        # compteur pour affichage "Groups x / y"
        group_num = start_index

        # ——— Analyse .txt optionnelle ———
        if resume_mode and prev and "config" in prev:
            cfg = prev.get("config", {})
            analyze_txt_files = cfg.get("analyze_txt_files", True)
            max_txt_size = cfg.get("max_txt_size", 1 * 1024 * 1024)
        else:
            if LANG == "es":
                print(f"{Fore.YELLOW}\n¿Quieres analizar también archivos .txt?{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} sí")
                print(f" {Fore.RED}2:{Fore.RESET} no")
                txt_choice = input(f"{Fore.YELLOW}Tu elección (1/2): {Fore.RESET}").strip()
            elif LANG == "it":
                print(f"{Fore.YELLOW}\nVuoi analizzare anche i file .txt?{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} sì")
                print(f" {Fore.RED}2:{Fore.RESET} no")
                txt_choice = input(f"{Fore.YELLOW}La tua scelta (1/2): {Fore.RESET}").strip()
            else:
                print(f"{Fore.YELLOW}\nDo you want to analyze .txt files too?{Fore.RESET}")
                print(f" {Fore.GREEN}1:{Fore.RESET} yes")
                print(f" {Fore.RED}2:{Fore.RESET} no")
                txt_choice = input(f"{Fore.YELLOW}Your choice (1/2): {Fore.RESET}").strip()

            analyze_txt_files = txt_choice != "2"

            if analyze_txt_files:
                if LANG == "es":
                    print(f"\n{Fore.YELLOW}📦 Tamaño máximo de archivo .txt a analizar:{Fore.RESET}")
                    print(f" {Fore.GREEN}1:{Fore.RESET} 1 MB")
                    print(f" {Fore.GREEN}2:{Fore.RESET} 2 MB")
                    print(f" {Fore.GREEN}3:{Fore.RESET} 3 MB")
                    print(f" {Fore.GREEN}4:{Fore.RESET} {Fore.LIGHTGREEN_EX}Sin límite{Fore.RESET}")
                    size_choice = input(f"{Fore.YELLOW}Tu elección: {Fore.RESET}").strip()
                elif LANG == "it":
                    print(f"\n{Fore.YELLOW}📦 Dimensione massima del file .txt da analizzare:{Fore.RESET}")
                    print(f" {Fore.GREEN}1:{Fore.RESET} 1 MB")
                    print(f" {Fore.GREEN}2:{Fore.RESET} 2 MB")
                    print(f" {Fore.GREEN}3:{Fore.RESET} 3 MB")
                    print(f" {Fore.GREEN}4:{Fore.RESET} {Fore.LIGHTGREEN_EX}Nessun limite{Fore.RESET}")
                    size_choice = input(f"{Fore.YELLOW}La tua scelta: {Fore.RESET}").strip()
                else:
                    print(f"\n{Fore.YELLOW}📦 Maximum .txt file size to analyze:{Fore.RESET}")
                    print(f" {Fore.GREEN}1:{Fore.RESET} 1 MB")
                    print(f" {Fore.GREEN}2:{Fore.RESET} 2 MB")
                    print(f" {Fore.GREEN}3:{Fore.RESET} 3 MB")
                    print(f" {Fore.GREEN}4:{Fore.RESET} {Fore.LIGHTGREEN_EX}No limit{Fore.RESET}")
                    size_choice = input(f"{Fore.YELLOW}Your choice: {Fore.RESET}").strip()

                size_dict = {
                    "1": 1 * 1024 * 1024,
                    "2": 2 * 1024 * 1024,
                    "3": 3 * 1024 * 1024,
                    "4": 100 * 1024 * 1024
                }
                max_txt_size = size_dict.get(size_choice, 1 * 1024 * 1024)
            else:
                max_txt_size = 0

        # Config à sauvegarder dans le JSON pour les futurs "RESUME"
        config = {
            "days_back_choice": days_back_choice,
            "mode": mode,
            "base_choice": base_choice,
            "analyze_txt_files": analyze_txt_files,
            "max_txt_size": max_txt_size,
            "detect_macs": detect_macs,
        }

        # ——— Boucle des groupes avec reprise ———
        for i in range(start_index, total_groups):
            group_num += 1  # pour l'affichage

            # Liste des IDs des groupes pour la progression
            ids = []
            for d in groups_to_process:
                try:
                    ids.append(d.entity.id)
                except Exception:
                    ids.append(getattr(d, "id", None))

            dialog = groups_to_process[i]
            entity = dialog.entity

            # Identifiant de ce groupe pour la reprise fine
            try:
                group_key = str(entity.id)
            except Exception:
                group_key = str(getattr(entity, "id", ""))

            # Date de reprise éventuelle pour CE groupe (timestamp → datetime)
            resume_after_date = None
            if resume_mode and last_dates_map:
                ts = last_dates_map.get(group_key)
                if isinstance(ts, (int, float)):
                    try:
                        resume_after_date = datetime.datetime.fromtimestamp(ts, tz=timezone.utc)
                    except Exception:
                        resume_after_date = None

            # Sauvegarde progression AVANT d'attaquer ce groupe
            save_progress({
                "filename": filename,
                "group_ids": ids,
                "next_index": i,          # ⇦ on reste sur CE groupe tant qu'il n'est pas fini
                "config": config,
                "last_dates": last_dates_map,
            })

            # Clear écran
            if sys.platform.startswith('win'):
                os.system("cls")
            else:
                sys.stdout.write("\033[H\033[2J")
                sys.stdout.flush()

            total = 0
            found_links_http = []
            found_links_m3u = []
            txt_messages = []
            last_url = [""]
            last_url_m3u = [""]
            last_combo = [""]
            last_portal = [""]
            last_mac = [""]
            last_date = [None]
            skip_group = [False]

            # Listener pour passer le groupe (touche '5')
            def check_skip():
                try:
                    import msvcrt
                    while True:
                        if msvcrt.kbhit():
                            key = msvcrt.getch().decode(errors="ignore")
                            if key == '5':
                                skip_group[0] = True
                                if LANG == "es":
                                    print("\n⏭️  Grupo saltado por el usuario!")
                                elif LANG == "it":
                                    print("\n⏭️  Gruppo saltato dall'utente!")
                                else:
                                    print("\n⏭️  Group skipped by user!")
                                break
                except Exception:
                    import select, termios, tty
                    fd = sys.stdin.fileno()
                    old_settings = termios.tcgetattr(fd)
                    try:
                        tty.setcbreak(fd)
                        while True:
                            r, _, _ = select.select([sys.stdin], [], [], 0.1)
                            if r:
                                key = sys.stdin.read(1)
                                if key == '5':
                                    skip_group[0] = True
                                    if LANG == "es":
                                        print("\n⏭️  Grupo saltado por el usuario!")
                                    elif LANG == "it":
                                        print("\n⏭️  Gruppo saltato dall'utente!")
                                    else:
                                        print("\n⏭️  Group skipped by user!")
                                    break
                    finally:
                        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

            skip_thread = threading.Thread(target=check_skip, daemon=True)
            skip_thread.start()

            next_group_name = groups_to_process[i + 1].name if i + 1 < len(groups_to_process) else "None"

            # ===== Affichage live (panel atomique + MAC / Portals) =====
            def live_status(new_url, new_m3u, new_combo, msg_date=None,
                            new_portal=None, new_mac=None):
                width = 43

                # Horodatage
                if msg_date is None:
                    msg_date = datetime.datetime.now()
                if msg_date.tzinfo is None:
                    msg_date = msg_date.replace(tzinfo=timezone.utc)
                now_str = msg_date.strftime("%Y/%m/%d %H:%M:%S")

                # Mise à jour des dernières valeurs
                if new_url:
                    last_url[0] = new_url
                if new_m3u:
                    last_url_m3u[0] = new_m3u
                if new_combo:
                    last_combo[0] = new_combo
                if new_portal:
                    last_portal[0] = new_portal
                if new_mac:
                    last_mac[0] = new_mac
                last_date[0] = msg_date

                # Compteurs globaux
                global_http  = global_counts["http"]
                global_m3u   = global_counts["m3u"]
                global_combo = global_counts["combo"]
                global_mac   = len(found_mac)
                global_port  = len(found_http_mac)

                # Animation aura
                try:
                    aura_color = next(AURA_CYCLE)
                except NameError:
                    aura_color = Fore.YELLOW

                try:
                    fx = next(ELECTRIC_CYCLE)
                except NameError:
                    fx = "⚡"

                inner_width = width - 4  # '║' + espace + contenu

                # === Titre centré proprement (calcul sans codes ANSI) ===
                plain_title = f"{fx} SUPER SCRAPER SOPI987 {fx}"
                if len(plain_title) > inner_width:
                    plain_title = plain_title[:inner_width]

                pad_left  = max(0, (inner_width - len(plain_title)) // 2)
                pad_right = max(0, inner_width - len(plain_title) - pad_left)
                visible_title = " " * pad_left + plain_title + " " * pad_right

                title_line = (
                    f"{Fore.MAGENTA}║{Fore.RESET} "
                    f"{aura_color}{visible_title}{Fore.RESET}"
                )

                def line_content(text: str) -> str:
                    """Barre gauche, contenu, pas de barre droite."""
                    visible = text.ljust(inner_width)
                    return f"{Fore.MAGENTA}║{Fore.RESET} {visible}"

                # ── Lignes dynamiques HTTP / M3U / COMBO (+ Portals / MAC si activés) ──
                if last_url[0]:
                    inner = width - 4 - len("🌐 HTTP: ")
                    http_line = line_content(f"🌐 HTTP: {last_url[0][:inner]}")
                else:
                    http_line = line_content("")

                if last_url_m3u[0]:
                    inner = width - 4 - len("📼 M3U: ")
                    m3u_line = line_content(f"📼 M3U: {last_url_m3u[0][:inner]}")
                else:
                    m3u_line = line_content("")

                if last_combo[0]:
                    inner = width - 4 - len("🔑 COMBO: ")
                    combo_line = line_content(f"🔑 COMBO: {last_combo[0][:inner]}")
                else:
                    combo_line = line_content("")

                # PORTALS (si MAC actif)
                if DETECT_MACS and last_portal[0]:
                    inner = width - 4 - len("🛰️ Portals: ")
                    portal_line = line_content(f"🛰️ Portals: {last_portal[0][:inner]}")
                elif DETECT_MACS:
                    portal_line = line_content("🛰️ Portals: ")
                else:
                    portal_line = None

                # MAC (si MAC actif)
                if DETECT_MACS and last_mac[0]:
                    inner = width - 4 - len("🖥️ MAC: ")
                    mac_line = line_content(f"🖥️ MAC: {last_mac[0][:inner]}")
                elif DETECT_MACS:
                    mac_line = line_content("🖥️ MAC: ")
                else:
                    mac_line = None

                # Lignes dynamiques conditionnelles (milieu)
                dyn = [http_line, m3u_line, combo_line]
                if DETECT_MACS:
                    dyn.append(portal_line)
                    dyn.append(mac_line)

                # ── Construction du frame (panel principal) ──
                frame_lines = [
                    f"{Fore.MAGENTA}╔{'═'*(width-2)}╗{Fore.RESET}",
                    title_line,
                    f"{Fore.MAGENTA}╠{'═'*(width-2)}╣{Fore.RESET}",
                    line_content(f"▶ {Fore.CYAN}Group:{Fore.RESET} {entity.title}"),
                    line_content(f"📍 {Fore.CYAN}Groups:{Fore.RESET} {group_num}/{total_groups}"),
                    line_content(f"📊 {Fore.CYAN}Messages:{Fore.RESET} {total}"),
                    line_content(f"📅 {now_str}"),
                    f"{Fore.MAGENTA}╠{'─'*(width-2)}╣{Fore.RESET}",
                ]

                # Ajoute les lignes dynamiques (HTTP/M3U/COMBO [+ Portals/MAC])
                frame_lines.extend([l for l in dyn if l])

                # ── Bloc du bas : stats globales ──
                frame_lines.append(f"{Fore.MAGENTA}╠{'─'*(width-2)}╣{Fore.RESET}")

                stats_lines = [
                    line_content(
                        f"🔍 {Fore.CYAN}HTTP:{Fore.RESET} {len(found_links_http):<4} │ "
                        f"M3U: {len(found_links_m3u):<4}"
                    ),
                    line_content(
                        f"🌐 Total HTTP: {Fore.LIGHTYELLOW_EX}{global_http}{Fore.RESET}"
                    ),
                    line_content(
                        f"📼 Total M3U: {Fore.LIGHTYELLOW_EX}{global_m3u}{Fore.RESET}"
                    ),
                    line_content(
                        f"🔑 COMBOS: {Fore.LIGHTYELLOW_EX}{global_combo}{Fore.RESET}"
                    ),
                ]

                if DETECT_MACS:
                    stats_lines.append(
                        line_content(
                            f"🛰️ Portals: {Fore.LIGHTYELLOW_EX}{global_port}{Fore.RESET}"
                        )
                    )
                    stats_lines.append(
                        line_content(
                            f"🖥️ MAC: {Fore.LIGHTYELLOW_EX}{global_mac}{Fore.RESET}"
                        )
                    )

                stats_lines.append(
                    line_content(
                        f"{Fore.RED}[5]{Fore.RESET} Skip: {next_group_name}"
                    )
                )

                frame_lines.extend(stats_lines)

                # ── Ligne de barre de progression TXT (si définie) ──
                prog = globals().get("CURRENT_TXT_PROGRESS", "")
                if prog:
                    frame_lines.append(line_content(prog))

                # Bas du cadre
                frame_lines.append(f"{Fore.MAGENTA}╚{'═'*(width-2)}╝{Fore.RESET}")

                # ── Cascade TXT sous le panel, avec TTL 10 s ──
                body = "\n".join(frame_lines)

                now_ts = time.time()
                if 'TXT_EVENTS' in globals():
                    valid_events = []
                    for ev in list(TXT_EVENTS):
                        ts = ev.get("ts", 0)
                        if now_ts - ts <= TXT_EVENT_TTL:
                            valid_events.append(ev)
                    TXT_EVENTS.clear()
                    TXT_EVENTS.extend(valid_events)

                    if TXT_EVENTS:
                        body += "\n"
                        for ev in TXT_EVENTS:
                            ts_str = time.strftime("%H:%M:%S", time.localtime(ev["ts"]))
                            line = (
                                f"{Fore.MAGENTA}📂 TXT{Fore.RESET} "
                                f"{Fore.YELLOW}{ev['label']}{Fore.RESET}   "
                                f"{Fore.BLACK}{Style.DIM}{ts_str}{Style.RESET_ALL}"
                            )
                            body += "\n" + line

                # Rendu atomique
                frame = "\033[H\033[J" + body + "\n\x1b[0m"
                with _display_lock:
                    sys.stdout.write(frame)
                    sys.stdout.flush()

            # primo rendering
            live_status("", "", "")

            # Generatore di messaggi CON ripresa per data se disponibile
            if resume_mode and resume_after_date is not None:
                msg_iter = client.iter_messages(entity, offset_date=resume_after_date)
            else:
                msg_iter = client.iter_messages(entity)

            # Scansione dei messaggi
            msg_count = 0
            for message in msg_iter:
                if skip_group[0]:
                    break
                if message.date and message.date < date_limit:
                    break

                total += 1

                # Aggiornamento della data grezza del messaggio
                msg_dt = message.date
                if msg_dt is not None and msg_dt.tzinfo is None:
                    msg_dt = msg_dt.replace(tzinfo=timezone.utc)
                last_date[0] = msg_dt

                if message.document and message.document.mime_type == 'text/plain':
                    if analyze_txt_files:
                        if hasattr(message.document, 'size') and message.document.size > max_txt_size:
                            file_name = getattr(message.document, 'file_name', f"document_{message.id}.txt")
                            if LANG == "es":
                                print(f"\n⛔ Archivo .txt demasiado grande (>{max_txt_size//1024//1024} MB) ignorado: {file_name}")
                            elif LANG == "it":
                                print(f"\n⛔ File .txt troppo grande (>{max_txt_size//1024//1024} MB) ignorato: {file_name}")
                            else:
                                print(f"\n⛔ .txt file too large (>{max_txt_size//1024//1024} MB) ignored: {file_name}")
                            continue
                        txt_messages.append(message)
                    else:
                        continue
                else:
                    try:
                        analyze_message(
                            message,
                            client,
                            found_links_http,
                            found_links_m3u,
                            live_status,
                            keep_pred=keep_pred
                        )
                    except InactivityTimeout:
                        # Message figé: on saute et on continue
                        if LANG == "es":
                            print(f"{Fore.YELLOW}⏭️ Mensaje bloqueado (> {INACTIVITY_TIMEOUT_SEC}s sin progreso). Saltando...{Fore.RESET}")
                        elif LANG == "it":
                            print(f"{Fore.YELLOW}⏭️ Messaggio bloccato (> {INACTIVITY_TIMEOUT_SEC}s senza progressi). Skip...{Fore.RESET}")
                        else:
                            print(f"{Fore.YELLOW}⏭️ Message stuck (> {INACTIVITY_TIMEOUT_SEC}s no progress). Skipping...{Fore.RESET}")

                msg_count += 1

                # Aggiornamento del pannello e salvataggio periodico della progressione
                if msg_count % 10 == 0:
                    live_status(
                        last_url[0],
                        last_url_m3u[0],
                        last_combo[0],
                        msg_dt if msg_dt is not None else datetime.datetime.now(timezone.utc)
                    )

                if msg_count % 20 == 0 and last_date[0] is not None:
                    # Salvataggio della data più recente per questo gruppo
                    try:
                        dt_utc = last_date[0]
                        if dt_utc.tzinfo is None:
                            dt_utc = dt_utc.replace(tzinfo=timezone.utc)
                        last_dates_map[group_key] = float(dt_utc.timestamp())
                    except Exception:
                        pass

                    save_progress({
                        "filename": filename,
                        "group_ids": ids,
                        "next_index": i,        # rimane su questo gruppo finché non è completato
                        "config": config,
                        "last_dates": last_dates_map,
                    })

            # Analisi dei file .txt accumulati (progression *interne* al file)
            if not skip_group[0] and txt_messages:
                total_txt = len(txt_messages)

                for idx, message in enumerate(txt_messages, 1):
                    # Infos sur le fichier en cours (2/10, 3/10, …)
                    globals()["CURRENT_TXT_FILE_INDEX"] = idx
                    globals()["CURRENT_TXT_FILE_TOTAL"] = total_txt

                    # Texte initial 0% (analyze_txt va mettre à jour pendant la lecture)
                    globals()["CURRENT_TXT_PROGRESS"] = (
                        f"📄 TXT {idx}/{total_txt} 0% [····················]"
                    )

                    # Petit refresh du panel
                    live_status(
                        last_url[0],
                        last_url_m3u[0],
                        last_combo[0],
                        last_date[0] or datetime.datetime.now(timezone.utc)
                    )

                    # Analyse du fichier TXT (c'est ici que la barre % se met à jour)
                    try:
                        analyze_txt(
                            message,
                            client,
                            found_links_http,
                            found_links_m3u,
                            live_status,
                            keep_pred=keep_pred
                        )
                    except InactivityTimeout:
                        if LANG == "es":
                            print(f"{Fore.YELLOW}⏭️ TXT bloqueado (> {INACTIVITY_TIMEOUT_SEC}s sin progreso). Saltando...{Fore.RESET}")
                        elif LANG == "it":
                            print(f"{Fore.YELLOW}⏭️ TXT bloccato (> {INACTIVITY_TIMEOUT_SEC}s senza progressi). Skip...{Fore.RESET}")
                        else:
                            print(f"{Fore.YELLOW}⏭️ TXT stuck (> {INACTIVITY_TIMEOUT_SEC}s no progress). Skipping...{Fore.RESET}")

                # Tous les TXT terminés → on nettoie les variables globales
                globals()["CURRENT_TXT_PROGRESS"] = ""
                globals().pop("CURRENT_TXT_FILE_INDEX", None)
                globals().pop("CURRENT_TXT_FILE_TOTAL", None)
            # Salvataggio finale della data per questo gruppo (fine gruppo)
            if last_date[0] is not None:
                try:
                    dt_utc = last_date[0]
                    if dt_utc.tzinfo is None:
                        dt_utc = dt_utc.replace(tzinfo=timezone.utc)
                    last_dates_map[group_key] = float(dt_utc.timestamp())
                except Exception:
                    pass

            # Visualizzazione finale del gruppo
            live_status(last_url[0], last_url_m3u[0], last_combo[0], last_date[0])
            if not skip_group[0]:
                if LANG == "es":
                    print(f"\n{Fore.GREEN}✅ Grupo completado:{Fore.RESET} {Fore.CYAN}{entity.title}{Fore.RESET}")
                    print(
                        f"{Fore.CYAN}🔎 Enlaces HTTP en este grupo:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_http)}{Fore.RESET} "
                        f"| {Fore.MAGENTA}Enlaces M3U:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_m3u)}{Fore.RESET}\n"
                    )
                elif LANG == "it":
                    print(f"\n{Fore.GREEN}✅ Gruppo completato:{Fore.RESET} {Fore.CYAN}{entity.title}{Fore.RESET}")
                    print(
                        f"{Fore.CYAN}🔎 Link HTTP in questo gruppo:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_http)}{Fore.RESET} "
                        f"| {Fore.MAGENTA}Link M3U:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_m3u)}{Fore.RESET}\n"
                    )
                else:
                    print(f"\n{Fore.GREEN}✅ Group completed:{Fore.RESET} {Fore.CYAN}{entity.title}{Fore.RESET}")
                    print(
                        f"{Fore.CYAN}🔎 HTTP links in this group:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_http)}{Fore.RESET} "
                        f"| {Fore.MAGENTA}M3U links:{Fore.RESET} "
                        f"{Fore.LIGHTYELLOW_EX}{len(found_links_m3u)}{Fore.RESET}\n"
                    )

            # Ora che il gruppo è terminato, si avanza l’indice
            save_progress({
                "filename": filename,
                "group_ids": ids,
                "next_index": i + 1,     # ⇦ prossimo gruppo al riavvio
                "config": config,
                "last_dates": last_dates_map,
            })

            time.sleep(2)

        # Fine analisi: nulla da riprendere
        clear_progress()

        # 🧹 Nettoyage final des fichiers .txt résiduels dans RESIDUAL_DIR
        clean_residual_files()


# ---------- Helpers pour mirrors / m3u ----------
def clear_screen():
    sys.stdout.write("\033[H\033[2J")
    sys.stdout.flush()

def country_flag_emoji(code):
    if not code or len(code) != 2: return ""
    return chr(0x1F1E6 + ord(code.upper()[0]) - ord('A')) + chr(0x1F1E6 + ord(code.upper()[1]) - ord('A'))

def resolve_ip(domain):
    try:
        r = requests.get(f"http://ip-api.com/json/{domain}", timeout=5)
        if r.status_code == 200:
            data = r.json()
            ip = data.get("query", "❓")
            if ":" in ip:
                import socket
                ip = socket.gethostbyname(domain)
            country = data.get("country", "❓")
            code = data.get("countryCode", "")
            city = data.get("city", "❓")
            flag = country_flag_emoji(code)
            return ip, city, country, flag
    except Exception:
        pass
    return "❓", "❓", "❓", ""

def extract_credentials(m3u_url):
    m = re.search(r"(?:username|user)=([^&]+)&(?:password|pass)=([^&]+)", m3u_url)
    if m:
        return m.group(1), m.group(2)
    # fallback parse_qs
    try:
        qs = parse_qs(urlparse(m3u_url).query)
        u = qs.get("username", qs.get("user", [None]))[0]
        p = qs.get("password", qs.get("pass", [None]))[0]
        return u, p
    except Exception:
        return None, None

# ======= Country categorization (keywords + helpers) =======

CATEGORY_KEYWORDS = {
    # 🇫🇷 FRANCE
    "FR": [
        "fr", "france", "francais", "français", "french",
        "france fhd", "france hd", "france sd",
        "fr ligue1", "fr ligue 1", "fr ligue1 vip", "fr ligue 1 vip",
        "fr dazn ppv", "fr canal plus live", "fr canal+ live",
        "l equipe live", "lequipe live",
        "fr cinema", "fr documentaire", "fr kids", "fr musique", "fr infos",
        "generale", "general", "sport", "ligue1", "dazn",
        "canal plus", "canal+", "films et series", "jeunesse",
        "divertissement", "information", "nature", "musique",
        "france 2", "france 3", "tf1", "m6", "c8", "w9", "arte"
    ],
    # 🇪🇸 ESPAGNE
    "ES": [
        "es", "espana", "españa", "spanish", "español", "AUTONOMICOS",
        "general", "laliga", "la liga", "hypermotion", "TDT", "LA LIGA TV",
        "uefa liga de campeones", "champions league", "M+", "ORANGE OGO", "EU- ES",
        "deportes", "dazn acb", "entretenimiento", "MOVISTAR+", "SVIP",
        "cine y series", "ninos", "niños", "cultura", "musica", "LIGA ACB",
        "max amazon", "toros", "regional", "dazn laliga", "M+ Cine", "CASTELLANO",
        "top canales vip", "laliga vip", "deportes vip", "M+ Toros",
        "dazn acb vip", "cine y series vip", "infantiles vip",
        "news vip", "estilo de vida vip", "dazn eventos",
        "antena 3", "telecinco", "cuatro", "la sexta", "generalistas"
    ],
    # 🇵🇹/🇧🇷 PORTUGAL + BRÉSIL
    "PT_BR": [
        "pt", "br", "portugal", "brasil", "portugues", "português", "desporto",
        "a fazenda", "hora do jogo", "globo", "record", "band", "sbt", "ÁREA DO CLIENTE",
        "globo sudeste", "globo sul", "globo centro oeste", "desenhos", "FILMES",
        "globo nordeste", "globo norte", "globo", "esportes", "legendados", "PORTUGAL",
        "noticias", "premiere", "espn", "abertos", "crianças", "JOGOS", "ESPORTES",
        "paramount", "telecine", "hbo", "filmes e series", "eventos do dia",
        "documentarios", "novelas", "canais", "atualizações"
    ],
    # 🌎 LATINO
    "LATINO": [
        "lat", "latino", "latin", "mexico", "argentina", "chile", "peru", "⚽deporte", "EVENTOS PPV DEL DIA",
        "colombia", "ecuador", "venezuela", "bolivia", "paraguay", "uruguay", "FUTBÓL", "LA GRANJA",
        "costa rica", "guatemala", "honduras", "el salvador", "canales", "ecuad⚽r", "TV ECUADOR",
        "nicaragua", "panama", "puerto rico", "republica dominicana", "premium", "LIBERTADORES",
        "haiti", "cuba", "caribe", "canales nacionales", "cable premium", "telenovelas", "EVENTOS DISNEY+",
        "eventos futbol", "eventos del dia", "pay per view","solo eventos", "vix", "ZONA REALITY",
        "premier league", "la serie a", "la bundesliga", "Noticias", "Deportes", "Ufc-Boxeo-LuchaLibre",
        "eventos y deportes", "deportes latinos", "infantiles", "deportes", "estrenos", "EVENTO",
        "fox sports", "espn", "tnt sports", "directv", "eventos", "ppv", "deportes ppv" ,"EVENTOS LALIGA DEL DIA"
    ],
    # 🇺🇸/🇬🇧/🇨🇦 ANGLAIS
    "EN": [
        "en", "uk", "us", "gb", "english", "ingles", "anglais", "usa cable", "cbs",
        "canada", "canada french", "usa", "united states", "united kingdom", "state",
        "usa news", "usa regionals", "movie networks", "events", "nbc", "sports", "usa", 
        "kids zone", "ppv ufc", "sports fanatic", "f1 formula", "fights", "cartoons",
        "24 7 channels", "mlb", "nba", "nhl", "nfl", "racing", "channels",
        "usa entertainment", "usa sports networks", "low bandwidth channels",
        "bbc", "itv", "sky sports", "hbo", "netflix", "disney"
    ],
    # 🇩🇪 ALLEMAGNE
    "DE": [
        "de", "germany", "deutschland", "alemania", "allemand",
        "germany vip", "sport", "sky sport", "magenta sport",
        "dazn sport", "dyn sport", "news doku music",
        "sky cinema", "sinema kino", "24 7 schauspieler",
        "24 7 series", "24 7 kinder", "kinder", "pluto tv",
        "amazon tv", "24 7 germany", "ard", "zdf", "rtl", "sat1"
    ],
    # 🇹🇷 TURQUIE
    "TR": [
        "tr", "turkiye", "turkey", "turquie", "turco", "önemli",
        "maxtv", "bein spor", "smart spor", "tivibu spor",
        "s sport", "exxen spor", "tabii spor", "turkcell tv", "türk",
        "cocuk kanallari", "cocuk", "muzik kanallari", "TR", 
        "ulusal", "haber", "belgesel", "spor", "merkezi",
        "bein sport", "bein sport vip", "dini islam", "ULUSAL",
        "trt", "atv", "show tv", "star tv", "ulusal", "haber"
    ],
    # 🇮🇳 INDE / PAKISTAN
    "IN": [
        "in", "ind", "pk", "india", "indian", "pakistan",
        "indian 4k ultra hd", "indian entertainment", "indian movies",
        "bigg boss 24hrs live", "vip cricket live", "t20 world cup",
        "ind pak sports", "pakistan 4k", "pakistan entertainment",
        "pakistan news", "pak islamic tv", "ind news",
        "ind documentary", "ind kids", "ind music",
        "indian dd channels", "ind english movies", "uk india",
        "bollywood", "star plus", "colors", "sony", "zee tv"
    ],
    # 🇷🇴 ROUMANIE
    "RO": [
        "ro", "romania", "roumanie", "rumano", "romania", "generale", "religie",
        "romania pro hd", "romania pro cinema", "romania pro sd", "muzica", "Rezerva",
        "romania pro fibra", "romania pro", "pro tv", "antena 1", "romania",
        "romania tv", "kanal d", "realitatea tv", "documentare", "FILME", "STIRI",
    ],
    # 🇵🇱🇷🇸🇭🇺 PAYS DE L'EST
    "EAST": [
        "east", "exyu", "europa del este", "europe de l'est", "dobra", "montenegro", "Hercegovina",
        "a1 tv", "albania", "austria", "bosnia", "croatia", "kosovo", "crna", "Makedonija", "ALB",
        "serbia", "slovenia", "macedonia", "pink media", "alb", "hercegovina", "FILMOWE", "Edukativni",
        "poland", "polska", "hungary", "magyar", "romania", "slovenija", "PL", "OGÓLNOTEMATYCZNE", 
        "bulgaria", "czech", "slovakia", "ukraine", "russia", "dokumentarni", "Hrvatska",
        "россия", "польша", "чехия", "tvp", "rtl", "nova", "srbija", "hrvatska" ,"Bosna",
    ],
    # 🇮🇹 ITALIE
    "IT": [
        "it", "italia", "italiano", "italie", "italian", "tivusat", "GRANDE FRATELLO",
        "sky cinema", "eagle cinema", "sky intrattenimento", "sky cinema",
        "sky cultura", "sky prem disney", "sky sport", "sky calcio", "fratello",
        "dazn serie a", "dazn serie b", "intratenimento", "intrattenimento",
        "documentari", "calcio", "campionato serie a", "tv sat", "TVSAT",
        "campionato serie b", "arena tv", "eleven tv", "bambini",
        "rai", "mediaset", "canale 5", "rete 4", "italia 1"
    ],
    # 🇦🇪 ARAB / ARABIC
    "ARAB": [
        "arab", "mena", "gcc", "arabic", "arabe", "árabe", "arryadia", "ALWAN",
        "arab countries", "bein qatar", "osn qatar", "shahid", "ma", "Arab Countries",
        "algeria", "bahrain", "egypt", "libya", "syria", "starz", "AR",
        "lebanon", "palestine", "morocco", "jordan", "kuwait", "bein",
        "uae", "iraq", "tunisia", "saudi arabia", "bein sports", "Afghanistan",
        "arabic news", "kids tv arabic", "mbc", "rotana", "osn",
        "quran", "islam tv", "arabico", "qatar", "starzplay", "ARAB SPORT",
        "بين سبورت", "الاخبار", "الدوري السعودي", "ثمانية",
        "ام بي سي", "شاهد", "روتانا", "سوريا", "لبنان",
        "قنوات الاطفال", "اطفال", "او اس ان", "ديني", "اسلامي",
        "الاسلامية", "المجد", "وثائقي", "تعليمي",
        "مسلسلات سورية", "مسلسلات لبنانية", "مسلسلات مصرية",
        "مسلسلات تركية", "مسلسلات عربية", "كوميديا", "انمي",
        "نتفلكس", "افلام عربي", "افلام مدبلجة", "باور", "فيفو"
    ],
    # 🔞 XXX / Adult
    "XXX": [
        "xxx",
        "adult channels",
        "female live webcam shows", "VERIFIED AMATEURS",
        "male live webcam shows", "STARS EXCLUSIVE",
        "trans live webcam shows", "PORNBOX" ,"PORNHUB",
    ],
    # 🌍 WORLD (+ ajout NL)
    "WORLD": [
        "nl", "nli", "nederland", "nederlands", "algemeen", "muziek", "Australia",
        "kinder", "kinderen", "regionaal", "buitenland", "MALTESE", "Africa",
        "viaplay", "ziggo", "odido", "vermaak", "films", "sport",
    ],
}

_REGION_EMOJI = {
    "WORLD": "🌍",
    "XXX": "🔞",

    # Overrides explicites pour les "buckets" régionaux/linguistiques
    "EN": "🇺🇸",       # English → US flag par défaut
    "LATINO": "🇲🇽",   # Latino → Mexique comme tu le souhaites
    "PT_BR": "🇧🇷",    # PT/BR → Brésil par défaut

    # (facultatif) quelques codes déjà pays pour homogénéité
    "FR": "🇫🇷",
    "ES": "🇪🇸",
    "DE": "🇩🇪",
    "IT": "🇮🇹",
    "TR": "🇹🇷",
    "IN": "🇮🇳",
    "RO": "🇷🇴",
    "ARAB": "🇦🇪",     # MENA : Emirats comme drapeau “pivot”
    "EAST": "🇭🇷",      # Bloc Est hétérogène → globe Asie
}

# --- à placer près de tes constantes/utilitaires ---
import re
from collections import defaultdict

_REGION_TAG_MAP = {
    "AR": "ARAB",
    "TR": "TR",

    # Anglophones → bucket EN
    "UK": "EN", "US": "EN", "USA": "EN", "GB": "EN", "EN": "EN", "CA": "EN",

    # Europe de l'Ouest
    "FR": "FR", "ES": "ES", "DE": "DE", "IT": "IT",

    # Balkans / Est
    "RO": "RO",                # Roumanie a son bucket dédié chez toi
    "ALB": "EAST", "AL": "EAST",   # ✅ Albanie
    "PL": "EAST", "POL": "EAST",   # ✅ Pologne

    # Inde / Pakistan
    "IN": "IN", "PK": "IN",

    # Lusophones
    "PT": "PT_BR", "BR": "PT_BR",
}
_TAG_PATTERN = re.compile(r"^\s*\|?\s*([A-Z]{2,3})\s*\|")  # ex: "|AR| BEIN SPORTS 4K"

def _normalize_txt(s: str) -> str:
    import unicodedata, re
    s = unicodedata.normalize("NFKD", str(s))
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"[^a-z0-9+]+", " ", s.casefold()).strip()
    return s

def _detect_regions_from_categories(cat_names, top_k=8, min_hits=2) -> list:
    """
    1) Fast path par TAGs explicites dans les 4 premières catégories (|AR|, |TR|, |UK|…):
       - si une région a ≥ min_hits (=2) tags et est strictement > aux autres → on la choisit.
    2) Sinon fallback '4 mots max':
       - on agrège les mots-clés DISTINCTS par région sur les 4 premières catégories,
       - seuil min_hits (=2). Un seul mot ne suffit pas.
       - tie-break: (a) plus de hits dans les 2 premières catégories, (b) premiers hits les plus tôt.
       - si égalité persistante ou aucun ≥ min_hits → WORLD.
    Retourne UNE région (dans une liste), ex: ['ARAB'].
    """
    names = list(cat_names or [])
    if not names:
        return ["WORLD"]

    # ------ Top K cat names ------
    top_raw = [str(n) for n in names[:top_k] if n]
    top_norm = [_normalize_txt(n) for n in top_raw]
    if not top_norm:
        return ["WORLD"]

    # ------ 1) TAGS explicites |XX| ------
    tag_scores = defaultdict(int)
    for raw in top_raw:
        m = _TAG_PATTERN.match(raw)
        if m:
            tag = m.group(1).upper()
            region = _REGION_TAG_MAP.get(tag)
            if region:
                tag_scores[region] += 1

    if tag_scores:
        best_region, best_count = max(tag_scores.items(), key=lambda kv: kv[1])
        if best_count >= min_hits:
            # vérifier qu'il est unique au max
            if list(tag_scores.values()).count(best_count) == 1:
                return [best_region]

    # ------ 2) Fallback mots-clés (4 premières, seuil 2) ------
    kw_by_code = {
        code: {_normalize_txt(k) for k in (kws or []) if k}
        for code, kws in CATEGORY_KEYWORDS.items()
    }

    matched_kw = {code: {} for code in CATEGORY_KEYWORDS.keys()}  # kw -> first idx
    first2count = {code: 0 for code in CATEGORY_KEYWORDS.keys()}

    for idx, catn in enumerate(top_norm):
        for code, kwset in kw_by_code.items():
            if not kwset or not catn:
                continue
            for kw in kwset:
                if kw and kw in catn and kw not in matched_kw[code]:
                    matched_kw[code][kw] = idx
                    if idx < 2:
                        first2count[code] += 1

    scores = {code: len(matched_kw[code]) for code in matched_kw}
    max_score = max(scores.values() or [0])
    if max_score < min_hits:
        return ["WORLD"]

    candidates = [c for c, s in scores.items() if s == max_score]
    if len(candidates) == 1:
        return [candidates[0]]

    # tie-break (a): plus de hits dans les 2 premières catégories
    best_first2 = max(first2count[c] for c in candidates)
    cands = [c for c in candidates if first2count[c] == best_first2]
    if len(cands) == 1:
        return [cands[0]]

    # tie-break (b): premiers hits les plus tôt
    INF = 10**9
    def early_tuple(c):
        pos = sorted(matched_kw[c].values())[:min_hits]
        while len(pos) < min_hits:
            pos.append(INF)
        return tuple(pos)

    best = min(cands, key=early_tuple)

    # si tout reste strictement identique: WORLD (évite un choix arbitraire)
    if sum(early_tuple(x) != early_tuple(best) for x in cands) == 0:
        return ["WORLD"]

    return [best]
                
def _region_code_to_suffix(code: str) -> str:
    if code in _REGION_EMOJI:
        return _REGION_EMOJI[code]
    if len(code) == 2:
        return country_flag_emoji(code) or code
    return code
    
# --- Catégories miroir: helpers ---
def _norm_cat_set(iterable):
    """Normalise un ensemble de noms de catégories (trim + casse insensible)."""
    import re as _re
    s = set()
    for name in (iterable or []):
        n = _re.sub(r"\s+", " ", str(name)).strip().casefold()
        if n:
            s.add(n)
    return s

def _src_categories_set(status):
    """
    Construit l'ensemble de catégories de référence à partir du M3U source.
    - priorité: status.categories (API get_live_categories)
    - fallback: clés de status.channel_counts (group-title du M3U)
    """
    base = list(getattr(status, "categories", {}).keys())
    if not base and getattr(status, "channel_counts", None):
        base = list(status.channel_counts.keys())
    return _norm_cat_set(base)

def _same_categories_as_source(status, host, port):
    """
    Retourne True si le panel candidat expose EXACTEMENT les mêmes catégories
    que le M3U source. API d'abord, fallback group-title du M3U sinon.
    """
    src_set = _src_categories_set(status)
    if not src_set:
        # Si on n'a aucune référence, on ne bloque pas.
        return True

    scheme = "https" if int(port) == 443 else "http"
    base_line = (
        f"{scheme}://{_fmt_host(host)}:{port}/get.php?"
        f"username={status.username}&password={status.password}&type=m3u_plus"
    )

    # 1) via API get_live_categories
    cand_api = extract_categories(base_line)  # utilise player_api du même host/creds
    cand_set = _norm_cat_set(list(cand_api.keys()))

    # 2) fallback: group-title du M3U
    if not cand_set:
        m3u_dl = base_line + "&output=m3u8"
        groups = count_tv_channels_by_group(m3u_dl)
        cand_set = _norm_cat_set(list(groups.keys()))

    return cand_set == src_set
    
# -------- Validation stricte M3U (pour les MIRRORS) --------
def is_valid_m3u(url, timeout=8):
    """
    HTTP 200/206 + contenu M3U (#EXTM3U ou #EXTINF).
    Timeout connect/lecture séparé pour éviter les threads pendus.
    """
    try:
        s = get_stealth_session()  # ✅ session furtive globale
        r = s.get(
            url,
            timeout=(max(2, timeout // 2), timeout),  # (connect, read)
            verify=False,
            allow_redirects=True,
            stream=True,
        )
        ok = (r.status_code in (200, 206)) and ("#EXTM3U" in r.text or "#EXTINF" in r.text)
        r.close()
        return ok
    except Exception:
        return False


def xtream_auth_ok(base_url: str, user: str, pwd: str, timeout=8):
    """
    Vérifie l'auth sur /player_api.php avec les mêmes credentials.
    Retourne (True/False, raison)
    """
    try:
        s = get_stealth_session()  # ✅ session furtive globale
        url = f"{base_url}/player_api.php?username={user}&password={pwd}"
        r = s.get(
            url,
            timeout=(max(2, timeout // 2), timeout),
            verify=False,
            allow_redirects=True,
        )
        if r.status_code != 200:
            return False, f"HTTP {r.status_code}"
        try:
            data = r.json()
        except Exception:
            return False, "not-json"
        ui = data.get("user_info", {})
        auth = str(ui.get("auth", ui.get("status", ""))).lower()
        # Auth OK si '1' / 'true' / 'active'
        if auth in ("1", "true", "active"):
            return True, "auth-ok"
        return False, f"auth={auth}"
    except Exception as e:
        return False, type(e).__name__


def m3u_belongs_to_host(m3u_text: str, host: str, user: str, pwd: str) -> bool:
    """
    Valide que la M3U contient des liens live VRAIMENT pour ce host et ces creds.
    """
    if "#EXTM3U" not in m3u_text and "#EXTINF" not in m3u_text:
        return False
    # liens live xtream
    pat = re.compile(rf"https?://{re.escape(host)}(?::\d+)?/(live|movie|series)/{re.escape(user)}/{re.escape(pwd)}/", re.IGNORECASE)
    if pat.search(m3u_text):
        return True
    # à défaut, on autorise rarement des panels qui servent get.php → on vérifie le host
    host_pat = re.compile(rf"https?://{re.escape(host)}(?::\d+)?/", re.IGNORECASE)
    return bool(host_pat.search(m3u_text))


def strict_mirror_check(host: str, port: int, user: str, pwd: str, timeout=10):
    """
    Vérification stricte d'un mirror:
      1) /player_api.php avec mêmes creds → auth OK
      2) /get.php → M3U contient des URLs du même host ET tes creds
    Retourne (True/False, raison)
    """
    scheme = "https" if int(port) == 443 else "http"
    base = f"{scheme}://{_fmt_host(host)}:{port}"

    # 1) Auth Xtream (⚠️ assure-toi que xtream_auth_ok utilise aussi une session furtive)
    ok, why = xtream_auth_ok(base, user, pwd, timeout=timeout)
    if not ok:
        return False, f"player_api:{why}"

    # 2) get.php avec session furtive thread-local
    try:
        s = _get_thread_session(stealth=True)  # ✅ session réutilisée par CE thread
        m3u_url = f"{base}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8"
        r = s.get(
            m3u_url,
            timeout=(max(2, timeout // 2), timeout),  # (connect, read)
            verify=False,
            allow_redirects=True,
            stream=True,  # on peut lire un petit chunk d’abord
        )
        if r.status_code not in (200, 206):
            return False, f"get.php:{r.status_code}"

        # Lis un petit chunk d’abord pour un check rapide,
        # puis retombe sur le texte si besoin.
        try:
            chunk = r.raw.read(65536, decode_content=True) or b""
            text = chunk.decode(errors="ignore")
        except Exception:
            # fallback si le stream n'a pas donné assez
            text = r.text[:100000]

        if not m3u_belongs_to_host(text, host, user, pwd):
            return False, "m3u-not-matching-host/creds"
        return True, "ok"
    except requests.RequestException as e:
        return False, type(e).__name__
        
# -------- Détection ROBUSTE (pour le M3U SOURCE uniquement) -----
def normalize_url(u: str) -> str:
    u = (u or "").strip()
    if not u:
        return u
    if not u.startswith(("http://", "https://")):
        u = "http://" + u
    # ✅ Répare les IPv6 sans crochets (sinon urlparse/requests peuvent lever "Invalid IPv6 URL")
    return _fix_ipv6_url(u)
def looks_like_m3u(text: str) -> bool:
    if not text: return False
    t = text.strip()
    return t.startswith("#EXTM3U") or "#EXTINF:" in t

def looks_like_json(text: str) -> bool:
    if not text: return False
    try:
        import json
        obj = json.loads(text)
        return isinstance(obj, (dict, list))
    except Exception:
        return False

def endpoint_ok(code: int) -> bool:
    # 200-204 OK + 206 (partial), + redirections, + auth guard
    if 200 <= code <= 204: 
        return True
    if code in (206, 301, 302, 307, 308, 401, 403): 
        return True
    return False


def build_probe_urls(m3u_url: str):
    m3u_url = normalize_url(m3u_url)
    user, pwd = extract_credentials(m3u_url)
    p = urlparse(m3u_url)
    if (not p.hostname) or _is_ipv6_host(p.hostname):
        return []
    base = f"{p.scheme}://{_fmt_host(p.hostname)}" + (f":{p.port}" if p.port else "")
    urls = []
    if user and pwd:
        # Player API
        urls.extend([
            f"{base}/player_api.php?username={user}&password={pwd}",
            f"{base}/player_api.php?username={user}&password={pwd}&action=get_live_categories",
        ])
        # Variantes get.php (on élargit un peu)
        urls.extend([
            f"{base}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8",
            f"{base}/get.php?username={user}&password={pwd}&type=m3u_plus",
            f"{base}/get.php?username={user}&password={pwd}&type=m3u&output=m3u8",
            f"{base}/get.php?username={user}&password={pwd}&type=m3u",
            f"{base}/get.php?username={user}&password={pwd}&output=ts",
            f"{base}/get.php?username={user}&password={pwd}"
        ])
    else:
        urls.append(f"{base}/playlist.m3u")
    return urls


def probe_m3u_activity(m3u_url: str, timeout=8, max_tries=2):
    """
    True si JSON/M3U/guard/rédirection.
    443: on allonge un peu timeout et réessais.
    + Fallback HTTP si la sonde HTTPS complète échoue (no-response).
    + Push dans la cascade (ACTIVE/INACTIVE).
    """
    # urlparse: utilise la version globale sécurisée
    m3u_url = normalize_url(m3u_url)
    p = urlparse(m3u_url)
    if (not p.hostname) or _is_ipv6_host(p.hostname):
        # Ignorer les URLs IPv6 pour éviter "Invalid IPv6 URL"
        return False, "skip-ipv6"
    is_https443 = (p.scheme == "https") and ((p.port or 443) == 443)
    tmo = max(timeout, 12 if is_https443 else timeout)
    tries = max(max_tries, 3 if is_https443 else max_tries)

    # libellé court/masqué pour l’affichage cascade
    try:
        label = clean_m3u_display(m3u_url)  # si tu as déjà cette fonction
    except Exception:
        # fallback minimal : host:port seulement
        host = (p.hostname or "").lower()
        port = (p.port or (443 if p.scheme == "https" else 80))
        label = f"{host}:{port}"

    # 1) Essai direct (non-stealth)
    headers, cookies = get_stealth_headers(stealth=False)
    sess = requests.Session()
    sess.headers.update(headers); sess.cookies.update(cookies)

    code, text = probe_once(sess, m3u_url, timeout=tmo)
    if code is not None and endpoint_ok(code):
        if looks_like_json(text):
            push_m3u_event(True, f"{label}  • {code} direct-json")
            return True, f"{code} direct-json"
        if looks_like_m3u(text):
            push_m3u_event(True, f"{label}  • {code} direct-m3u")
            return True, f"{code} direct-m3u"
        if code in (301,302,307,308,401,403):
            push_m3u_event(True, f"{label}  • {code} direct-guard")
            return True, f"{code} direct-guard"

    # 2) Dérivés en stealth
    headers2, cookies2 = get_stealth_headers(stealth=True)
    sess.headers.update(headers2); sess.cookies.update(cookies2)

    reasons = []
    for u in build_probe_urls(m3u_url):
        for _ in range(tries):
            code, text = probe_once(sess, u, timeout=tmo)
            if code is None:
                continue
            if endpoint_ok(code):
                suf = u.split('/')[-1]
                if looks_like_json(text):
                    push_m3u_event(True, f"{label}  • {code} json@{suf}")
                    return True, f"{code} json@{suf}"
                if looks_like_m3u(text):
                    push_m3u_event(True, f"{label}  • {code} m3u@{suf}")
                    return True, f"{code} m3u@{suf}"
                if code in (301,302,307,308,401,403):
                    push_m3u_event(True, f"{label}  • {code} guard@{suf}")
                    return True, f"{code} guard@{suf}"
            reasons.append(f"{u.split('/')[-1]}:{code}")
            break

    # 3) Fallback HTTP si la cible originale était HTTPS:443 et qu'on a "no-response"
    if is_https443:
        try:
            http_variants = []
            for u in build_probe_urls(m3u_url):
                up = urlparse(u)
                http_variants.append(
                    f"http://{up.hostname}:80{up.path}?{up.query}" if up.query else
                    f"http://{up.hostname}:80{up.path}"
                )
            for u in http_variants:
                for _ in range(max(2, tries-1)):
                    code, text = probe_once(sess, u, timeout=timeout)
                    if code is None:
                        continue
                    if endpoint_ok(code):
                        if looks_like_json(text):
                            push_m3u_event(True, f"{label}  • {code} http-fallback-json")
                            return True, f"{code} http-fallback-json"
                        if looks_like_m3u(text):
                            push_m3u_event(True, f"{label}  • {code} http-fallback-m3u")
                            return True, f"{code} http-fallback-m3u"
                        if code in (301,302,307,308,401,403):
                            push_m3u_event(True, f"{label}  • {code} http-fallback-guard")
                            return True, f"{code} http-fallback-guard"
        except Exception:
            pass

    # INACTIF → on pousse une ligne rouge dans la cascade
    push_m3u_event(False, f"{label}  • {', '.join(reasons[-3:]) if reasons else 'no-response'}")
    return False, (", ".join(reasons[-3:]) if reasons else "no-response")    

def probe_once(session, url, timeout=8):
    try:
        # urlparse: utilise la version globale sécurisée
        p = urlparse(url)


        if (p.hostname) and _is_ipv6_host(p.hostname):
            return None, ""
        # HEAD d'abord si HTTPS 443
        if (p.scheme == "https") and ((p.port or 443) == 443):
            try:
                r = session.head(url, timeout=timeout, allow_redirects=True, verify=False)
                if r.status_code is not None and endpoint_ok(r.status_code):
                    # petit GET léger juste pour détecter #EXTM3U
                    rg = session.get(url, timeout=timeout, allow_redirects=True, verify=False, stream=True)
                    chunk = (rg.raw.read(8192, decode_content=True) or b"")
                    try:
                        chunk = chunk.decode(errors="ignore")
                    except Exception:
                        chunk = ""
                    return rg.status_code, chunk
            except requests.RequestException:
                pass

        # Fallback GET classique
        r = session.get(url, timeout=timeout, allow_redirects=True, verify=False)
        return r.status_code, r.text[:60000]

    except requests.RequestException:
        return None, None

        
def extract_categories(m3u_url, max_retries=3):
    parsed = urlparse(m3u_url)
    domain = parsed.scheme + "://" + parsed.netloc
    username, password = extract_credentials(m3u_url)
    if not username or not password:
        return OrderedDict()

    url = f"{domain}/player_api.php?username={username}&password={password}&action=get_live_categories"

    for _ in range(max_retries):
        try:
            # ✅ Session furtive thread-local
            s = _get_thread_session(stealth=True)
            r = s.get(url, timeout=5, verify=False, allow_redirects=True)

            if r.status_code == 200:
                data = r.json()
                ordered = OrderedDict()
                for item in data:
                    name = item.get("category_name", "").strip()
                    if name and name not in ordered:
                        ordered[name] = 0
                return ordered

        except Exception:
            # petit délai aléatoire pour rester furtif
            time.sleep(random.uniform(1.2, 2.4))

    return OrderedDict()
    
def count_tv_channels_by_group(m3u_url, max_retries=5):
    """
    Télécharge (le moins possible) un M3U et compte les groupes (group-title="...").
    Utilise une session furtive thread-local pour la vitesse (keep-alive) et la stabilité.
    """
    for _ in range(max_retries):
        try:
            s = _get_thread_session(stealth=True)  # ✅ session par thread
            # Stream pour lire peu de données si possible
            r = s.get(m3u_url, timeout=6, verify=False, allow_redirects=True, stream=True)

            # Lire un petit chunk d'abord pour valider rapidement
            try:
                chunk = r.raw.read(65536, decode_content=True) or b""
                head_txt = chunk.decode(errors="ignore")
            except Exception:
                head_txt = ""

            if r.status_code in (200, 206) and ("#EXTINF" in head_txt or "#EXTM3U" in head_txt):
                text = head_txt
                # Si le chunk n’a pas de EXTINF mais l’entête est M3U, on peut lire le reste (fallback)
                if "#EXTINF" not in text:
                    # ⚠️ fallback: récupérer le corps complet (peut être plus lourd)
                    r.close()
                    r = s.get(m3u_url, timeout=6, verify=False, allow_redirects=True)
                    if r.status_code not in (200, 206):
                        raise Exception("bad-status")
                    text = r.text

                groups = re.findall(r'group-title="([^"]+)"', text)
                cleaned = [re.sub(r'[→←]', '', g).strip() for g in groups]
                return Counter(cleaned)

            # Si pas bon statut/contenu, on retente
            r.close()
            time.sleep(random.uniform(1.2, 2.4))

        except Exception:
            time.sleep(random.uniform(1.2, 2.4))
    return Counter()
    
def _analyze_line(line):
    """Analyse une ligne du fichier M3U, retourne catégorie si trouvée."""
    try:
        if line.startswith("#EXTINF"):
            match = re.search(r'group-title="([^"]+)"', line)
            if match:
                return match.group(1).strip()
        return None
    except Exception:
        return None

def parse_m3u_fast(filepath, max_workers=30):
    """
    Lecture multi-thread d'un gros fichier M3U.
    Retourne l'ensemble des catégories trouvées.
    """
    categories = set()
    with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
        lines = f.readlines()

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(_analyze_line, line) for line in lines]

        for future in as_completed(futures):
            cat = future.result()
            if cat:
                categories.add(cat)

    return categories
    
def _safe_int(x, default=None):
    try:
        return int(float(str(x).strip()))
    except Exception:
        return default

def _fmt_date(dt):
    # Format portable partout
    s = dt.strftime("%m/%d/%Y")
    # Enlève les zéros en tête proprement (07/03/2023 -> 7/3/2023)
    try:
        m, d, y = s.split("/")
        return f"{int(m)}/{int(d)}/{y}"
    except Exception:
        return s

def _fmt_epoch(epoch):
    try:
        iv = _safe_int(epoch)
        if iv:
            import datetime as _dt
            return _fmt_date(_dt.datetime.fromtimestamp(iv))
    except Exception:
        pass
    return "N/A"

def _parse_created_at(s):
    if not s:
        return "N/A"

    # 1) Si c’est un timestamp (int/float ou string numérique)
    try:
        # accepte "1661710787" ou 1661710787
        if isinstance(s, (int, float)) or (isinstance(s, str) and s.strip().isdigit()):
            iv = _safe_int(s)
            if iv:
                import datetime as _dt
                return _fmt_date(_dt.datetime.fromtimestamp(iv))
    except Exception:
        pass

    # 2) Sinon, on tente les formats texte connus
    for fmt in ("%Y-%m-%d %H:%M:%S", "%d/%m/%Y %H:%M", "%Y-%m-%d", "%m/%d/%Y"):
        try:
            import datetime as _dt
            return _fmt_date(_dt.datetime.strptime(str(s), fmt))
        except Exception:
            continue

    # 3) fallback: renvoie tel quel
    return str(s)
    
def _player_api_fetch(host, port, user, pwd, timeout=8):
    scheme = "https" if str(port) == "443" or int(port) == 443 else "http"
    headers, cookies = get_stealth_headers()
    url = f"{scheme}://{_fmt_host(host)}:{port}/player_api.php?username={user}&password={pwd}"
    try:
        r = requests.get(url, headers=headers, cookies=cookies,
                         timeout=(max(2, timeout//2), timeout),
                         verify=False, allow_redirects=True)
        if r.status_code == 200:
            return True, r.json()
        return False, {"http": r.status_code}
    except Exception as e:
        return False, {"error": type(e).__name__}

def _get_m3u_text(host, port, user, pwd, timeout=8):
    """
    Essaie de télécharger le fichier M3U brut.
    Si port == 443 → utilise https://
    Sinon → http://
    """
    scheme = "https" if str(port) == "443" or int(port) == 443 else "http"
    headers, cookies = get_stealth_headers()
    url = f"{scheme}://{_fmt_host(host)}:{port}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8"
    try:
        r = requests.get(url, headers=headers, cookies=cookies,
                         timeout=(max(2, timeout//2), timeout),
                         verify=False, allow_redirects=True)
        if r.status_code in (200, 206) and ("#EXTM3U" in r.text or "#EXTINF" in r.text):
            return True, r.text
        return False, None
    except Exception:
        return False, None

def _pretty_status(ui):
    val = str(ui.get("auth", ui.get("status", ""))).lower()
    if val in ("1", "true", "active", "enabled"):
        return "Active"
    if val in ("0", "false", "disabled", "expired"):
        return "Disabled"
    return val.capitalize() or "N/A"

def _extract_userinfo(ui):
    created = _parse_created_at(ui.get("created_at"))
    expires = _fmt_epoch(ui.get("exp_date"))
    max_conn = ui.get("max_connections", ui.get("max_connections", "N/A"))
    active   = ui.get("active_cons", ui.get("active_connections", "N/A"))
    status   = _pretty_status(ui)
    return created, expires, max_conn, active, status

def _split_m3u(url):
    """
    Supporte IPv4 et domaines.
    IPv6 est ignoré (préférence utilisateur).
    Retourne (host, port:int, user, pwd)
    """
    u = (url or "").strip()
    if not u:
        return "", 0, "", ""

    if not u.lower().startswith(("http://", "https://")):
        u = "http://" + u

    try:
        p = urlparse(u)
    except Exception:
        return "", 0, "", ""

    netloc = p.netloc or ""
    if not netloc and "://" in u:
        netloc = u.split("://", 1)[1].split("/", 1)[0]

    # --- IPv6 -> IGNORER ---
    # IPv6 entre crochets [::1]:8080
    m = re.match(r"^\[([0-9a-fA-F:]+)\](?::(\d+))?$", netloc)
    if m or (netloc.count(":") >= 2):
        user, pwd = extract_credentials(u)
        return "", 0, user, pwd

    host = ""
    port = 80

    # IPv4 ou domaine avec :port
    if ":" in netloc:
        h, po = netloc.rsplit(":", 1)
        host = h
        try:
            port = int(po)
        except Exception:
            port = 80
    else:
        host = netloc
        port = 80

    user, pwd = extract_credentials(u)

    # Sécurité supplémentaire
    if host and _is_ipv6_host(host):
        return "", 0, user, pwd

    return host, port, user, pwd

def get_m3u_list_by_menu():

    clear_screen()

    lang = globals().get("LANG", "en")

    if lang == "es":
        # ───── ENTÊTE ESPAGNOL ─────
        print(f"{Fore.YELLOW}═══════════════════════════════════════════")
        print(f"{Fore.RED}  PANEL ESPEJO MULTI-SCAN - EDICIÓN SOPI987{Fore.YELLOW}")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        print(f"{Fore.YELLOW}  {Fore.RED}1.{Fore.YELLOW} 📎 Pegar manualmente un solo enlace M3U activo")
        print(f"  {Fore.RED}2.{Fore.YELLOW} 📁 Escanear todos los enlaces desde un archivo de Telegram")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        while True:
            choix = input(f"\n{Fore.YELLOW}👉 ¿Qué quieres hacer? (1 o 2): {Fore.RESET}").strip()
            if choix == "1":
                link = input(f"\n{Fore.YELLOW}🔑 Pega aquí tu enlace M3U activo:\n{Fore.RESET}").strip()
                if "username=" in link and "password=" in link:
                    return [link]
                else:
                    print(f"{Fore.RED}❌ Enlace inválido. Necesitas un enlace M3U completo con username/password.{Fore.RESET}")
            elif choix == "2":
                return None
            else:
                print(f"{Fore.RED}❌ Entrada incorrecta.{Fore.RESET}")

    elif lang == "it":
        # ───── INTESTAZIONE ITALIANA ─────
        print(f"{Fore.YELLOW}═══════════════════════════════════════════")
        print(f"{Fore.RED}  PANNELLO SPECCHIO MULTI-SCAN - EDIZIONE SOPI987{Fore.YELLOW}")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        print(f"{Fore.YELLOW}  {Fore.RED}1.{Fore.YELLOW} 📎 Incolla manualmente un solo link M3U attivo")
        print(f"  {Fore.RED}2.{Fore.YELLOW} 📁 Scansiona tutti i link da un file di Telegram")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        while True:
            choix = input(f"\n{Fore.YELLOW}👉 Cosa vuoi fare? (1 o 2): {Fore.RESET}").strip()
            if choix == "1":
                link = input(f"\n{Fore.YELLOW}🔑 Incolla qui il tuo link M3U attivo:\n{Fore.RESET}").strip()
                if "username=" in link and "password=" in link:
                    return [link]
                else:
                    print(f"{Fore.RED}❌ Link non valido. Serve un link M3U completo con username/password.{Fore.RESET}")
            elif choix == "2":
                return None
            else:
                print(f"{Fore.RED}❌ Voce non valida.{Fore.RESET}")

    else:
        # ───── ENTÊTE ANGLAIS ─────
        print(f"{Fore.YELLOW}═══════════════════════════════════════════")
        print(f"{Fore.RED}  MIRROR PANEL MULTI-SCAN - SOPI987 EDITION{Fore.YELLOW}")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        print(f"{Fore.YELLOW}  {Fore.RED}1.{Fore.YELLOW} 📎 Paste a single active M3U link manually")
        print(f"  {Fore.RED}2.{Fore.YELLOW} 📁 Scan all links from a Telegram file")
        print(f"═══════════════════════════════════════════{Fore.RESET}")
        while True:
            choix = input(f"\n{Fore.YELLOW}👉 What would you like to do? (1 or 2): {Fore.RESET}").strip()
            if choix == "1":
                link = input(f"\n{Fore.YELLOW}🔑 Paste your active M3U link here:\n{Fore.RESET}").strip()
                if "username=" in link and "password=" in link:
                    return [link]
                else:
                    print(f"{Fore.RED}❌ Invalid link. You need a full M3U link with username/password.{Fore.RESET}")
            elif choix == "2":
                return None
            else:
                print(f"{Fore.RED}❌ Incorrect entry.{Fore.RESET}")
                                
# ===== Panel console pour CHECK M3U =====
def _render_m3u_check_panel(total, done, active, inactive, current=""):
    """
    Panneau CHECK M3U toujours en haut de l'écran.
    - \033[H\033[2J : curseur en haut + clear écran complet
    - Cadre + compteurs + barre + % + 'Current'
    - Cascade des 5 derniers événements (LAST_EVENTS)
    """
    import sys
    from colorama import Fore, Style

    # utilise la langue globale (en / es / it)
    try:
        lang = LANG
    except NameError:
        lang = "en"

    PANEL_WIDTH = 41  # largeur intérieure (entre ║ ║)

    # --- Progress ---
    pct = (done / total * 100.0) if total else 0.0
    bar_len = 16
    fill = int(bar_len * pct / 100.0)
    bar = "█" * fill + "░" * (bar_len - fill)
    pct_str = f"{Fore.LIGHTYELLOW_EX}{pct:5.1f}%{Fore.RESET}"

    # --- Textes selon la langue ---
    if lang == "es":
        title_label = "CHECK M3U – PANEL SOPI987"
        row1_text = (
            f"📦 A analizar : {Fore.LIGHTYELLOW_EX}{total}{Fore.RESET}   "
            f"🔁 Hechos : {Fore.LIGHTYELLOW_EX}{done}{Fore.RESET}"
        )
        row2_text = (
            f"✅ Activos    : {Fore.LIGHTYELLOW_EX}{active}{Fore.RESET}   "
            f"❌ Inactivos: {Fore.LIGHTYELLOW_EX}{inactive}{Fore.RESET}"
        )
        row3_text = (
            f"⏳ Progreso :  [{Fore.GREEN}{bar}{Fore.RESET}]{pct_str}"
        )
        cur_label = "🔍 Actual     : "
        cascade_header = f" {Fore.CYAN}↓ Últimos chequeos:{Fore.RESET}"

    elif lang == "it":
        title_label = "CHECK M3U – PANNELLO SOPI987"
        row1_text = (
            f"📦 Da analizzare : {Fore.LIGHTYELLOW_EX}{total}{Fore.RESET}   "
            f"🔁 Fatti : {Fore.LIGHTYELLOW_EX}{done}{Fore.RESET}"
        )
        row2_text = (
            f"✅ Attivi      : {Fore.LIGHTYELLOW_EX}{active}{Fore.RESET}   "
            f"❌ Non attivi: {Fore.LIGHTYELLOW_EX}{inactive}{Fore.RESET}"
        )
        row3_text = (
            f"⏳ Progresso :  [{Fore.GREEN}{bar}{Fore.RESET}]{pct_str}"
        )
        cur_label = "🔍 Corrente    : "
        cascade_header = f" {Fore.CYAN}↓ Ultimi controlli:{Fore.RESET}"

    else:
        title_label = "CHECK M3U – SOPI987 PANEL"
        row1_text = (
            f"📦 To analyze : {Fore.LIGHTYELLOW_EX}{total}{Fore.RESET}   "
            f"🔁 Done : {Fore.LIGHTYELLOW_EX}{done}{Fore.RESET}"
        )
        row2_text = (
            f"✅ Active     : {Fore.LIGHTYELLOW_EX}{active}{Fore.RESET}   "
            f"❌ Inactive : {Fore.LIGHTYELLOW_EX}{inactive}{Fore.RESET}"
        )
        row3_text = (
            f"⏳ Progress :  [{Fore.GREEN}{bar}{Fore.RESET}]{pct_str}"
        )
        cur_label = "🔍 Current    : "
        cascade_header = f" {Fore.CYAN}↓ Latest checks:{Fore.RESET}"

    # --- Titre & lignes ---
    header = f"{Fore.MAGENTA}╔{'═'*PANEL_WIDTH}╗{Fore.RESET}"

    # on centre le titre dans la largeur intérieure - 2 (car on ajoute un espace après '║')
    inner_title_width = PANEL_WIDTH - 2
    title_centered = f"{title_label:^{inner_title_width}}"
    title = (
        f"{Fore.MAGENTA}║{Fore.RESET} "
        f"{Fore.YELLOW}{title_centered}{Fore.RESET}"
    )

    sep = f"{Fore.MAGENTA}╠{'═'*PANEL_WIDTH}╣{Fore.RESET}"

    row1 = f"{Fore.MAGENTA}║{Fore.RESET} {row1_text}"
    row2 = f"{Fore.MAGENTA}║{Fore.RESET} {row2_text}"
    row3 = f"{Fore.MAGENTA}║{Fore.RESET} {row3_text}"

    # --- Current (tronqué propre) ---
    if current:
        max_cur = PANEL_WIDTH - len(" " + cur_label) - 1
        disp = (current[:max_cur-1] + "…") if len(current) > max_cur else current
        current_line = (
            f"{Fore.MAGENTA}║{Fore.RESET} "
            f"{cur_label}{Fore.CYAN}{disp}{Fore.RESET}"
        )
    else:
        current_line = f"{Fore.MAGENTA}║{Fore.RESET}{' ' * (PANEL_WIDTH)}{Fore.MAGENTA}║{Fore.RESET}"

    footer = f"{Fore.MAGENTA}╚{'═'*PANEL_WIDTH}╝{Fore.RESET}"

    # --- Cascade (hors cadre) : 5 dernières lignes, la plus récente en bas ---
    try:
        cascade_lines = list(LAST_EVENTS)[-5:]
    except NameError:
        cascade_lines = []
    if len(cascade_lines) < 5:
        cascade_lines = ([""] * (5 - len(cascade_lines))) + cascade_lines

    # === Rendu fixe : Home + Clear + Cadre + Cascade ===
    sys.stdout.write("\033[H\033[2J")  # aller en haut + effacer tout l'écran

    # Cadre
    sys.stdout.write(header + "\n")
    sys.stdout.write(title  + "\n")
    sys.stdout.write(sep    + "\n")
    sys.stdout.write(row1   + "\n")
    sys.stdout.write(row2   + "\n")
    sys.stdout.write(row3   + "\n")
    sys.stdout.write(current_line + "\n")
    sys.stdout.write(footer + "\n")

    # Espace + cascade
    sys.stdout.write("\n")
    sys.stdout.write(cascade_header + "\n")
    for idx, L in enumerate(cascade_lines):
        if not L:
            sys.stdout.write("\n")
            continue
        dim = Style.DIM if idx < 4 else Style.NORMAL  # anciennes lignes atténuées
        sys.stdout.write(dim + L + Style.RESET_ALL + "\n")

    sys.stdout.flush()
        
def _render_active_domains_panel(total, done, active, inactive, current=""):
    """
    Panel atomique pour le filtrage des domaines actifs (_http.txt → _active.txt).
    Toujours en haut de l'écran, remis à jour à chaque domaine terminé,
    avec une cascade de max 5 lignes en dessous (ACTIVE / INACTIVE).
    """
    import sys
    from colorama import Fore, Style

    PANEL_WIDTH = 41  # largeur intérieure

    # langue globale (par défaut anglais si pas défini)
    lang = globals().get("LANG", "en")

    # ─── Progression ──────────────────────────────────────────────
    pct = (done / total * 100.0) if total else 0.0
    bar_len = 12
    fill = int(bar_len * pct / 100.0)
    bar = "█" * fill + "░" * (bar_len - fill)
    pct_str = f"{Fore.LIGHTYELLOW_EX}{pct:5.1f}%{Fore.RESET}"

    # ─── Textes selon la langue ───────────────────────────────────
    if lang == "es":
        title_text = "FILTRO DOMINIOS ACTIVOS – SOPI987"
        row1_label = (
            f"📦 A analizar : {Fore.LIGHTYELLOW_EX}{total:<3}{Fore.RESET}"
            f"   🔁 Hechos : {Fore.LIGHTYELLOW_EX}{done:<3}{Fore.RESET}"
        )
        row2_label = (
            f"✅ Activos   : {Fore.LIGHTYELLOW_EX}{active:<3}{Fore.RESET}"
            f"   ❌ Inactivos : {Fore.LIGHTYELLOW_EX}{inactive:<3}{Fore.RESET}"
        )
        prog_label = f"⏳ Progreso : [{Fore.GREEN}{bar}{Fore.RESET}] {pct_str}"
        cur_prefix = "🔍 Actual : "
        cascade_header = f" {Fore.CYAN}↓ Últimas comprobaciones de dominios:{Fore.RESET}"

    elif lang == "it":
        title_text = "FILTRO DOMINI ATTIVI – SOPI987"
        row1_label = (
            f"📦 Da analizzare : {Fore.LIGHTYELLOW_EX}{total:<3}{Fore.RESET}"
            f"   🔁 Fatti : {Fore.LIGHTYELLOW_EX}{done:<3}{Fore.RESET}"
        )
        row2_label = (
            f"✅ Attivi    : {Fore.LIGHTYELLOW_EX}{active:<3}{Fore.RESET}"
            f"   ❌ Non attivi : {Fore.LIGHTYELLOW_EX}{inactive:<3}{Fore.RESET}"
        )
        prog_label = f"⏳ Progresso : [{Fore.GREEN}{bar}{Fore.RESET}] {pct_str}"
        cur_prefix = "🔍 Corrente : "
        cascade_header = f" {Fore.CYAN}↓ Ultime verifiche dei domini:{Fore.RESET}"

    else:
        title_text = "ACTIVE DOMAIN FILTER – SOPI987"
        row1_label = (
            f"📦 To analyze : {Fore.LIGHTYELLOW_EX}{total:<3}{Fore.RESET}"
            f"   🔁 Done : {Fore.LIGHTYELLOW_EX}{done:<3}{Fore.RESET}"
        )
        row2_label = (
            f"✅ Active   : {Fore.LIGHTYELLOW_EX}{active:<3}{Fore.RESET}"
            f"   ❌ Inactive : {Fore.LIGHTYELLOW_EX}{inactive:<3}{Fore.RESET}"
        )
        prog_label = f"⏳ Progress : [{Fore.GREEN}{bar}{Fore.RESET}] {pct_str}"
        cur_prefix = "🔍 Current : "
        cascade_header = f" {Fore.CYAN}↓ Latest domain checks:{Fore.RESET}"

    # ─── Domaine courant (tronqué proprement) ────────────────────
    if current:
        max_cur = PANEL_WIDTH - len(" " + cur_prefix) - 1
        disp = (current[:max_cur - 1] + "…") if len(current) > max_cur else current
        current_line = (
            f"{Fore.MAGENTA}║{Fore.RESET} "
            f"{cur_prefix}{Fore.CYAN}{disp:<{PANEL_WIDTH-20}}{Fore.RESET}"
            f"{Fore.MAGENTA}{Fore.RESET}"
        )
    else:
        current_line = (
            f"{Fore.MAGENTA}║{Fore.RESET}"
            f"{' ' * PANEL_WIDTH}"
            f"{Fore.MAGENTA}{Fore.RESET}"
        )

    # ─── Cadre principal ─────────────────────────────────────────
    header = f"{Fore.MAGENTA}╔{'═'*PANEL_WIDTH}╗{Fore.RESET}"
    title  = (
        f"{Fore.MAGENTA}║{Fore.RESET} "
        f"{Fore.YELLOW}{title_text:^{PANEL_WIDTH-2}}{Fore.RESET} "
        f"{Fore.MAGENTA}{Fore.RESET}"
    )
    sep    = f"{Fore.MAGENTA}╠{'═'*PANEL_WIDTH}╣{Fore.RESET}"

    row1 = (
        f"{Fore.MAGENTA}║{Fore.RESET} "
        f"{row1_label}"
        f"{' ' * (PANEL_WIDTH-41)}"
        f"{Fore.MAGENTA}{Fore.RESET}"
    )

    row2 = (
        f"{Fore.MAGENTA}║{Fore.RESET} "
        f"{row2_label}"
        f"{' ' * (PANEL_WIDTH-41)}"
        f"{Fore.MAGENTA}{Fore.RESET}"
    )

    row3 = (
        f"{Fore.MAGENTA}║{Fore.RESET} "
        f"{prog_label}"
        f"{' ' * (PANEL_WIDTH-41)}"
        f"{Fore.MAGENTA}{Fore.RESET}"
    )

    footer = f"{Fore.MAGENTA}╚{'═'*PANEL_WIDTH}╝{Fore.RESET}"

    # ─── Cascade (max 5 lignes) ───────────────────────────────────
    try:
        cascade_lines = list(ACTIVE_EVENTS)[-5:]
    except NameError:
        cascade_lines = []

    if len(cascade_lines) < 5:
        cascade_lines = ([""] * (5 - len(cascade_lines))) + cascade_lines

    processed_cascade = []
    for idx, L in enumerate(cascade_lines):
        if not L:
            processed_cascade.append("")
            continue
        dim = Style.DIM if idx < 4 else Style.NORMAL  # les + anciennes atténuées
        processed_cascade.append(dim + L + Style.RESET_ALL)

    # ─── Construction du frame complet (panel + cascade) ─────────
    frame_lines = [
        header,
        title,
        sep,
        row1,
        row2,
        row3,
        current_line,
        footer,
        "",
        cascade_header,
        *processed_cascade,
    ]

    # ⛓️ Rendu ATOMIQUE : clear + tout le bloc d'un coup sous verrou
    frame = "\033[H\033[J" + "\n".join(frame_lines) + "\n\x1b[0m"
    with _display_lock:
        sys.stdout.write(frame)
        sys.stdout.flush()
                            
def choisir_m3u_file():
    try:
        # keep ONLY original source lists like 123_m3u.txt, 1209_m3u.txt, etc.
        files = [
            f for f in os.listdir(hits_dir)
            if f.endswith("_m3u.txt") and not f.endswith("_check_m3u.txt")
        ]
        if not files:
            # ─── NO FILE FOUND ───
            lang = globals().get("LANG", "en")
            if lang == "es":
                print(f"{Fore.RED}❌ No se encontró ningún archivo '_m3u.txt' en {hits_dir}{Fore.RESET}")
            elif lang == "it":
                print(f"{Fore.RED}❌ Nessun file '_m3u.txt' trovato in {hits_dir}{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ No source '_m3u.txt' file found in {hits_dir}{Fore.RESET}")
            sys.exit(1)

        # optional: nice, stable order
        files.sort(key=str.lower)

        lang = globals().get("LANG", "en")

        # ─── TITRE LISTE DE FICHIERS ───
        if lang == "es":
            print(f"\n{Fore.YELLOW}Lista de archivos M3U encontrados:{Fore.RESET}\n")
        elif lang == "it":
            print(f"\n{Fore.YELLOW}Lista dei file M3U trovati:{Fore.RESET}\n")
        else:
            print(f"\n{Fore.YELLOW}List of found M3U files:{Fore.RESET}\n")

        for idx, f in enumerate(files, 1):
            print(f"  {Fore.RED}{idx}.{Fore.RESET} {f}")

        # ─── CHOIX UTILISATEUR ───
        while True:
            if lang == "es":
                choix = input(f"\n{Fore.YELLOW}Introduce el número del archivo a usar: {Fore.RESET}").strip()
            elif lang == "it":
                choix = input(f"\n{Fore.YELLOW}Inserisci il numero del file da usare: {Fore.RESET}").strip()
            else:
                choix = input(f"\n{Fore.YELLOW}Enter the number of the file to use: {Fore.RESET}").strip()

            if choix.isdigit() and 1 <= int(choix) <= len(files):
                return os.path.join(hits_dir, files[int(choix) - 1])

            # ─── ERREUR ───
            if lang == "es":
                print(f"{Fore.RED}❌ Elección inválida, intenta de nuevo.{Fore.RESET}")
            elif lang == "it":
                print(f"{Fore.RED}❌ Scelta non valida, riprova.{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ Invalid choice, try again.{Fore.RESET}")

    except Exception as e:
        lang = globals().get("LANG", "en")

        if lang == "es":
            print(f"{Fore.RED}❌ Error al seleccionar archivo M3U: {e}{Fore.RESET}")
        elif lang == "it":
            print(f"{Fore.RED}❌ Errore nella selezione del file M3U: {e}{Fore.RESET}")
        else:
            print(f"{Fore.RED}❌ Error selecting M3U file: {e}{Fore.RESET}")
        sys.exit(1)
                
def get_scanned_domains(all_results_file):
    scanned = set()
    if os.path.exists(all_results_file):
        with open(all_results_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("📥 Domain :"):
                    domain = line.strip().split(":", 1)[-1].strip()
                    if domain: scanned.add(domain)
    return scanned

class ScanStatus:
    def __init__(self, m3u, domain, port, username, password):
        self.m3u = m3u
        self.domain = domain
        self.port = port
        self.username = username
        self.password = password
        self.output_file = os.path.join(MIRROR_DIR, f"{self.domain}.txt")
        self.valid_results = []
        self.domains_tested = 0
        self.total_domains = 0
        self.results_found = 0
        self.categories = OrderedDict()
        self.channel_counts = Counter()
        self.ip, self.city, self.country, self.flag = resolve_ip(domain)
        self.total_streams = 0
        self.done = False

def _validate_panel_with_fallback(host: str, port: int, user: str, pwd: str, base_scheme: str,
                                  timeout_file=12, timeout_auth=8):
    """
    Valide un panel via:
      - fichier M3U (#EXTM3U/#EXTINF) ET/OU
      - auth Xtream (player_api.php)
    Si HTTPS:443 échoue sur les deux, on retente en HTTP:80 (fallback).
    Retourne: (ok: bool, tag: str, scheme_used: str, port_used: int)
    """
    scheme = base_scheme
    # 1) tentative primaire
    m3u_dl = f"{scheme}://{_fmt_host(host)}:{port}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8"
    valid_file = is_valid_m3u(m3u_dl, timeout=timeout_file)
    auth_ok, why_auth = xtream_auth_ok(f"{scheme}://{_fmt_host(host)}:{port}", user, pwd, timeout=timeout_auth)
    if valid_file or auth_ok:
        tag = ("m3u-ok" if valid_file else "auth-ok")
        return True, tag, scheme, port

    # 2) fallback http si on était en https:443
    if (scheme == "https" and port == 443):
        scheme2, port2 = "http", 80
        m3u_dl2 = f"{scheme2}://{host}:{port2}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8"
        valid_file2 = is_valid_m3u(m3u_dl2, timeout=10)
        auth_ok2, why_auth2 = xtream_auth_ok(f"{scheme2}://{host}:{port2}", user, pwd, timeout=8)
        if valid_file2 or auth_ok2:
            tag2 = ("http-fallback-m3u" if valid_file2 else "http-fallback-auth")
            return True, tag2, scheme2, port2

    return False, "m3u/auth failed", scheme, port
    
# --- Détection M3U ACTIF (source) : robuste ---
def find_first_n_active_m3u(m3u_links, n=5, scanned_domains=None):
    from concurrent.futures import ThreadPoolExecutor, as_completed
    import threading, time
    global _STOP_M3U_SOURCE_SCAN

    # couleurs fixées
    GREY   = Fore.LIGHTBLACK_EX
    RED    = Fore.RED
    YELLOW = Fore.YELLOW
    GREEN  = Fore.GREEN
    CYAN   = Fore.CYAN

    if scanned_domains is None:
        scanned_domains = set()

    _STOP_M3U_SOURCE_SCAN.clear()

    # --- TIMEOUTS ---
    REQUEST_TIMEOUT = 25          # timeout M3U augmenté
    MAX_TRIES = 1                 # 1 seule tentative (strict)
    GUARD_FENCE = REQUEST_TIMEOUT + 10   # garde-fou 15 s max

    print_lock = threading.Lock()

    # langue globale (en / es / it)
    lang = globals().get("LANG", "en")

    # ─────────────────────────────────────────────
    #  AFFICHAGE 2 LIGNES PAR DOMAINE
    # ─────────────────────────────────────────────
    def print_m3u_result(domain: str, status: str, details: str = ""):
        nonlocal lang
        domain = (domain or "").strip().lower()
        if len(domain) > 40:
            domain = domain[:37] + "..."

        # Ligne 1 : domaine
        line1 = f"{CYAN}🔍 {domain}{Fore.RESET}"

        # Libellés selon la langue
        if lang == "es":
            label_active   = "ACTIVO"
            label_inactive = "INACTIVO"
            label_skipped  = "SALTADO"
        elif lang == "it":
            label_active   = "ATTIVO"
            label_inactive = "NON ATTIVO"
            label_skipped  = "SALTATO"
        else:
            label_active   = "ACTIVE"
            label_inactive = "INACTIVE"
            label_skipped  = "SKIPPED"

        # Ligne 2 : statut
        if status == "active":
            status_str   = f"{GREEN}✅ {label_active}{Fore.RESET}"
            detail_color = YELLOW
        elif status == "skipped":
            status_str   = f"{RED}⏹ {label_skipped}{Fore.RESET}"
            detail_color = RED
        else:
            status_str   = f"{RED}❌ {label_inactive}{Fore.RESET}"
            detail_color = GREY

        details = details.strip() if details else ""
        if len(details) > 60:
            details = details[:57] + "..."

        if details:
            line2 = f" → {status_str} {detail_color}{details}{Fore.RESET}"
        else:
            line2 = f" → {status_str}"

        with print_lock:
            print(line1 + "\n" + line2)

    # ─────────────────────────────────────────────
    #  PRÉPARATION DES CANDIDATS
    # ─────────────────────────────────────────────
    candidates = []
    seen_domains = set()

    for line in m3u_links:
        if "username=" not in line or "password=" not in line:
            continue

        parsed = urlparse(line)
        domain = (parsed.hostname or "").lower()
        if not domain:
            continue

        if domain in scanned_domains or domain in BLOCKED_DOMAINS:
            print_m3u_result(domain, "skipped", "already scanned / blocked")
            continue

        if domain not in seen_domains:
            seen_domains.add(domain)
            candidates.append(line)

    if not candidates:
        return []

    active_list = []
    max_workers = min(10, len(candidates))

    # ─────────────────────────────────────────────
    #  WORKER AVEC GARDE-FOU
    # ─────────────────────────────────────────────
    def worker(line):
        start_time = time.time()
        parsed = urlparse(line)
        domain = (parsed.hostname or "").lower()

        if time.time() - start_time > GUARD_FENCE:
            print_m3u_result(domain, "skipped", "timeout exceeded (pre-check)")
            return None

        if _STOP_M3U_SOURCE_SCAN.is_set():
            print_m3u_result(domain, "skipped", "stop flag")
            return None

        try:
            label = clean_m3u_display(line)
        except:
            label = f"{parsed.hostname}:{parsed.port or 80}"

        ok, reason = probe_m3u_activity(line, timeout=REQUEST_TIMEOUT, max_tries=MAX_TRIES)

        if time.time() - start_time > GUARD_FENCE:
            print_m3u_result(domain, "skipped", "timeout exceeded")
            return None

        if not ok:
            try:
                push_m3u_event(False, f"{label} • {reason}")
            except:
                pass
            print_m3u_result(domain, "inactive", reason or "no-response")
            return None

        # Analyse M3U
        host = parsed.hostname
        port = parsed.port or (443 if parsed.scheme == "https" else 80)
        user, pwd = extract_credentials(line)
        scheme = "https" if port == 443 else "http"

        m3u_dl_https = (
            f"{scheme}://{_fmt_host(host)}:{port}/get.php?"
            f"username={user}&password={pwd}&type=m3u_plus&output=m3u8"
        )

        cats_https   = extract_categories(line)
        groups_https = count_tv_channels_by_group(m3u_dl_https)

        cats_http, groups_http = None, None
        used_scheme, used_port = scheme, port

        # fallback HTTP
        if not cats_https and not groups_https and scheme == "https":
            m3u_dl_http = f"http://{host}:80/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8"
            line_http   = f"http://{host}:80/get.php?username={user}&password={pwd}&type=m3u_plus"

            cats_http   = extract_categories(line_http)
            groups_http = count_tv_channels_by_group(m3u_dl_http)

            if cats_http or groups_http:
                used_scheme, used_port = "http", 80

        if not any([cats_https, groups_https, cats_http, groups_http]):
            print_m3u_result(domain, "inactive", "no categories/groups")
            return None

        extras = []
        if reason:
            extras.append(reason)
        if used_scheme == "http":
            extras.append("http-fallback")
        if cats_https or cats_http:
            extras.append("cats")
        if groups_https or groups_http:
            extras.append("groups")

        summary = " ".join(extras) if extras else "OK"
        print_m3u_result(domain, "active", summary)

        try:
            push_m3u_event(True, f"{label} • {summary}")
        except:
            pass

        if used_scheme == scheme and used_port == port:
            return line

        return f"{used_scheme}://{host}:{used_port}/get.php?username={user}&password={pwd}&type=m3u_plus"

    # ─────────────────────────────────────────────
    #  LANCEMENT PAR THREADPOOL
    # ─────────────────────────────────────────────
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(worker, line) for line in candidates]

        for fut in as_completed(futures):
            if _STOP_M3U_SOURCE_SCAN.is_set() and len(active_list) >= n:
                break

            try:
                res = fut.result(timeout=GUARD_FENCE)
            except:
                continue

            if res:
                active_list.append(res)
                if len(active_list) >= n:
                    _STOP_M3U_SOURCE_SCAN.set()
                    break

    return active_list
    
# --- Scan MIRRORS (STRICT) ---
from threading import Lock
lock = Lock()
def scan_m3u_panels(status: ScanStatus, all_domains, lock):
    status.total_domains = len(all_domains)
    tested_set = set()

    # ✅ Détection région IPTV (UNIQUEMENT pour le nom du fichier)
    try:
        names_for_region = list(status.categories or []) or list((status.channel_counts or {}).keys())
    except Exception:
        names_for_region = list(status.categories or [])

    try:
        _regions = _detect_regions_from_categories(names_for_region) or ["WORLD"]
        region_code = _regions[0]
    except Exception:
        region_code = "WORLD"

    try:
        flag_for_region = _REGION_EMOJI.get(region_code, "🌍")
    except Exception:
        flag_for_region = "🌍"

    # On garde l’info si jamais tu veux l’utiliser ailleurs (Telegram, etc.)
    try:
        status.region_code = region_code
        status.region_flag = flag_for_region
    except Exception:
        pass

    # ✅ Si l’utilisateur a répondu OUI, on met le drapeau DIRECT dans le nom du fichier
    #    AVANT la première écriture
    if MIRROR_FLAG_RENAME:
        try:
            domain_name = status.domain.split("://")[-1].split("/")[0]
            new_name = f"{domain_name}_{flag_for_region}.txt"
            status.output_file = os.path.join(MIRROR_DIR, new_name)
        except Exception:
            # en cas de souci, on laisse le nom déjà prévu
            pass

    # ── En-tête fichier miroir (COMME AU DÉBUT, SANS 🗣️ / SANS LABEL RÉGION) ──
    with open(status.output_file, "w", encoding="utf-8") as indivf:
        indivf.write(f"📥 Domain : {status.domain}\n")
        indivf.write(f"🌐 IP     : {status.ip}\n")
        indivf.write(f"📍 Geo    : {status.flag} {status.city}, {status.country}\n\n")

        indivf.write("📺 IPTV Categories:\n")
        indivf.write("━━━━━━━━━━━━━━━\n")
        for cat in status.categories:
            cat_display = cat if len(cat) <= 32 else cat[:29] + "..."
            indivf.write(f"• {cat_display}\n")
        indivf.write(f"\n📊 Total channels detected : {status.total_streams}\n")
        indivf.write(f"\n🌐 Mirror panels found:\n")

    # ── Helper local: parse "domain[:port]" / "http(s)://domain[:port]" ──
    def _parse_domain_port(entry: str):
        # urlparse: utilise la version globale sécurisée
        s = (entry or "").strip()
        if not s:
            return None, None, None

        if not s.lower().startswith(("http://", "https://")):
            s_for_parse = "http://" + s
            scheme_hint = None
        else:
            s_for_parse = s
            scheme_hint = s.split("://", 1)[0].lower()

        p = urlparse(s_for_parse)
        host = (p.hostname or "").strip().lower()
        port = p.port
        return host, port, scheme_hint

    # ── Worker de test d’un domaine candidat ──
    def scan_domain(domain_line):
        host, port_hint, scheme_hint = _parse_domain_port(domain_line)
        if not host:
            return
        if host in BLOCKED_DOMAINS:
            return

        port = port_hint if port_hint else status.port

        # Schéma: respecte scheme_hint si fourni, sinon règle existante (443 -> https)
        if scheme_hint in ("http", "https"):
            scheme = scheme_hint
        else:
            scheme = "https" if port == 443 else "http"

        key = f"{host}:{port}"
        try:
            test_url = (
                f"{scheme}://{_fmt_host(host)}:{port}/get.php"
                f"?username={status.username}&password={status.password}&type=m3u_plus"
            )

            if is_valid_m3u(test_url):
                if _same_categories_as_source(status, host, port):
                    with lock:
                        if key not in tested_set:
                            tested_set.add(key)
                            status.domains_tested += 1
                        status.results_found += 1

                    result_url = f"{scheme}://{_fmt_host(host)}:{port}"
                    status.valid_results.append(f"{Fore.GREEN}✅ {result_url}{Fore.RESET}")

                    with open(status.output_file, "a", encoding="utf-8") as f:
                        f.write(f"✅ {result_url}\n")
                else:
                    with lock:
                        if key not in tested_set:
                            tested_set.add(key)
                            status.domains_tested += 1
            else:
                with lock:
                    if key not in tested_set:
                        tested_set.add(key)
                        status.domains_tested += 1

        except Exception:
            with lock:
                if key not in tested_set:
                    tested_set.add(key)
                    status.domains_tested += 1

    # ── Lancement en ThreadPool ──
    max_workers = 20
    per_domain_timeout = 15
    from concurrent.futures import ThreadPoolExecutor, TimeoutError

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(scan_domain, domain): domain for domain in all_domains}

        start_time = time.time()
        for future in futures:
            domain = futures[future]
            try:
                future.result(timeout=per_domain_timeout)
            except TimeoutError:
                host, port_hint, _ = _parse_domain_port(domain)
                port = port_hint if port_hint else status.port
                key = f"{host}:{port}"
                with lock:
                    if key not in tested_set:
                        tested_set.add(key)
                        status.domains_tested += 1
                print(f"{Fore.RED}[TIMEOUT] {domain} : dépassé {per_domain_timeout}s, ignoré.{Fore.RESET}")
            except Exception as e:
                host, port_hint, _ = _parse_domain_port(domain)
                port = port_hint if port_hint else status.port
                key = f"{host}:{port}"
                with lock:
                    if key not in tested_set:
                        tested_set.add(key)
                        status.domains_tested += 1
                print(f"{Fore.RED}[ERROR] {domain} : {e}{Fore.RESET}")

        elapsed = time.time() - start_time
        if status.domains_tested < status.total_domains:
            remaining = status.total_domains - status.domains_tested
            print(f"{Fore.YELLOW}[!] Forcing end for {remaining} remaining domains after {elapsed:.1f}s{Fore.RESET}")
            status.domains_tested = status.total_domains

    status.done = True
                
AURA_COLORS = [
    Fore.RED,
    Fore.LIGHTRED_EX,
    Fore.YELLOW,
    Fore.LIGHTYELLOW_EX,
    Fore.YELLOW,
    Fore.LIGHTRED_EX,
]

AURA_CYCLE = itertools.cycle(AURA_COLORS)

def print_global_progress(status_list, all_domains):
    import threading, re

    # Lock d'affichage global
    global _display_lock
    try:
        lock = _display_lock
    except NameError:
        _display_lock = threading.Lock()
        lock = _display_lock

    # langue globale
    lang = globals().get("LANG", "en")

    total_global = sum(s.total_domains for s in status_list)
    tested_global = sum(s.domains_tested for s in status_list)
    percent = (tested_global / total_global) * 100 if total_global else 0

    bar_len = 10
    fill_len = int(bar_len * percent / 100)
    bar = f"{Fore.YELLOW}" + "█" * fill_len + "-" * (bar_len - fill_len) + f"{Fore.RESET}"

    SEP    = "═══════════════════════════════════════════"
    GREY   = Fore.LIGHTBLACK_EX
    YELLOW = Fore.YELLOW
    GREEN  = Fore.GREEN

    PANEL_WIDTH = len(SEP)

    # Regex ANSI pour calcul largeur réelle
    ANSI_RE = re.compile(r'\x1b\[[0-9;]*m')

    def remove_ansi(t): 
        return ANSI_RE.sub("", t)

    def center_fixed(text, width=PANEL_WIDTH):
        pad = (width - len(remove_ansi(text))) // 2
        return " " * max(0, pad) + text

    def short_domain(name, max_len=10):
        name = (name or "").strip()
        return name if len(name) <= max_len else name[:max_len] + "..."

    # ----- TITRE -----
    if lang == "es":
        MAIN = "PANEL ESPEJO MULTI-SCAN"
        SUB  = "EDICIÓN SOPI987"
    elif lang == "it":
        MAIN = "PANNELLO MULTI-SCAN MIRROR"
        SUB  = "EDIZIONE SOPI987"
    else:
        MAIN = "MIRROR PANEL MULTI-SCAN"
        SUB  = "SOPI987 EDITION"

    # Centrage du texte brut
    line1_fixed = center_fixed(MAIN)
    line2_fixed = center_fixed(SUB)

    # Aura dynamique (couleur uniquement)
    try:
        aura = next(AURA_CYCLE)
    except:
        aura = Fore.YELLOW

    colored_line1 = line1_fixed.replace(MAIN, f"{aura}{MAIN}{Fore.RESET}")
    colored_line2 = line2_fixed.replace(SUB, f"{aura}{SUB}{Fore.RESET}")

    frame_lines = []

    # ----- HEADER -----
    frame_lines.append(f"{GREY}{SEP}{Fore.RESET}")
    frame_lines.append(colored_line1)
    frame_lines.append(colored_line2)
    frame_lines.append(f"{GREY}{SEP}{Fore.RESET}")
    frame_lines.append("")

    # ----- GLOBAL PROGRESS -----
    if lang == "es":
        frame_lines.append(
            f"{GREY}Progreso Global:{Fore.RESET} "
            f"{YELLOW}{tested_global}{Fore.RESET}{GREY} / {Fore.RESET}{YELLOW}{total_global}{Fore.RESET} "
            f"{GREY}dominios{Fore.RESET}"
        )
    elif lang == "it":
        frame_lines.append(
            f"{GREY}Progresso Globale:{Fore.RESET} "
            f"{YELLOW}{tested_global}{Fore.RESET}{GREY} / {Fore.RESET}{YELLOW}{total_global}{Fore.RESET} "
            f"{GREY}domini{Fore.RESET}"
        )
    else:
        frame_lines.append(
            f"{GREY}Global Progress:{Fore.RESET} "
            f"{YELLOW}{tested_global}{Fore.RESET}{GREY} / {Fore.RESET}{YELLOW}{total_global}{Fore.RESET} "
            f"{GREY}domains{Fore.RESET}"
        )

    frame_lines.append(f"[{bar}]{GREY} ({percent:.1f}%){Fore.RESET}")
    frame_lines.append("")

    # ----- PANELS SUMMARY -----
    if lang == "es":
        frame_lines.append(f"{GREY}Paneles:{Fore.RESET}")
    elif lang == "it":
        frame_lines.append(f"{GREY}Pannelli:{Fore.RESET}")
    else:
        frame_lines.append(f"{GREY}Panels:{Fore.RESET}")

    for idx, s in enumerate(status_list, 1):
        dom = short_domain(s.domain)
        panel_percent = (s.domains_tested / s.total_domains) * 100 if s.total_domains else 0

        if lang == "es":
            frame_lines.append(
                f" [{idx}] {YELLOW}{dom.ljust(14)}{Fore.RESET}{GREY} : "
                f"{GREEN}{len(s.valid_results)}{Fore.RESET}{GREY} espejo(s) "
                f"({panel_percent:.1f}%){Fore.RESET}"
            )
        elif lang == "it":
            frame_lines.append(
                f" [{idx}] {YELLOW}{dom.ljust(14)}{Fore.RESET}{GREY} : "
                f"{GREEN}{len(s.valid_results)}{Fore.RESET}{GREY} specchio(i) "
                f"({panel_percent:.1f}%){Fore.RESET}"
            )
        else:
            frame_lines.append(
                f" [{idx}] {YELLOW}{dom.ljust(14)}{Fore.RESET}{GREY} : "
                f"{GREEN}{len(s.valid_results)}{Fore.RESET}{GREY} mirror(s) "
                f"({panel_percent:.1f}%){Fore.RESET}"
            )

    frame_lines.append("")

    # ----- DOMAIN DETAILS -----
    for idx, s in enumerate(status_list, 1):
        dom = short_domain(s.domain)

        if lang == "es":
            frame_lines.append(
                f" ▶ {YELLOW}{dom}{Fore.RESET}{GREY} : "
                f"{YELLOW}{s.domains_tested}{Fore.RESET}{GREY}/{Fore.RESET}{YELLOW}{s.total_domains}{Fore.RESET} "
                f"{GREY}dominios{Fore.RESET}"
            )
        elif lang == "it":
            frame_lines.append(
                f" ▶ {YELLOW}{dom}{Fore.RESET}{GREY} : "
                f"{YELLOW}{s.domains_tested}{Fore.RESET}{GREY}/{Fore.RESET}{YELLOW}{s.total_domains}{Fore.RESET} "
                f"{GREY}domini{Fore.RESET}"
            )
        else:
            frame_lines.append(
                f" ▶ {YELLOW}{dom}{Fore.RESET}{GREY} : "
                f"{YELLOW}{s.domains_tested}{Fore.RESET}{GREY}/{Fore.RESET}{YELLOW}{s.total_domains}{Fore.RESET} "
                f"{GREY}domains{Fore.RESET}"
            )

    frame_lines.append("")
    frame_lines.append(f"{GREY}{SEP}{Fore.RESET}")
    frame_lines.append(colored_line1)
    frame_lines.append(colored_line2)
    frame_lines.append(f"{GREY}{SEP}{Fore.RESET}")

    # ----- MODE ATOMIQUE -----
    frame = "\033[H\033[J" + "\n".join(frame_lines) + "\n\x1b[0m"
    with lock:
        sys.stdout.write(frame)
        sys.stdout.flush()

def ask_mirror_flag_rename(ui_lang: str) -> bool:
    from colorama import Fore
    ui_lang = (ui_lang or "en").lower()

    Y = Fore.YELLOW
    G = Fore.GREEN
    R = Fore.RED
    C = Fore.CYAN
    W = Fore.RESET

    if ui_lang == "es":
        q = f"{Y}🏷️ ¿Renombrar los archivos mirror con bandera? {C}[Enter=SI | 1=NO]{W} ➤ "
        yes = f"{G}✅ Renombrado con bandera ACTIVADO.{W}"
        no  = f"{R}⛔ Renombrado con bandera DESACTIVADO.{W}"

    elif ui_lang == "it":
        q = f"{Y}🏷️ Rinominare i file mirror con una bandiera? {C}[Invio=SI | 1=NO]{W} ➤ "
        yes = f"{G}✅ Rinomina con bandiera ATTIVATA.{W}"
        no  = f"{R}⛔ Rinomina con bandiera DISATTIVATA.{W}"

    else:  # EN
        q = f"{Y}🏷️ Rename mirror files with flag? {C}[Enter=YES | 1=NO]{W} ➤ "
        yes = f"{G}✅ Flag rename ENABLED.{W}"
        no  = f"{R}⛔ Flag rename DISABLED.{W}"

    resp = input(q).strip()
    enabled = (resp != "1")

    print(yes if enabled else no)
    return enabled
                                        
def multi_scan_main():
    # langue globale (par défaut anglais)
    lang = globals().get("LANG", "en")

    # 🔥 POSER LA QUESTION ICI
    global MIRROR_FLAG_RENAME
    MIRROR_FLAG_RENAME = ask_mirror_flag_rename(lang)

    os.makedirs(MIRROR_DIR, exist_ok=True)
    m3u_manual_list = get_m3u_list_by_menu()
    if m3u_manual_list is not None:
        m3u_links = m3u_manual_list
    else:
        m3u_file = choisir_m3u_file()
        if not os.path.exists(m3u_file):
            if lang == "es":
                print(f"{Fore.RED}❌ Archivo no encontrado: {m3u_file}{Fore.RESET}")
            elif lang == "it":
                print(f"{Fore.RED}❌ File non trovato: {m3u_file}{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ File not found: {m3u_file}{Fore.RESET}")
            return
        with open(m3u_file, "r") as f:
            m3u_links = [
                line.strip()
                for line in f
                if "username=" in line and "password=" in line
            ]
        if not m3u_links:
            if lang == "es":
                print(f"{Fore.RED}❌ No se han encontrado enlaces M3U válidos en el archivo.{Fore.RESET}")
            elif lang == "it":
                print(f"{Fore.RED}❌ Nessun link M3U valido trovato nel file.{Fore.RESET}")
            else:
                print(f"{Fore.RED}❌ No valid M3U links found in the file.{Fore.RESET}")
            return
            
    scanned_domains = get_scanned_domains(ALL_RESULTS_FILE)
    total_m3u = len(m3u_links)
    remaining_m3u = list(m3u_links)

    while True:
        active_m3u = find_first_n_active_m3u(
            remaining_m3u, n=5, scanned_domains=scanned_domains
        )
        if not active_m3u:
            if lang == "es":
                print(
                    f"{Fore.GREEN}✅ Análisis completado. No quedan M3U activos por escanear.{Fore.RESET}"
                )
            elif lang == "it":
                print(
                    f"{Fore.GREEN}✅ Analisi completata. Nessun M3U attivo rimasto da analizzare.{Fore.RESET}"
                )
            else:
                print(
                    f"{Fore.GREEN}✅ Analysis completed. No active M3Us remaining to scan.{Fore.RESET}"
                )
            break

        # marquer ces domaines comme déjà scannés
        for m3u in active_m3u:
            parsed = urlparse(m3u)
            domain = parsed.hostname or parsed.netloc.split(":")[0]
            scanned_domains.add(domain)

        if lang == "es":
            print(f"\n{Fore.GREEN}🎯 {len(active_m3u)} M3U activos encontrados:{Fore.RESET}")
        elif lang == "it":
            print(f"\n{Fore.GREEN}🎯 {len(active_m3u)} M3U attivi trovati:{Fore.RESET}")
        else:
            print(f"\n{Fore.GREEN}🎯 {len(active_m3u)} Active M3U found :{Fore.RESET}")
            
        for idx, m3u in enumerate(active_m3u, 1):
            parsed = urlparse(m3u)
            domain = parsed.hostname or parsed.netloc.split(":")[0]
            print(f"{Fore.CYAN} [{idx}] {domain}{Fore.RESET}")
            
        # ─── Préparation des statuts de scan ───
        status_list = []
        for m3u in active_m3u:
            username, password = extract_credentials(m3u)
            parsed = urlparse(m3u)
            domain = parsed.hostname or parsed.netloc.split(":")[0]

            # Choix port / schéma cohérent avec l’URL
            port = parsed.port or (443 if parsed.scheme == "https" else 80)
            scheme = "https" if port == 443 else "http"

            status = ScanStatus(m3u, domain, port, username, password)

            # URL utilisée pour re-télécharger le M3U avec le bon schéma
            m3u_download_url = (
                f"{scheme}://{domain}:{port}/get.php?"
                f"username={username}&password={password}"
                f"&type=m3u_plus&output=m3u8"
            )

            # Catégories + comptage des chaînes
            status.categories = extract_categories(m3u)
            status.channel_counts = count_tv_channels_by_group(m3u_download_url)
            if not status.categories and status.channel_counts:
                status.categories = OrderedDict()
                for grp in status.channel_counts.keys():
                    status.categories[grp] = 0
            status.total_streams = sum(status.channel_counts.values())
            status_list.append(status)

        # ─── Chargement des domaines à tester ───
        if not os.path.exists(DOMAINS_FILE):
            print(f"{Fore.RED}❌ File not found: {DOMAINS_FILE}{Fore.RESET}")
            return
        with open(DOMAINS_FILE, "r") as f:
            all_domains = list(set(line.strip() for line in f if line.strip()))

        # ─── Lancement des threads de scan ───
        lock = threading.Lock()
        threads = []
        for status in status_list:
            t = threading.Thread(
                target=scan_m3u_panels, args=(status, all_domains, lock)
            )
            t.daemon = True
            t.start()
            threads.append(t)

        # ─── Suivi de progression globale ───
        while True:
            print_global_progress(status_list, all_domains)
            time.sleep(0.13)

            if all(s.done for s in status_list):
                break

            if all(s.domains_tested >= s.total_domains for s in status_list):
                print(
                    f"{Fore.YELLOW}⚠️  considérée comme terminée (100%) "
                    f"car tous les domaines ont été testés.{Fore.RESET}"
                )
                for s in status_list:
                    s.done = True
                break

        print_global_progress(status_list, all_domains)

        # ─── Résumé par M3U + écriture dans ALL_RESULTS_FILE ───
        for status in status_list:
            clear_screen()
            print(f"{Fore.YELLOW}═══════════════════════════════════════════════{Fore.RESET}")
            print(f"{Fore.CYAN}📥 Domain : {status.domain}{Fore.RESET}")
            print(f"{Fore.BLUE}🌐 IP     : {status.ip}{Fore.RESET}")
            print(
                f"{Fore.GREEN}📍 Geo    : {status.flag} {status.city}, "
                f"{status.country}{Fore.RESET}\n"
            )
            print(f"{Fore.MAGENTA}📺 IPTV Categories:{Fore.RESET}")
            print(f"{Fore.YELLOW}━━━━━━━━━━━━━━━{Fore.RESET}")
            for cat in status.categories:
                cat_display = cat if len(cat) <= 32 else cat[:29] + "..."
                print(f"{Fore.CYAN}• {cat_display}{Fore.RESET}")
            print(
                f"\n{Fore.GREEN}📊 Total channels detected : "
                f"{status.total_streams}{Fore.RESET}"
            )
            print(f"\n{Fore.CYAN}🌐 Mirror domains found:{Fore.RESET}")
            for result in status.valid_results:
                print(result)
            print(
                f"\n{Fore.YELLOW}📄 Results saved in: "
                f"{status.output_file}{Fore.RESET}\n"
            )

            # 🔽 Ecriture propre (sans codes ANSI) dans ALL_RESULTS_FILE
            with open(ALL_RESULTS_FILE, "a", encoding="utf-8") as allf:
                allf.write(f"📥 Domain : {status.domain}\n")
                allf.write(f"🌐 IP     : {status.ip}\n")
                allf.write(
                    f"📍 Geo    : {status.flag} {status.city}, "
                    f"{status.country}\n\n"
                )
                allf.write("📺 IPTV Categories:\n")
                allf.write("━━━━━━━━━━━━━━━\n")
                for cat in status.categories:
                    cat_display = cat if len(cat) <= 32 else cat[:29] + "..."
                    allf.write(f"• {cat_display}\n")
                allf.write(
                    f"\n📊 Total channels detected : "
                    f"{status.total_streams}\n"
                )
                allf.write("\n🌐 Mirror panels found:\n")
                if status.valid_results:
                    for result in status.valid_results:
                        # ➜ on supprime les couleurs avant d’écrire
                        allf.write(remove_ansi(str(result)) + "\n")
                else:
                    allf.write("❌ No mirror panel found.\n")
                allf.write("\n" + "=" * 43 + "\n\n")

        # retirer de remaining_m3u les domaines déjà scannés
        remaining_m3u = [
            line
            for line in remaining_m3u
            if urlparse(line).hostname not in scanned_domains
        ]
                
def check_m3u_details_from_file():
    """
    V2 multi-thread — ACTIVE ONLY

    - Lit un fichier *_m3u.txt
    - Vérifie chaque panel via player_api.php (fallback get.php)
    - Affiche un panel live : total, done, active, inactive, barre de progression
    - Alimente la cascade (derniers M3U testés)

    ⚠️ IMPORTANT :
    ➜ Le(s) fichier(s) de sortie contiennent UNIQUEMENT les M3U ACTIFS.
    """
    from concurrent.futures import ThreadPoolExecutor, as_completed
    import threading
    import os, time

    # —— Choix du mode d’écriture (Yes=1 / No=0) — EN/ES/IT uniquement ——
    def _ask_multi_mode():
        try:
            from colorama import Fore, Style  # couleurs
        except Exception:
            class _F: RESET=""; RED=""; GREEN=""; YELLOW=""; CYAN=""
            Fore = _F(); Style = _F()

        if LANG == "es":
            q = f"{Fore.CYAN}¿Carpetas múltiples por país?{Fore.RESET}"
            y = f"{Fore.GREEN}[1] Sí{Fore.RESET}"
            n = f"{Fore.RED}[0] No (archivo único){Fore.RESET}"
            p = f"{Fore.YELLOW}➤ Selección: {Fore.RESET}"
            ok = f"{Fore.GREEN}→ MODO MULTI-PAÍS activo (archivos con banderas).{Fore.RESET}"
            ko = f"{Fore.RED}→ MODO GENERAL (un solo archivo).{Fore.RESET}"
        elif LANG == "it":
            q = f"{Fore.CYAN}Cartelle multiple per Paese?{Fore.RESET}"
            y = f"{Fore.GREEN}[1] Sì{Fore.RESET}"
            n = f"{Fore.RED}[0] No (file unico){Fore.RESET}"
            p = f"{Fore.YELLOW}➤ Scelta: {Fore.RESET}"
            ok = f"{Fore.GREEN}→ MODALITÀ MULTI-PAESE attiva (file con bandiere).{Fore.RESET}"
            ko = f"{Fore.RED}→ MODALITÀ GENERALE (un solo file).{Fore.RESET}"
        else:
            # EN (default)
            q = f"{Fore.CYAN}Multi-folders by country?{Fore.RESET}"
            y = f"{Fore.GREEN}[1] Yes{Fore.RESET}"
            n = f"{Fore.RED}[0] No (single file){Fore.RESET}"
            p = f"{Fore.YELLOW}➤ Select: {Fore.RESET}"
            ok = f"{Fore.GREEN}→ MULTI-COUNTRY mode ON (flag-suffixed files).{Fore.RESET}"
            ko = f"{Fore.RED}→ GENERAL mode (single file).{Fore.RESET}"

        print(q)
        print("   ", y, "   ", n)
        s = input(p).strip()
        mode = "multi" if s == "1" else "general"
        print(ok if mode == "multi" else ko)
        return mode

    m3u_file = choisir_m3u_file()
    if not m3u_file or not os.path.exists(m3u_file):
        print(f"{Fore.RED}❌ File not found.{Fore.RESET}")
        return

    # Nom de base
    base = os.path.splitext(os.path.basename(m3u_file))[0]        # ex: 1209_m3u
    prefix = base[:-4] if base.endswith("_m3u") else base         # ex: 1209
    out_dir = os.path.dirname(m3u_file)
    out_name_main = f"{prefix}_check_m3u.txt"
    out_path_main = os.path.join(out_dir, out_name_main)

    # —— Sélection du mode (EN/ES/IT uniquement) ——
    mode = _ask_multi_mode()

    # Lecture des lignes M3U brutes
    with open(m3u_file, "r", encoding="utf-8") as f:
        raw = [l.strip() for l in f if l.strip() and "username=" in l and "password=" in l]

    # Déduplication (host,port,user,pass)
    pairs = []
    seen = set()
    for link in raw:
        h, p, u, pw = _split_m3u(link)
        safe_port = p if isinstance(p, int) else _safe_int(p, 80)
        key = (str(h).lower(), safe_port, u, pw)
        if h and u and pw and key not in seen:
            seen.add(key)
            pairs.append((link, h, safe_port, u, pw))

    total = len(pairs)
    if not total:
        print(f"{Fore.RED}❌ No valid M3U link found in the file.{Fore.RESET}")
        return

    def _append_block(outfile_path: str, lines: list):
        first_time = not os.path.exists(outfile_path)
        with open(outfile_path, "a", encoding="utf-8") as out:
            if first_time:
                out.write(f"=== CHECK M3U REPORT — ACTIVE ONLY ({time.strftime('%Y-%m-%d %H:%M:%S')}) ===\n")
                out.write(f"Source file: {os.path.basename(m3u_file)}\n")
                out.write(f"Only ACTIVE M3U accounts are listed below.\n\n")
            out.writelines(lines)

    # Header unique (mode général uniquement)
    if mode == "general":
        with open(out_path_main, "w", encoding="utf-8") as out:
            out.write(f"=== CHECK M3U REPORT — ACTIVE ONLY ({time.strftime('%Y-%m-%d %H:%M:%S')}) ===\n")
            out.write(f"Source file: {os.path.basename(m3u_file)}\n")
            out.write(f"Only ACTIVE M3U accounts are listed below.\n\n")

    # Stats partagées
    done = 0
    actives = 0
    inactives = 0

    panel_lock = threading.Lock()
    file_lock = threading.Lock()

    print()
    _render_m3u_check_panel(total, done, actives, inactives, current="")

    def process_one(idx, link, host, port, user, pwd):
        nonlocal done, actives, inactives

        current_disp = f"{host}:{port}"

        try:
            ok_api, data = _player_api_fetch(host, port, user, pwd, timeout=TIMEOUT)
            ui = (data or {}).get("user_info", {}) if ok_api else {}

            # Catégories via API / M3U
            cats = list(extract_categories(link).keys())
            if not ok_api:
                ok_m3u, _ = _get_m3u_text(host, port, user, pwd, timeout=TIMEOUT)
                if ok_m3u and not cats:
                    m3u_url = (
                        f"http://{_fmt_host(host)}:{port}/get.php?"
                        f"username={user}&password={pwd}&type=m3u_plus&output=m3u8"
                    )
                    groups = count_tv_channels_by_group(m3u_url)
                    cats = list(groups.keys())

            created, expires, max_conn, active_conn, status = (
                _extract_userinfo(ui) if ui else ("N/A", "N/A", "N/A", "N/A", "Unknown")
            )

            s = (status or "").strip().lower()
            is_active = ok_api and (s in {"active", "1", "true", "enabled", "ok"})

            if is_active:
                # Prépare le bloc à écrire (même format qu’avant)
                lines = []
                lines.append("⚡ SOPI987 TV ⚡\n")
                lines.append(f"🌐 Host: {host}\n")
                lines.append(f"🚪 Port: {port}\n")
                lines.append(f"👤 User: {user}\n")
                lines.append(f"🔑 Password: {pwd}\n")
                lines.append(f"📅 Created: {created}\n")
                lines.append(f"⏳ Expires: {expires}\n")
                lines.append(f"✅ Status: {status}\n")
                lines.append(f"👥 Maximum connections: {max_conn}\n")
                lines.append(f"🔌 Active connections: {active_conn}\n")

                # --- Categories header (conservé) + 1 seule ligne de catégories ---
                lines.append("📺 IPTV Categories:\n")
                lines.append("━━━━━━━━━━━━━━━\n")

                def _uniq_preserve(seq):
                    seen = set()
                    out = []
                    for x in seq or []:
                        s = str(x).strip()
                        k = s.casefold()
                        if s and k not in seen:
                            seen.add(k)
                            out.append(s)
                    return out

                if cats:
                    cats_inline = " • ".join(_uniq_preserve(cats))
                    lines.append(f"• {cats_inline}\n")
                else:
                    lines.append("• N/A\n")

                # — espace entre catégories et le lien M3U —
                lines.append("\n")

                lines.append(
                    f"🔗Link M3U: http://{host}:{port}/get.php?username={user}&password={pwd}&type=m3u_plus&output=m3u8\n"
                )
                lines.append("\n" + ("-" * 44) + "\n\n")

                with file_lock:
                    if mode == "general":
                        _append_block(out_path_main, lines)
                    else:
                        # —— Multi-pays : choisit 1 ou 2 régions depuis les catégories
                        regions = _detect_regions_from_categories(cats) or ["WORLD"]
                        for code in regions:
                            suffix = _region_code_to_suffix(code) or "🌍"
                            out_path_flag = os.path.join(out_dir, f"{prefix}_check_m3u_{suffix}.txt")
                            _append_block(out_path_flag, lines)

            # MAJ stats, panel, cascade
            with panel_lock:
                if is_active:
                    actives += 1
                    try:
                        push_m3u_event(True, f"{host}:{port}")
                    except Exception:
                        pass
                else:
                    inactives += 1
                    try:
                        push_m3u_event(False, f"{host}:{port}")
                    except Exception:
                        pass

                done += 1
                _render_m3u_check_panel(total, done, actives, inactives, current=current_disp)

                color = (Fore.GREEN if is_active else Fore.RED)
                print(
                    f"{color}→ [{idx}/{total}] {host}:{port} "
                    f"{'(Active)' if is_active else '(Inactive)'}{Fore.RESET}"
                )

        except Exception as e:
            with panel_lock:
                inactives += 1
                done += 1
                try:
                    push_m3u_event(False, f"{host}:{port} • Error")
                except Exception:
                    pass
                _render_m3u_check_panel(total, done, actives, inactives, current=current_disp)
                print(
                    f"{Fore.RED}⛔ [{idx}/{total}] {host}:{port} "
                    f"Error: {type(e).__name__} - {e}{Fore.RESET}"
                )

    max_workers = max(1, min(NB_THREADS, total))
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(process_one, idx, link, host, port, user, pwd)
                   for idx, (link, host, port, user, pwd) in enumerate(pairs, 1)]
        for _ in as_completed(futures):
            pass

    print(
        f"\n{Fore.GREEN}✅ Check finished.{Fore.RESET} "
        f"{Fore.YELLOW}Active:{Fore.RESET} {actives}  "
        f"{Fore.YELLOW}Inactive (not saved):{Fore.RESET} {inactives}  "
        f"{Fore.YELLOW}Total:{Fore.RESET} {total}"
    )
    if mode == "general":
        print(f"{Fore.CYAN}📄 Active-only report saved to:{Fore.RESET} {out_path_main}\n")
    else:
        print(f"{Fore.CYAN}📄 Active-only reports saved to:{Fore.RESET} {os.path.join(out_dir, prefix)}_check_m3u_[flags].txt\n")
                                                       
def main():
    global LANG

    # Start cleaning thread
    thread_cleaner = threading.Thread(target=clean_residual_files, daemon=True)
    thread_cleaner.start()

    # 🈯 Sélection de langue au démarrage
    choose_language()

    while True:
        BANNER_WIDTH = 42
        print(f"\n{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
        print(f"{Fore.YELLOW}    SUPER SCRAPER SOPI987 v9 {Fore.RESET}".center(BANNER_WIDTH+8))
        print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")

                        # ─── MENU MULTILANGUE ───
        if LANG == "es":
            print(f"1. {Fore.YELLOW}🔍 Ejecutar scraper de Telegram {Fore.RESET}")
            print(f"2. {Fore.YELLOW}🌐 Filtrar HTTP activos {Fore.RESET}")
            print(f"3. {Fore.YELLOW}📍 Geolocalización HTTP {Fore.RESET}")
            print(f"4. {Fore.YELLOW}👥 Buscar dominios espejo {Fore.RESET}")
            print(f"5. {Fore.YELLOW}🧪 Comprobar detalles M3U (desde *_m3u.txt){Fore.RESET}")
            print(f"6. {Fore.YELLOW}❌ Salir{Fore.RESET}")
            print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
            choice = input(f"{Fore.YELLOW}Elige opción (1-6): {Fore.RESET}").strip()

        elif LANG == "it":
            print(f"1. {Fore.YELLOW}🔍 Esegui scraper Telegram {Fore.RESET}")
            print(f"2. {Fore.YELLOW}🌐 Filtra HTTP attivi {Fore.RESET}")
            print(f"3. {Fore.YELLOW}📍 Geolocalizzazione HTTP {Fore.RESET}")
            print(f"4. {Fore.YELLOW}👥 Cerca domini mirror {Fore.RESET}")
            print(f"5. {Fore.YELLOW}🧪 Controlla dettagli M3U (da *_m3u.txt){Fore.RESET}")
            print(f"6. {Fore.YELLOW}❌ Esci{Fore.RESET}")
            print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
            choice = input(f"{Fore.YELLOW}Scegli opzione (1-6): {Fore.RESET}").strip()

        else:
            # default: English
            print(f"1. {Fore.YELLOW}🔍 Run Telegram scraper {Fore.RESET}")
            print(f"2. {Fore.YELLOW}🌐 Filter active HTTP {Fore.RESET}")
            print(f"3. {Fore.YELLOW}📍 HTTP geolocation {Fore.RESET}")
            print(f"4. {Fore.YELLOW}👥 Search mirror domains {Fore.RESET}")
            print(f"5. {Fore.YELLOW}🧪 Check M3U details (from *_m3u.txt){Fore.RESET}")
            print(f"6. {Fore.YELLOW}❌ Quit{Fore.RESET}")
            print(f"{Fore.YELLOW}{'='*BANNER_WIDTH}{Fore.RESET}")
            choice = input(f"{Fore.YELLOW}Your choice (1-6): {Fore.RESET}").strip()

        # ─── ROUTAGE ───
        if choice == "1":
            run_scraper()
        elif choice == "2":
            input_file = list_http_files()
            if input_file:
                check_active_domains(input_file)
        elif choice == "3":
            geolocalizacion_http()
        elif choice == "4":
            multi_scan_main()
        elif choice == "5":
            check_m3u_details_from_file()   # <-- nouvelle fonction
        elif choice == "6":
            if LANG == "es":
                print(f"\n{Fore.YELLOW}¡Hasta luego!{Fore.RESET}")
            elif LANG == "it":
                print(f"\n{Fore.YELLOW}Arrivederci!{Fore.RESET}")
            else:
                print(f"\n{Fore.YELLOW}Goodbye!{Fore.RESET}")
            break
        else:
            if LANG == "es":
                print(f"\n{Fore.RED}❌ ¡Opción inválida!{Fore.RESET}")
            elif LANG == "it":
                print(f"\n{Fore.RED}❌ Scelta non valida!{Fore.RESET}")
            else:
                print(f"\n{Fore.RED}❌ Invalid choice!{Fore.RESET}")
if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print(f"\n\n{Fore.RED}User interruption. Goodbye!{Fore.RESET}")
        sys.exit()
    except Exception as e:
        print(f"\n{Fore.RED}❌ Unexpected error: {e}{Fore.RESET}")
    finally:
        colorama.deinit()
