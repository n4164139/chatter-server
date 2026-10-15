import asyncio
import json
import threading
import queue
import re
import sys
import math
import uuid
import time
import sqlite3
import hashlib
import secrets
import socket
import os
import traceback
import base64
import mimetypes
import io
import wave
import subprocess
import shutil
import signal
import tkinter as tk
import tkinter.font as tkfont
from datetime import datetime

try:
    import winsound
    HAS_WINSOUND = True
except Exception:
    HAS_WINSOUND = False

try:
    import sounddevice as sd
    HAS_AUDIO = True
except Exception:
    sd = None
    HAS_AUDIO = False

try:
    import numpy as np
    HAS_NUMPY = True
except Exception:
    np = None
    HAS_NUMPY = False

try:
    from cryptography.hazmat.primitives.asymmetric.x25519 import (
        X25519PrivateKey, X25519PublicKey)
    from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    HAS_CRYPTO = True
except Exception:
    HAS_CRYPTO = False

import customtkinter as ctk
from tkinter import Menu, filedialog
from PIL import Image, ImageDraw, ImageFont

HAS_PIL = True

TCP_PORT = 9999
UDP_PORT = 9998
DISCOVER_MSG = b'CHATTER_DISCOVER'
SERVER_PREFIX = b'CHATTER_SERVER:'
HEARTBEAT_INTERVAL = 3.0
SESSION_MAX_AGE = 7 * 24 * 3600
NOTIFICATION_TIMEOUT_MS = 5000

APP_NAME = 'Chatter'
CREATOR_USERNAME = 'nikit'

ABOUT_TEXT = (
    "Привет, меня зовут Никита, мне 12 лет, и этот мессенджер я сделал "
    "по зову сердца. Мне хотелось объединить легкость и простоту "
    "использования любого мессенджера, и я сделал тот мессенджер, какой "
    "я хотел все эти годы. Я каждый день стараюсь над усовершенствованием "
    "этого мессенджера, чтобы он был еще лучше и ближе к современным "
    "технологиям. Я живу по правилу \"если хочешь сделать что-то хорошо, "
    "сделай это сам\", и это правило меня сильно толкнуло вперед в моей "
    "жизни. Я верю и знаю, что если действительно захотеть и взяться за "
    "какое-то дело, которым реально хочется заняться - то человек все "
    "сделает ради того, чтобы заняться этим делом. Я рад, что я взялся "
    "за разработку этого мессенджера, и это дело увенчалось успехом. "
    "Этот мессенджер бесплатный, поскольку я считаю, что если ты вложил "
    "все свои силы для того, чтобы сделать какое-то дело, это должны "
    "оценить все без каких либо ограничений и т.п."
)

MAX_ATTACHMENT_SIZE = 2 * 1024 * 1024 * 1024
MAX_AVATAR_SIZE = 100 * 1024
MAX_VOICE_SECONDS = 60.0
MAX_LINE_BYTES = 64 * 1024 * 1024

AVATAR_SIZE = 40
AVATAR_SIZE_CHAT = 32
AVATAR_SIZE_BIG = 100

AUDIO_SAMPLE_RATE = 16000
AUDIO_CHANNELS = 1
AUDIO_BLOCK = 320
CALL_TIMEOUT_SEC = 30.0

E2E_PREFIX = 'e2e:v1:'

OFFICIAL_SERVER = ''


# ============================================================
#                    DDOS PROTECTION
# ============================================================

DDOS_MAX_CONNS_PER_IP        = 5
DDOS_MAX_TOTAL_CONNS         = 500
DDOS_CONN_RATE_PER_SEC       = 2.0
DDOS_CONN_BURST              = 10
DDOS_MSG_RATE_PER_SEC        = 30.0
DDOS_MSG_BURST               = 60
DDOS_LOGIN_RATE_PER_SEC      = 0.2
DDOS_LOGIN_BURST             = 5
DDOS_UDP_RATE_PER_SEC        = 5.0
DDOS_UDP_BURST               = 10
DDOS_VIOLATIONS_TO_BAN       = 5
DDOS_BAN_SEC                 = 300
DDOS_IDLE_TIMEOUT_SEC        = 180
DDOS_MAX_JSON_DEPTH          = 20
DDOS_MAX_ATTACHMENT_BYTES    = 2 * 1024 * 1024 * 1024
DDOS_MAX_VOICE_BYTES         = 5 * 1024 * 1024
DDOS_MAX_AVATAR_BYTES        = 200 * 1024


class TokenBucket:
    __slots__ = ('rate', 'capacity', 'tokens', 'last', '_lock')

    def __init__(self, rate, capacity):
        self.rate = float(rate)
        self.capacity = float(capacity)
        self.tokens = float(capacity)
        self.last = time.monotonic()
        self._lock = threading.Lock()

    def allow(self, tokens=1.0):
        with self._lock:
            now = time.monotonic()
            self.tokens = min(
                self.capacity,
                self.tokens + (now - self.last) * self.rate)
            self.last = now
            if self.tokens >= tokens:
                self.tokens -= tokens
                return True
            return False


def _json_depth_ok(obj, max_depth=DDOS_MAX_JSON_DEPTH):
    stack = [(obj, 1)]
    while stack:
        cur, d = stack.pop()
        if d > max_depth:
            return False
        if isinstance(cur, dict):
            for v in cur.values():
                stack.append((v, d + 1))
        elif isinstance(cur, (list, tuple)):
            for v in cur:
                stack.append((v, d + 1))
    return True


class DDoSProtector:
    def __init__(self):
        self._lock = threading.Lock()
        self.total_connections = 0
        self.active_conns = {}
        self.conn_buckets = {}
        self.msg_buckets = {}
        self.login_buckets = {}
        self.udp_buckets = {}
        self.violations = {}
        self.bans = {}

    def _bucket(self, table, ip, rate, burst):
        b = table.get(ip)
        if b is None:
            b = TokenBucket(rate, burst)
            table[ip] = b
        return b

    def _violate(self, ip, reason):
        count = 0
        with self._lock:
            self.violations[ip] = self.violations.get(ip, 0) + 1
            count = self.violations[ip]
            if count >= DDOS_VIOLATIONS_TO_BAN:
                self.bans[ip] = time.time() + DDOS_BAN_SEC
        if count >= DDOS_VIOLATIONS_TO_BAN:
            log_error(f'[DDOS] IP {ip} banned for '
                      f'{DDOS_BAN_SEC}s ({reason})')
        else:
            log_error(f'[DDOS] IP {ip} violation #{count}: {reason}')

    def is_banned(self, ip):
        with self._lock:
            until = self.bans.get(ip, 0)
            if until <= time.time():
                if ip in self.bans:
                    del self.bans[ip]
                    self.violations.pop(ip, None)
                return False
            return True

    def accept_connection(self, ip):
        if self.is_banned(ip):
            return False
        with self._lock:
            if self.total_connections >= DDOS_MAX_TOTAL_CONNS:
                return False
            n = self.active_conns.get(ip, 0)
            if n >= DDOS_MAX_CONNS_PER_IP:
                self._violate(ip, 'too many connections')
                return False
        if not self._bucket(self.conn_buckets, ip,
                            DDOS_CONN_RATE_PER_SEC,
                            DDOS_CONN_BURST).allow():
            self._violate(ip, 'connection rate')
            return False
        with self._lock:
            self.active_conns[ip] = self.active_conns.get(ip, 0) + 1
            self.total_connections += 1
        return True

    def release_connection(self, ip):
        with self._lock:
            self.total_connections = max(0, self.total_connections - 1)
            n = self.active_conns.get(ip, 0)
            if n <= 1:
                self.active_conns.pop(ip, None)
            else:
                self.active_conns[ip] = n - 1

    def allow_message(self, ip):
        if self.is_banned(ip):
            return False
        if not self._bucket(self.msg_buckets, ip,
                            DDOS_MSG_RATE_PER_SEC,
                            DDOS_MSG_BURST).allow():
            self._violate(ip, 'message flood')
            return False
        return True

    def allow_login(self, ip):
        if self.is_banned(ip):
            return False
        if not self._bucket(self.login_buckets, ip,
                            DDOS_LOGIN_RATE_PER_SEC,
                            DDOS_LOGIN_BURST).allow():
            self._violate(ip, 'login flood')
            return False
        return True

    def allow_udp(self, ip):
        if self.is_banned(ip):
            return False
        if not self._bucket(self.udp_buckets, ip,
                            DDOS_UDP_RATE_PER_SEC,
                            DDOS_UDP_BURST).allow():
            self._violate(ip, 'udp flood')
            return False
        return True

    def gc(self):
        now = time.time()
        with self._lock:
            expired = [ip for ip, u in self.bans.items() if u <= now]
            for ip in expired:
                del self.bans[ip]
                self.violations.pop(ip, None)
            if len(self.conn_buckets) > 10000:
                self.conn_buckets.clear()
            if len(self.msg_buckets) > 20000:
                self.msg_buckets.clear()
            if len(self.login_buckets) > 10000:
                self.login_buckets.clear()
            if len(self.udp_buckets) > 20000:
                self.udp_buckets.clear()


def validate_attachment_sizes(obj):
    if not isinstance(obj, dict):
        return True
    att = obj.get('attachment')
    if isinstance(att, dict):
        b64 = att.get('data', '')
        if isinstance(b64, str):
            approx_bytes = (len(b64) // 4) * 3
            is_voice = bool(att.get('voice'))
            limit = DDOS_MAX_VOICE_BYTES if is_voice else DDOS_MAX_ATTACHMENT_BYTES
            if approx_bytes > limit:
                return False
    avatar = obj.get('avatar')
    if isinstance(avatar, str) and len(avatar) > DDOS_MAX_AVATAR_BYTES * 2:
        return False
    return True


# ============================================================
#                    E2E ENCRYPTION
# ============================================================

def _get_data_dir():
    if sys.platform == 'win32':
        base = os.environ.get('APPDATA') or os.path.expanduser('~')
        path = os.path.join(base, APP_NAME)
    else:
        base = os.path.expanduser('~')
        path = os.path.join(base, '.config', APP_NAME)
    try:
        os.makedirs(path, exist_ok=True)
    except Exception:
        path = os.path.dirname(os.path.abspath(__file__))
    return path


if getattr(sys, 'frozen', False):
    SCRIPT_DIR = os.path.dirname(sys.executable)
else:
    SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

BASE_DIR = _get_data_dir()
ATTACHMENTS_DIR = os.path.join(BASE_DIR, 'attachments')
try:
    os.makedirs(ATTACHMENTS_DIR, exist_ok=True)
except Exception:
    pass

DB_PATH = os.path.join(BASE_DIR, 'chatter_local.db')
LOG_PATH = os.path.join(BASE_DIR, 'chatter_error.log')
SESSION_PATH = os.path.join(BASE_DIR, 'chatter_session.json')
SETTINGS_PATH = os.path.join(BASE_DIR, 'chatter_settings.json')
E2E_KEY_PATH = os.path.join(BASE_DIR, 'chatter_e2e.key')
NOTIFY_SOUND_PATH = os.path.join(SCRIPT_DIR, 'Информация', 'Звуки', 'message1.wav')


def _b64e(b):
    return base64.b64encode(b).decode('ascii')


def _b64d(s):
    return base64.b64decode(s)


def log_error(msg):
    try:
        with open(LOG_PATH, 'a', encoding='utf-8') as f:
            f.write(f'{time.strftime("%Y-%m-%d %H:%M:%S")} {msg}\n')
    except Exception:
        pass


# ============================================================
#                WINDOW CENTERING HELPER
# ============================================================

def center_toplevel(win, w=None, h=None):
    def _do_center():
        try:
            win.update_idletasks()
        except Exception:
            pass
        try:
            rw = win.winfo_reqwidth()
            rh = win.winfo_reqheight()
        except Exception:
            rw, rh = 400, 300
        ww = int(w) if w is not None else rw
        hh = int(h) if h is not None else rh
        if ww < rw:
            ww = rw
        if hh < rh:
            hh = rh
        ww = max(ww, 120)
        hh = max(hh, 100)
        try:
            sw = win.winfo_screenwidth()
            sh = win.winfo_screenheight()
        except Exception:
            return
        x = max(0, (sw - ww) // 2)
        y = max(0, (sh - hh) // 2)
        try:
            win.geometry(f"{ww}x{hh}+{x}+{y}")
        except Exception as e:
            log_error(f'center_toplevel geometry: {e}')
        try:
            win.lift()
        except Exception:
            pass
    _do_center()
    for delay in (30, 80, 160, 300, 500):
        try:
            win.after(delay, _do_center)
        except Exception:
            pass


def bring_to_front(win):
    try:
        win.lift()
    except Exception:
        pass
    try:
        win.focus_force()
    except Exception:
        pass


class E2EIdentity:
    def __init__(self):
        self.private_key = None
        self.public_key_b64 = ''
        self._load_or_create()

    def _load_or_create(self):
        if not HAS_CRYPTO:
            return
        try:
            if os.path.exists(E2E_KEY_PATH):
                with open(E2E_KEY_PATH, 'rb') as f:
                    priv_bytes = f.read()
                if len(priv_bytes) == 32:
                    self.private_key = X25519PrivateKey.from_private_bytes(
                        priv_bytes)
                    self.public_key_b64 = self._pub_b64()
                    return
        except Exception as e:
            log_error(f'E2E key load: {e}')
        try:
            self.private_key = X25519PrivateKey.generate()
            priv_bytes = self.private_key.private_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PrivateFormat.Raw,
                encryption_algorithm=serialization.NoEncryption())
            with open(E2E_KEY_PATH, 'wb') as f:
                f.write(priv_bytes)
            try:
                os.chmod(E2E_KEY_PATH, 0o600)
            except Exception:
                pass
            self.public_key_b64 = self._pub_b64()
        except Exception as e:
            log_error(f'E2E key gen: {e}')
            self.private_key = None
            self.public_key_b64 = ''

    def _pub_b64(self):
        try:
            pub_bytes = self.private_key.public_key().public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw)
            return _b64e(pub_bytes)
        except Exception:
            return ''

    def derive_shared_key(self, peer_pub_b64):
        if not self.private_key or not peer_pub_b64:
            return None
        try:
            peer_pub_bytes = _b64d(peer_pub_b64)
            if len(peer_pub_bytes) != 32:
                return None
            peer_pub = X25519PublicKey.from_public_bytes(peer_pub_bytes)
            shared = self.private_key.exchange(peer_pub)
            hkdf = HKDF(algorithm=hashes.SHA256(), length=32,
                        salt=None, info=b'chatter-e2e-v1')
            return hkdf.derive(shared)
        except Exception as e:
            log_error(f'derive_shared_key: {e}')
            return None


def e2e_encrypt(key, plaintext_bytes):
    if not key:
        return None
    try:
        aead = ChaCha20Poly1305(key)
        nonce = os.urandom(12)
        ct = aead.encrypt(nonce, plaintext_bytes, None)
        return _b64e(nonce + ct)
    except Exception as e:
        log_error(f'e2e_encrypt: {e}')
        return None


def e2e_decrypt(key, b64_payload):
    if not key or not b64_payload:
        return None
    try:
        raw = _b64d(b64_payload)
        if len(raw) < 12 + 16:
            return None
        nonce, ct = raw[:12], raw[12:]
        aead = ChaCha20Poly1305(key)
        return aead.decrypt(nonce, ct, None)
    except Exception:
        return None


def e2e_fingerprint(pub1_b64, pub2_b64):
    try:
        if not pub1_b64 or not pub2_b64:
            return ''
        a = _b64d(pub1_b64)
        b = _b64d(pub2_b64)
        data = b''.join(sorted([a, b]))
        digest = hashlib.sha256(data).digest()
        num = int.from_bytes(digest[:20], 'big') % (10 ** 60)
        s = f'{num:060d}'
        return ' '.join(s[i:i + 5] for i in range(0, 60, 5))
    except Exception:
        return ''


LANGUAGES = {
    'ru': ('🇷🇺', 'Русский'),
    'en': ('🇬🇧', 'English'),
    'zh': ('🇨🇳', '简体中文'),
    'hi': ('🇮🇳', 'हिन्दी'),
    'es': ('🇪🇸', 'Español'),
    'ar': ('🇸🇦', 'العربية'),
    'fr': ('🇫🇷', 'Français'),
    'bn': ('🇧🇩', 'বাংলা'),
    'pt': ('🇵🇹', 'Português'),
    'id': ('🇮🇩', 'Bahasa Indonesia'),
    'tr': ('🇹🇷', 'Türkçe'),
    'pl': ('🇵🇱', 'Polski'),
}


FONTS = [
    ('standard',    'font_standard', None),
    ('arial',       'Arial',         'Arial'),
    ('comic_sans',  'Comic Sans MC', 'Comic Sans MS'),
    ('segoe_print', 'Segoe Print',   'Segoe Print'),
    ('consolas',    'Consolas',      'Consolas'),
    ('constantia',  'Constantia',    'Constantia'),
    ('corbel',      'Corbel',        'Corbel'),
    ('courier',     'Courier',       'Courier New'),
]

_current_font_code = 'standard'
_current_font_family = None


def get_font(size, weight='normal'):
    fam = _current_font_family
    if fam:
        try:
            return ctk.CTkFont(family=fam, size=size, weight=weight)
        except Exception:
            pass
    return ctk.CTkFont(size=size, weight=weight)


def set_font_by_code(code):
    global _current_font_code, _current_font_family
    for c, _label, fam in FONTS:
        if c == code:
            _current_font_code = c
            _current_font_family = fam
            return
    _current_font_code = 'standard'
    _current_font_family = None


def get_current_font():
    return _current_font_code


def get_font_display(code):
    for c, label, _fam in FONTS:
        if c == code:
            if label.startswith('font_'):
                return t(label)
            return label
    return code


def _apply_ctk_theme_font(family):
    if not family:
        return
    try:
        theme_mgr = getattr(ctk, "ThemeManager", None)
        if theme_mgr is None:
            return
        theme = getattr(theme_mgr, "theme", None)
        if isinstance(theme, dict):
            ct_font = theme.get("CTkFont")
            if isinstance(ct_font, dict):
                ct_font["family"] = family
            for sub in ("light", "dark"):
                if isinstance(theme.get(sub), dict):
                    sub_font = theme[sub].get("CTkFont")
                    if isinstance(sub_font, dict):
                        sub_font["family"] = family
    except Exception:
        pass


def _apply_global_font_family(family):
    if not family:
        return
    _apply_ctk_theme_font(family)
    for name in ('TkDefaultFont', 'TkTextFont', 'TkFixedFont',
                 'TkMenuFont', 'TkHeadingFont', 'TkCaptionFont',
                 'TkSmallCaptionFont', 'TkIconFont', 'TkTooltipFont'):
        try:
            f = tkfont.nametofont(name)
            f.configure(family=family)
        except Exception:
            pass


def _apply_ctk_button_colors():
    try:
        theme_mgr = getattr(ctk, "ThemeManager", None)
        if theme_mgr is None:
            return
        theme = getattr(theme_mgr, "theme", None)
        if not isinstance(theme, dict):
            return
        pairs = (
            ("CTkButton", "fg_color", (BTN, BTN)),
            ("CTkButton", "hover_color", (BTN_HOVER, BTN_HOVER)),
            ("CTkSegmentedButton", "selected_color", (BTN, BTN)),
            ("CTkSegmentedButton", "selected_hover_color",
             (BTN_HOVER, BTN_HOVER)),
            ("CTkOptionMenu", "fg_color", (BTN, BTN)),
            ("CTkOptionMenu", "button_color", (BTN, BTN)),
            ("CTkOptionMenu", "button_hover_color",
             (BTN_HOVER, BTN_HOVER)),
            ("CTkComboBox", "button_color", (BTN, BTN)),
            ("CTkComboBox", "button_hover_color",
             (BTN_HOVER, BTN_HOVER)),
        )
        for widget_key, color_key, value in pairs:
            sub = theme.get(widget_key)
            if isinstance(sub, dict) and color_key in sub:
                sub[color_key] = value
    except Exception as e:
        log_error(f'_apply_ctk_button_colors: {e}')


# ============================================================
#                    THEMES
# ============================================================

THEMES = {
    'black': {
        'name_key': 'theme_black',
        'appearance': 'dark',
        'colors': {
            'BG_DARK':      "#1a1a1a",
            'BG_MID':       "#252525",
            'BG_LIGHT':     "#2f2f2f",
            'BG_INPUT':     "#333333",
            'FG_TEXT':      "#e0e0e0",
            'FG_DIM':       "#888888",
            'FG_STATUS':    "#7a7a7a",
            'YELLOW':       "#FFD700",
            'MENTION_BG':   "#EAD67C",
            'RED':          "#8B0000",
            'RED_HOVER':    "#A00000",
            'BLUE':         "#1f6aa5",
            'GREEN':        "#4CAF50",
            'ORANGE':       "#FF8C00",
            'ERROR_TEXT':   "#ff6b6b",
            'CREATOR_COLOR':"#1DA1F2",
            'OWN_BUBBLE':   "#1e3a52",
            'SENDER_OTHER': "#c678dd",
            'BTN':          "#1f6aa5",
            'BTN_HOVER':    "#2a7ec0",
            'SWITCH':       "#1f6aa5",
        },
    },
    'light': {
        'name_key': 'theme_light',
        'appearance': 'light',
        'colors': {
            'BG_DARK':      "#f5f5f5",
            'BG_MID':       "#e8e8e8",
            'BG_LIGHT':     "#dcdcdc",
            'BG_INPUT':     "#ffffff",
            'FG_TEXT':      "#1a1a1a",
            'FG_DIM':       "#666666",
            'FG_STATUS':    "#999999",
            'YELLOW':       "#B8860B",
            'MENTION_BG':   "#FFE082",
            'RED':          "#C62828",
            'RED_HOVER':    "#E53935",
            'BLUE':         "#1976D2",
            'GREEN':        "#388E3C",
            'ORANGE':       "#F57C00",
            'ERROR_TEXT':   "#D32F2F",
            'CREATOR_COLOR':"#1976D2",
            'OWN_BUBBLE':   "#BBDEFB",
            'SENDER_OTHER': "#7B1FA2",
            'BTN':          "#1976D2",
            'BTN_HOVER':    "#2196F3",
            'SWITCH':       "#1976D2",
        },
    },
    'coffee': {
        'name_key': 'theme_coffee',
        'appearance': 'light',
        'colors': {
            'BG_DARK':      "#FBF3E4",
            'BG_MID':       "#F5E6CE",
            'BG_LIGHT':     "#E8D5B5",
            'BG_INPUT':     "#FFFFFF",
            'FG_TEXT':      "#4A3728",
            'FG_DIM':       "#8B7355",
            'FG_STATUS':    "#A08C6C",
            'YELLOW':       "#B8843D",
            'MENTION_BG':   "#E8D5B5",
            'RED':          "#A0522D",
            'RED_HOVER':    "#C26A3D",
            'BLUE':         "#C89B4A",
            'GREEN':        "#6B8E3D",
            'ORANGE':       "#D68C45",
            'ERROR_TEXT':   "#B7472A",
            'CREATOR_COLOR':"#B8843D",
            'OWN_BUBBLE':   "#E8D5B5",
            'SENDER_OTHER': "#8B6F47",
            'BTN':          "#B4823C",
            'BTN_HOVER':    "#C89448",
            'SWITCH':       "#B4823C",
        },
    },
    'sakura': {
        'name_key': 'theme_sakura',
        'appearance': 'light',
        'colors': {
            'BG_DARK':      "#FFF5F8",
            'BG_MID':       "#FFE4EC",
            'BG_LIGHT':     "#FFD1DC",
            'BG_INPUT':     "#FFFFFF",
            'FG_TEXT':      "#5C2A3F",
            'FG_DIM':       "#A67285",
            'FG_STATUS':    "#C090A0",
            'YELLOW':       "#D81B60",
            'MENTION_BG':   "#FFD1DC",
            'RED':          "#C2185B",
            'RED_HOVER':    "#E91E63",
            'BLUE':         "#E91E63",
            'GREEN':        "#7CB342",
            'ORANGE':       "#FF7043",
            'ERROR_TEXT':   "#C2185B",
            'CREATOR_COLOR':"#E91E63",
            'OWN_BUBBLE':   "#FFD1DC",
            'SENDER_OTHER': "#9C27B0",
            'BTN':          "#E91E63",
            'BTN_HOVER':    "#F06292",
            'SWITCH':       "#E91E63",
        },
    },
}

THEME_ORDER = ['black', 'light', 'coffee', 'sakura']

_current_theme = 'black'

BG_DARK       = "#1a1a1a"
BG_MID        = "#252525"
BG_LIGHT      = "#2f2f2f"
BG_INPUT      = "#333333"
FG_TEXT       = "#e0e0e0"
FG_DIM        = "#888888"
FG_STATUS     = "#7a7a7a"
YELLOW        = "#FFD700"
MENTION_BG    = "#EAD67C"
RED           = "#8B0000"
RED_HOVER     = "#A00000"
BLUE          = "#1f6aa5"
GREEN         = "#4CAF50"
ORANGE        = "#FF8C00"
ERROR_TEXT    = "#ff6b6b"
CREATOR_COLOR = "#1DA1F2"
OWN_BUBBLE    = "#1e3a52"
SENDER_OTHER  = "#c678dd"
BTN           = "#1f6aa5"
BTN_HOVER     = "#2a7ec0"
SWITCH_COLOR  = "#1f6aa5"


def apply_theme(code):
    global _current_theme
    global BG_DARK, BG_MID, BG_LIGHT, BG_INPUT
    global FG_TEXT, FG_DIM, FG_STATUS
    global YELLOW, MENTION_BG, RED, RED_HOVER, BLUE, GREEN, ORANGE
    global ERROR_TEXT, CREATOR_COLOR, OWN_BUBBLE, SENDER_OTHER
    global BTN, BTN_HOVER, SWITCH_COLOR

    if code not in THEMES:
        code = 'black'
    _current_theme = code

    c = THEMES[code]['colors']
    BG_DARK       = c['BG_DARK']
    BG_MID        = c['BG_MID']
    BG_LIGHT      = c['BG_LIGHT']
    BG_INPUT      = c['BG_INPUT']
    FG_TEXT       = c['FG_TEXT']
    FG_DIM        = c['FG_DIM']
    FG_STATUS     = c['FG_STATUS']
    YELLOW        = c['YELLOW']
    MENTION_BG    = c['MENTION_BG']
    RED           = c['RED']
    RED_HOVER     = c['RED_HOVER']
    BLUE          = c['BLUE']
    GREEN         = c['GREEN']
    ORANGE        = c['ORANGE']
    ERROR_TEXT    = c['ERROR_TEXT']
    CREATOR_COLOR = c['CREATOR_COLOR']
    OWN_BUBBLE    = c['OWN_BUBBLE']
    SENDER_OTHER  = c['SENDER_OTHER']
    BTN           = c.get('BTN', c['BLUE'])
    BTN_HOVER     = c.get('BTN_HOVER', c['BLUE'])
    SWITCH_COLOR  = c.get('SWITCH', c['BLUE'])

    try:
        ctk.set_appearance_mode(THEMES[code].get('appearance', 'dark'))
    except Exception:
        pass
    try:
        _apply_ctk_button_colors()
    except Exception:
        pass


def get_current_theme():
    return _current_theme


def get_theme_display(code):
    for c in THEME_ORDER:
        if c == code:
            return t(THEMES[c]['name_key'])
    return code


TRANSLATIONS = {
    'ru': {
        'chats': 'Чаты', 'find_user': '🔍 Найти пользователя',
        'select_chat': 'Выберите, кому хотите написать',
        'input_placeholder': 'Введите сообщение...', 'send': 'Отправить',
        'settings': 'Настройки', 'close': 'Закрыть',
        'account_settings': 'Настройки аккаунта',
        'change_nick': 'Сменить ник', 'change_password': 'Сменить пароль',
        'fullscreen': 'Полный экран / Выйти из него',
        'reconnect': 'Переподключиться', 'notifications': 'Уведомления:',
        'language': 'Язык:', 'delete_account': 'Удалить аккаунт',
        'logout': 'Выйти с аккаунта', 'exit': 'Выйти',
        'username': 'Имя пользователя:', 'password': 'Пароль:',
        'first_name': 'Имя (необязательно):',
        'last_name': 'Фамилия (необязательно):',
        'confirm_password': 'Повторите пароль:',
        'login': 'Войти', 'register': 'Создать аккаунт',
        'login_tab': 'Вход', 'register_tab': 'Регистрация',
        'welcome': 'Добро пожаловать!', 'online': 'В сети',
        'was_online': 'Был(а) недавно', 'typing': '{0} печатает',
        'error': 'Ошибка', 'done': 'Готово', 'cancel': 'Отмена', 'ok': 'OK',
        'save': 'Сохранить', 'saved': 'Сохранено',
        'connecting': 'Подключение...', 'reconnecting': 'Переподключение...',
        'disconnected': 'Разъединено', 'connect_fail': 'Не удалось подключиться',
        'search_title': 'Найти пользователя', 'search_placeholder': 'Имя...',
        'search_btn': 'Искать', 'searching': 'Поиск...',
        'search_found': 'Найдено: {0}', 'search_nothing': 'Ничего не найдено',
        'fill_both': 'Заполните оба поля',
        'fill_all': 'Заполните все обязательные поля',
        'passwords_dont_match': 'Пароли не совпадают',
        'password_min_6': 'Пароль: минимум 6 символов',
        'password_changed': 'Пароль изменён', 'wrong_password': 'Неверный пароль',
        'user_not_found': 'Пользователь не найден',
        'name_taken': 'Это имя уже занято',
        'session_replaced': 'Вы вошли в аккаунт с другого устройства. Текущая сессия завершена.',
        'account_deleted': 'Аккаунт удалён. Сейчас вы выйдете из него.',
        'enter_old_password': 'Введите текущий пароль:',
        'enter_new_password': 'Введите новый пароль (минимум 6 символов):',
        'enter_new_password_again': 'Повторите новый пароль:',
        'change_password_title': 'Смена пароля', 'change_nick_title': 'Смена ника',
        'enter_new_nick': 'Введите новый ник:',
        'delete_account_warning': 'Аккаунт и все данные будут удалены безвозвратно.\nПродолжить?',
        'enter_password_confirm': 'Введите пароль для подтверждения:',
        'language_changed': 'Язык изменён. Chatter будет перезапущен.',
        'choose_language': 'Выбрать язык', 'not_delivered': 'Не доставлено',
        'sending': 'Отправка...', 'sent_at': 'Отправлено в {0}',
        'reply_to': 'Отвечает @{0}: "{1}"', 'edit_message': 'Введите новый текст:',
        'edit_message_title': 'Изменить сообщение', 'menu_reply': 'Ответить',
        'menu_edit': 'Изменить', 'menu_delete': 'Удалить',
        'menu_block': 'Заблокировать', 'menu_unblock': 'Разблокировать',
        'menu_delete_local': 'Удалить у меня', 'menu_dm': 'Личное сообщение',
        'menu_delete_chat': 'Удалить',
        'changed_suffix': ' (изменено)', 'left_chat': '{0} покинул чат',
        'joined_chat': '{0} присоединился к чату',
        'search_ip_btn': 'Не находите человека?',
        'enter_ip_title': 'Подключение по IP',
        'enter_ip_text': 'Введите IP адрес сервера:',
        'enter_ip_title2': 'Подключиться к серверу',
        'enter_ip_text2': 'Введите IP адрес сервера:',
        'searching_by_ip': 'Поиск людей по {0}...',
        'attach': 'Прикрепить файл', 'attach_file': '📎',
        'attachment': 'Вложение', 'save_file': 'Сохранить файл',
        'open_file': 'Открыть файл', 'file_saved': 'Файл сохранён',
        'file_too_big': 'Файл слишком большой (макс. 2 ГБ)',
        'upload_avatar': 'Загрузить аватар',
        'avatar_saved': 'Аватар сохранён',
        'avatar_too_big': 'Аватар слишком большой (макс. 100 КБ)',
        'send_file': 'Отправить', 'user_blocked': 'Пользователь заблокирован',
        'user_unblocked': 'Пользователь разблокирован',
        'you_blocked': 'Вы заблокировали этого пользователя',
        'blocked_warning': 'Вы больше не будете получать сообщения от @{0}.\nЗаблокировать?',
        'delete_chat_warning': 'Удалить переписку с @{0}?',
        'no_name': 'Без имени', 'restart_title': 'Перезапуск',
        'restart_msg': 'Chatter будет перезапущен для применения языка...',
        'restart_msg_font': 'Chatter будет перезапущен для применения шрифта...',
        'restart_msg_theme': 'Chatter будет перезапущен для применения темы...',
        'attach_too_big_short': 'Максимум 2 ГБ',
        'call': 'Позвонить', 'call_title': 'Звонок',
        'incoming_call': 'Входящий звонок от {0}',
        'calling_you': '{0} звонит вам',
        'call_calling': 'Соединение...',
        'call_ringing': 'Идёт вызов...',
        'call_active': 'В разговоре',
        'call_ended': 'Звонок завершён',
        'call_rejected': 'Звонок отклонён',
        'call_busy': 'Абонент занят',
        'call_timeout': 'Нет ответа',
        'call_peer_offline': 'Пользователь не в сети',
        'accept': 'Принять', 'reject': 'Отклонить',
        'hangup': 'Завершить', 'mute': 'Выкл. микрофон',
        'unmute': 'Вкл. микрофон',
        'no_audio_device': 'Нет аудиоустройства. Установите sounddevice и numpy.',
        'call_self': 'Нельзя позвонить самому себе',
        'call_in_progress': 'Недоступно во время звонка',
        'forward': 'Переслать',
        'forward_title': 'Переслать сообщение',
        'forward_choose': 'Выберите чат:',
        'forwarded_from': 'Переслано от @{0}',
        'forwarded': 'Переслано',
        'forward_no_chats': 'Нет доступных чатов для пересылки',
        'forward_empty': 'Нечего пересылать',
        'change_font': 'Сменить шрифт',
        'choose_font': 'Выбрать шрифт',
        'font': 'Шрифт:',
        'font_standard': 'Стандартный',
        'font_current': 'установлен сейчас',
        'font_changed': 'Шрифт изменён. Chatter будет перезапущен.',
        'interface_settings': 'Настройки интерфейса',
        'change_theme': 'Сменить тему',
        'choose_theme': 'Выбрать тему',
        'theme': 'Тема:',
        'theme_black': 'Чёрная (стандартная)',
        'theme_light': 'Светлая',
        'theme_coffee': 'Кофейная',
        'theme_sakura': 'Сакура',
        'theme_changed': 'Тема изменена. Chatter будет перезапущен.',
        'voice_message': 'Голосовое сообщение',
        'voice_recording': '🔴 Запись',
        'voice_too_short': 'Сообщение слишком короткое',
        'voice_cancel': 'Отменить запись',
        'you_suffix': '(вы)',
        'offline_suffix': '(офлайн)',
        'rate_limited': 'Слишком много запросов. Подождите немного.',
        'e2e_verify': '🔒 Проверить шифрование',
        'e2e_title': 'Сквозное шифрование',
        'e2e_fingerprint':
            'Номер безопасности с @{0}:\n\n{1}\n\n'
            'Сравните этот номер с собеседником '
            '(лично или по другому каналу). '
            'Если совпадает — переписка защищена от сервера.',
        'e2e_unavailable':
            'Сквозное шифрование отключено. Установите:\n'
            'pip install cryptography',
        'e2e_badge': '🔒 Сквозное шифрование',
        'e2e_decrypt_fail': '[Не удалось расшифровать]',
        'e2e_wait_key': 'Ожидание ключа шифрования...',
        'e2e_notice': '🔒 Защищено сквозным шифрованием',
        'e2e_unverified': '⚠️ Шифрование не подтверждено',
        'e2e_confirm_match': 'Номер совпадает?',
        'e2e_marked_verified': 'Отмечено как проверенное',
        'e2e_marked_unverified': 'Отмечено как непроверенное',
        'empty_chat': 'Здесь пока ничего нет...',
        'creator_badge': 'Создатель',
    },
    'en': {
        'chats': 'Chats', 'find_user': '🔍 Find user',
        'select_chat': 'Select who to write to',
        'input_placeholder': 'Enter a message...', 'send': 'Send',
        'settings': 'Settings', 'close': 'Close',
        'account_settings': 'Account settings',
        'change_nick': 'Change nickname', 'change_password': 'Change password',
        'fullscreen': 'Fullscreen / Exit fullscreen', 'reconnect': 'Reconnect',
        'notifications': 'Notifications:', 'language': 'Language:',
        'delete_account': 'Delete account', 'logout': 'Log out', 'exit': 'Exit',
        'username': 'Username:', 'password': 'Password:',
        'first_name': 'First name (optional):',
        'last_name': 'Last name (optional):',
        'confirm_password': 'Confirm password:', 'login': 'Log in',
        'register': 'Create account', 'login_tab': 'Login',
        'register_tab': 'Register', 'welcome': 'Welcome!', 'online': 'Online',
        'was_online': 'Recently online', 'typing': '{0} is typing',
        'error': 'Error', 'done': 'Done', 'cancel': 'Cancel', 'ok': 'OK',
        'save': 'Save', 'saved': 'Saved',
        'connecting': 'Connecting...', 'reconnecting': 'Reconnecting...',
        'disconnected': 'Disconnected', 'connect_fail': 'Failed to connect',
        'search_title': 'Find user', 'search_placeholder': 'Name...',
        'search_btn': 'Search', 'searching': 'Searching...',
        'search_found': 'Found: {0}', 'search_nothing': 'Nothing found',
        'fill_both': 'Fill in both fields',
        'fill_all': 'Fill in all required fields',
        'passwords_dont_match': 'Passwords do not match',
        'password_min_6': 'Password: at least 6 characters',
        'password_changed': 'Password changed', 'wrong_password': 'Wrong password',
        'user_not_found': 'User not found',
        'name_taken': 'This name is already taken',
        'session_replaced': 'You logged in from another device. Current session ended.',
        'account_deleted': 'Account deleted. You will be logged out.',
        'enter_old_password': 'Enter current password:',
        'enter_new_password': 'Enter new password (min 6 chars):',
        'enter_new_password_again': 'Repeat new password:',
        'change_password_title': 'Change password',
        'change_nick_title': 'Change nickname',
        'enter_new_nick': 'Enter new nickname:',
        'delete_account_warning': 'Account and all data will be deleted.\nContinue?',
        'enter_password_confirm': 'Enter password to confirm:',
        'language_changed': 'Language changed. Chatter will restart.',
        'choose_language': 'Choose language', 'not_delivered': 'Not delivered',
        'sending': 'Sending...', 'sent_at': 'Sent at {0}',
        'reply_to': 'Replying to @{0}: "{1}"', 'edit_message': 'Enter new text:',
        'edit_message_title': 'Edit message', 'menu_reply': 'Reply',
        'menu_edit': 'Edit', 'menu_delete': 'Delete',
        'menu_block': 'Block', 'menu_unblock': 'Unblock',
        'menu_delete_local': 'Delete for me', 'menu_dm': 'Private message',
        'menu_delete_chat': 'Delete',
        'changed_suffix': ' (edited)', 'left_chat': '{0} left the chat',
        'joined_chat': '{0} joined the chat',
        'search_ip_btn': "Can't find the person?",
        'enter_ip_title': 'Connect by IP',
        'enter_ip_text': 'Enter server IP address:',
        'enter_ip_title2': 'Connect to server',
        'enter_ip_text2': 'Enter server IP address:',
        'searching_by_ip': 'Searching people at {0}...',
        'attach': 'Attach file', 'attach_file': '📎',
        'attachment': 'Attachment', 'save_file': 'Save file',
        'open_file': 'Open file', 'file_saved': 'File saved',
        'file_too_big': 'File is too big (max 2 GB)',
        'upload_avatar': 'Upload avatar',
        'avatar_saved': 'Avatar saved',
        'avatar_too_big': 'Avatar is too big (max 100 KB)',
        'send_file': 'Send', 'user_blocked': 'User blocked',
        'user_unblocked': 'User unblocked',
        'you_blocked': 'You blocked this user',
        'blocked_warning': 'You will no longer receive messages from @{0}.\nBlock?',
        'delete_chat_warning': 'Delete conversation with @{0}?',
        'no_name': 'No name', 'restart_title': 'Restart',
        'restart_msg': 'Chatter will restart to apply the language...',
        'restart_msg_font': 'Chatter will restart to apply the font...',
        'restart_msg_theme': 'Chatter will restart to apply the theme...',
        'attach_too_big_short': 'Max 2 GB',
        'call': 'Call', 'call_title': 'Call',
        'incoming_call': 'Incoming call from {0}',
        'calling_you': '{0} is calling you',
        'call_calling': 'Connecting...',
        'call_ringing': 'Ringing...',
        'call_active': 'In call',
        'call_ended': 'Call ended',
        'call_rejected': 'Call rejected',
        'call_busy': 'User busy',
        'call_timeout': 'No answer',
        'call_peer_offline': 'User is offline',
        'accept': 'Accept', 'reject': 'Reject',
        'hangup': 'Hang up', 'mute': 'Mute',
        'unmute': 'Unmute',
        'no_audio_device': 'No audio device. Install sounddevice and numpy.',
        'call_self': 'You cannot call yourself',
        'call_in_progress': 'Not available during a call',
        'forward': 'Forward',
        'forward_title': 'Forward message',
        'forward_choose': 'Choose a chat:',
        'forwarded_from': 'Forwarded from @{0}',
        'forwarded': 'Forwarded',
        'forward_no_chats': 'No chats available to forward to',
        'forward_empty': 'Nothing to forward',
        'change_font': 'Change font',
        'choose_font': 'Choose font',
        'font': 'Font:',
        'font_standard': 'Standard',
        'font_current': 'installed now',
        'font_changed': 'Font changed. Chatter will restart.',
        'interface_settings': 'Interface settings',
        'change_theme': 'Change theme',
        'choose_theme': 'Choose theme',
        'theme': 'Theme:',
        'theme_black': 'Black (standard)',
        'theme_light': 'Light',
        'theme_coffee': 'Coffee',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Theme changed. Chatter will restart.',
        'voice_message': 'Voice message',
        'voice_recording': '🔴 Recording',
        'voice_too_short': 'Message is too short',
        'voice_cancel': 'Cancel recording',
        'you_suffix': '(you)',
        'offline_suffix': '(offline)',
        'rate_limited': 'Too many requests. Please wait.',
        'e2e_verify': '🔒 Verify encryption',
        'e2e_title': 'End-to-end encryption',
        'e2e_fingerprint':
            'Safety number with @{0}:\n\n{1}\n\n'
            'Compare this number with your contact '
            '(in person or via another channel). '
            'If they match — the conversation is '
            'protected from the server.',
        'e2e_unavailable':
            'End-to-end encryption is disabled. Install:\n'
            'pip install cryptography',
        'e2e_badge': '🔒 End-to-end encrypted',
        'e2e_decrypt_fail': '[Unable to decrypt]',
        'e2e_wait_key': 'Waiting for encryption key...',
        'e2e_notice': '🔒 End-to-end encrypted',
        'e2e_unverified': '⚠️ Encryption not verified',
        'e2e_confirm_match': 'Does the number match?',
        'e2e_marked_verified': 'Marked as verified',
        'e2e_marked_unverified': 'Marked as unverified',
        'empty_chat': 'Nothing here yet...',
        'creator_badge': 'Creator',
    },
    'zh': {
        'chats': '聊天', 'find_user': '🔍 查找用户',
        'select_chat': '选择要聊天的对象',
        'input_placeholder': '输入消息...', 'send': '发送',
        'settings': '设置', 'close': '关闭',
        'account_settings': '账户设置',
        'change_nick': '更改昵称', 'change_password': '更改密码',
        'fullscreen': '全屏 / 退出全屏', 'reconnect': '重新连接',
        'notifications': '通知:', 'language': '语言:',
        'delete_account': '删除账户', 'logout': '退出登录', 'exit': '退出',
        'username': '用户名:', 'password': '密码:',
        'first_name': '名 (可选):', 'last_name': '姓 (可选):',
        'confirm_password': '确认密码:', 'login': '登录',
        'register': '创建账户', 'login_tab': '登录',
        'register_tab': '注册', 'welcome': '欢迎!', 'online': '在线',
        'was_online': '最近在线', 'typing': '{0} 正在输入',
        'error': '错误', 'done': '完成', 'cancel': '取消', 'ok': '确定',
        'save': '保存', 'saved': '已保存',
        'connecting': '正在连接...', 'reconnecting': '正在重新连接...',
        'disconnected': '已断开', 'connect_fail': '连接失败',
        'search_title': '查找用户', 'search_placeholder': '姓名...',
        'search_btn': '搜索', 'searching': '搜索中...',
        'search_found': '找到: {0}', 'search_nothing': '未找到',
        'fill_both': '请填写两个字段', 'fill_all': '请填写所有必填字段',
        'passwords_dont_match': '密码不匹配',
        'password_min_6': '密码: 至少 6 个字符',
        'password_changed': '密码已更改', 'wrong_password': '密码错误',
        'user_not_found': '用户未找到',
        'name_taken': '此名称已被占用',
        'session_replaced': '您已从另一台设备登录。当前会话已结束。',
        'account_deleted': '账户已删除。您将退出登录。',
        'enter_old_password': '输入当前密码:',
        'enter_new_password': '输入新密码 (至少 6 字符):',
        'enter_new_password_again': '重复新密码:',
        'change_password_title': '更改密码',
        'change_nick_title': '更改昵称',
        'enter_new_nick': '输入新昵称:',
        'delete_account_warning': '账户及所有数据将被删除。\n继续?',
        'enter_password_confirm': '输入密码以确认:',
        'language_changed': '语言已更改。Chatter 将重新启动。',
        'choose_language': '选择语言', 'not_delivered': '未送达',
        'sending': '发送中...', 'sent_at': '发送于 {0}',
        'reply_to': '回复 @{0}: "{1}"', 'edit_message': '输入新文本:',
        'edit_message_title': '编辑消息', 'menu_reply': '回复',
        'menu_edit': '编辑', 'menu_delete': '删除',
        'menu_block': '屏蔽', 'menu_unblock': '取消屏蔽',
        'menu_delete_local': '为我删除', 'menu_dm': '私信',
        'menu_delete_chat': '删除',
        'changed_suffix': ' (已编辑)', 'left_chat': '{0} 离开了聊天',
        'joined_chat': '{0} 加入了聊天',
        'search_ip_btn': '找不到这个人?',
        'enter_ip_title': '通过 IP 连接',
        'enter_ip_text': '输入服务器 IP 地址:',
        'enter_ip_title2': '连接到服务器',
        'enter_ip_text2': '输入服务器 IP 地址:',
        'searching_by_ip': '在 {0} 搜索用户...',
        'attach': '附加文件', 'attach_file': '📎',
        'attachment': '附件', 'save_file': '保存文件',
        'open_file': '打开文件', 'file_saved': '文件已保存',
        'file_too_big': '文件过大 (最大 2 GB)',
        'upload_avatar': '上传头像',
        'avatar_saved': '头像已保存',
        'avatar_too_big': '头像过大 (最大 100 KB)',
        'send_file': '发送', 'user_blocked': '用户已屏蔽',
        'user_unblocked': '用户已取消屏蔽',
        'you_blocked': '你屏蔽了此用户',
        'blocked_warning': '你将不再收到 @{0} 的消息。\n屏蔽?',
        'delete_chat_warning': '删除与 @{0} 的对话?',
        'no_name': '无名称', 'restart_title': '重启',
        'restart_msg': 'Chatter 将重新启动以应用语言...',
        'restart_msg_font': 'Chatter 将重新启动以应用字体...',
        'restart_msg_theme': 'Chatter 将重新启动以应用主题...',
        'attach_too_big_short': '最大 2 GB',
        'call': '呼叫', 'call_title': '通话',
        'incoming_call': '来自 {0} 的来电',
        'calling_you': '{0} 正在呼叫你',
        'call_calling': '正在连接...',
        'call_ringing': '正在响铃...',
        'call_active': '通话中',
        'call_ended': '通话已结束',
        'call_rejected': '通话被拒绝',
        'call_busy': '用户忙',
        'call_timeout': '无应答',
        'call_peer_offline': '用户离线',
        'accept': '接听', 'reject': '拒绝',
        'hangup': '挂断', 'mute': '静音',
        'unmute': '取消静音',
        'no_audio_device': '无音频设备。请安装 sounddevice 和 numpy。',
        'call_self': '不能呼叫自己',
        'call_in_progress': '通话中不可用',
        'forward': '转发',
        'forward_title': '转发消息',
        'forward_choose': '选择聊天:',
        'forwarded_from': '转发自 @{0}',
        'forwarded': '已转发',
        'forward_no_chats': '没有可转发的聊天',
        'forward_empty': '没有可转发的内容',
        'change_font': '更改字体',
        'choose_font': '选择字体',
        'font': '字体:',
        'font_standard': '标准',
        'font_current': '当前使用',
        'font_changed': '字体已更改。Chatter 将重新启动。',
        'interface_settings': '界面设置',
        'change_theme': '更改主题',
        'choose_theme': '选择主题',
        'theme': '主题:',
        'theme_black': '黑色 (标准)',
        'theme_light': '浅色',
        'theme_coffee': '咖啡色',
        'theme_sakura': '樱花',
        'theme_changed': '主题已更改。Chatter 将重新启动。',
        'voice_message': '语音消息',
        'voice_recording': '🔴 录音中',
        'voice_too_short': '消息太短',
        'voice_cancel': '取消录音',
        'you_suffix': '(你)',
        'offline_suffix': '(离线)',
        'rate_limited': '请求过多。请稍后再试。',
        'e2e_verify': '🔒 验证加密',
        'e2e_title': '端到端加密',
        'e2e_fingerprint':
            '与 @{0} 的安全号码:\n\n{1}\n\n'
            '请与联系人核对这个号码。如果一致, 会话对服务器保密。',
        'e2e_unavailable':
            '端到端加密已禁用。请安装:\npip install cryptography',
        'e2e_badge': '🔒 端到端加密',
        'e2e_decrypt_fail': '[无法解密]',
        'e2e_wait_key': '等待加密密钥...',
        'e2e_notice': '🔒 端到端加密',
        'e2e_unverified': '⚠️ 加密未验证',
        'e2e_confirm_match': '号码匹配吗?',
        'e2e_marked_verified': '已标记为已验证',
        'e2e_marked_unverified': '已标记为未验证',
        'empty_chat': '这里还什么都没有...',
        'creator_badge': '创建者',
    },
    'hi': {
        'chats': 'चैट', 'find_user': '🔍 उपयोगकर्ता खोजें',
        'select_chat': 'किसे लिखना है चुनें',
        'input_placeholder': 'संदेश लिखें...', 'send': 'भेजें',
        'settings': 'सेटिंग्स', 'close': 'बंद करें',
        'account_settings': 'खाता सेटिंग्स',
        'change_nick': 'उपनाम बदलें', 'change_password': 'पासवर्ड बदलें',
        'fullscreen': 'पूर्ण स्क्रीन / बाहर निकलें', 'reconnect': 'पुनः कनेक्ट',
        'notifications': 'सूचनाएँ:', 'language': 'भाषा:',
        'delete_account': 'खाता हटाएँ', 'logout': 'लॉग आउट', 'exit': 'बाहर',
        'username': 'उपयोगकर्ता नाम:', 'password': 'पासवर्ड:',
        'first_name': 'पहला नाम (वैकल्पिक):',
        'last_name': 'अंतिम नाम (वैकल्पिक):',
        'confirm_password': 'पासवर्ड दोहराएँ:', 'login': 'लॉग इन',
        'register': 'खाता बनाएँ', 'login_tab': 'लॉग इन',
        'register_tab': 'रजिस्टर', 'welcome': 'स्वागत!', 'online': 'ऑनलाइन',
        'was_online': 'हाल ही में ऑनलाइन', 'typing': '{0} टाइप कर रहा है',
        'error': 'त्रुटि', 'done': 'हो गया', 'cancel': 'रद्द करें', 'ok': 'ठीक',
        'save': 'सहेजें', 'saved': 'सहेजा गया',
        'connecting': 'कनेक्ट हो रहा है...', 'reconnecting': 'पुनः कनेक्ट...',
        'disconnected': 'डिस्कनेक्ट', 'connect_fail': 'कनेक्ट नहीं हो सका',
        'search_title': 'उपयोगकर्ता खोजें', 'search_placeholder': 'नाम...',
        'search_btn': 'खोजें', 'searching': 'खोज रहे हैं...',
        'search_found': 'मिला: {0}', 'search_nothing': 'कुछ नहीं मिला',
        'fill_both': 'दोनों फ़ील्ड भरें',
        'fill_all': 'सभी आवश्यक फ़ील्ड भरें',
        'passwords_dont_match': 'पासवर्ड मेल नहीं खाते',
        'password_min_6': 'पासवर्ड: कम से कम 6 अक्षर',
        'password_changed': 'पासवर्ड बदला गया', 'wrong_password': 'गलत पासवर्ड',
        'user_not_found': 'उपयोगकर्ता नहीं मिला',
        'name_taken': 'यह नाम पहले से लिया है',
        'session_replaced': 'आपने दूसरी डिवाइस से लॉग इन किया। वर्तमान सत्र समाप्त।',
        'account_deleted': 'खाता हटा दिया। आप लॉग आउट हो जाएँगे।',
        'enter_old_password': 'वर्तमान पासवर्ड दर्ज करें:',
        'enter_new_password': 'नया पासवर्ड दर्ज करें (कम 6 अक्षर):',
        'enter_new_password_again': 'नया पासवर्ड दोहराएँ:',
        'change_password_title': 'पासवर्ड बदलें',
        'change_nick_title': 'उपनाम बदलें',
        'enter_new_nick': 'नया उपनाम दर्ज करें:',
        'delete_account_warning': 'खाता और सभी डेटा हटा दिए जाएँगे।\nजारी रखें?',
        'enter_password_confirm': 'पुष्टि के लिए पासवर्ड दर्ज करें:',
        'language_changed': 'भाषा बदली गई। Chatter पुनः आरंभ होगा।',
        'choose_language': 'भाषा चुनें', 'not_delivered': 'डिलीवर नहीं हुआ',
        'sending': 'भेजा जा रहा...', 'sent_at': '{0} पर भेजा',
        'reply_to': '@{0} को उत्तर: "{1}"', 'edit_message': 'नया टेक्स्ट दर्ज करें:',
        'edit_message_title': 'संदेश संपादित करें', 'menu_reply': 'उत्तर',
        'menu_edit': 'संपादित', 'menu_delete': 'हटाएँ',
        'menu_block': 'ब्लॉक', 'menu_unblock': 'अनब्लॉक',
        'menu_delete_local': 'मेरे लिए हटाएँ', 'menu_dm': 'निजी संदेश',
        'menu_delete_chat': 'हटाएँ',
        'changed_suffix': ' (संपादित)', 'left_chat': '{0} चैट छोड़ गया',
        'joined_chat': '{0} चैट में शामिल हुआ',
        'search_ip_btn': 'व्यक्ति नहीं मिल रहा?',
        'enter_ip_title': 'IP से कनेक्ट करें',
        'enter_ip_text': 'सर्वर IP पता दर्ज करें:',
        'enter_ip_title2': 'सर्वर से कनेक्ट करें',
        'enter_ip_text2': 'सर्वर IP पता दर्ज करें:',
        'searching_by_ip': '{0} पर लोग खोज रहे हैं...',
        'attach': 'फ़ाइल संलग्न करें', 'attach_file': '📎',
        'attachment': 'संलग्न', 'save_file': 'फ़ाइल सहेजें',
        'open_file': 'फ़ाइल खोलें', 'file_saved': 'फ़ाइल सहेजी गई',
        'file_too_big': 'फ़ाइल बहुत बड़ी (अधिकतम 2 GB)',
        'upload_avatar': 'अवतार अपलोड करें',
        'avatar_saved': 'अवतार सहेजा गया',
        'avatar_too_big': 'अवतार बहुत बड़ा (अधिकतम 100 KB)',
        'send_file': 'भेजें', 'user_blocked': 'उपयोगकर्ता ब्लॉक',
        'user_unblocked': 'उपयोगकर्ता अनब्लॉक',
        'you_blocked': 'आपने इस उपयोगकर्ता को ब्लॉक किया',
        'blocked_warning': 'आप @{0} से संदेश नहीं पाएँगे।\nब्लॉक?',
        'delete_chat_warning': '@{0} के साथ बातचीत हटाएँ?',
        'no_name': 'कोई नाम नहीं', 'restart_title': 'पुनः आरंभ',
        'restart_msg': 'भाषा लागू करने के लिए Chatter पुनः आरंभ होगा...',
        'restart_msg_font': 'फ़ॉन्ट लागू करने के लिए Chatter पुनः आरंभ होगा...',
        'attach_too_big_short': 'अधिकतम 2 GB',
        'call': 'कॉल', 'call_title': 'कॉल',
        'incoming_call': '{0} से आने वाला कॉल',
        'calling_you': '{0} आपको कॉल कर रहा है',
        'call_calling': 'कनेक्ट हो रहा...',
        'call_ringing': 'बज रहा है...',
        'call_active': 'कॉल में',
        'call_ended': 'कॉल समाप्त',
        'call_rejected': 'कॉल अस्वीकृत',
        'call_busy': 'उपयोगकर्ता व्यस्त',
        'call_timeout': 'कोई जवाब नहीं',
        'call_peer_offline': 'उपयोगकर्ता ऑफ़लाइन',
        'accept': 'स्वीकार', 'reject': 'अस्वीकार',
        'hangup': 'काटें', 'mute': 'म्यूट',
        'unmute': 'अनम्यूट',
        'no_audio_device': 'कोई ऑडियो डिवाइस नहीं। sounddevice और numpy स्थापित करें।',
        'call_self': 'आप स्वयं को कॉल नहीं कर सकते',
        'call_in_progress': 'कॉल के दौरान उपलब्ध नहीं',
        'forward': 'अग्रेषित',
        'forward_title': 'संदेश अग्रेषित करें',
        'forward_choose': 'चैट चुनें:',
        'forwarded_from': '@{0} से अग्रेषित',
        'forwarded': 'अग्रेषित',
        'forward_no_chats': 'अग्रेषित करने के लिए कोई चैट नहीं',
        'forward_empty': 'अग्रेषित करने के लिए कुछ नहीं',
        'change_font': 'फ़ॉन्ट बदलें',
        'choose_font': 'फ़ॉन्ट चुनें',
        'font': 'फ़ॉन्ट:',
        'font_standard': 'मानक',
        'font_current': 'अभी स्थापित',
        'font_changed': 'फ़ॉन्ट बदल गया। Chatter पुनः आरंभ होगा।',
        'interface_settings': 'इंटरफ़ेस सेटिंग्स',
        'change_theme': 'थीम बदलें',
        'choose_theme': 'थीम चुनें',
        'theme': 'थीम:',
        'theme_black': 'काला (मानक)',
        'theme_light': 'हल्का',
        'theme_coffee': 'कॉफ़ी',
        'theme_sakura': 'सकुरा',
        'theme_changed': 'थीम बदल गई। Chatter पुनः आरंभ होगा।',
        'voice_message': 'ध्वनि संदेश',
        'voice_recording': '🔴 रिकॉर्डिंग',
        'voice_too_short': 'संदेश बहुत छोटा',
        'voice_cancel': 'रिकॉर्डिंग रद्द करें',
        'you_suffix': '(आप)',
        'offline_suffix': '(ऑफ़लाइन)',
        'rate_limited': 'बहुत सारे अनुरोध। कृपया प्रतीक्षा करें।',
        'e2e_verify': '🔒 एन्क्रिप्शन सत्यापित करें',
        'e2e_title': 'एंड-टू-एंड एन्क्रिप्शन',
        'e2e_fingerprint':
            '@{0} के साथ सुरक्षा संख्या:\n\n{1}\n\n'
            'इस संख्या को संपर्क से मिलाएँ। मेल खाने पर '
            'बातचीत सर्वर से सुरक्षित है।',
        'e2e_unavailable':
            'एन्क्रिप्शन अक्षम। स्थापित करें:\npip install cryptography',
        'e2e_badge': '🔒 एंड-टू-एंड एन्क्रिप्टेड',
        'e2e_decrypt_fail': '[डिक्रिप्ट नहीं हो सका]',
        'e2e_wait_key': 'एन्क्रिप्शन कुंजी की प्रतीक्षा...',
        'e2e_notice': '🔒 एंड-टू-एंड एन्क्रिप्टेड',
        'e2e_unverified': '⚠️ एन्क्रिप्शन सत्यापित नहीं',
        'e2e_confirm_match': 'क्या संख्या मेल खाती है?',
        'e2e_marked_verified': 'सत्यापित के रूप में चिह्नित',
        'e2e_marked_unverified': 'असत्यापित के रूप में चिह्नित',
        'empty_chat': 'यहाँ अभी कुछ नहीं है...',
        'creator_badge': 'निर्माता',
    },
    'es': {
        'chats': 'Chats', 'find_user': '🔍 Buscar usuario',
        'select_chat': 'Selecciona a quién escribir',
        'input_placeholder': 'Escribe un mensaje...', 'send': 'Enviar',
        'settings': 'Ajustes', 'close': 'Cerrar',
        'account_settings': 'Ajustes de cuenta',
        'change_nick': 'Cambiar apodo', 'change_password': 'Cambiar contraseña',
        'fullscreen': 'Pantalla completa / Salir', 'reconnect': 'Reconectar',
        'notifications': 'Notificaciones:', 'language': 'Idioma:',
        'delete_account': 'Eliminar cuenta', 'logout': 'Cerrar sesión', 'exit': 'Salir',
        'username': 'Usuario:', 'password': 'Contraseña:',
        'first_name': 'Nombre (opcional):',
        'last_name': 'Apellido (opcional):',
        'confirm_password': 'Confirmar contraseña:', 'login': 'Iniciar sesión',
        'register': 'Crear cuenta', 'login_tab': 'Iniciar sesión',
        'register_tab': 'Registrarse', 'welcome': '¡Bienvenido!', 'online': 'En línea',
        'was_online': 'Recientemente en línea', 'typing': '{0} está escribiendo',
        'error': 'Error', 'done': 'Listo', 'cancel': 'Cancelar', 'ok': 'OK',
        'save': 'Guardar', 'saved': 'Guardado',
        'connecting': 'Conectando...', 'reconnecting': 'Reconectando...',
        'disconnected': 'Desconectado', 'connect_fail': 'No se pudo conectar',
        'search_title': 'Buscar usuario', 'search_placeholder': 'Nombre...',
        'search_btn': 'Buscar', 'searching': 'Buscando...',
        'search_found': 'Encontrados: {0}', 'search_nothing': 'Nada encontrado',
        'fill_both': 'Rellena ambos campos',
        'fill_all': 'Rellena todos los campos obligatorios',
        'passwords_dont_match': 'Las contraseñas no coinciden',
        'password_min_6': 'Contraseña: al menos 6 caracteres',
        'password_changed': 'Contraseña cambiada', 'wrong_password': 'Contraseña incorrecta',
        'user_not_found': 'Usuario no encontrado',
        'name_taken': 'Este nombre ya está en uso',
        'session_replaced': 'Iniciaste sesión desde otro dispositivo. Sesión actual finalizada.',
        'account_deleted': 'Cuenta eliminada. Se cerrará tu sesión.',
        'enter_old_password': 'Introduce la contraseña actual:',
        'enter_new_password': 'Introduce la nueva contraseña (mín 6):',
        'enter_new_password_again': 'Repite la nueva contraseña:',
        'change_password_title': 'Cambiar contraseña',
        'change_nick_title': 'Cambiar apodo',
        'enter_new_nick': 'Introduce el nuevo apodo:',
        'delete_account_warning': 'La cuenta y todos los datos serán eliminados.\n¿Continuar?',
        'enter_password_confirm': 'Introduce la contraseña para confirmar:',
        'language_changed': 'Idioma cambiado. Chatter se reiniciará.',
        'choose_language': 'Elegir idioma', 'not_delivered': 'No entregado',
        'sending': 'Enviando...', 'sent_at': 'Enviado a las {0}',
        'reply_to': 'Respondiendo a @{0}: "{1}"', 'edit_message': 'Introduce el nuevo texto:',
        'edit_message_title': 'Editar mensaje', 'menu_reply': 'Responder',
        'menu_edit': 'Editar', 'menu_delete': 'Eliminar',
        'menu_block': 'Bloquear', 'menu_unblock': 'Desbloquear',
        'menu_delete_local': 'Eliminar para mí', 'menu_dm': 'Mensaje privado',
        'menu_delete_chat': 'Eliminar',
        'changed_suffix': ' (editado)', 'left_chat': '{0} salió del chat',
        'joined_chat': '{0} se unió al chat',
        'search_ip_btn': '¿No encuentras a la persona?',
        'enter_ip_title': 'Conectar por IP',
        'enter_ip_text': 'Introduce la IP del servidor:',
        'enter_ip_title2': 'Conectar al servidor',
        'enter_ip_text2': 'Introduce la IP del servidor:',
        'searching_by_ip': 'Buscando personas en {0}...',
        'attach': 'Adjuntar archivo', 'attach_file': '📎',
        'attachment': 'Adjunto', 'save_file': 'Guardar archivo',
        'open_file': 'Abrir archivo', 'file_saved': 'Archivo guardado',
        'file_too_big': 'Archivo demasiado grande (máx 2 GB)',
        'upload_avatar': 'Subir avatar',
        'avatar_saved': 'Avatar guardado',
        'avatar_too_big': 'Avatar demasiado grande (máx 100 KB)',
        'send_file': 'Enviar', 'user_blocked': 'Usuario bloqueado',
        'user_unblocked': 'Usuario desbloqueado',
        'you_blocked': 'Bloqueaste a este usuario',
        'blocked_warning': 'Ya no recibirás mensajes de @{0}.\n¿Bloquear?',
        'delete_chat_warning': '¿Eliminar la conversación con @{0}?',
        'no_name': 'Sin nombre', 'restart_title': 'Reinicio',
        'restart_msg': 'Chatter se reiniciará para aplicar el idioma...',
        'restart_msg_font': 'Chatter se reiniciará para aplicar la fuente...',
        'attach_too_big_short': 'Máx 2 GB',
        'call': 'Llamar', 'call_title': 'Llamada',
        'incoming_call': 'Llamada entrante de {0}',
        'calling_you': '{0} te está llamando',
        'call_calling': 'Conectando...',
        'call_ringing': 'Sonando...',
        'call_active': 'En llamada',
        'call_ended': 'Llamada finalizada',
        'call_rejected': 'Llamada rechazada',
        'call_busy': 'Usuario ocupado',
        'call_timeout': 'Sin respuesta',
        'call_peer_offline': 'Usuario desconectado',
        'accept': 'Aceptar', 'reject': 'Rechazar',
        'hangup': 'Colgar', 'mute': 'Silenciar',
        'unmute': 'Activar micrófono',
        'no_audio_device': 'Sin dispositivo de audio. Instala sounddevice y numpy.',
        'call_self': 'No puedes llamarte a ti mismo',
        'call_in_progress': 'No disponible durante una llamada',
        'forward': 'Reenviar',
        'forward_title': 'Reenviar mensaje',
        'forward_choose': 'Elige un chat:',
        'forwarded_from': 'Reenviado de @{0}',
        'forwarded': 'Reenviado',
        'forward_no_chats': 'No hay chats para reenviar',
        'forward_empty': 'Nada que reenviar',
        'change_font': 'Cambiar fuente',
        'choose_font': 'Elegir fuente',
        'font': 'Fuente:',
        'font_standard': 'Predeterminada',
        'font_current': 'instalada ahora',
        'font_changed': 'Fuente cambiada. Chatter se reiniciará.',
        'interface_settings': 'Ajustes de interfaz',
        'change_theme': 'Cambiar tema',
        'choose_theme': 'Elegir tema',
        'theme': 'Tema:',
        'theme_black': 'Negro (estándar)',
        'theme_light': 'Claro',
        'theme_coffee': 'Café',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Tema cambiado. Chatter se reiniciará.',
        'voice_message': 'Mensaje de voz',
        'voice_recording': '🔴 Grabando',
        'voice_too_short': 'Mensaje demasiado corto',
        'voice_cancel': 'Cancelar grabación',
        'you_suffix': '(tú)',
        'offline_suffix': '(desconectado)',
        'rate_limited': 'Demasiadas solicitudes. Espera un momento.',
        'e2e_verify': '🔒 Verificar cifrado',
        'e2e_title': 'Cifrado de extremo a extremo',
        'e2e_fingerprint':
            'Número de seguridad con @{0}:\n\n{1}\n\n'
            'Compáralo con tu contacto. Si coinciden, '
            'la conversación está protegida del servidor.',
        'e2e_unavailable':
            'Cifrado deshabilitado. Instala:\npip install cryptography',
        'e2e_badge': '🔒 Cifrado extremo a extremo',
        'e2e_decrypt_fail': '[No se pudo descifrar]',
        'e2e_wait_key': 'Esperando clave de cifrado...',
        'e2e_notice': '🔒 Cifrado de extremo a extremo',
        'e2e_unverified': '⚠️ Cifrado sin verificar',
        'e2e_confirm_match': '¿Coincide el número?',
        'e2e_marked_verified': 'Marcado como verificado',
        'e2e_marked_unverified': 'Marcado como no verificado',
        'empty_chat': 'Aquí no hay nada todavía...',
        'creator_badge': 'Creador',
    },
    'ar': {
        'chats': 'المحادثات', 'find_user': '🔍 البحث عن مستخدم',
        'select_chat': 'اختر من تريد مراسلته',
        'input_placeholder': 'اكتب رسالة...', 'send': 'إرسال',
        'settings': 'الإعدادات', 'close': 'إغلاق',
        'account_settings': 'إعدادات الحساب',
        'change_nick': 'تغيير اللقب', 'change_password': 'تغيير كلمة المرور',
        'fullscreen': 'ملء الشاشة / خروج', 'reconnect': 'إعادة الاتصال',
        'notifications': 'الإشعارات:', 'language': 'اللغة:',
        'delete_account': 'حذف الحساب', 'logout': 'تسجيل الخروج', 'exit': 'خروج',
        'username': 'اسم المستخدم:', 'password': 'كلمة المرور:',
        'first_name': 'الاسم الأول (اختياري):',
        'last_name': 'اسم العائلة (اختياري):',
        'confirm_password': 'تأكيد كلمة المرور:', 'login': 'تسجيل الدخول',
        'register': 'إنشاء حساب', 'login_tab': 'تسجيل الدخول',
        'register_tab': 'التسجيل', 'welcome': 'مرحبًا!', 'online': 'متصل',
        'was_online': 'متصل مؤخرًا', 'typing': '{0} يكتب',
        'error': 'خطأ', 'done': 'تم', 'cancel': 'إلغاء', 'ok': 'موافق',
        'save': 'حفظ', 'saved': 'تم الحفظ',
        'connecting': 'جارٍ الاتصال...', 'reconnecting': 'جارٍ إعادة الاتصال...',
        'disconnected': 'انقطع الاتصال', 'connect_fail': 'فشل الاتصال',
        'search_title': 'البحث عن مستخدم', 'search_placeholder': 'الاسم...',
        'search_btn': 'بحث', 'searching': 'جارٍ البحث...',
        'search_found': 'النتائج: {0}', 'search_nothing': 'لا يوجد',
        'fill_both': 'املأ الحقلين',
        'fill_all': 'املأ جميع الحقول المطلوبة',
        'passwords_dont_match': 'كلمتا المرور غير متطابقتين',
        'password_min_6': 'كلمة المرور: 6 أحرف على الأقل',
        'password_changed': 'تم تغيير كلمة المرور', 'wrong_password': 'كلمة المرور خاطئة',
        'user_not_found': 'المستخدم غير موجود',
        'name_taken': 'هذا الاسم مستخدم بالفعل',
        'session_replaced': 'سجلت الدخول من جهاز آخر. انتهت الجلسة الحالية.',
        'account_deleted': 'تم حذف الحساب. سيتم تسجيل خروجك.',
        'enter_old_password': 'أدخل كلمة المرور الحالية:',
        'enter_new_password': 'أدخل كلمة المرور الجديدة (6 أحرف على الأقل):',
        'enter_new_password_again': 'كرر كلمة المرور الجديدة:',
        'change_password_title': 'تغيير كلمة المرور',
        'change_nick_title': 'تغيير اللقب',
        'enter_new_nick': 'أدخل اللقب الجديد:',
        'delete_account_warning': 'سيتم حذف الحساب وجميع البيانات.\nمتابعة؟',
        'enter_password_confirm': 'أدخل كلمة المرور للتأكيد:',
        'language_changed': 'تم تغيير اللغة. سيعاد تشغيل Chatter.',
        'choose_language': 'اختر اللغة', 'not_delivered': 'لم يتم التسليم',
        'sending': 'جارٍ الإرسال...', 'sent_at': 'أُرسلت في {0}',
        'reply_to': 'ردًا على @{0}: "{1}"', 'edit_message': 'أدخل النص الجديد:',
        'edit_message_title': 'تعديل الرسالة', 'menu_reply': 'رد',
        'menu_edit': 'تعديل', 'menu_delete': 'حذف',
        'menu_block': 'حظر', 'menu_unblock': 'إلغاء الحظر',
        'menu_delete_local': 'حذف عندي', 'menu_dm': 'رسالة خاصة',
        'menu_delete_chat': 'حذف',
        'changed_suffix': ' (تم التعديل)', 'left_chat': '{0} غادر المحادثة',
        'joined_chat': '{0} انضم إلى المحادثة',
        'search_ip_btn': 'لا تجد الشخص؟',
        'enter_ip_title': 'الاتصال عبر IP',
        'enter_ip_text': 'أدخل عنوان IP للخادم:',
        'enter_ip_title2': 'الاتصال بالخادم',
        'enter_ip_text2': 'أدخل عنوان IP للخادم:',
        'searching_by_ip': 'البحث عن أشخاص في {0}...',
        'attach': 'إرفاق ملف', 'attach_file': '📎',
        'attachment': 'مرفق', 'save_file': 'حفظ الملف',
        'open_file': 'فتح الملف', 'file_saved': 'تم حفظ الملف',
        'file_too_big': 'الملف كبير جدًا (2 جيجابايت كحد أقصى)',
        'upload_avatar': 'تحميل صورة شخصية',
        'avatar_saved': 'تم حفظ الصورة',
        'avatar_too_big': 'الصورة كبيرة جدًا (100 كيلوبايت كحد أقصى)',
        'send_file': 'إرسال', 'user_blocked': 'تم حظر المستخدم',
        'user_unblocked': 'تم إلغاء الحظر',
        'you_blocked': 'لقد حظرت هذا المستخدم',
        'blocked_warning': 'لن تستقبل رسائل من @{0}.\nحظر؟',
        'delete_chat_warning': 'حذف المحادثة مع @{0}؟',
        'no_name': 'بدون اسم', 'restart_title': 'إعادة التشغيل',
        'restart_msg': 'سيعاد تشغيل Chatter لتطبيق اللغة...',
        'restart_msg_font': 'سيعاد تشغيل Chatter لتطبيق الخط...',
        'attach_too_big_short': '2 جيجابايت كحد أقصى',
        'call': 'اتصال', 'call_title': 'مكالمة',
        'incoming_call': 'مكالمة واردة من {0}',
        'calling_you': '{0} يتصل بك',
        'call_calling': 'جارٍ الاتصال...',
        'call_ringing': 'جارٍ الرنين...',
        'call_active': 'في مكالمة',
        'call_ended': 'انتهت المكالمة',
        'call_rejected': 'تم رفض المكالمة',
        'call_busy': 'المستخدم مشغول',
        'call_timeout': 'لا يوجد رد',
        'call_peer_offline': 'المستخدم غير متصل',
        'accept': 'قبول', 'reject': 'رفض',
        'hangup': 'إنهاء', 'mute': 'كتم',
        'unmute': 'إلغاء الكتم',
        'no_audio_device': 'لا يوجد جهاز صوتي. ثبّت sounddevice و numpy.',
        'call_self': 'لا يمكنك الاتصال بنفسك',
        'call_in_progress': 'غير متاح أثناء المكالمة',
        'forward': 'إعادة توجيه',
        'forward_title': 'إعادة توجيه الرسالة',
        'forward_choose': 'اختر محادثة:',
        'forwarded_from': 'معاد توجيهها من @{0}',
        'forwarded': 'تمت إعادة التوجيه',
        'forward_no_chats': 'لا توجد محادثات لإعادة التوجيه',
        'forward_empty': 'لا شيء لإعادة توجيهه',
        'change_font': 'تغيير الخط',
        'choose_font': 'اختر الخط',
        'font': 'الخط:',
        'font_standard': 'افتراضي',
        'font_current': 'المثبت حالياً',
        'font_changed': 'تم تغيير الخط. سيعاد تشغيل Chatter.',
        'interface_settings': 'إعدادات الواجهة',
        'change_theme': 'تغيير السمة',
        'choose_theme': 'اختر السمة',
        'theme': 'السمة:',
        'theme_black': 'أسود (افتراضي)',
        'theme_light': 'فاتح',
        'theme_coffee': 'قهوي',
        'theme_sakura': 'ساكورا',
        'theme_changed': 'تم تغيير السمة. سيعاد تشغيل Chatter.',
        'voice_message': 'رسالة صوتية',
        'voice_recording': '🔴 تسجيل',
        'voice_too_short': 'الرسالة قصيرة جدًا',
        'voice_cancel': 'إلغاء التسجيل',
        'you_suffix': '(أنت)',
        'offline_suffix': '(غير متصل)',
        'rate_limited': 'طلبات كثيرة جدًا. الرجاء الانتظار.',
        'e2e_verify': '🔒 التحقق من التشفير',
        'e2e_title': 'التشفير من طرف إلى طرف',
        'e2e_fingerprint':
            'رقم الأمان مع @{0}:\n\n{1}\n\n'
            'قارن هذا الرقم مع جهة الاتصال. عند التطابق '
            'تكون المحادثة محمية من الخادم.',
        'e2e_unavailable':
            'التشفير معطل. ثبّت:\npip install cryptography',
        'e2e_badge': '🔒 مشفر من طرف إلى طرف',
        'e2e_decrypt_fail': '[تعذر فك التشفير]',
        'e2e_wait_key': 'في انتظار مفتاح التشفير...',
        'e2e_notice': '🔒 مشفر من طرف إلى طرف',
        'e2e_unverified': '⚠️ التشفير غير مؤكد',
        'e2e_confirm_match': 'هل الرقم متطابق؟',
        'e2e_marked_verified': 'تم وضع علامة موثق',
        'e2e_marked_unverified': 'تم وضع علامة غير موثق',
        'empty_chat': 'لا يوجد شيء هنا بعد...',
        'creator_badge': 'المنشئ',
    },
    'fr': {
        'chats': 'Discussions', 'find_user': '🔍 Trouver un utilisateur',
        'select_chat': 'Choisissez à qui écrire',
        'input_placeholder': 'Tapez un message...', 'send': 'Envoyer',
        'settings': 'Paramètres', 'close': 'Fermer',
        'account_settings': 'Paramètres du compte',
        'change_nick': 'Changer le pseudo', 'change_password': 'Changer le mot de passe',
        'fullscreen': 'Plein écran / Quitter', 'reconnect': 'Reconnecter',
        'notifications': 'Notifications :', 'language': 'Langue :',
        'delete_account': 'Supprimer le compte', 'logout': 'Déconnexion', 'exit': 'Quitter',
        'username': "Nom d'utilisateur :", 'password': 'Mot de passe :',
        'first_name': 'Prénom (facultatif) :',
        'last_name': 'Nom (facultatif) :',
        'confirm_password': 'Confirmer le mot de passe :', 'login': 'Se connecter',
        'register': 'Créer un compte', 'login_tab': 'Connexion',
        'register_tab': 'Inscription', 'welcome': 'Bienvenue !', 'online': 'En ligne',
        'was_online': 'Récemment en ligne', 'typing': "{0} est en train d'écrire",
        'error': 'Erreur', 'done': 'Terminé', 'cancel': 'Annuler', 'ok': 'OK',
        'save': 'Enregistrer', 'saved': 'Enregistré',
        'connecting': 'Connexion...', 'reconnecting': 'Reconnexion...',
        'disconnected': 'Déconnecté', 'connect_fail': 'Échec de la connexion',
        'search_title': 'Trouver un utilisateur', 'search_placeholder': 'Nom...',
        'search_btn': 'Rechercher', 'searching': 'Recherche...',
        'search_found': 'Trouvés : {0}', 'search_nothing': 'Aucun résultat',
        'fill_both': 'Remplissez les deux champs',
        'fill_all': 'Remplissez tous les champs obligatoires',
        'passwords_dont_match': 'Les mots de passe ne correspondent pas',
        'password_min_6': 'Mot de passe : au moins 6 caractères',
        'password_changed': 'Mot de passe modifié', 'wrong_password': 'Mot de passe incorrect',
        'user_not_found': 'Utilisateur introuvable',
        'name_taken': 'Ce nom est déjà pris',
        'session_replaced': 'Vous vous êtes connecté depuis un autre appareil. Session terminée.',
        'account_deleted': 'Compte supprimé. Vous serez déconnecté.',
        'enter_old_password': 'Entrez le mot de passe actuel :',
        'enter_new_password': 'Entrez le nouveau mot de passe (min 6) :',
        'enter_new_password_again': 'Répétez le nouveau mot de passe :',
        'change_password_title': 'Changer le mot de passe',
        'change_nick_title': 'Changer le pseudo',
        'enter_new_nick': 'Entrez le nouveau pseudo :',
        'delete_account_warning': 'Le compte et toutes les données seront supprimés.\nContinuer ?',
        'enter_password_confirm': 'Entrez le mot de passe pour confirmer :',
        'language_changed': 'Langue modifiée. Chatter va redémarrer.',
        'choose_language': 'Choisir la langue', 'not_delivered': 'Non distribué',
        'sending': 'Envoi...', 'sent_at': 'Envoyé à {0}',
        'reply_to': 'En réponse à @{0} : "{1}"', 'edit_message': 'Entrez le nouveau texte :',
        'edit_message_title': 'Modifier le message', 'menu_reply': 'Répondre',
        'menu_edit': 'Modifier', 'menu_delete': 'Supprimer',
        'menu_block': 'Bloquer', 'menu_unblock': 'Débloquer',
        'menu_delete_local': 'Supprimer pour moi', 'menu_dm': 'Message privé',
        'menu_delete_chat': 'Supprimer',
        'changed_suffix': ' (modifié)', 'left_chat': '{0} a quitté la discussion',
        'joined_chat': '{0} a rejoint la discussion',
        'search_ip_btn': 'Vous ne trouvez pas la personne ?',
        'enter_ip_title': 'Connexion par IP',
        'enter_ip_text': "Entrez l'adresse IP du serveur :",
        'enter_ip_title2': 'Se connecter au serveur',
        'enter_ip_text2': "Entrez l'adresse IP du serveur :",
        'searching_by_ip': 'Recherche de personnes à {0}...',
        'attach': 'Joindre un fichier', 'attach_file': '📎',
        'attachment': 'Pièce jointe', 'save_file': 'Enregistrer le fichier',
        'open_file': 'Ouvrir le fichier', 'file_saved': 'Fichier enregistré',
        'file_too_big': 'Fichier trop volumineux (max 2 Go)',
        'upload_avatar': 'Téléverser un avatar',
        'avatar_saved': 'Avatar enregistré',
        'avatar_too_big': 'Avatar trop volumineux (max 100 Ko)',
        'send_file': 'Envoyer', 'user_blocked': 'Utilisateur bloqué',
        'user_unblocked': 'Utilisateur débloqué',
        'you_blocked': 'Vous avez bloqué cet utilisateur',
        'blocked_warning': 'Vous ne recevrez plus de messages de @{0}.\nBloquer ?',
        'delete_chat_warning': 'Supprimer la conversation avec @{0} ?',
        'no_name': 'Sans nom', 'restart_title': 'Redémarrage',
        'restart_msg': 'Chatter va redémarrer pour appliquer la langue...',
        'restart_msg_font': 'Chatter va redémarrer pour appliquer la police...',
        'attach_too_big_short': 'Max 2 Go',
        'call': 'Appeler', 'call_title': 'Appel',
        'incoming_call': 'Appel entrant de {0}',
        'calling_you': '{0} vous appelle',
        'call_calling': 'Connexion...',
        'call_ringing': 'Sonnerie...',
        'call_active': 'En appel',
        'call_ended': 'Appel terminé',
        'call_rejected': 'Appel refusé',
        'call_busy': 'Utilisateur occupé',
        'call_timeout': 'Pas de réponse',
        'call_peer_offline': 'Utilisateur hors ligne',
        'accept': 'Accepter', 'reject': 'Refuser',
        'hangup': 'Raccrocher', 'mute': 'Muet',
        'unmute': 'Activer micro',
        'no_audio_device': 'Aucun périphérique audio. Installez sounddevice et numpy.',
        'call_self': 'Vous ne pouvez pas vous appeler',
        'call_in_progress': 'Indisponible pendant un appel',
        'forward': 'Transférer',
        'forward_title': 'Transférer le message',
        'forward_choose': 'Choisissez une discussion :',
        'forwarded_from': 'Transféré de @{0}',
        'forwarded': 'Transféré',
        'forward_no_chats': 'Aucune discussion pour transférer',
        'forward_empty': 'Rien à transférer',
        'change_font': 'Changer la police',
        'choose_font': 'Choisir la police',
        'font': 'Police :',
        'font_standard': 'Standard',
        'font_current': 'installée',
        'font_changed': 'Police modifiée. Chatter va redémarrer.',
        'interface_settings': "Paramètres d'interface",
        'change_theme': 'Changer le thème',
        'choose_theme': 'Choisir le thème',
        'theme': 'Thème :',
        'theme_black': 'Noir (standard)',
        'theme_light': 'Clair',
        'theme_coffee': 'Café',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Thème modifié. Chatter va redémarrer.',
        'voice_message': 'Message vocal',
        'voice_recording': '🔴 Enregistrement',
        'voice_too_short': 'Message trop court',
        'voice_cancel': "Annuler l'enregistrement",
        'you_suffix': '(vous)',
        'offline_suffix': '(hors ligne)',
        'rate_limited': 'Trop de requêtes. Veuillez patienter.',
        'e2e_verify': '🔒 Vérifier le chiffrement',
        'e2e_title': 'Chiffrement de bout en bout',
        'e2e_fingerprint':
            'Numéro de sécurité avec @{0} :\n\n{1}\n\n'
            'Comparez ce numéro avec votre contact. '
            "S'ils correspondent, la conversation est "
            'protégée du serveur.',
        'e2e_unavailable':
            'Chiffrement désactivé. Installez :\npip install cryptography',
        'e2e_badge': '🔒 Chiffré de bout en bout',
        'e2e_decrypt_fail': '[Impossible de déchiffrer]',
        'e2e_wait_key': 'En attente de la clé de chiffrement...',
        'e2e_notice': '🔒 Chiffrement de bout en bout',
        'e2e_unverified': '⚠️ Chiffrement non vérifié',
        'e2e_confirm_match': 'Le numéro correspond-il ?',
        'e2e_marked_verified': 'Marqué comme vérifié',
        'e2e_marked_unverified': 'Marqué comme non vérifié',
        'empty_chat': 'Rien ici pour le moment...',
        'creator_badge': 'Créateur',
    },
    'bn': {
        'chats': 'চ্যাট', 'find_user': '🔍 ব্যবহারকারী খুঁজুন',
        'select_chat': 'কার কাছে লিখবেন নির্বাচন করুন',
        'input_placeholder': 'বার্তা লিখুন...', 'send': 'পাঠান',
        'settings': 'সেটিংস', 'close': 'বন্ধ',
        'account_settings': 'অ্যাকাউন্ট সেটিংস',
        'change_nick': 'ডাকনাম পরিবর্তন', 'change_password': 'পাসওয়ার্ড পরিবর্তন',
        'fullscreen': 'ফুলস্ক্রিন / প্রস্থান', 'reconnect': 'পুনঃসংযোগ',
        'notifications': 'বিজ্ঞপ্তি:', 'language': 'ভাষা:',
        'delete_account': 'অ্যাকাউন্ট মুছুন', 'logout': 'লগ আউট', 'exit': 'প্রস্থান',
        'username': 'ব্যবহারকারীর নাম:', 'password': 'পাসওয়ার্ড:',
        'first_name': 'প্রথম নাম (ঐচ্ছিক):',
        'last_name': 'শেষ নাম (ঐচ্ছিক):',
        'confirm_password': 'পাসওয়ার্ড নিশ্চিত করুন:', 'login': 'লগ ইন',
        'register': 'অ্যাকাউন্ট তৈরি', 'login_tab': 'লগ ইন',
        'register_tab': 'নিবন্ধন', 'welcome': 'স্বাগতম!', 'online': 'অনলাইন',
        'was_online': 'সম্প্রতি অনলাইন', 'typing': '{0} লিখছে',
        'error': 'ত্রুটি', 'done': 'সম্পন্ন', 'cancel': 'বাতিল', 'ok': 'ঠিক আছে',
        'save': 'সংরক্ষণ', 'saved': 'সংরক্ষিত',
        'connecting': 'সংযোগ হচ্ছে...', 'reconnecting': 'পুনঃসংযোগ...',
        'disconnected': 'সংযোগ বিচ্ছিন্ন', 'connect_fail': 'সংযোগ ব্যর্থ',
        'search_title': 'ব্যবহারকারী খুঁজুন', 'search_placeholder': 'নাম...',
        'search_btn': 'খুঁজুন', 'searching': 'খোঁজা হচ্ছে...',
        'search_found': 'পাওয়া গেছে: {0}', 'search_nothing': 'কিছু পাওয়া যায়নি',
        'fill_both': 'উভয় ঘর পূরণ করুন',
        'fill_all': 'সমস্ত প্রয়োজনীয় ঘর পূরণ করুন',
        'passwords_dont_match': 'পাসওয়ার্ড মিলছে না',
        'password_min_6': 'পাসওয়ার্ড: কমপক্ষে ৬ অক্ষর',
        'password_changed': 'পাসওয়ার্ড পরিবর্তিত', 'wrong_password': 'ভুল পাসওয়ার্ড',
        'user_not_found': 'ব্যবহারকারী পাওয়া যায়নি',
        'name_taken': 'এই নাম ইতিমধ্যে নেওয়া',
        'session_replaced': 'অন্য ডিভাইস থেকে লগ ইন করেছেন। বর্তমান সেশন শেষ।',
        'account_deleted': 'অ্যাকাউন্ট মুছে ফেলা হয়েছে। লগ আউট হবেন।',
        'enter_old_password': 'বর্তমান পাসওয়ার্ড দিন:',
        'enter_new_password': 'নতুন পাসওয়ার্ড দিন (সর্বনিম্ন ৬ অক্ষর):',
        'enter_new_password_again': 'নতুন পাসওয়ার্ড পুনরায় দিন:',
        'change_password_title': 'পাসওয়ার্ড পরিবর্তন',
        'change_nick_title': 'ডাকনাম পরিবর্তন',
        'enter_new_nick': 'নতুন ডাকনাম দিন:',
        'delete_account_warning': 'অ্যাকাউন্ট এবং সমস্ত ডেটা মুছে ফেলা হবে।\nচালিয়ে যাবেন?',
        'enter_password_confirm': 'নিশ্চিত করতে পাসওয়ার্ড দিন:',
        'language_changed': 'ভাষা পরিবর্তিত। Chatter পুনরায় চালু হবে।',
        'choose_language': 'ভাষা নির্বাচন করুন', 'not_delivered': 'বিতরণ হয়নি',
        'sending': 'পাঠানো হচ্ছে...', 'sent_at': '{0}-এ পাঠানো হয়েছে',
        'reply_to': '@{0} কে উত্তর: "{1}"', 'edit_message': 'নতুন টেক্সট দিন:',
        'edit_message_title': 'বার্তা সম্পাদনা', 'menu_reply': 'উত্তর',
        'menu_edit': 'সম্পাদনা', 'menu_delete': 'মুছুন',
        'menu_block': 'ব্লক', 'menu_unblock': 'আনব্লক',
        'menu_delete_local': 'আমার থেকে মুছুন', 'menu_dm': 'ব্যক্তিগত বার্তা',
        'menu_delete_chat': 'মুছুন',
        'changed_suffix': ' (সম্পাদিত)', 'left_chat': '{0} চ্যাট ত্যাগ করেছেন',
        'joined_chat': '{0} চ্যাটে যোগ দিয়েছেন',
        'search_ip_btn': 'ব্যক্তিকে খুঁজে পাচ্ছেন না?',
        'enter_ip_title': 'IP দ্বারা সংযোগ',
        'enter_ip_text': 'সার্ভার IP ঠিকানা দিন:',
        'enter_ip_title2': 'সার্ভারে সংযোগ',
        'enter_ip_text2': 'সার্ভার IP ঠিকানা দিন:',
        'searching_by_ip': '{0}-এ মানুষ খোঁজা হচ্ছে...',
        'attach': 'ফাইল সংযুক্ত করুন', 'attach_file': '📎',
        'attachment': 'সংযুক্তি', 'save_file': 'ফাইল সংরক্ষণ',
        'open_file': 'ফাইল খুলুন', 'file_saved': 'ফাইল সংরক্ষিত',
        'file_too_big': 'ফাইল খুব বড় (সর্বোচ্চ ২ জিবি)',
        'upload_avatar': 'অ্যাভাটার আপলোড',
        'avatar_saved': 'অ্যাভাটার সংরক্ষিত',
        'avatar_too_big': 'অ্যাভাটার খুব বড় (সর্বোচ্চ ১০০ কেবি)',
        'send_file': 'পাঠান', 'user_blocked': 'ব্যবহারকারী ব্লকড',
        'user_unblocked': 'ব্যবহারকারী আনব্লকড',
        'you_blocked': 'আপনি এই ব্যবহারকারীকে ব্লক করেছেন',
        'blocked_warning': '@{0} থেকে আর বার্তা পাবেন না।\nব্লক করবেন?',
        'delete_chat_warning': '@{0}-এর সাথে কথোপকথন মুছবেন?',
        'no_name': 'নাম নেই', 'restart_title': 'পুনরায় চালু',
        'restart_msg': 'ভাষা প্রয়োগের জন্য Chatter পুনরায় চালু হবে...',
        'restart_msg_font': 'ফন্ট প্রয়োগের জন্য Chatter পুনরায় চালু হবে...',
        'attach_too_big_short': 'সর্বোচ্চ ২ জিবি',
        'call': 'কল', 'call_title': 'কল',
        'incoming_call': '{0} থেকে ইনকামিং কল',
        'calling_you': '{0} আপনাকে কল করছেন',
        'call_calling': 'সংযোগ হচ্ছে...',
        'call_ringing': 'বাজছে...',
        'call_active': 'কলে',
        'call_ended': 'কল শেষ',
        'call_rejected': 'কল প্রত্যাখ্যাত',
        'call_busy': 'ব্যবহারকারী ব্যস্ত',
        'call_timeout': 'কোনো উত্তর নেই',
        'call_peer_offline': 'ব্যবহারকারী অফলাইন',
        'accept': 'গ্রহণ', 'reject': 'প্রত্যাখ্যান',
        'hangup': 'কেটে দিন', 'mute': 'নিঃশব্দ',
        'unmute': 'আনমিউট',
        'no_audio_device': 'কোনো অডিও ডিভাইস নেই। sounddevice এবং numpy ইনস্টল করুন।',
        'call_self': 'নিজেকে কল করতে পারবেন না',
        'call_in_progress': 'কলের সময় উপলব্ধ নয়',
        'forward': 'ফরওয়ার্ড',
        'forward_title': 'বার্তা ফরওয়ার্ড',
        'forward_choose': 'একটি চ্যাট চয়ন করুন:',
        'forwarded_from': '@{0} থেকে ফরওয়ার্ড',
        'forwarded': 'ফরওয়ার্ড করা হয়েছে',
        'forward_no_chats': 'ফরওয়ার্ডের জন্য কোনো চ্যাট নেই',
        'forward_empty': 'ফরওয়ার্ড করার কিছু নেই',
        'change_font': 'ফন্ট পরিবর্তন',
        'choose_font': 'ফন্ট নির্বাচন',
        'font': 'ফন্ট:',
        'font_standard': 'স্ট্যান্ডার্ড',
        'font_current': 'বর্তমানে সেট',
        'font_changed': 'ফন্ট পরিবর্তিত। Chatter পুনরায় চালু হবে।',
        'interface_settings': 'ইন্টারফেস সেটিংস',
        'change_theme': 'থিম পরিবর্তন',
        'choose_theme': 'থিম নির্বাচন',
        'theme': 'থিম:',
        'theme_black': 'কালো (স্ট্যান্ডার্ড)',
        'theme_light': 'হালকা',
        'theme_coffee': 'কফি',
        'theme_sakura': 'সাকুরা',
        'theme_changed': 'থিম পরিবর্তিত। Chatter পুনরায় চালু হবে।',
        'voice_message': 'ভয়েস বার্তা',
        'voice_recording': '🔴 রেকর্ডিং',
        'voice_too_short': 'বার্তা খুব ছোট',
        'voice_cancel': 'রেকর্ডিং বাতিল করুন',
        'you_suffix': '(আপনি)',
        'offline_suffix': '(অফলাইন)',
        'rate_limited': 'অনেক অনুরোধ। অপেক্ষা করুন।',
        'e2e_verify': '🔒 এনক্রিপশন যাচাই করুন',
        'e2e_title': 'এন্ড-টু-এন্ড এনক্রিপশন',
        'e2e_fingerprint':
            '@{0} এর সাথে সুরক্ষা নম্বর:\n\n{1}\n\n'
            'এই নম্বরটি যোগাযোগের সাথে মেলান। মিলে গেলে '
            'কথোপকথন সার্ভার থেকে সুরক্ষিত।',
        'e2e_unavailable':
            'এনক্রিপশন নিষ্ক্রিয়। ইনস্টল করুন:\npip install cryptography',
        'e2e_badge': '🔒 এন্ড-টু-এন্ড এনক্রিপ্টেড',
        'e2e_decrypt_fail': '[ডিক্রিপ্ট করা যায়নি]',
        'e2e_wait_key': 'এনক্রিপশন কী-এর জন্য অপেক্ষা...',
        'e2e_notice': '🔒 এন্ড-টু-এন্ড এনক্রিপ্টেড',
        'e2e_unverified': '⚠️ এনক্রিপশন যাচাই হয়নি',
        'e2e_confirm_match': 'নম্বর কি মিলছে?',
        'e2e_marked_verified': 'যাচাইকৃত হিসাবে চিহ্নিত',
        'e2e_marked_unverified': 'অযাচাইকৃত হিসাবে চিহ্নিত',
        'empty_chat': 'এখানে এখনো কিছু নেই...',
        'creator_badge': 'নির্মাতা',
    },
    'pt': {
        'chats': 'Conversas', 'find_user': '🔍 Procurar usuário',
        'select_chat': 'Escolha para quem escrever',
        'input_placeholder': 'Digite uma mensagem...', 'send': 'Enviar',
        'settings': 'Configurações', 'close': 'Fechar',
        'account_settings': 'Configurações da conta',
        'change_nick': 'Mudar apelido', 'change_password': 'Mudar senha',
        'fullscreen': 'Tela cheia / Sair', 'reconnect': 'Reconectar',
        'notifications': 'Notificações:', 'language': 'Idioma:',
        'delete_account': 'Excluir conta', 'logout': 'Sair', 'exit': 'Sair',
        'username': 'Usuário:', 'password': 'Senha:',
        'first_name': 'Nome (opcional):',
        'last_name': 'Sobrenome (opcional):',
        'confirm_password': 'Confirmar senha:', 'login': 'Entrar',
        'register': 'Criar conta', 'login_tab': 'Entrar',
        'register_tab': 'Registrar', 'welcome': 'Bem-vindo!', 'online': 'Online',
        'was_online': 'Recentemente online', 'typing': '{0} está digitando',
        'error': 'Erro', 'done': 'Pronto', 'cancel': 'Cancelar', 'ok': 'OK',
        'save': 'Salvar', 'saved': 'Salvo',
        'connecting': 'Conectando...', 'reconnecting': 'Reconectando...',
        'disconnected': 'Desconectado', 'connect_fail': 'Falha ao conectar',
        'search_title': 'Procurar usuário', 'search_placeholder': 'Nome...',
        'search_btn': 'Procurar', 'searching': 'Procurando...',
        'search_found': 'Encontrados: {0}', 'search_nothing': 'Nada encontrado',
        'fill_both': 'Preencha os dois campos',
        'fill_all': 'Preencha todos os campos obrigatórios',
        'passwords_dont_match': 'As senhas não coincidem',
        'password_min_6': 'Senha: pelo menos 6 caracteres',
        'password_changed': 'Senha alterada', 'wrong_password': 'Senha incorreta',
        'user_not_found': 'Usuário não encontrado',
        'name_taken': 'Este nome já está em uso',
        'session_replaced': 'Você entrou de outro dispositivo. Sessão atual encerrada.',
        'account_deleted': 'Conta excluída. Você será desconectado.',
        'enter_old_password': 'Digite a senha atual:',
        'enter_new_password': 'Digite a nova senha (mín 6):',
        'enter_new_password_again': 'Repita a nova senha:',
        'change_password_title': 'Mudar senha',
        'change_nick_title': 'Mudar apelido',
        'enter_new_nick': 'Digite o novo apelido:',
        'delete_account_warning': 'A conta e todos os dados serão excluídos.\nContinuar?',
        'enter_password_confirm': 'Digite a senha para confirmar:',
        'language_changed': 'Idioma alterado. Chatter será reiniciado.',
        'choose_language': 'Escolher idioma', 'not_delivered': 'Não entregue',
        'sending': 'Enviando...', 'sent_at': 'Enviado às {0}',
        'reply_to': 'Respondendo a @{0}: "{1}"', 'edit_message': 'Digite o novo texto:',
        'edit_message_title': 'Editar mensagem', 'menu_reply': 'Responder',
        'menu_edit': 'Editar', 'menu_delete': 'Excluir',
        'menu_block': 'Bloquear', 'menu_unblock': 'Desbloquear',
        'menu_delete_local': 'Excluir para mim', 'menu_dm': 'Mensagem privada',
        'menu_delete_chat': 'Excluir',
        'changed_suffix': ' (editado)', 'left_chat': '{0} saiu da conversa',
        'joined_chat': '{0} entrou na conversa',
        'search_ip_btn': 'Não encontra a pessoa?',
        'enter_ip_title': 'Conectar por IP',
        'enter_ip_text': 'Digite o IP do servidor:',
        'enter_ip_title2': 'Conectar ao servidor',
        'enter_ip_text2': 'Digite o IP do servidor:',
        'searching_by_ip': 'Procurando pessoas em {0}...',
        'attach': 'Anexar arquivo', 'attach_file': '📎',
        'attachment': 'Anexo', 'save_file': 'Salvar arquivo',
        'open_file': 'Abrir arquivo', 'file_saved': 'Arquivo salvo',
        'file_too_big': 'Arquivo muito grande (máx 2 GB)',
        'upload_avatar': 'Enviar avatar',
        'avatar_saved': 'Avatar salvo',
        'avatar_too_big': 'Avatar muito grande (máx 100 KB)',
        'send_file': 'Enviar', 'user_blocked': 'Usuário bloqueado',
        'user_unblocked': 'Usuário desbloqueado',
        'you_blocked': 'Você bloqueou este usuário',
        'blocked_warning': 'Você não receberá mais mensagens de @{0}.\nBloquear?',
        'delete_chat_warning': 'Excluir conversa com @{0}?',
        'no_name': 'Sem nome', 'restart_title': 'Reiniciar',
        'restart_msg': 'Chatter será reiniciado para aplicar o idioma...',
        'restart_msg_font': 'Chatter será reiniciado para aplicar a fonte...',
        'attach_too_big_short': 'Máx 2 GB',
        'call': 'Ligar', 'call_title': 'Chamada',
        'incoming_call': 'Chamada de {0}',
        'calling_you': '{0} está ligando',
        'call_calling': 'Conectando...',
        'call_ringing': 'Chamando...',
        'call_active': 'Em chamada',
        'call_ended': 'Chamada encerrada',
        'call_rejected': 'Chamada rejeitada',
        'call_busy': 'Usuário ocupado',
        'call_timeout': 'Sem resposta',
        'call_peer_offline': 'Usuário offline',
        'accept': 'Aceitar', 'reject': 'Rejeitar',
        'hangup': 'Desligar', 'mute': 'Mudo',
        'unmute': 'Ativar microfone',
        'no_audio_device': 'Sem dispositivo de áudio. Instale sounddevice e numpy.',
        'call_self': 'Você não pode ligar para si mesmo',
        'call_in_progress': 'Indisponível durante uma chamada',
        'forward': 'Encaminhar',
        'forward_title': 'Encaminhar mensagem',
        'forward_choose': 'Escolha uma conversa:',
        'forwarded_from': 'Encaminhada de @{0}',
        'forwarded': 'Encaminhada',
        'forward_no_chats': 'Nenhuma conversa para encaminhar',
        'forward_empty': 'Nada para encaminhar',
        'change_font': 'Mudar fonte',
        'choose_font': 'Escolher fonte',
        'font': 'Fonte:',
        'font_standard': 'Padrão',
        'font_current': 'instalada agora',
        'font_changed': 'Fonte alterada. Chatter será reiniciado.',
        'interface_settings': 'Configurações de interface',
        'change_theme': 'Mudar tema',
        'choose_theme': 'Escolher tema',
        'theme': 'Tema:',
        'theme_black': 'Preto (padrão)',
        'theme_light': 'Claro',
        'theme_coffee': 'Café',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Tema alterado. Chatter será reiniciado.',
        'voice_message': 'Mensagem de voz',
        'voice_recording': '🔴 Gravando',
        'voice_too_short': 'Mensagem muito curta',
        'voice_cancel': 'Cancelar gravação',
        'you_suffix': '(você)',
        'offline_suffix': '(offline)',
        'rate_limited': 'Muitas solicitações. Aguarde um momento.',
        'e2e_verify': '🔒 Verificar criptografia',
        'e2e_title': 'Criptografia ponta a ponta',
        'e2e_fingerprint':
            'Número de segurança com @{0}:\n\n{1}\n\n'
            'Compare este número com seu contato. Se '
            'coincidirem, a conversa está protegida do servidor.',
        'e2e_unavailable':
            'Criptografia desativada. Instale:\npip install cryptography',
        'e2e_badge': '🔒 Criptografado ponta a ponta',
        'e2e_decrypt_fail': '[Não foi possível descriptografar]',
        'e2e_wait_key': 'Aguardando chave de criptografia...',
        'e2e_notice': '🔒 Criptografia ponta a ponta',
        'e2e_unverified': '⚠️ Criptografia não verificada',
        'e2e_confirm_match': 'O número coincide?',
        'e2e_marked_verified': 'Marcado como verificado',
        'e2e_marked_unverified': 'Marcado como não verificado',
        'empty_chat': 'Nada aqui ainda...',
        'creator_badge': 'Criador',
    },
    'id': {
        'chats': 'Obrolan', 'find_user': '🔍 Cari pengguna',
        'select_chat': 'Pilih siapa yang ingin Anda kirimi',
        'input_placeholder': 'Ketik pesan...', 'send': 'Kirim',
        'settings': 'Pengaturan', 'close': 'Tutup',
        'account_settings': 'Pengaturan akun',
        'change_nick': 'Ubah nama panggilan', 'change_password': 'Ubah kata sandi',
        'fullscreen': 'Layar penuh / Keluar', 'reconnect': 'Sambung ulang',
        'notifications': 'Notifikasi:', 'language': 'Bahasa:',
        'delete_account': 'Hapus akun', 'logout': 'Keluar', 'exit': 'Keluar',
        'username': 'Nama pengguna:', 'password': 'Kata sandi:',
        'first_name': 'Nama depan (opsional):',
        'last_name': 'Nama belakang (opsional):',
        'confirm_password': 'Konfirmasi kata sandi:', 'login': 'Masuk',
        'register': 'Buat akun', 'login_tab': 'Masuk',
        'register_tab': 'Daftar', 'welcome': 'Selamat datang!', 'online': 'Online',
        'was_online': 'Baru-baru ini online', 'typing': '{0} sedang mengetik',
        'error': 'Kesalahan', 'done': 'Selesai', 'cancel': 'Batal', 'ok': 'OK',
        'save': 'Simpan', 'saved': 'Tersimpan',
        'connecting': 'Menghubungkan...', 'reconnecting': 'Menyambung ulang...',
        'disconnected': 'Terputus', 'connect_fail': 'Gagal terhubung',
        'search_title': 'Cari pengguna', 'search_placeholder': 'Nama...',
        'search_btn': 'Cari', 'searching': 'Mencari...',
        'search_found': 'Ditemukan: {0}', 'search_nothing': 'Tidak ada',
        'fill_both': 'Isi kedua kolom',
        'fill_all': 'Isi semua kolom wajib',
        'passwords_dont_match': 'Kata sandi tidak cocok',
        'password_min_6': 'Kata sandi: minimal 6 karakter',
        'password_changed': 'Kata sandi diubah', 'wrong_password': 'Kata sandi salah',
        'user_not_found': 'Pengguna tidak ditemukan',
        'name_taken': 'Nama ini sudah dipakai',
        'session_replaced': 'Anda masuk dari perangkat lain. Sesi saat ini berakhir.',
        'account_deleted': 'Akun dihapus. Anda akan keluar.',
        'enter_old_password': 'Masukkan kata sandi saat ini:',
        'enter_new_password': 'Masukkan kata sandi baru (min 6):',
        'enter_new_password_again': 'Ulangi kata sandi baru:',
        'change_password_title': 'Ubah kata sandi',
        'change_nick_title': 'Ubah nama panggilan',
        'enter_new_nick': 'Masukkan nama panggilan baru:',
        'delete_account_warning': 'Akun dan semua data akan dihapus.\nLanjutkan?',
        'enter_password_confirm': 'Masukkan kata sandi untuk konfirmasi:',
        'language_changed': 'Bahasa diubah. Chatter akan dimulai ulang.',
        'choose_language': 'Pilih bahasa', 'not_delivered': 'Tidak terkirim',
        'sending': 'Mengirim...', 'sent_at': 'Terkirim pukul {0}',
        'reply_to': 'Membalas @{0}: "{1}"', 'edit_message': 'Masukkan teks baru:',
        'edit_message_title': 'Edit pesan', 'menu_reply': 'Balas',
        'menu_edit': 'Edit', 'menu_delete': 'Hapus',
        'menu_block': 'Blokir', 'menu_unblock': 'Buka blokir',
        'menu_delete_local': 'Hapus untuk saya', 'menu_dm': 'Pesan pribadi',
        'menu_delete_chat': 'Hapus',
        'changed_suffix': ' (diedit)', 'left_chat': '{0} meninggalkan obrolan',
        'joined_chat': '{0} bergabung ke obrolan',
        'search_ip_btn': 'Tidak menemukan orangnya?',
        'enter_ip_title': 'Hubungkan lewat IP',
        'enter_ip_text': 'Masukkan alamat IP server:',
        'enter_ip_title2': 'Hubungkan ke server',
        'enter_ip_text2': 'Masukkan alamat IP server:',
        'searching_by_ip': 'Mencari orang di {0}...',
        'attach': 'Lampirkan file', 'attach_file': '📎',
        'attachment': 'Lampiran', 'save_file': 'Simpan file',
        'open_file': 'Buka file', 'file_saved': 'File tersimpan',
        'file_too_big': 'File terlalu besar (maks 2 GB)',
        'upload_avatar': 'Unggah avatar',
        'avatar_saved': 'Avatar tersimpan',
        'avatar_too_big': 'Avatar terlalu besar (maks 100 KB)',
        'send_file': 'Kirim', 'user_blocked': 'Pengguna diblokir',
        'user_unblocked': 'Blokir pengguna dibuka',
        'you_blocked': 'Anda memblokir pengguna ini',
        'blocked_warning': 'Anda tidak akan menerima pesan dari @{0}.\nBlokir?',
        'delete_chat_warning': 'Hapus percakapan dengan @{0}?',
        'no_name': 'Tanpa nama', 'restart_title': 'Mulai ulang',
        'restart_msg': 'Chatter akan dimulai ulang untuk menerapkan bahasa...',
        'restart_msg_font': 'Chatter akan dimulai ulang untuk menerapkan font...',
        'attach_too_big_short': 'Maks 2 GB',
        'call': 'Panggil', 'call_title': 'Panggilan',
        'incoming_call': 'Panggilan masuk dari {0}',
        'calling_you': '{0} menelepon Anda',
        'call_calling': 'Menghubungkan...',
        'call_ringing': 'Berdering...',
        'call_active': 'Dalam panggilan',
        'call_ended': 'Panggilan berakhir',
        'call_rejected': 'Panggilan ditolak',
        'call_busy': 'Pengguna sibuk',
        'call_timeout': 'Tidak ada jawaban',
        'call_peer_offline': 'Pengguna offline',
        'accept': 'Terima', 'reject': 'Tolak',
        'hangup': 'Tutup', 'mute': 'Bisukan',
        'unmute': 'Aktifkan mikrofon',
        'no_audio_device': 'Tidak ada perangkat audio. Pasang sounddevice dan numpy.',
        'call_self': 'Anda tidak dapat menelepon diri sendiri',
        'call_in_progress': 'Tidak tersedia selama panggilan',
        'forward': 'Teruskan',
        'forward_title': 'Teruskan pesan',
        'forward_choose': 'Pilih obrolan:',
        'forwarded_from': 'Diteruskan dari @{0}',
        'forwarded': 'Diteruskan',
        'forward_no_chats': 'Tidak ada obrolan untuk diteruskan',
        'forward_empty': 'Tidak ada yang bisa diteruskan',
        'change_font': 'Ubah font',
        'choose_font': 'Pilih font',
        'font': 'Font:',
        'font_standard': 'Standar',
        'font_current': 'terpasang sekarang',
        'font_changed': 'Font diubah. Chatter akan dimulai ulang.',
        'interface_settings': 'Pengaturan antarmuka',
        'change_theme': 'Ubah tema',
        'choose_theme': 'Pilih tema',
        'theme': 'Tema:',
        'theme_black': 'Hitam (standar)',
        'theme_light': 'Terang',
        'theme_coffee': 'Kopi',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Tema diubah. Chatter akan dimulai ulang.',
        'voice_message': 'Pesan suara',
        'voice_recording': '🔴 Merekam',
        'voice_too_short': 'Pesan terlalu pendek',
        'voice_cancel': 'Batalkan rekaman',
        'you_suffix': '(Anda)',
        'offline_suffix': '(offline)',
        'rate_limited': 'Terlalu banyak permintaan. Tunggu sebentar.',
        'e2e_verify': '🔒 Verifikasi enkripsi',
        'e2e_title': 'Enkripsi end-to-end',
        'e2e_fingerprint':
            'Nomor keamanan dengan @{0}:\n\n{1}\n\n'
            'Bandingkan nomor ini dengan kontak Anda. '
            'Jika cocok, percakapan aman dari server.',
        'e2e_unavailable':
            'Enkripsi dinonaktifkan. Pasang:\npip install cryptography',
        'e2e_badge': '🔒 Dienkripsi end-to-end',
        'e2e_decrypt_fail': '[Tidak dapat mendekripsi]',
        'e2e_wait_key': 'Menunggu kunci enkripsi...',
        'e2e_notice': '🔒 Enkripsi end-to-end',
        'e2e_unverified': '⚠️ Enkripsi belum diverifikasi',
        'e2e_confirm_match': 'Apakah nomornya cocok?',
        'e2e_marked_verified': 'Ditandai terverifikasi',
        'e2e_marked_unverified': 'Ditandai belum terverifikasi',
        'empty_chat': 'Belum ada apa-apa di sini...',
        'creator_badge': 'Pembuat',
    },
    'tr': {
        'chats': 'Sohbetler', 'find_user': '🔍 Kullanıcı ara',
        'select_chat': 'Kime yazmak istediğinizi seçin',
        'input_placeholder': 'Bir mesaj yazın...', 'send': 'Gönder',
        'settings': 'Ayarlar', 'close': 'Kapat',
        'account_settings': 'Hesap ayarları',
        'change_nick': 'Takma adı değiştir', 'change_password': 'Şifreyi değiştir',
        'fullscreen': 'Tam ekran / Çık', 'reconnect': 'Yeniden bağlan',
        'notifications': 'Bildirimler:', 'language': 'Dil:',
        'delete_account': 'Hesabı sil', 'logout': 'Çıkış yap', 'exit': 'Çıkış',
        'username': 'Kullanıcı adı:', 'password': 'Şifre:',
        'first_name': 'Ad (isteğe bağlı):',
        'last_name': 'Soyad (isteğe bağlı):',
        'confirm_password': 'Şifreyi onayla:', 'login': 'Giriş yap',
        'register': 'Hesap oluştur', 'login_tab': 'Giriş',
        'register_tab': 'Kayıt', 'welcome': 'Hoş geldiniz!', 'online': 'Çevrimiçi',
        'was_online': 'Yakın zamanda çevrimiçi', 'typing': '{0} yazıyor',
        'error': 'Hata', 'done': 'Tamam', 'cancel': 'İptal', 'ok': 'Tamam',
        'save': 'Kaydet', 'saved': 'Kaydedildi',
        'connecting': 'Bağlanıyor...', 'reconnecting': 'Yeniden bağlanıyor...',
        'disconnected': 'Bağlantı kesildi', 'connect_fail': 'Bağlanılamadı',
        'search_title': 'Kullanıcı ara', 'search_placeholder': 'Ad...',
        'search_btn': 'Ara', 'searching': 'Aranıyor...',
        'search_found': 'Bulundu: {0}', 'search_nothing': 'Hiçbir şey bulunamadı',
        'fill_both': 'Her iki alanı da doldurun',
        'fill_all': 'Tüm zorunlu alanları doldurun',
        'passwords_dont_match': 'Şifreler eşleşmiyor',
        'password_min_6': 'Şifre: en az 6 karakter',
        'password_changed': 'Şifre değiştirildi', 'wrong_password': 'Yanlış şifre',
        'user_not_found': 'Kullanıcı bulunamadı',
        'name_taken': 'Bu ad zaten alınmış',
        'session_replaced': 'Başka bir cihazdan giriş yaptınız. Mevcut oturum sonlandırıldı.',
        'account_deleted': 'Hesap silindi. Çıkış yapacaksınız.',
        'enter_old_password': 'Mevcut şifreyi girin:',
        'enter_new_password': 'Yeni şifre girin (min 6 karakter):',
        'enter_new_password_again': 'Yeni şifreyi tekrar girin:',
        'change_password_title': 'Şifre değiştir',
        'change_nick_title': 'Takma adı değiştir',
        'enter_new_nick': 'Yeni takma adı girin:',
        'delete_account_warning': 'Hesap ve tüm veriler silinecek.\nDevam edilsin mi?',
        'enter_password_confirm': 'Onaylamak için şifreyi girin:',
        'language_changed': 'Dil değiştirildi. Chatter yeniden başlatılacak.',
        'choose_language': 'Dil seç', 'not_delivered': 'İletilmedi',
        'sending': 'Gönderiliyor...', 'sent_at': '{0} tarihinde gönderildi',
        'reply_to': '@{0} kullanıcısına yanıt: "{1}"',
        'edit_message': 'Yeni metni girin:',
        'edit_message_title': 'Mesajı düzenle',
        'menu_reply': 'Yanıtla', 'menu_edit': 'Düzenle',
        'menu_delete': 'Sil', 'menu_block': 'Engelle',
        'menu_unblock': 'Engeli kaldır',
        'menu_delete_local': 'Benden sil',
        'menu_dm': 'Özel mesaj', 'menu_delete_chat': 'Sil',
        'changed_suffix': ' (düzenlendi)',
        'left_chat': '{0} sohbetten ayrıldı',
        'joined_chat': '{0} sohbete katıldı',
        'search_ip_btn': 'Kişiyi bulamıyor musunuz?',
        'enter_ip_title': 'IP ile bağlan',
        'enter_ip_text': 'Sunucu IP adresini girin:',
        'enter_ip_title2': 'Sunucuya bağlan',
        'enter_ip_text2': 'Sunucu IP adresini girin:',
        'searching_by_ip': '{0} adresinde kişiler aranıyor...',
        'attach': 'Dosya ekle', 'attach_file': '📎',
        'attachment': 'Ek', 'save_file': 'Dosyayı kaydet',
        'open_file': 'Dosyayı aç', 'file_saved': 'Dosya kaydedildi',
        'file_too_big': 'Dosya çok büyük (maks 2 GB)',
        'upload_avatar': 'Avatar yükle',
        'avatar_saved': 'Avatar kaydedildi',
        'avatar_too_big': 'Avatar çok büyük (maks 100 KB)',
        'send_file': 'Gönder',
        'user_blocked': 'Kullanıcı engellendi',
        'user_unblocked': 'Kullanıcının engeli kaldırıldı',
        'you_blocked': 'Bu kullanıcıyı engellediniz',
        'blocked_warning': '@{0} kullanıcısından artık mesaj almayacaksınız.\nEngellensin mi?',
        'delete_chat_warning': '@{0} ile sohbet silinsin mi?',
        'no_name': 'İsimsiz', 'restart_title': 'Yeniden başlat',
        'restart_msg': 'Dili uygulamak için Chatter yeniden başlatılacak...',
        'restart_msg_font': 'Yazı tipini uygulamak için Chatter yeniden başlatılacak...',
        'attach_too_big_short': 'Maks 2 GB',
        'call': 'Ara', 'call_title': 'Arama',
        'incoming_call': '{0} kişisinden gelen arama',
        'calling_you': '{0} sizi arıyor',
        'call_calling': 'Bağlanıyor...',
        'call_ringing': 'Çalıyor...',
        'call_active': 'Görüşmede',
        'call_ended': 'Arama sona erdi',
        'call_rejected': 'Arama reddedildi',
        'call_busy': 'Kullanıcı meşgul',
        'call_timeout': 'Yanıt yok',
        'call_peer_offline': 'Kullanıcı çevrimdışı',
        'accept': 'Kabul et', 'reject': 'Reddet',
        'hangup': 'Kapat', 'mute': 'Sessize al',
        'unmute': 'Sesi aç',
        'no_audio_device': 'Ses cihazı yok. sounddevice ve numpy yükleyin.',
        'call_self': 'Kendinizi arayamazsınız',
        'call_in_progress': 'Arama sırasında kullanılamaz',
        'forward': 'İlet',
        'forward_title': 'Mesajı ilet',
        'forward_choose': 'Bir sohbet seçin:',
        'forwarded_from': '@{0} kişisinden iletildi',
        'forwarded': 'İletildi',
        'forward_no_chats': 'İletilecek sohbet yok',
        'forward_empty': 'İletilecek bir şey yok',
        'change_font': 'Yazı tipini değiştir',
        'choose_font': 'Yazı tipi seç',
        'font': 'Yazı tipi:',
        'font_standard': 'Standart',
        'font_current': 'şu anda yüklü',
        'font_changed': 'Yazı tipi değiştirildi. Chatter yeniden başlatılacak.',
        'interface_settings': 'Arayüz ayarları',
        'change_theme': 'Temayı değiştir',
        'choose_theme': 'Tema seç',
        'theme': 'Tema:',
        'theme_black': 'Siyah (standart)',
        'theme_light': 'Açık',
        'theme_coffee': 'Kahve',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Tema değiştirildi. Chatter yeniden başlatılacak.',
        'voice_message': 'Sesli mesaj',
        'voice_recording': '🔴 Kaydediliyor',
        'voice_too_short': 'Mesaj çok kısa',
        'voice_cancel': 'Kaydı iptal et',
        'you_suffix': '(siz)',
        'offline_suffix': '(çevrimdışı)',
        'rate_limited': 'Çok fazla istek. Lütfen bekleyin.',
        'e2e_verify': '🔒 Şifrelemeyi doğrula',
        'e2e_title': 'Uçtan uca şifreleme',
        'e2e_fingerprint':
            '@{0} ile güvenlik numarası:\n\n{1}\n\n'
            'Bu numarayı kişiyle karşılaştırın. Eşleşirse '
            'sohbet sunucudan korunur.',
        'e2e_unavailable':
            'Şifreleme devre dışı. Yükleyin:\npip install cryptography',
        'e2e_badge': '🔒 Uçtan uca şifreli',
        'e2e_decrypt_fail': '[Şifre çözülemedi]',
        'e2e_wait_key': 'Şifreleme anahtarı bekleniyor...',
        'e2e_notice': '🔒 Uçtan uca şifreli',
        'e2e_unverified': '⚠️ Şifreleme doğrulanmadı',
        'e2e_confirm_match': 'Numara eşleşiyor mu?',
        'e2e_marked_verified': 'Doğrulanmış olarak işaretlendi',
        'e2e_marked_unverified': 'Doğrulanmamış olarak işaretlendi',
        'empty_chat': 'Burada henüz bir şey yok...',
        'creator_badge': 'Oluşturucu',
    },
    'pl': {
        'chats': 'Czaty', 'find_user': '🔍 Znajdź użytkownika',
        'select_chat': 'Wybierz, do kogo napisać',
        'input_placeholder': 'Wpisz wiadomość...', 'send': 'Wyślij',
        'settings': 'Ustawienia', 'close': 'Zamknij',
        'account_settings': 'Ustawienia konta',
        'change_nick': 'Zmień pseudonim', 'change_password': 'Zmień hasło',
        'fullscreen': 'Pełny ekran / Wyjdź', 'reconnect': 'Połącz ponownie',
        'notifications': 'Powiadomienia:', 'language': 'Język:',
        'delete_account': 'Usuń konto', 'logout': 'Wyloguj', 'exit': 'Wyjście',
        'username': 'Nazwa użytkownika:', 'password': 'Hasło:',
        'first_name': 'Imię (opcjonalnie):',
        'last_name': 'Nazwisko (opcjonalnie):',
        'confirm_password': 'Powtórz hasło:', 'login': 'Zaloguj',
        'register': 'Załóż konto', 'login_tab': 'Logowanie',
        'register_tab': 'Rejestracja', 'welcome': 'Witaj!', 'online': 'Online',
        'was_online': 'Niedawno online', 'typing': '{0} pisze',
        'error': 'Błąd', 'done': 'Gotowe', 'cancel': 'Anuluj', 'ok': 'OK',
        'save': 'Zapisz', 'saved': 'Zapisano',
        'connecting': 'Łączenie...', 'reconnecting': 'Ponowne łączenie...',
        'disconnected': 'Rozłączono', 'connect_fail': 'Nie udało się połączyć',
        'search_title': 'Znajdź użytkownika', 'search_placeholder': 'Imię...',
        'search_btn': 'Szukaj', 'searching': 'Szukam...',
        'search_found': 'Znaleziono: {0}', 'search_nothing': 'Nic nie znaleziono',
        'fill_both': 'Wypełnij oba pola',
        'fill_all': 'Wypełnij wszystkie wymagane pola',
        'passwords_dont_match': 'Hasła nie pasują',
        'password_min_6': 'Hasło: co najmniej 6 znaków',
        'password_changed': 'Hasło zmienione', 'wrong_password': 'Błędne hasło',
        'user_not_found': 'Nie znaleziono użytkownika',
        'name_taken': 'Ta nazwa jest już zajęta',
        'session_replaced': 'Zalogowano z innego urządzenia. Bieżąca sesja zakończona.',
        'account_deleted': 'Konto usunięte. Zostaniesz wylogowany.',
        'enter_old_password': 'Podaj obecne hasło:',
        'enter_new_password': 'Podaj nowe hasło (min 6 znaków):',
        'enter_new_password_again': 'Powtórz nowe hasło:',
        'change_password_title': 'Zmiana hasła',
        'change_nick_title': 'Zmiana pseudonimu',
        'enter_new_nick': 'Podaj nowy pseudonim:',
        'delete_account_warning': 'Konto i wszystkie dane zostaną usunięte.\nKontynuować?',
        'enter_password_confirm': 'Podaj hasło, aby potwierdzić:',
        'language_changed': 'Język zmieniony. Chatter zostanie zrestartowany.',
        'choose_language': 'Wybierz język', 'not_delivered': 'Nie dostarczono',
        'sending': 'Wysyłanie...', 'sent_at': 'Wysłano o {0}',
        'reply_to': 'Odpowiedź do @{0}: "{1}"', 'edit_message': 'Wpisz nowy tekst:',
        'edit_message_title': 'Edytuj wiadomość', 'menu_reply': 'Odpowiedz',
        'menu_edit': 'Edytuj', 'menu_delete': 'Usuń',
        'menu_block': 'Zablokuj', 'menu_unblock': 'Odblokuj',
        'menu_delete_local': 'Usuń u mnie', 'menu_dm': 'Wiadomość prywatna',
        'menu_delete_chat': 'Usuń',
        'changed_suffix': ' (edytowano)', 'left_chat': '{0} opuścił czat',
        'joined_chat': '{0} dołączył do czatu',
        'search_ip_btn': 'Nie możesz znaleźć osoby?',
        'enter_ip_title': 'Połącz przez IP',
        'enter_ip_text': 'Podaj adres IP serwera:',
        'enter_ip_title2': 'Połącz z serwerem',
        'enter_ip_text2': 'Podaj adres IP serwera:',
        'searching_by_ip': 'Szukam osób w {0}...',
        'attach': 'Załącz plik', 'attach_file': '📎',
        'attachment': 'Załącznik', 'save_file': 'Zapisz plik',
        'open_file': 'Otwórz plik', 'file_saved': 'Plik zapisany',
        'file_too_big': 'Plik jest za duży (maks. 2 GB)',
        'upload_avatar': 'Prześlij awatar',
        'avatar_saved': 'Awatar zapisany',
        'avatar_too_big': 'Awatar jest za duży (maks. 100 KB)',
        'send_file': 'Wyślij', 'user_blocked': 'Użytkownik zablokowany',
        'user_unblocked': 'Użytkownik odblokowany',
        'you_blocked': 'Zablokowałeś tego użytkownika',
        'blocked_warning': 'Nie będziesz już otrzymywać wiadomości od @{0}.\nZablokować?',
        'delete_chat_warning': 'Usunąć rozmowę z @{0}?',
        'no_name': 'Bez nazwy', 'restart_title': 'Restart',
        'restart_msg': 'Chatter zostanie zrestartowany, aby zastosować język...',
        'restart_msg_font': 'Chatter zostanie zrestartowany, aby zastosować czcionkę...',
        'attach_too_big_short': 'Maks. 2 GB',
        'call': 'Zadzwoń', 'call_title': 'Połączenie',
        'incoming_call': 'Połączenie od {0}',
        'calling_you': '{0} dzwoni',
        'call_calling': 'Łączenie...',
        'call_ringing': 'Dzwoni...',
        'call_active': 'W trakcie rozmowy',
        'call_ended': 'Połączenie zakończone',
        'call_rejected': 'Połączenie odrzucone',
        'call_busy': 'Użytkownik zajęty',
        'call_timeout': 'Brak odpowiedzi',
        'call_peer_offline': 'Użytkownik offline',
        'accept': 'Odbierz', 'reject': 'Odrzuć',
        'hangup': 'Zakończ', 'mute': 'Wycisz',
        'unmute': 'Włącz mikrofon',
        'no_audio_device': 'Brak urządzenia audio. Zainstaluj sounddevice i numpy.',
        'call_self': 'Nie możesz zadzwonić do siebie',
        'call_in_progress': 'Niedostępne podczas połączenia',
        'forward': 'Przekaż',
        'forward_title': 'Przekaż wiadomość',
        'forward_choose': 'Wybierz czat:',
        'forwarded_from': 'Przekazano od @{0}',
        'forwarded': 'Przekazano',
        'forward_no_chats': 'Brak czatów do przekazania',
        'forward_empty': 'Nie ma czego przekazywać',
        'change_font': 'Zmień czcionkę',
        'choose_font': 'Wybierz czcionkę',
        'font': 'Czcionka:',
        'font_standard': 'Standardowa',
        'font_current': 'zainstalowana',
        'font_changed': 'Czcionka zmieniona. Chatter zostanie zrestartowany.',
        'interface_settings': 'Ustawienia interfejsu',
        'change_theme': 'Zmień motyw',
        'choose_theme': 'Wybierz motyw',
        'theme': 'Motyw:',
        'theme_black': 'Czarny (standardowy)',
        'theme_light': 'Jasny',
        'theme_coffee': 'Kawowy',
        'theme_sakura': 'Sakura',
        'theme_changed': 'Motyw zmieniony. Chatter zostanie zrestartowany.',
        'voice_message': 'Wiadomość głosowa',
        'voice_recording': '🔴 Nagrywanie',
        'voice_too_short': 'Wiadomość zbyt krótka',
        'voice_cancel': 'Anuluj nagrywanie',
        'you_suffix': '(ty)',
        'offline_suffix': '(offline)',
        'rate_limited': 'Zbyt wiele żądań. Poczekaj chwilę.',
        'e2e_verify': '🔒 Zweryfikuj szyfrowanie',
        'e2e_title': 'Szyfrowanie end-to-end',
        'e2e_fingerprint':
            'Numer bezpieczeństwa z @{0}:\n\n{1}\n\n'
            'Porównaj ten numer z kontaktem. Jeśli się '
            'zgadzają, rozmowa jest chroniona przed serwerem.',
        'e2e_unavailable':
            'Szyfrowanie wyłączone. Zainstaluj:\npip install cryptography',
        'e2e_badge': '🔒 Szyfrowane end-to-end',
        'e2e_decrypt_fail': '[Nie można odszyfrować]',
        'e2e_wait_key': 'Oczekiwanie na klucz szyfrowania...',
        'e2e_notice': '🔒 Szyfrowanie end-to-end',
        'e2e_unverified': '⚠️ Szyfrowanie niezweryfikowane',
        'e2e_confirm_match': 'Czy numer się zgadza?',
        'e2e_marked_verified': 'Oznaczono jako zweryfikowane',
        'e2e_marked_unverified': 'Oznaczono jako niezweryfikowane',
        'empty_chat': 'Jeszcze nic tu nie ma...',
        'creator_badge': 'Twórca',
    },
}

EXTRA_KEYS = [
    'account_settings', 'first_name', 'last_name', 'save', 'saved',
    'menu_block', 'menu_unblock', 'attach', 'attach_file', 'attachment',
    'save_file', 'open_file', 'file_saved', 'file_too_big',
    'upload_avatar', 'avatar_saved', 'avatar_too_big', 'send_file',
    'user_blocked', 'user_unblocked', 'you_blocked', 'blocked_warning',
    'no_name', 'menu_delete_chat', 'delete_chat_warning',
    'restart_title', 'restart_msg', 'restart_msg_font', 'restart_msg_theme',
    'attach_too_big_short',
    'session_replaced',
    'call', 'call_title', 'incoming_call', 'calling_you',
    'call_calling', 'call_ringing', 'call_active', 'call_ended',
    'call_rejected', 'call_busy', 'call_timeout', 'call_peer_offline',
    'accept', 'reject', 'hangup', 'mute', 'unmute',
    'no_audio_device', 'call_self', 'call_in_progress',
    'forward', 'forward_title', 'forward_choose',
    'forwarded_from', 'forwarded', 'forward_no_chats', 'forward_empty',
    'change_font', 'choose_font', 'font', 'font_standard', 'font_current',
    'font_changed',
    'interface_settings', 'change_theme', 'choose_theme', 'theme',
    'theme_black', 'theme_light', 'theme_coffee', 'theme_sakura',
    'theme_changed',
    'voice_message', 'voice_recording', 'voice_too_short', 'voice_cancel',
    'you_suffix', 'offline_suffix', 'rate_limited',
    'e2e_verify', 'e2e_title', 'e2e_fingerprint', 'e2e_unavailable',
    'e2e_badge', 'e2e_decrypt_fail', 'e2e_wait_key',
    'e2e_notice', 'e2e_unverified', 'e2e_confirm_match',
    'e2e_marked_verified', 'e2e_marked_unverified', 'empty_chat',
    'creator_badge',
    'enter_ip_title2', 'enter_ip_text2',
]

for _lang_code in LANGUAGES:
    if _lang_code not in TRANSLATIONS:
        TRANSLATIONS[_lang_code] = {}
    for _k, _v in TRANSLATIONS['en'].items():
        if _k not in TRANSLATIONS[_lang_code]:
            TRANSLATIONS[_lang_code][_k] = _v


SELF_CHAT_ID = '__self__'
MENTION_RE = re.compile(r'(?:^|\s)@([\w\-]+)', flags=re.UNICODE)
HISTORY_LIMIT = 10000
DELIVERY_TIMEOUT_MS = 10000
TYPING_TIMEOUT = 3.0
TYPING_SEND_INTERVAL = 2.0
ERROR_HIDE_MS = 5000
STATUS_REFRESH_MS = 5000
SYSTEM_SENDER = "система"

_current_lang = 'ru'


def t(key, *args):
    lang_dict = TRANSLATIONS.get(_current_lang, TRANSLATIONS['ru'])
    text = lang_dict.get(key)
    if text is None:
        text = TRANSLATIONS['en'].get(key, key)
    if args:
        try:
            return text.format(*args)
        except Exception:
            return text
    return text


def set_language(code):
    global _current_lang
    if code in TRANSLATIONS:
        _current_lang = code


def get_current_lang():
    return _current_lang


EMOJI_LIST = [
    "😀", "😃", "😄", "😁", "😆", "😅", "😂", "🤣",
    "😊", "😇", "🙂", "🙃", "😉", "😌", "😍", "🥰",
    "😘", "😗", "😙", "😚", "😋", "😛", "😝", "😜",
    "🤪", "🤨", "🧐", "🤓", "😎", "🤩", "🥳", "😏",
    "😒", "😞", "😔", "😟", "😕", "🙁", "😣", "😖",
    "😫", "😩", "🥺", "😢", "😭", "😤", "😠", "😡",
    "🤬", "🤯", "😳", "🥵", "🥶", "😱", "😨", "😰",
    "😥", "😓", "🤗", "🤔", "🤭", "🤫", "🤥", "😶",
    "😐", "😑", "😬", "🙄", "😯", "😦", "😧", "😮",
    "😲", "🥱", "😴", "🤤", "😪", "😵", "🤐", "🥴",
    "🤢", "🤮", "🤧", "😷", "🤒", "🤕", "❤️", "🧡",
    "💛", "💚", "💙", "💜", "🖤", "🤍", "🤎", "💔",
    "❣️", "💕", "💞", "💓", "💗", "💖", "💘", "💝",
    "👍", "👎", "👌", "✌️", "🤞", "🤟", "🤘", "🤙",
    "👈", "👉", "👆", "👇", "☝️", "✋", "🤚", "🖐",
    "🖖", "👋", "🤝", "🙏", "✍️", "💅", "🤳", "💪",
    "🎉", "🎊", "🎈", "🎁", "🔥", "⭐", "✨", "💫",
    "💥", "💯", "✅", "❌", "❓", "❗", "⚠️", "🚀",
]


def ease_out_back(t, s=1.9):
    if t <= 0:
        return 0.0
    if t >= 1:
        return 1.0
    t -= 1.0
    return t * t * ((s + 1.0) * t + s) + 1.0


def ease_out_elastic(t, amplitude=1.0, period=0.45):
    if t <= 0:
        return 0.0
    if t >= 1:
        return 1.0
    if period == 0:
        period = 0.45
    s = period / (2.0 * math.pi) * math.asin(1.0 / max(amplitude, 1.0))
    return (amplitude *
            math.pow(2.0, -10.0 * t) *
            math.sin((t - s) * (2.0 * math.pi) / period) + 1.0)


def ease_in_out_quad(t):
    if t <= 0:
        return 0.0
    if t >= 1:
        return 1.0
    if t < 0.5:
        return 2.0 * t * t
    return 1.0 - math.pow(-2.0 * t + 2.0, 2.0) / 2.0


def animate_alpha(window, start=0.0, end=1.0,
                  duration_ms=220, steps=12,
                  ease='quad', overshoot=False):
    try:
        window.attributes('-alpha', start)
    except Exception:
        return
    interval = max(1, duration_ms // max(1, steps))

    def tick(i):
        try:
            if not window.winfo_exists():
                return
            t = i / float(steps)
            if ease == 'linear':
                e = t
            elif ease == 'back':
                e = ease_out_back(t)
            elif ease == 'elastic':
                e = ease_out_elastic(t)
            else:
                e = ease_in_out_quad(t)
            a = start + (end - start) * e
            a = 0.0 if a < 0 else (1.0 if a > 1 else a)
            window.attributes('-alpha', a)
            if i < steps:
                window.after(interval, lambda: tick(i + 1))
        except Exception:
            pass

    try:
        window.after(interval, lambda: tick(1))
    except Exception:
        pass


class Tooltip:
    def __init__(self, widget, text, delay=350):
        self.widget = widget
        self.text = text
        self.delay = delay
        self._job = None
        self._tip = None
        try:
            widget.bind('<Enter>', self._enter, add='+')
            widget.bind('<Leave>', self._leave, add='+')
            widget.bind('<ButtonPress>', self._leave, add='+')
        except Exception:
            pass

    def _enter(self, event=None):
        self._cancel()
        try:
            self._job = self.widget.after(self.delay, self._show)
        except Exception:
            self._job = None

    def _leave(self, event=None):
        self._cancel()
        self._hide()

    def _cancel(self):
        if self._job is not None:
            try:
                self.widget.after_cancel(self._job)
            except Exception:
                pass
            self._job = None

    def _show(self):
        self._job = None
        if self._tip is not None:
            return
        try:
            x = self.widget.winfo_rootx() + self.widget.winfo_width() // 2
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
            self._tip = tk.Toplevel(self.widget)
            self._tip.wm_overrideredirect(True)
            self._tip.wm_geometry(f"+{x}+{y}")
            try:
                self._tip.attributes('-topmost', True)
            except Exception:
                pass
            lbl = tk.Label(self._tip, text=self.text,
                           bg="#333333", fg="#e0e0e0",
                           font=("Arial", 10), padx=8, pady=4,
                           relief="solid", borderwidth=1)
            lbl.pack()
            animate_alpha(self._tip, 0.0, 1.0,
                          duration_ms=160, steps=10, ease='back')
        except Exception as e:
            log_error(f'Tooltip show: {e}')
            self._tip = None

    def _hide(self):
        if self._tip is not None:
            try:
                self._tip.destroy()
            except Exception:
                pass
            self._tip = None


def save_session(username, password):
    try:
        data = {'username': username, 'password': password,
                'timestamp': time.time()}
        with open(SESSION_PATH, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        log_error(f'save_session: {e}')


def load_session():
    try:
        if not os.path.exists(SESSION_PATH):
            return None
        with open(SESSION_PATH, 'r', encoding='utf-8') as f:
            data = json.load(f)
        age = time.time() - data.get('timestamp', 0)
        if age > SESSION_MAX_AGE:
            delete_session()
            return None
        password = data.get('password', '')
        username = data.get('username', '')
        if not username or not password:
            return None
        return username, password
    except Exception as e:
        log_error(f'load_session: {e}')
        return None


def delete_session():
    try:
        if os.path.exists(SESSION_PATH):
            os.remove(SESSION_PATH)
    except Exception:
        pass


def load_settings():
    defaults = {'notifications': True, 'language': 'ru',
                'font': 'standard', 'theme': 'black',
                'blocked': [], 'avatar': '',
                'first_name': '', 'last_name': '',
                'e2e_verified': []}
    try:
        if not os.path.exists(SETTINGS_PATH):
            return dict(defaults)
        with open(SETTINGS_PATH, 'r', encoding='utf-8') as f:
            data = json.load(f)
        for k, v in defaults.items():
            if k not in data:
                data[k] = v
        return data
    except Exception as e:
        log_error(f'load_settings: {e}')
        return dict(defaults)


def save_settings(data):
    try:
        with open(SETTINGS_PATH, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        log_error(f'save_settings: {e}')


def safe_filename(name):
    try:
        name = os.path.basename(name)
        name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', '_', name)
        if not name:
            name = 'file'
        return name[:150]
    except Exception:
        return 'file'


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        'CREATE TABLE IF NOT EXISTS users ('
        'id INTEGER PRIMARY KEY AUTOINCREMENT,'
        'first_name TEXT NOT NULL DEFAULT "",'
        'last_name TEXT NOT NULL DEFAULT "",'
        'username TEXT UNIQUE NOT NULL,'
        'password_hash TEXT NOT NULL,'
        'salt TEXT NOT NULL,'
        'avatar TEXT NOT NULL DEFAULT "",'
        'public_key TEXT NOT NULL DEFAULT "",'
        'created_at TEXT NOT NULL)'
    )
    conn.commit()
    cur = conn.execute('PRAGMA table_info(users)')
    cols = [r[1] for r in cur.fetchall()]
    for col in ('first_name', 'last_name', 'avatar', 'public_key'):
        if col not in cols:
            try:
                conn.execute(
                    f"ALTER TABLE users ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
            except Exception:
                pass
    conn.commit()
    conn.close()


def db_user_exists(username):
    conn = sqlite3.connect(DB_PATH)
    try:
        return bool(conn.execute(
            'SELECT 1 FROM users WHERE username=?',
            (username,)).fetchone())
    finally:
        conn.close()


def db_get_user(username):
    conn = sqlite3.connect(DB_PATH)
    try:
        return conn.execute(
            'SELECT password_hash, salt FROM users WHERE username=?',
            (username,)).fetchone()
    finally:
        conn.close()


def db_get_profile(username):
    conn = sqlite3.connect(DB_PATH)
    try:
        row = conn.execute(
            'SELECT first_name, last_name, avatar, public_key '
            'FROM users WHERE username=?',
            (username,)).fetchone()
        if row:
            return {'first_name': row[0] or '',
                    'last_name': row[1] or '',
                    'avatar': row[2] or '',
                    'public_key': row[3] or ''}
        return None
    finally:
        conn.close()


def db_update_public_key(username, public_key):
    conn = sqlite3.connect(DB_PATH)
    try:
        conn.execute('UPDATE users SET public_key=? WHERE username=?',
                     (public_key or '', username))
        conn.commit()
    finally:
        conn.close()


def db_add_user(first_name, last_name, username, password_hash, salt,
                avatar='', public_key=''):
    conn = sqlite3.connect(DB_PATH)
    try:
        existing = conn.execute(
            'SELECT id FROM users WHERE username=?', (username,)
        ).fetchone()
        if existing:
            if password_hash != 'SYNCED':
                conn.execute(
                    'UPDATE users SET password_hash=?, salt=?, '
                    'first_name=?, last_name=?, avatar=?, public_key=? '
                    'WHERE username=?',
                    (password_hash, salt, first_name, last_name,
                     avatar, public_key, username))
            else:
                if public_key:
                    conn.execute(
                        'UPDATE users SET public_key=? WHERE username=?',
                        (public_key, username))
        else:
            conn.execute(
                'INSERT INTO users '
                '(first_name, last_name, username, password_hash, salt, '
                'avatar, public_key, created_at) '
                'VALUES (?, ?, ?, ?, ?, ?, ?, ?)',
                (first_name, last_name, username, password_hash, salt,
                 avatar, public_key, datetime.now().isoformat()))
        conn.commit()
    finally:
        conn.close()


def db_update_profile(username, first_name=None, last_name=None,
                      avatar=None):
    conn = sqlite3.connect(DB_PATH)
    try:
        parts = []
        args = []
        if first_name is not None:
            parts.append('first_name=?')
            args.append(first_name)
        if last_name is not None:
            parts.append('last_name=?')
            args.append(last_name)
        if avatar is not None:
            parts.append('avatar=?')
            args.append(avatar)
        if not parts:
            return
        args.append(username)
        conn.execute(
            f'UPDATE users SET {", ".join(parts)} WHERE username=?',
            args)
        conn.commit()
    finally:
        conn.close()


def db_delete_user(username):
    conn = sqlite3.connect(DB_PATH)
    try:
        conn.execute('DELETE FROM users WHERE username=?', (username,))
        conn.commit()
    finally:
        conn.close()


def db_rename_user(old, new):
    conn = sqlite3.connect(DB_PATH)
    try:
        conn.execute('UPDATE users SET username=? WHERE username=?',
                     (new, old))
        conn.commit()
    finally:
        conn.close()


def db_search_users(query):
    conn = sqlite3.connect(DB_PATH)
    try:
        rows = conn.execute(
            'SELECT username FROM users WHERE username LIKE ? '
            'ORDER BY username LIMIT 50',
            (f'%{query}%',)).fetchall()
        return [r[0] for r in rows]
    finally:
        conn.close()


def db_all_users():
    conn = sqlite3.connect(DB_PATH)
    try:
        rows = conn.execute('SELECT username FROM users').fetchall()
        return [r[0] for r in rows]
    finally:
        conn.close()


def db_all_users_with_hashes():
    conn = sqlite3.connect(DB_PATH)
    try:
        rows = conn.execute(
            'SELECT username, password_hash, salt, first_name, '
            'last_name, avatar FROM users '
            'WHERE password_hash != ? AND salt != ?',
            ('SYNCED', 'SYNCED')
        ).fetchall()
        return [(r[0], r[1], r[2], r[3], r[4], r[5]) for r in rows]
    finally:
        conn.close()


def hash_password(password, salt=None):
    if salt is None:
        salt = secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac('sha256', password.encode(),
                            bytes.fromhex(salt), 100000)
    return h.hex(), salt


def valid_username(u):
    if not u or not (3 <= len(u) <= 20):
        return False
    return all(c.isascii() and (c.isalnum() or c == '_') for c in u)


def valid_password(p):
    return bool(p) and 6 <= len(p) <= 100


def port_bound(port):
    try:
        s = socket.socket()
        s.settimeout(0.3)
        try:
            s.connect(('127.0.0.1', port))
            return True
        except Exception:
            return False
        finally:
            s.close()
    except Exception:
        return False


def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('8.8.8.8', 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return '127.0.0.1'


def make_avatar_image(b64_str, size):
    try:
        if not b64_str:
            return None
        if ',' in b64_str and b64_str.startswith('data:'):
            b64_str = b64_str.split(',', 1)[1]
        raw = base64.b64decode(b64_str)
        img = Image.open(io.BytesIO(raw)).convert('RGBA')
        img = img.resize((size, size), Image.LANCZOS)
        return ctk.CTkImage(light_image=img, dark_image=img,
                            size=(size, size))
    except Exception as e:
        log_error(f'make_avatar_image: {e}')
        return None


def make_initials_avatar(first_name, last_name, username, size):
    try:
        img = Image.new('RGBA', (size, size), (60, 60, 60, 255))
        draw = ImageDraw.Draw(img)
        ini = ''
        if first_name:
            ini += first_name[0].upper()
        if last_name:
            ini += last_name[0].upper()
        if not ini and username:
            ini = username[0].upper()
        draw.ellipse((0, 0, size, size), fill=(31, 106, 165, 255))
        try:
            font = None
            for fname in ('arial.ttf', 'DejaVuSans.ttf',
                          'LiberationSans-Regular.ttf'):
                try:
                    font = ImageFont.truetype(fname, int(size * 0.5))
                    break
                except Exception:
                    continue
            if font is None:
                font = ImageFont.load_default()
            bbox = draw.textbbox((0, 0), ini, font=font)
            tw = bbox[2] - bbox[0]
            th = bbox[3] - bbox[1]
            draw.text(((size - tw) / 2 - bbox[0],
                       (size - th) / 2 - bbox[1]),
                      ini, font=font, fill=(255, 255, 255, 255))
        except Exception:
            try:
                draw.text((size / 3, size / 3), ini,
                          fill=(255, 255, 255, 255))
            except Exception:
                pass
        return ctk.CTkImage(light_image=img, dark_image=img,
                            size=(size, size))
    except Exception as e:
        log_error(f'make_initials_avatar: {e}')
        return None


def human_size(n):
    for unit in ('Б', 'КБ', 'МБ', 'ГБ'):
        if n < 1024:
            return f'{n:.1f} {unit}'
        n /= 1024
    return f'{n:.1f} ТБ'


def format_duration(secs):
    try:
        secs = int(max(0, secs))
        return f"{secs // 60}:{secs % 60:02d}"
    except Exception:
        return "0:00"


def pick_file():
    return filedialog.askopenfilename(title='Выберите файл')


def save_file_to_disk(raw_bytes, original_name):
    try:
        safe = safe_filename(original_name)
        unique = f'{uuid.uuid4().hex[:12]}_{safe}'
        path = os.path.join(ATTACHMENTS_DIR, unique)
        with open(path, 'wb') as f:
            f.write(raw_bytes)
        return path
    except Exception as e:
        log_error(f'save_file_to_disk: {e}')
        return None


def encode_file(path):
    try:
        size = os.path.getsize(path)
        if size > MAX_ATTACHMENT_SIZE:
            return None, None, None, t('file_too_big')
        with open(path, 'rb') as f:
            raw = f.read()
        b64 = base64.b64encode(raw).decode('ascii')
        name = os.path.basename(path)
        mime, _ = mimetypes.guess_type(path)
        if not mime:
            mime = 'application/octet-stream'
        return b64, name, mime, None
    except Exception as e:
        return None, None, None, f'{e}'


class AudioEngine:
    def __init__(self):
        self.udp_sock = None
        self.local_port = 0
        self.peer_addr = None
        self.in_stream = None
        self.out_stream = None
        self.muted = False
        self.running = False
        self._lock = threading.Lock()
        self._last_rx = 0.0

    def start(self):
        if not HAS_AUDIO:
            log_error('AudioEngine: sounddevice not available')
            return False
        if self.running:
            return True
        try:
            self.udp_sock = socket.socket(socket.AF_INET,
                                          socket.SOCK_DGRAM)
            self.udp_sock.bind(('0.0.0.0', 0))
            self.udp_sock.setblocking(False)
            self.local_port = self.udp_sock.getsockname()[1]

            self.in_stream = sd.RawInputStream(
                samplerate=AUDIO_SAMPLE_RATE,
                channels=AUDIO_CHANNELS,
                dtype='int16',
                blocksize=AUDIO_BLOCK,
                callback=self._in_cb)
            self.out_stream = sd.RawOutputStream(
                samplerate=AUDIO_SAMPLE_RATE,
                channels=AUDIO_CHANNELS,
                dtype='int16',
                blocksize=AUDIO_BLOCK,
                callback=self._out_cb)
            self.in_stream.start()
            self.out_stream.start()
            with self._lock:
                self.running = True
            return True
        except Exception as e:
            log_error(f'AudioEngine.start: {e}')
            self.stop()
            return False

    def _in_cb(self, indata, frames, time_info, status):
        if not self.running or self.muted:
            return
        peer = self.peer_addr
        if peer is None:
            return
        try:
            self.udp_sock.sendto(bytes(indata), peer)
        except Exception:
            pass

    def _out_cb(self, outdata, frames, time_info, status):
        silence = b'\x00' * len(outdata)
        if not self.running:
            try:
                outdata[:] = silence
            except Exception:
                pass
            return
        got = False
        try:
            data, addr = self.udp_sock.recvfrom(4096)
            if self.peer_addr is None:
                self.peer_addr = addr
            n = min(len(data), len(outdata))
            outdata[:n] = data[:n]
            if n < len(outdata):
                outdata[n:] = silence[n:]
            self._last_rx = time.time()
            got = True
        except BlockingIOError:
            pass
        except Exception:
            pass
        if not got:
            try:
                outdata[:] = silence
            except Exception:
                pass

    def set_peer(self, ip, port):
        try:
            self.peer_addr = (ip, int(port))
        except Exception:
            self.peer_addr = None

    def set_muted(self, m):
        self.muted = bool(m)

    def stop(self):
        with self._lock:
            self.running = False
        for s in (self.in_stream, self.out_stream):
            if s is not None:
                try:
                    s.stop()
                except Exception:
                    pass
                try:
                    s.close()
                except Exception:
                    pass
        self.in_stream = None
        self.out_stream = None
        if self.udp_sock is not None:
            try:
                self.udp_sock.close()
            except Exception:
                pass
            self.udp_sock = None
        self.peer_addr = None
        self.local_port = 0


class VoiceRecorder:
    def __init__(self):
        self.recording = False
        self.frames = []
        self.stream = None
        self._lock = threading.Lock()

    def start(self):
        if not HAS_AUDIO:
            return False
        if self.recording:
            return False
        try:
            with self._lock:
                self.frames = []
                self.recording = True
            self.stream = sd.RawInputStream(
                samplerate=AUDIO_SAMPLE_RATE,
                channels=AUDIO_CHANNELS,
                dtype='int16',
                blocksize=AUDIO_BLOCK,
                callback=self._cb)
            self.stream.start()
            return True
        except Exception as e:
            log_error(f'VoiceRecorder.start: {e}')
            with self._lock:
                self.recording = False
            return False

    def _cb(self, indata, frames, time_info, status):
        with self._lock:
            if self.recording:
                self.frames.append(bytes(indata))

    def stop(self):
        with self._lock:
            self.recording = False
            frames = list(self.frames)
            self.frames = []
        if self.stream is not None:
            try:
                self.stream.stop()
                self.stream.close()
            except Exception:
                pass
            self.stream = None
        return b''.join(frames)

    def cancel(self):
        with self._lock:
            self.recording = False
            self.frames = []
        if self.stream is not None:
            try:
                self.stream.stop()
                self.stream.close()
            except Exception:
                pass
            self.stream = None


class VoicePlayer:
    def __init__(self):
        self.playing = False
        self.thread = None
        self.on_finished = None
        self._lock = threading.Lock()

    def play(self, wav_bytes, on_finished=None):
        if not HAS_AUDIO:
            return False
        self.stop()
        with self._lock:
            self.on_finished = on_finished
            self.playing = True
        self.thread = threading.Thread(
            target=self._run, args=(wav_bytes,), daemon=True)
        self.thread.start()
        return True

    def _run(self, wav_bytes):
        try:
            with wave.open(io.BytesIO(wav_bytes), 'rb') as wf:
                nchannels = wf.getnchannels()
                sampwidth = wf.getsampwidth()
                framerate = wf.getframerate()
                raw = wf.readframes(wf.getnframes())
            if HAS_NUMPY:
                if sampwidth == 2:
                    dtype = np.int16
                elif sampwidth == 1:
                    dtype = np.int8
                elif sampwidth == 4:
                    dtype = np.int32
                else:
                    dtype = np.int16
                data = np.frombuffer(raw, dtype=dtype)
                if nchannels > 1:
                    data = data.reshape(-1, nchannels)
                sd.play(data, framerate)
                sd.wait()
            else:
                import tempfile
                with tempfile.NamedTemporaryFile(
                        suffix='.wav', delete=False) as tmp:
                    tmp.write(wav_bytes)
                    tmp_path = tmp.name
                if HAS_WINSOUND:
                    winsound.PlaySound(
                        tmp_path,
                        winsound.SND_FILENAME | winsound.SND_NODEFAULT)
                try:
                    os.unlink(tmp_path)
                except Exception:
                    pass
        except Exception as e:
            log_error(f'VoicePlayer: {e}')
        finally:
            with self._lock:
                self.playing = False
                cb = self.on_finished
                self.on_finished = None
            if cb is not None:
                try:
                    cb()
                except Exception:
                    pass

    def stop(self):
        with self._lock:
            if not self.playing:
                self.on_finished = None
                return
            self.playing = False
            self.on_finished = None
        try:
            sd.stop()
        except Exception:
            pass
        try:
            if HAS_WINSOUND:
                winsound.PlaySound(None, winsound.SND_PURGE)
        except Exception:
            pass


class IncomingCallDialog(ctk.CTkToplevel):
    def __init__(self, master, peer, on_accept, on_reject):
        super().__init__(master)
        self.title(t('call_title'))
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_accept_cb = on_accept
        self.on_reject_cb = on_reject
        self._done = False

        try:
            self.attributes('-topmost', True)
        except Exception:
            pass

        ctk.CTkLabel(self, text="📞", text_color=GREEN,
                     font=get_font(42)
                     ).pack(pady=(20, 4))

        ctk.CTkLabel(self, text=t('calling_you', peer),
                     text_color=FG_TEXT,
                     font=get_font(15, "bold"),
                     wraplength=320, justify="center"
                     ).pack(padx=25, pady=(0, 18))

        row = ctk.CTkFrame(self, fg_color=BG_MID)
        row.pack(padx=25, pady=(0, 22))
        ctk.CTkButton(row, text=t('reject'), width=140, height=40,
                      fg_color=RED, hover_color=RED_HOVER,
                      font=get_font(13, "bold"),
                      command=self._reject
                      ).pack(side="left", padx=(0, 8))
        ctk.CTkButton(row, text=t('accept'), width=140, height=40,
                      fg_color=GREEN, hover_color="#3d8b40",
                      font=get_font(13, "bold"),
                      command=self._accept
                      ).pack(side="left")

        self.transient(master)
        self.grab_set()
        self.protocol("WM_DELETE_WINDOW", self._reject)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 360, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _accept(self):
        if self._done:
            return
        self._done = True
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_accept_cb()
        except Exception as e:
            log_error(f'incoming accept: {e}')

    def _reject(self):
        if self._done:
            return
        self._done = True
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_reject_cb()
        except Exception as e:
            log_error(f'incoming reject: {e}')


class CallWindow(ctk.CTkToplevel):
    def __init__(self, master, peer, on_hangup, on_toggle_mute):
        super().__init__(master)
        self.title(t('call_title'))
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_hangup_cb = on_hangup
        self.on_toggle_mute_cb = on_toggle_mute
        self._muted = False
        self._started_at = None
        self._timer_job = None
        self._closing = False
        self._pulse_job = None
        self._pulse_state = 0

        try:
            self.attributes('-topmost', True)
        except Exception:
            pass

        self.icon_lbl = ctk.CTkLabel(self, text="📞",
                                     text_color=GREEN,
                                     font=get_font(42))
        self.icon_lbl.pack(pady=(20, 4))

        self.peer_label = ctk.CTkLabel(
            self, text=peer, text_color=FG_TEXT,
            font=get_font(15, "bold"),
            wraplength=320, justify="center")
        self.peer_label.pack(padx=25, pady=(0, 4))

        self.status_label = ctk.CTkLabel(
            self, text=t('call_calling'),
            text_color=FG_DIM, font=get_font(12))
        self.status_label.pack(padx=25, pady=(0, 16))

        row = ctk.CTkFrame(self, fg_color=BG_MID)
        row.pack(padx=25, pady=(0, 22))

        self.mute_btn = ctk.CTkButton(
            row, text="🎤", width=90, height=44,
            fg_color=BG_LIGHT, hover_color=BG_DARK,
            font=get_font(20),
            command=self._toggle_mute)
        self.mute_btn.pack(side="left", padx=(0, 8))

        self.hangup_btn = ctk.CTkButton(
            row, text="📞", width=140, height=44,
            fg_color=RED, hover_color=RED_HOVER,
            font=get_font(22),
            command=self._hangup)
        self.hangup_btn.pack(side="left")

        self.transient(master)
        self.protocol("WM_DELETE_WINDOW", self._hangup)
        self.after(50, self._center)
        self.after(200, self._start_timer)
        self.after(300, self._start_pulse)
        self.after(320, self._start_icon_bounce)

    def _start_icon_bounce(self):
        if self._closing:
            return
        if self._started_at is not None:
            return
        sizes = [42, 48, 44, 50, 42]
        idx = [0]

        def tick():
            if self._closing or self._started_at is not None:
                return
            try:
                self.icon_lbl.configure(font=get_font(sizes[idx[0]]))
            except Exception:
                pass
            idx[0] = (idx[0] + 1) % len(sizes)
            try:
                self.after(180, tick)
            except Exception:
                pass

        try:
            tick()
        except Exception:
            pass

    def _start_pulse(self):
        if self._closing:
            return
        if self._started_at is not None:
            return
        self._pulse_state = 1 - self._pulse_state
        try:
            self.hangup_btn.configure(
                fg_color=RED_HOVER if self._pulse_state else RED)
        except Exception:
            pass
        try:
            self._pulse_job = self.after(500, self._start_pulse)
        except Exception:
            self._pulse_job = None

    def set_status(self, text):
        try:
            self.status_label.configure(text=text)
        except Exception:
            pass

    def mark_active(self):
        self._started_at = time.time()
        self.set_status("00:00")
        if self._pulse_job:
            try:
                self.after_cancel(self._pulse_job)
            except Exception:
                pass
            self._pulse_job = None
        try:
            self.hangup_btn.configure(fg_color=RED)
        except Exception:
            pass
        try:
            self.icon_lbl.configure(font=get_font(42))
        except Exception:
            pass

    def _start_timer(self):
        if self._closing:
            return
        if self._started_at is not None:
            elapsed = int(time.time() - self._started_at)
            mm = elapsed // 60
            ss = elapsed % 60
            self.set_status(f"{mm:02d}:{ss:02d}")
        try:
            self._timer_job = self.after(1000, self._start_timer)
        except Exception:
            self._timer_job = None

    def _center(self):
        center_toplevel(self, 360, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=220, steps=12,
                      ease='back')
        bring_to_front(self)

    def _toggle_mute(self):
        self._muted = not self._muted
        try:
            self.mute_btn.configure(
                fg_color=RED if self._muted else BG_LIGHT,
                text="🔇" if self._muted else "🎤")
        except Exception:
            pass
        try:
            self.on_toggle_mute_cb(self._muted)
        except Exception:
            pass

    def _hangup(self):
        if self._closing:
            return
        self._closing = True
        if self._timer_job:
            try:
                self.after_cancel(self._timer_job)
            except Exception:
                pass
            self._timer_job = None
        if self._pulse_job:
            try:
                self.after_cancel(self._pulse_job)
            except Exception:
                pass
            self._pulse_job = None
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_hangup_cb()
        except Exception:
            pass

    def force_close(self):
        self._closing = True
        if self._timer_job:
            try:
                self.after_cancel(self._timer_job)
            except Exception:
                pass
            self._timer_job = None
        if self._pulse_job:
            try:
                self.after_cancel(self._pulse_job)
            except Exception:
                pass
            self._pulse_job = None
        try:
            self.destroy()
        except Exception:
            pass


class ChatPickerDialog(ctk.CTkToplevel):
    def __init__(self, master, chats, on_pick):
        super().__init__(master)
        self.title(t('forward_title'))
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_pick_cb = on_pick
        self._picked = False

        try:
            self.attributes('-topmost', True)
        except Exception:
            pass

        ctk.CTkLabel(self, text=t('forward_choose'),
                     text_color=FG_TEXT,
                     font=get_font(14, "bold"),
                     anchor="w"
                     ).pack(fill="x", padx=18, pady=(15, 6))

        body = ctk.CTkScrollableFrame(self, fg_color=BG_MID,
                                      width=320, height=320)
        body.pack(fill="both", expand=True, padx=15, pady=(0, 15))

        for cid, info in chats:
            name = info.get('name', cid) or cid
            try:
                btn = ctk.CTkButton(
                    body, text=name, anchor="w", height=38,
                    fg_color="transparent", hover_color=BG_LIGHT,
                    text_color=FG_TEXT, font=get_font(13),
                    command=lambda c=cid: self._pick(c))
                btn.pack(fill="x", padx=2, pady=2)
            except Exception:
                continue

        self.transient(master)
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 380, 440)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _pick(self, cid):
        if self._picked:
            return
        self._picked = True
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_pick_cb(cid)
        except Exception as e:
            log_error(f'ChatPickerDialog pick: {e}')


class CustomDialog(ctk.CTkToplevel):
    def __init__(self, master, title, message, yes_no=False,
                 danger=False, auto_close_ms=None):
        super().__init__(master)
        self.title(title)
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.result = False
        self._auto_timer = None

        ctk.CTkLabel(self, text=message, text_color=FG_TEXT,
                     font=get_font(13),
                     wraplength=380, justify="center"
                     ).pack(padx=30, pady=(25, 20))

        if auto_close_ms is None:
            row = ctk.CTkFrame(self, fg_color=BG_MID)
            row.pack(padx=30, pady=(0, 25))

            if yes_no:
                ctk.CTkButton(
                    row, text=t('cancel'), width=130, height=36,
                    fg_color=BG_LIGHT, hover_color=BG_DARK,
                    command=self.on_no).pack(side="left",
                                             padx=(0, 8))
                ctk.CTkButton(
                    row, text="OK", width=130, height=36,
                    fg_color=RED if danger else BTN,
                    hover_color=RED_HOVER if danger else BTN_HOVER,
                    command=self.on_yes).pack(side="left")
            else:
                ctk.CTkButton(
                    row, text=t('ok'), width=220, height=36,
                    fg_color=BTN, hover_color=BTN_HOVER,
                    command=self.on_yes).pack()
        else:
            ctk.CTkFrame(self, fg_color=BG_MID,
                         height=5).pack()

        self.transient(master)
        self.grab_set()
        self.after(50, self._center)
        if yes_no:
            self.protocol("WM_DELETE_WINDOW", self.on_no)
        else:
            self.protocol("WM_DELETE_WINDOW", self.on_yes)
        if auto_close_ms:
            try:
                self._auto_timer = self.after(
                    auto_close_ms, self.on_yes)
            except Exception:
                self._auto_timer = None

    def _center(self):
        center_toplevel(self, 340, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _cancel_auto(self):
        if self._auto_timer:
            try:
                self.after_cancel(self._auto_timer)
            except Exception:
                pass
            self._auto_timer = None

    def on_yes(self):
        self._cancel_auto()
        self.result = True
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass

    def on_no(self):
        self._cancel_auto()
        self.result = False
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


def custom_alert(master, title, message, danger=False,
                 auto_close_ms=None):
    try:
        d = CustomDialog(master, title, message, yes_no=False,
                         danger=danger,
                         auto_close_ms=auto_close_ms)
        d.wait_window()
    except Exception as e:
        log_error(f'custom_alert: {e}')


def custom_confirm(master, title, message, danger=False):
    try:
        d = CustomDialog(master, title, message, yes_no=True,
                         danger=danger)
        d.wait_window()
        return d.result
    except Exception as e:
        log_error(f'custom_confirm: {e}')
        return False


class NotificationPopup(ctk.CTkToplevel):
    def __init__(self, master, sender, text, on_click):
        super().__init__(master)
        self.configure(fg_color=BG_MID)
        self.on_click_cb = on_click
        self._closed = False

        try:
            self.overrideredirect(True)
        except Exception:
            pass
        try:
            self.attributes('-topmost', True)
        except Exception:
            pass

        body = ctk.CTkFrame(self, fg_color=BG_MID,
                            corner_radius=8,
                            border_width=1, border_color=BLUE)
        body.pack(fill="both", expand=True)

        title_row = ctk.CTkFrame(body, fg_color=BG_MID)
        title_row.pack(fill="x", padx=12, pady=(10, 2))

        ctk.CTkLabel(title_row, text="🔔", text_color=YELLOW,
                     font=get_font(14)
                     ).pack(side="left", padx=(0, 6))

        ctk.CTkLabel(title_row, text=sender,
                     text_color=BLUE,
                     font=get_font(13, "bold"),
                     anchor="w"
                     ).pack(side="left", fill="x", expand=True)

        preview = text if len(text) <= 80 else text[:77] + "..."
        ctk.CTkLabel(body, text=preview, text_color=FG_TEXT,
                     font=get_font(12),
                     anchor="w", justify="left",
                     wraplength=280
                     ).pack(fill="x", padx=12, pady=(0, 12))

        for w in [body, title_row]:
            w.bind("<Button-1>", lambda e: self._clicked())
        for w in body.winfo_children():
            w.bind("<Button-1>", lambda e: self._clicked())

        self.after(30, self._position)
        self.after(NOTIFICATION_TIMEOUT_MS, self._close)

    def _position(self):
        try:
            self.update_idletasks()
            w = 320
            h = self.winfo_reqheight()
            if h < 80:
                h = 80
            sw = self.winfo_screenwidth()
            sh = self.winfo_screenheight()
            target_x = sw - w - 20
            target_y = sh - h - 60
            start_x = sw + 20
            self.geometry(f"{w}x{h}+{start_x}+{target_y}")

            try:
                self.attributes('-alpha', 0.0)
            except Exception:
                pass

            steps = 18
            duration = 380
            interval = max(1, duration // steps)

            def tick(i):
                try:
                    if not self.winfo_exists():
                        return
                    t = i / float(steps)
                    e = ease_out_back(t, 2.4)
                    x = int(start_x + (target_x - start_x) * e)
                    a = 0.4 + 0.6 * min(1.0, t * 1.6)
                    try:
                        self.attributes('-alpha', a)
                    except Exception:
                        pass
                    self.geometry(f"{w}x{h}+{x}+{target_y}")
                    if i < steps:
                        self.after(interval, lambda: tick(i + 1))
                    else:
                        self.geometry(
                            f"{w}x{h}+{target_x}+{target_y}")
                        try:
                            self.attributes('-alpha', 1.0)
                        except Exception:
                            pass
                except Exception:
                    pass

            self.after(interval, lambda: tick(1))
        except Exception as e:
            log_error(f'NotificationPopup position: {e}')

    def _clicked(self):
        try:
            self.on_click_cb()
        except Exception:
            pass
        self._close()

    def _close(self):
        if self._closed:
            return
        self._closed = True
        try:
            self.destroy()
        except Exception:
            pass


class ChatServer:
    def __init__(self):
        self.loop = None
        self.tcp_server = None
        self.udp_sock = None
        self.clients = {}
        self.last_seen = {}
        self.running = False
        self.main_thread = None
        self.udp_thread = None
        self.ddos = DDoSProtector()
        self._gc_job_started = False

    def start(self):
        if self.running:
            return
        self.running = True

        def runner():
            try:
                self.loop = asyncio.new_event_loop()
                asyncio.set_event_loop(self.loop)
                self.loop.run_until_complete(self._serve())
            except Exception as e:
                log_error(f'ChatServer runner: {e}')

        self.main_thread = threading.Thread(target=runner, daemon=True)
        self.main_thread.start()

        self.udp_thread = threading.Thread(
            target=self._udp_responder, daemon=True)
        self.udp_thread.start()

        if not self._gc_job_started:
            self._gc_job_started = True
            threading.Thread(
                target=self._ddos_gc_loop, daemon=True).start()

    def _ddos_gc_loop(self):
        while self.running:
            try:
                time.sleep(60)
            except Exception:
                break
            try:
                self.ddos.gc()
            except Exception as e:
                log_error(f'ddos gc: {e}')

    def stop(self):
        self.running = False
        try:
            if self.loop:
                self.loop.call_soon_threadsafe(self.loop.stop)
        except Exception:
            pass
        try:
            if self.udp_sock:
                self.udp_sock.close()
        except Exception:
            pass

    def _udp_responder(self):
        s = None
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            s.bind(('', UDP_PORT))
            s.settimeout(1.0)
            self.udp_sock = s
        except Exception as e:
            log_error(f'UDP bind error: {e}')
            if s:
                try:
                    s.close()
                except Exception:
                    pass
            return

        while self.running:
            try:
                data, addr = s.recvfrom(1024)
                if data == DISCOVER_MSG:
                    if not self.ddos.allow_udp(addr[0]):
                        continue
                    try:
                        s.sendto(
                            SERVER_PREFIX + str(TCP_PORT).encode(),
                            addr)
                    except Exception:
                        pass
            except socket.timeout:
                continue
            except Exception:
                break

    async def _serve(self):
        try:
            self.tcp_server = await asyncio.start_server(
                self._handle, '0.0.0.0', TCP_PORT)
        except Exception as e:
            log_error(f'TCP bind error: {e}')
            return
        async with self.tcp_server:
            await self.tcp_server.serve_forever()

    async def _send(self, client, obj):
        try:
            async with client['lock']:
                try:
                    data = json.dumps(obj, ensure_ascii=False) + '\n'
                    client['writer'].write(data.encode())
                    await client['writer'].drain()
                    return True
                except Exception:
                    return False
        except Exception:
            return False

    async def _broadcast(self, obj, exclude=None):
        dead = []
        for u, c in list(self.clients.items()):
            if u == exclude:
                continue
            if not await self._send(c, obj):
                dead.append(u)
        for u in dead:
            self.clients.pop(u, None)

    async def _send_userlist(self):
        await self._broadcast({
            'type': 'userlist',
            'users': sorted(self.clients.keys())
        })

    async def _handle(self, reader, writer):
        try:
            peer = writer.get_extra_info('peername')
            client_ip = peer[0] if peer else '0.0.0.0'
        except Exception:
            client_ip = '0.0.0.0'

        if not self.ddos.accept_connection(client_ip):
            log_error(f'[DDOS] Connection rejected from {client_ip}')
            try:
                writer.close()
            except Exception:
                pass
            return

        client = {'reader': reader, 'writer': writer,
                  'username': None, 'lock': asyncio.Lock(),
                  'ip': client_ip}
        buf = b''
        try:
            while True:
                try:
                    data = await asyncio.wait_for(
                        reader.read(1048576),
                        timeout=DDOS_IDLE_TIMEOUT_SEC)
                except asyncio.TimeoutError:
                    log_error(f'[DDOS] Idle timeout for {client_ip}')
                    break
                if not data:
                    break
                buf += data
                if len(buf) > MAX_LINE_BYTES and b'\n' not in buf:
                    log_error('Client buffer overflow, dropping')
                    break
                while b'\n' in buf:
                    line, buf = buf.split(b'\n', 1)
                    if len(line) > MAX_LINE_BYTES:
                        log_error('Oversized line, skipping')
                        self.ddos._violate(client_ip, 'oversized line')
                        continue
                    try:
                        obj = json.loads(line.decode(
                            'utf-8', errors='replace'))
                    except Exception:
                        self.ddos._violate(client_ip, 'bad json')
                        continue
                    if not _json_depth_ok(obj):
                        self.ddos._violate(client_ip, 'json too deep')
                        continue
                    if not validate_attachment_sizes(obj):
                        self.ddos._violate(
                            client_ip, 'oversized attachment')
                        continue
                    try:
                        await self._dispatch(client, obj)
                    except Exception as e:
                        log_error(f'Dispatch error: {e}\n'
                                  f'{traceback.format_exc()}')
        except Exception as e:
            log_error(f'Handle error: {e}')
        finally:
            u = client.get('username')
            if u and self.clients.get(u) is client:
                self.clients.pop(u, None)
                self.last_seen[u] = time.time()
                try:
                    await self._send_userlist()
                except Exception:
                    pass
            try:
                writer.close()
            except Exception:
                pass
            try:
                self.ddos.release_connection(client_ip)
            except Exception:
                pass

    async def _dispatch(self, client, obj):
        if not isinstance(obj, dict):
            return
        t_type = obj.get('type')
        if t_type == '__ping__':
            return

        ip = client.get('ip', '0.0.0.0')
        if not self.ddos.allow_message(ip):
            return

        if t_type in ('register', 'login',
                      'change_password', 'delete_account'):
            if not self.ddos.allow_login(ip):
                await self._send(client, {
                    'type': 'error',
                    'text': 'rate_limited'})
                return

        if t_type == 'register':
            await self._register(client, obj)
        elif t_type == 'login':
            await self._login(client, obj)
        elif t_type == 'search':
            await self._search(client, obj)
        elif t_type == 'dm':
            await self._dm(client, obj)
        elif t_type == 'edit':
            await self._edit(client, obj)
        elif t_type == 'delete':
            await self._delete(client, obj)
        elif t_type == 'typing':
            await self._typing(client, obj)
        elif t_type == 'change_nick':
            await self._change_nick(client, obj)
        elif t_type == 'change_password':
            await self._change_password(client, obj)
        elif t_type == 'delete_account':
            await self._delete_account(client, obj)
        elif t_type == 'status':
            await self._status(client, obj)
        elif t_type == 'update_profile':
            await self._update_profile(client, obj)
        elif t_type == 'call_signal':
            await self._call_signal(client, obj)
        elif t_type == 'request_all_users':
            try:
                names = db_all_users()
            except Exception as e:
                log_error(f'request_all_users: {e}')
                names = []
            online = set(self.clients.keys())
            await self._send(client, {
                'type': 'all_users_result',
                'users': [{'name': n, 'online': n in online}
                          for n in names if n]})
        elif t_type == 'request_profile':
            target = obj.get('user') or ''
            prof = db_get_profile(target) or {}
            await self._send(client, {
                'type': 'profile_result',
                'user': target,
                'first_name': prof.get('first_name', ''),
                'last_name': prof.get('last_name', ''),
                'avatar': prof.get('avatar', ''),
                'public_key': prof.get('public_key', '')})
        elif t_type == 'sync_users':
            users = obj.get('users') or []
            for u in users:
                if valid_username(u):
                    try:
                        db_add_user('', '', u, 'SYNCED', 'SYNCED')
                    except Exception:
                        pass
            await self._send(client, {'type': 'ok',
                                      'action': 'sync'})
        elif t_type == 'sync_users_full':
            users = obj.get('users') or []
            count = 0
            for item in users:
                try:
                    if not isinstance(item, (list, tuple)):
                        continue
                    if len(item) < 3:
                        continue
                    uname = str(item[0]).strip()
                    uhash = str(item[1])
                    usalt = str(item[2])
                    ufirst = str(item[3]) if len(item) > 3 else ''
                    ulast = str(item[4]) if len(item) > 4 else ''
                    uavatar = str(item[5]) if len(item) > 5 else ''
                    if not valid_username(uname):
                        continue
                    if uhash == 'SYNCED' or usalt == 'SYNCED':
                        continue
                    existing = db_get_user(uname)
                    if existing and existing[0] != 'SYNCED':
                        continue
                    db_add_user(ufirst, ulast, uname, uhash, usalt,
                                uavatar)
                    count += 1
                except Exception as e:
                    log_error(f'sync_users_full item: {e}')
            if count:
                log_error(f'sync_users_full: {count} accounts added')
            await self._send(client, {'type': 'ok',
                                      'action': 'sync'})

    async def _call_signal(self, client, data):
        sender = client.get('username')
        if not sender:
            return
        to = (data.get('to') or '').strip()
        action = data.get('action') or ''
        call_id = data.get('call_id') or ''
        if not to or not action or not call_id:
            return
        target = self.clients.get(to)
        if target is None:
            if action == 'invite':
                await self._send(client, {
                    'type': 'call_signal',
                    'action': 'unreachable',
                    'from': to,
                    'to': sender,
                    'call_id': call_id,
                    'reason': 'call_peer_offline'})
            return
        msg = {
            'type': 'call_signal',
            'action': action,
            'from': sender,
            'to': to,
            'call_id': call_id,
        }
        for k in ('udp_port', 'ip', 'reason'):
            if k in data:
                msg[k] = data[k]
        await self._send(target, msg)

    async def _update_profile(self, client, data):
        if not client.get('username'):
            return
        username = client['username']
        first_name = data.get('first_name')
        last_name = data.get('last_name')
        avatar = data.get('avatar')
        try:
            db_update_profile(username,
                              first_name=first_name,
                              last_name=last_name,
                              avatar=avatar)
        except Exception as e:
            log_error(f'update_profile: {e}')
        await self._send(client, {'type': 'ok',
                                  'action': 'profile_updated'})

    async def _status(self, client, data):
        user = (data.get('user') or '').strip()
        if not user:
            return
        if user in self.clients:
            await self._send(client, {
                'type': 'status_result',
                'user': user,
                'online': True,
                'last_seen': time.time()})
        else:
            last = self.last_seen.get(user, 0)
            await self._send(client, {
                'type': 'status_result',
                'user': user,
                'online': False,
                'last_seen': last})

    async def _register(self, client, data):
        first_name = (data.get('first_name') or '').strip()
        last_name = (data.get('last_name') or '').strip()
        username = (data.get('username') or '').strip()
        password = data.get('password') or ''
        public_key = data.get('public_key') or ''
        if not valid_username(username):
            await self._send(client, {'type': 'error',
                                      'text': 'fill_all'})
            return
        if not valid_password(password):
            await self._send(client, {'type': 'error',
                                      'text': 'password_min_6'})
            return
        try:
            existing = db_get_user(username)
            if existing and existing[0] != 'SYNCED':
                await self._send(client, {'type': 'error',
                                          'text': 'name_taken'})
                return
            ph, salt = hash_password(password)
            db_add_user(first_name, last_name, username, ph, salt,
                        public_key=public_key)
        except Exception as e:
            log_error(f'Register DB error: {e}\n'
                      f'{traceback.format_exc()}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return

        client['username'] = username
        self.clients[username] = client
        await self._broadcast({'type': 'user_registered',
                               'username': username},
                              exclude=username)
        await self._send(client, {'type': 'ok', 'action': 'login',
                                  'username': username,
                                  'first_name': first_name,
                                  'last_name': last_name,
                                  'registered': True})
        await self._send_userlist()

    async def _login(self, client, data):
        username = (data.get('username') or '').strip()
        password = data.get('password') or ''
        public_key = data.get('public_key') or ''
        if not username or not password:
            await self._send(client, {'type': 'error',
                                      'text': 'fill_both'})
            return
        try:
            row = db_get_user(username)
        except Exception as e:
            log_error(f'Login DB error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return

        if not row:
            local_hash = data.get('local_hash')
            local_salt = data.get('local_salt')
            if local_hash and local_salt:
                try:
                    db_add_user('', '', username,
                                local_hash, local_salt,
                                public_key=public_key)
                    row = (local_hash, local_salt)
                except Exception as e:
                    log_error(f'Login using local: {e}')
            if not row:
                await self._send(client, {'type': 'error',
                                          'text': 'user_not_found'})
                return

        ph, salt = row
        if salt == 'SYNCED' or ph == 'SYNCED':
            local_hash = data.get('local_hash')
            local_salt = data.get('local_salt')
            if local_hash and local_salt:
                try:
                    db_add_user('', '', username,
                                local_hash, local_salt,
                                public_key=public_key)
                    ph, salt = local_hash, local_salt
                except Exception as e:
                    log_error(f'login SYNCED fix: {e}')
                    await self._send(client, {'type': 'error',
                                              'text': 'wrong_password'})
                    return
            else:
                await self._send(client, {'type': 'error',
                                          'text': 'user_not_found'})
                return
        try:
            computed, _ = hash_password(password, salt)
        except Exception as e:
            log_error(f'Login hash error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'wrong_password'})
            return
        if computed != ph:
            await self._send(client, {'type': 'error',
                                      'text': 'wrong_password'})
            return

        if public_key:
            try:
                db_update_public_key(username, public_key)
            except Exception as e:
                log_error(f'login update public_key: {e}')

        old_client = self.clients.get(username)
        if old_client is not None and old_client is not client:
            try:
                await self._send(old_client, {
                    'type': 'session_replaced'})
            except Exception:
                pass
            try:
                old_client['writer'].close()
            except Exception:
                pass
            self.clients.pop(username, None)

        client['username'] = username
        self.clients[username] = client
        prof = db_get_profile(username) or {}
        await self._send(client, {'type': 'ok', 'action': 'login',
                                  'username': username,
                                  'first_name': prof.get('first_name', ''),
                                  'last_name': prof.get('last_name', ''),
                                  'avatar': prof.get('avatar', '')})
        await self._send_userlist()

    async def _change_password(self, client, data):
        if not client.get('username'):
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        old_password = data.get('old_password') or ''
        new_password = data.get('new_password') or ''
        username = client['username']

        if not old_password or not new_password:
            await self._send(client, {'type': 'error',
                                      'text': 'fill_both'})
            return
        if not valid_password(new_password):
            await self._send(client, {'type': 'error',
                                      'text': 'password_min_6'})
            return

        try:
            row = db_get_user(username)
        except Exception as e:
            log_error(f'Change pwd DB error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        if not row:
            await self._send(client, {'type': 'error',
                                      'text': 'user_not_found'})
            return
        ph, salt = row
        if salt == 'SYNCED' or ph == 'SYNCED':
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return

        computed, _ = hash_password(old_password, salt)
        if computed != ph:
            await self._send(client, {'type': 'error',
                                      'text': 'wrong_password'})
            return

        try:
            new_ph, new_salt = hash_password(new_password)
            prof = db_get_profile(username) or {}
            db_add_user(prof.get('first_name', ''),
                        prof.get('last_name', ''),
                        username, new_ph, new_salt,
                        prof.get('avatar', ''),
                        prof.get('public_key', ''))
        except Exception as e:
            log_error(f'Change pwd save error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return

        await self._send(client, {'type': 'ok',
                                  'action': 'password_changed'})

    async def _delete_account(self, client, data):
        if not client.get('username'):
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        password = data.get('password') or ''
        username = client['username']
        try:
            row = db_get_user(username)
        except Exception as e:
            log_error(f'Delete acc DB error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        if not row:
            await self._send(client, {'type': 'error',
                                      'text': 'user_not_found'})
            return
        ph, salt = row
        if salt == 'SYNCED' or ph == 'SYNCED':
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        computed, _ = hash_password(password, salt)
        if computed != ph:
            await self._send(client, {'type': 'error',
                                      'text': 'wrong_password'})
            return
        try:
            db_delete_user(username)
        except Exception as e:
            log_error(f'Delete acc error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        self.clients.pop(username, None)
        client['username'] = None
        await self._send(client, {'type': 'ok', 'action': 'deleted'})
        await self._send_userlist()

    async def _search(self, client, data):
        q = (data.get('query') or '').strip()
        if not q:
            await self._send(client, {'type': 'search_result',
                                      'users': [], 'query': ''})
            return
        try:
            names = db_search_users(q)
        except Exception as e:
            log_error(f'Search DB error: {e}')
            names = []
        online = set(self.clients.keys())
        await self._send(client, {
            'type': 'search_result',
            'users': [{'name': n, 'online': n in online}
                      for n in names],
            'query': q})

    async def _dm(self, client, data):
        if not client.get('username'):
            return
        to = (data.get('to') or '').strip()
        text = (data.get('text') or '').strip()
        attachment = data.get('attachment')
        if not to:
            return
        if not text and not attachment:
            return
        if len(text) > 5000:
            text = text[:5000]
        mid = data.get('id') or str(uuid.uuid4())
        if to not in self.clients:
            await self._send(client, {
                'type': 'error',
                'text': 'user_not_found',
                'msg_id': mid})
            return
        msg = {
            'type': 'dm',
            'from': client['username'],
            'to': to,
            'text': text,
            'id': mid,
            'time': datetime.now().strftime('%H:%M')}
        if data.get('reply'):
            msg['reply'] = data['reply']
        if data.get('forwarded_from'):
            msg['forwarded_from'] = data['forwarded_from']
        if attachment:
            msg['attachment'] = attachment
        if data.get('encrypted'):
            msg['encrypted'] = True
        await self._send(self.clients[to], msg)
        if to != client['username']:
            await self._send(client, {'type': 'ack', 'id': mid})

    async def _edit(self, client, data):
        if not client.get('username'):
            return
        to = (data.get('to') or '').strip()
        msg_id = data.get('id') or ''
        new_text = data.get('new_text') or ''
        if not to or not msg_id or not new_text:
            return
        target = self.clients.get(to)
        if target is None:
            return
        msg = {
            'type': 'edit',
            'from': client['username'],
            'to': to,
            'id': msg_id,
            'new_text': new_text,
        }
        if data.get('encrypted'):
            msg['encrypted'] = True
        await self._send(target, msg)

    async def _delete(self, client, data):
        if not client.get('username'):
            return
        mid = data.get('id') or ''
        if not mid or not mid.startswith(client['username'] + '-'):
            return
        for u, c in list(self.clients.items()):
            if u == client['username']:
                continue
            await self._send(c, {'type': 'delete', 'id': mid})

    async def _typing(self, client, data):
        if not client.get('username'):
            return
        to = (data.get('to') or '').strip()
        if to in self.clients:
            await self._send(self.clients[to], {
                'type': 'typing',
                'from': client['username']})

    async def _change_nick(self, client, data):
        if not client.get('username'):
            return
        new_nick = (data.get('new') or '').strip()
        if not valid_username(new_nick):
            await self._send(client, {'type': 'error',
                                      'text': 'fill_all'})
            return
        old = client['username']
        if new_nick == old:
            await self._send(client, {'type': 'error',
                                      'text': 'fill_both'})
            return
        if new_nick in self.clients:
            await self._send(client, {'type': 'error',
                                      'text': 'name_taken'})
            return
        try:
            if db_user_exists(new_nick):
                await self._send(client, {'type': 'error',
                                          'text': 'name_taken'})
                return
            db_rename_user(old, new_nick)
        except Exception as e:
            log_error(f'Rename DB error: {e}')
            await self._send(client, {'type': 'error',
                                      'text': 'error'})
            return
        self.clients.pop(old, None)
        client['username'] = new_nick
        self.clients[new_nick] = client
        await self._send(client, {'type': 'ok', 'action': 'nick',
                                  'username': new_nick})
        await self._send_userlist()


class DiscoveryClient:
    def find_server(self, timeout=1.5):
        s = None
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            s.settimeout(timeout)
            s.sendto(DISCOVER_MSG, ('255.255.255.255', UDP_PORT))
            data, addr = s.recvfrom(1024)
            if data.startswith(SERVER_PREFIX):
                return addr[0]
        except socket.timeout:
            return None
        except Exception:
            return None
        finally:
            if s:
                try:
                    s.close()
                except Exception:
                    pass
        return None


class AuthWindow(ctk.CTkToplevel):
    def __init__(self, master, on_login, on_register, on_cancel):
        super().__init__(master)
        self.title("Chatter")
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_login_cb = on_login
        self.on_register_cb = on_register
        self.on_cancel_cb = on_cancel
        self._busy = False
        self._clear_timer = None

        top = ctk.CTkFrame(self, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.pack(fill="x")
        top.pack_propagate(False)

        ctk.CTkLabel(top, text="●", text_color=RED,
                     font=get_font(14)
                     ).pack(side="left", padx=(15, 6), pady=13)
        self.title_label = ctk.CTkLabel(
            top, text="Chatter", text_color=FG_TEXT,
            font=get_font(14, "bold"))
        self.title_label.pack(side="left", pady=13)

        ctk.CTkButton(top, text=t('exit'), width=80, height=32,
                      fg_color=RED, hover_color=RED_HOVER,
                      command=self.on_exit
                      ).pack(side="right", padx=(5, 15), pady=13)

        self.tab_selector = ctk.CTkSegmentedButton(
            top, values=[t('login_tab'), t('register_tab')],
            command=self._switch_tab,
            selected_color=BTN, selected_hover_color=BTN_HOVER,
            unselected_color=BG_LIGHT,
            unselected_hover_color=BG_LIGHT,
            text_color=FG_TEXT,
            font=get_font(13))
        self.tab_selector.set(t('login_tab'))
        self.tab_selector.pack(side="left", padx=20, pady=13)

        self.body = ctk.CTkFrame(self, fg_color=BG_DARK,
                                 corner_radius=0)
        self.body.pack(fill="both", expand=True, padx=15, pady=15)

        self.login_frame = ctk.CTkFrame(self.body, fg_color=BG_MID,
                                        corner_radius=10)
        self.register_frame = ctk.CTkFrame(self.body,
                                           fg_color=BG_MID,
                                           corner_radius=10)

        self._build_login_tab()
        self._build_register_tab()
        self._switch_tab(t('login_tab'))
        self._bind_enter_keys()

        self.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.after(80, self._center)
        self.after(150, self._focus)

    def _bind_enter_keys(self):
        for entry in (self.login_username, self.login_password):
            try:
                entry.bind("<Return>",
                           lambda e: self._enter_login())
            except Exception:
                pass
        for entry in (self.reg_first_name, self.reg_last_name,
                      self.reg_username, self.reg_password,
                      self.reg_password2):
            try:
                entry.bind("<Return>",
                           lambda e: self._enter_register())
            except Exception:
                pass

    def _enter_login(self):
        self._try_login()
        return "break"

    def _enter_register(self):
        self._try_register()
        return "break"

    def _build_login_tab(self):
        f = self.login_frame
        ctk.CTkLabel(f, text=t('username'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(20, 6))
        self.login_username = ctk.CTkEntry(
            f, height=36, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.login_username.pack(fill="x", padx=25)

        ctk.CTkLabel(f, text=t('password'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(12, 6))
        self.login_password = ctk.CTkEntry(
            f, height=36, fg_color=BG_INPUT, border_width=0,
            show="●", font=get_font(13))
        self.login_password.pack(fill="x", padx=25)

        self.login_btn = ctk.CTkButton(
            f, text=t('login'), height=42,
            font=get_font(14, "bold"),
            fg_color=BTN, hover_color=BTN_HOVER,
            command=self._try_login)
        self.login_btn.pack(fill="x", padx=25, pady=(20, 6))

        self.login_error = ctk.CTkLabel(
            f, text="", text_color=ERROR_TEXT,
            font=get_font(12),
            wraplength=380, justify="left",
            height=36, anchor="nw")
        self.login_error.pack(fill="x", padx=25, pady=(0, 20))

    def _build_register_tab(self):
        f = self.register_frame
        ctk.CTkLabel(f, text=t('first_name'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(15, 4))
        self.reg_first_name = ctk.CTkEntry(
            f, height=34, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.reg_first_name.pack(fill="x", padx=25)

        ctk.CTkLabel(f, text=t('last_name'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(8, 4))
        self.reg_last_name = ctk.CTkEntry(
            f, height=34, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.reg_last_name.pack(fill="x", padx=25)

        ctk.CTkLabel(f, text=t('username'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(8, 4))
        self.reg_username = ctk.CTkEntry(
            f, height=34, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.reg_username.pack(fill="x", padx=25)

        ctk.CTkLabel(f, text=t('password'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(8, 4))
        self.reg_password = ctk.CTkEntry(
            f, height=34, fg_color=BG_INPUT, border_width=0,
            show="●", font=get_font(13))
        self.reg_password.pack(fill="x", padx=25)

        ctk.CTkLabel(f, text=t('confirm_password'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", padx=25, pady=(8, 4))
        self.reg_password2 = ctk.CTkEntry(
            f, height=34, fg_color=BG_INPUT, border_width=0,
            show="●", font=get_font(13))
        self.reg_password2.pack(fill="x", padx=25)

        self.register_btn = ctk.CTkButton(
            f, text=t('register'), height=42,
            font=get_font(14, "bold"),
            fg_color=BTN, hover_color=BTN_HOVER,
            command=self._try_register)
        self.register_btn.pack(fill="x", padx=25, pady=(15, 6))

        self.register_error = ctk.CTkLabel(
            f, text="", text_color=ERROR_TEXT,
            font=get_font(12),
            wraplength=380, justify="left",
            height=36, anchor="nw")
        self.register_error.pack(fill="x", padx=25, pady=(0, 15))

    def _switch_tab(self, name):
        try:
            self.login_frame.pack_forget()
            self.register_frame.pack_forget()
        except Exception:
            pass
        if name == t('login_tab'):
            self.login_frame.pack(fill="both", expand=True,
                                  padx=5, pady=5)
            try:
                self.login_username.focus_set()
            except Exception:
                pass
        else:
            self.register_frame.pack(fill="both", expand=True,
                                     padx=5, pady=5)
            try:
                self.reg_first_name.focus_set()
            except Exception:
                pass

    def _focus(self):
        try:
            self.login_username.focus_set()
        except Exception:
            pass

    def _center(self):
        try:
            self.update_idletasks()
            h = max(self.winfo_reqheight(), 660)
            sh = self.winfo_screenheight()
            if h > sh - 40:
                h = sh - 40
            center_toplevel(self, 500, h)
        except Exception:
            center_toplevel(self, 500, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=240, steps=14,
                      ease='back')
        bring_to_front(self)

    def set_busy(self, b):
        self._busy = b
        s = "disabled" if b else "normal"
        try:
            self.login_btn.configure(
                state=s,
                text=t('connecting') if b else t('login'))
            self.register_btn.configure(
                state=s,
                text=t('connecting') if b else t('register'))
        except Exception:
            pass

    def set_connecting(self, b):
        try:
            if b:
                try:
                    self.title_label.configure(text=t('connecting'))
                except Exception:
                    pass
                self.set_busy(True)
                try:
                    self.tab_selector.configure(state="disabled")
                except Exception:
                    pass
            else:
                try:
                    self.title_label.configure(text="Chatter")
                except Exception:
                    pass
                self.set_busy(False)
                try:
                    self.tab_selector.configure(state="normal")
                except Exception:
                    pass
        except Exception as e:
            log_error(f'AuthWindow.set_connecting: {e}')

    def _schedule_clear(self):
        if self._clear_timer:
            try:
                self.after_cancel(self._clear_timer)
            except Exception:
                pass
            self._clear_timer = None
        try:
            self._clear_timer = self.after(
                ERROR_HIDE_MS, self._clear_errors)
        except Exception:
            pass

    def _clear_errors(self):
        self._clear_timer = None
        try:
            self.login_error.configure(text="")
            self.register_error.configure(text="")
        except Exception:
            pass

    def _friendly_error(self, msg):
        s = str(msg or '')
        if len(s) > 120:
            s = s[:117] + '...'
        return s

    def _translate_error(self, msg):
        if msg in TRANSLATIONS['ru']:
            return t(msg)
        return self._friendly_error(msg)

    def show_error(self, msg):
        self.set_busy(False)
        text = self._translate_error(msg)
        try:
            self.login_error.configure(text=text)
            self.register_error.configure(text=text)
        except Exception:
            pass
        self._schedule_clear()

    def _try_login(self):
        if self._busy:
            return
        u = self.login_username.get().strip()
        p = self.login_password.get()
        try:
            self.login_error.configure(text="")
            self.register_error.configure(text="")
        except Exception:
            pass
        if not u or not p:
            self.show_error("fill_both")
            return
        self.set_busy(True)
        try:
            self.on_login_cb(u, p)
        except Exception as e:
            log_error(f'Login callback: {e}')
            self.show_error(f'{e}')

    def _try_register(self):
        if self._busy:
            return
        fn = self.reg_first_name.get().strip()
        ln = self.reg_last_name.get().strip()
        u = self.reg_username.get().strip()
        p = self.reg_password.get()
        p2 = self.reg_password2.get()
        try:
            self.login_error.configure(text="")
            self.register_error.configure(text="")
        except Exception:
            pass
        if not u or not p or not p2:
            self.show_error("fill_all")
            return
        if p != p2:
            self.show_error("passwords_dont_match")
            return
        if len(p) < 6:
            self.show_error("password_min_6")
            return
        self.set_busy(True)
        try:
            self.on_register_cb(fn, ln, u, p)
        except Exception as ex:
            log_error(f'Register callback: {ex}')
            self.show_error(f'{ex}')

    def on_exit(self):
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_cancel_cb()
        except Exception:
            pass


class LanguagePicker(ctk.CTkToplevel):
    def __init__(self, master, current, on_pick):
        super().__init__(master)
        self.title(t('choose_language'))
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_pick_cb = on_pick

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      width=280, height=440)
        body.pack(padx=15, pady=15, fill="both", expand=True)

        for code, (flag, name) in LANGUAGES.items():
            check = "✓" if code == current else " "
            label = f"{check}   {flag}  {name}"
            btn = ctk.CTkButton(
                body, text=label, anchor="w", height=38,
                fg_color=BTN if code == current else "transparent",
                hover_color=BTN_HOVER if code == current else BG_LIGHT,
                text_color=FG_TEXT,
                font=get_font(13),
                command=lambda c=code: self._pick(c))
            btn.pack(fill="x", padx=4, pady=2)

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 340, 500)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _pick(self, code):
        try:
            self.on_pick_cb(code)
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


class FontPicker(ctk.CTkToplevel):
    def __init__(self, master, current, on_pick):
        super().__init__(master)
        self.title(t('choose_font'))
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_pick_cb = on_pick

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      width=340, height=400)
        body.pack(padx=15, pady=15, fill="both", expand=True)

        for code, label_key, _fam in FONTS:
            if label_key.startswith('font_'):
                display = t(label_key)
                if code == 'standard':
                    display = f"{display} (Roboto)"
            else:
                display = label_key
            check = "✓" if code == current else " "
            display = f"{check}   {display}"
            try:
                btn = ctk.CTkButton(
                    body, text=display, anchor="w", height=38,
                    fg_color=BTN if code == current else "transparent",
                    hover_color=BTN_HOVER if code == current else BG_LIGHT,
                    text_color=FG_TEXT,
                    font=get_font(13),
                    command=lambda c=code: self._pick(c))
                btn.pack(fill="x", padx=4, pady=2)
            except Exception:
                continue

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 400, 480)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _pick(self, code):
        try:
            self.on_pick_cb(code)
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


class ThemePicker(ctk.CTkToplevel):
    PREVIEW_COLORS = {
        'black':  ('#1a1a1a', '#1f6aa5'),
        'light':  ('#f5f5f5', '#1976D2'),
        'coffee': ('#FBF3E4', '#B4823C'),
        'sakura': ('#FFF5F8', '#E91E63'),
    }

    def __init__(self, master, current, on_pick):
        super().__init__(master)
        self.title(t('choose_theme'))
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_pick_cb = on_pick

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      width=380, height=360)
        body.pack(padx=15, pady=15, fill="both", expand=True)

        for code in THEME_ORDER:
            display = get_theme_display(code)
            is_current = (code == current)
            check = "✓" if is_current else " "
            row = ctk.CTkFrame(body, fg_color="transparent",
                               height=44)
            row.pack(fill="x", padx=4, pady=3)
            row.pack_propagate(False)

            try:
                bg_col, accent = self.PREVIEW_COLORS.get(
                    code, ('#1a1a1a', '#1f6aa5'))
                swatch = ctk.CTkFrame(row, width=22, height=22,
                                      corner_radius=4,
                                      fg_color=bg_col,
                                      border_width=1,
                                      border_color=accent)
                swatch.pack(side="left", padx=(4, 8), pady=11)
                swatch.pack_propagate(False)
                dot = ctk.CTkFrame(swatch, width=10, height=10,
                                   corner_radius=5,
                                   fg_color=accent,
                                   border_width=0)
                dot.place(relx=0.5, rely=0.5, anchor="center")
            except Exception:
                pass

            btn = ctk.CTkButton(
                row, text=f"   {display}", anchor="w", height=40,
                fg_color=BTN if is_current else "transparent",
                hover_color=BTN_HOVER if is_current else BG_LIGHT,
                text_color=FG_TEXT,
                font=get_font(13),
                command=lambda c=code: self._pick(c))
            btn.pack(side="left", fill="both", expand=True,
                     padx=(0, 4))

            check_lbl = ctk.CTkLabel(
                row, text=check, text_color=GREEN if is_current else FG_DIM,
                width=24, font=get_font(16, "bold"))
            check_lbl.pack(side="right", padx=(2, 8))

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 440, 440)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _pick(self, code):
        try:
            self.on_pick_cb(code)
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


class InterfaceSettingsWindow(ctk.CTkToplevel):
    def __init__(self, master, on_pick_font, on_pick_theme):
        super().__init__(master)
        self.title(t('interface_settings'))
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_pick_font_cb = on_pick_font
        self.on_pick_theme_cb = on_pick_theme

        top = ctk.CTkFrame(self, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.pack(fill="x")
        top.pack_propagate(False)
        ctk.CTkLabel(top, text=t('interface_settings'),
                     text_color=FG_TEXT,
                     font=get_font(16, "bold")
                     ).pack(side="left", padx=15, pady=13)
        ctk.CTkButton(top, text=t('close'), width=90, height=32,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.destroy
                      ).pack(side="right", padx=(5, 15), pady=13)

        body = ctk.CTkFrame(self, fg_color=BG_DARK,
                            corner_radius=0)
        body.pack(fill="both", expand=True, padx=25, pady=25)

        font_row = ctk.CTkFrame(body, fg_color=BG_MID,
                                corner_radius=8)
        font_row.pack(fill="x", pady=(0, 10))
        ctk.CTkLabel(font_row, text=t('font'),
                     text_color=FG_TEXT,
                     font=get_font(14, "bold"), anchor="w"
                     ).pack(side="left", padx=(15, 10), pady=14)
        ctk.CTkLabel(font_row,
                     text=str(get_font_display(get_current_font())),
                     text_color=FG_DIM,
                     font=get_font(12), anchor="w"
                     ).pack(side="left", pady=14, fill="x", expand=True)
        ctk.CTkButton(font_row, text=t('change_font'),
                      width=170, height=36,
                      font=get_font(13),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_pick_font
                      ).pack(side="right", padx=15, pady=10)

        theme_row = ctk.CTkFrame(body, fg_color=BG_MID,
                                 corner_radius=8)
        theme_row.pack(fill="x", pady=(0, 10))
        ctk.CTkLabel(theme_row, text=t('theme'),
                     text_color=FG_TEXT,
                     font=get_font(14, "bold"), anchor="w"
                     ).pack(side="left", padx=(15, 10), pady=14)
        ctk.CTkLabel(theme_row,
                     text=str(get_theme_display(get_current_theme())),
                     text_color=FG_DIM,
                     font=get_font(12), anchor="w"
                     ).pack(side="left", pady=14, fill="x", expand=True)
        ctk.CTkButton(theme_row, text=t('change_theme'),
                      width=170, height=36,
                      font=get_font(13),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_pick_theme
                      ).pack(side="right", padx=15, pady=10)

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 520, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _do_pick_font(self):
        try:
            self.on_pick_font_cb(self)
        except Exception as e:
            log_error(f'interface pick font: {e}')

    def _do_pick_theme(self):
        try:
            self.on_pick_theme_cb(self)
        except Exception as e:
            log_error(f'interface pick theme: {e}')


class AccountSettingsWindow(ctk.CTkToplevel):
    def __init__(self, master, current_username,
                 first_name, last_name, avatar_b64,
                 on_save, on_nick_change, on_avatar_pick,
                 on_change_password, on_delete_account, on_logout):
        super().__init__(master)
        self.title(t('account_settings'))
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_save_cb = on_save
        self.on_nick_change_cb = on_nick_change
        self.on_avatar_pick_cb = on_avatar_pick
        self.on_change_password_cb = on_change_password
        self.on_delete_account_cb = on_delete_account
        self.on_logout_cb = on_logout
        self._avatar_b64 = avatar_b64 or ''
        self._first_name = first_name or ''
        self._last_name = last_name or ''
        self._current_username = current_username or ''

        top = ctk.CTkFrame(self, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.pack(fill="x")
        top.pack_propagate(False)
        ctk.CTkLabel(top, text=t('account_settings'),
                     text_color=FG_TEXT,
                     font=get_font(16, "bold")
                     ).pack(side="left", padx=15, pady=13)
        ctk.CTkButton(top, text=t('close'), width=90, height=32,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.destroy
                      ).pack(side="right", padx=(5, 15), pady=13)

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      corner_radius=0)
        body.pack(fill="both", expand=True, padx=25, pady=20)

        avatar_wrap = ctk.CTkFrame(body, fg_color=BG_DARK)
        avatar_wrap.pack(anchor="center", pady=(0, 10))

        try:
            self.avatar_btn = ctk.CTkButton(
                avatar_wrap, text='📎',
                width=AVATAR_SIZE_BIG, height=AVATAR_SIZE_BIG,
                corner_radius=AVATAR_SIZE_BIG // 2,
                fg_color=BG_LIGHT, hover_color=BG_MID,
                font=get_font(30),
                compound='center',
                command=self._pick_avatar)
        except Exception:
            self.avatar_btn = ctk.CTkButton(
                avatar_wrap, text='📎',
                width=AVATAR_SIZE_BIG, height=AVATAR_SIZE_BIG,
                corner_radius=AVATAR_SIZE_BIG // 2,
                fg_color=BG_LIGHT, hover_color=BG_MID,
                font=get_font(30),
                command=self._pick_avatar)
        self.avatar_btn.pack()

        ctk.CTkLabel(body, text=t('first_name'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", pady=(10, 4))
        self.first_entry = ctk.CTkEntry(
            body, height=36, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.first_entry.insert(0, self._first_name)
        self.first_entry.pack(fill="x")

        ctk.CTkLabel(body, text=t('last_name'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", pady=(10, 4))
        self.last_entry = ctk.CTkEntry(
            body, height=36, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.last_entry.insert(0, self._last_name)
        self.last_entry.pack(fill="x")

        ctk.CTkLabel(body, text=t('username'), anchor="w",
                     text_color=FG_TEXT,
                     font=get_font(13)
                     ).pack(fill="x", pady=(10, 4))
        self.nick_entry = ctk.CTkEntry(
            body, height=36, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.nick_entry.insert(0, self._current_username)
        self.nick_entry.pack(fill="x")

        ctk.CTkButton(body, text=t('save'), height=42,
                      font=get_font(14, "bold"),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._save).pack(fill="x", pady=(20, 5))

        ctk.CTkFrame(body, height=2, fg_color=BG_LIGHT
                     ).pack(fill="x", pady=15)

        ctk.CTkButton(body, text=t('change_password'), height=42,
                      font=get_font(14),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_change_password
                      ).pack(fill="x", pady=5)

        ctk.CTkFrame(body, height=2, fg_color=BG_LIGHT
                     ).pack(fill="x", pady=15)

        ctk.CTkButton(body, text=t('delete_account'), height=42,
                      fg_color=RED, hover_color=RED_HOVER,
                      font=get_font(14),
                      command=self._do_delete
                      ).pack(fill="x", pady=5)

        ctk.CTkButton(body, text=t('logout'), height=42,
                      fg_color=RED, hover_color=RED_HOVER,
                      font=get_font(14),
                      command=self._do_logout
                      ).pack(fill="x", pady=5)

        self._refresh_avatar()
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _refresh_avatar(self):
        try:
            img = make_avatar_image(self._avatar_b64, AVATAR_SIZE_BIG)
            if img is not None:
                self.avatar_btn.configure(image=img, text='📎')
                try:
                    self.avatar_btn.configure(compound='center')
                except Exception:
                    pass
            else:
                self.avatar_btn.configure(image=None, text='📎')
        except Exception as e:
            log_error(f'refresh_avatar: {e}')

    def _pick_avatar(self):
        try:
            path = self.on_avatar_pick_cb()
            if not path:
                return
            size = os.path.getsize(path)
            if size > MAX_AVATAR_SIZE:
                custom_alert(self, t('error'),
                             t('avatar_too_big'))
                return
            with open(path, 'rb') as f:
                raw = f.read()
            self._avatar_b64 = base64.b64encode(raw).decode('ascii')
            self._refresh_avatar()
        except Exception as e:
            log_error(f'pick_avatar: {e}')

    def _save(self):
        fn = self.first_entry.get().strip()
        ln = self.last_entry.get().strip()
        nn = self.nick_entry.get().strip()
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_save_cb(fn, ln, self._avatar_b64)
            if nn and nn != self._current_username:
                self.on_nick_change_cb(nn)
        except Exception as e:
            log_error(f'account save: {e}')

    def _do_change_password(self):
        try:
            self.destroy()
        except Exception:
            pass
        self.on_change_password_cb()

    def _do_delete(self):
        try:
            self.destroy()
        except Exception:
            pass
        self.on_delete_account_cb()

    def _do_logout(self):
        try:
            self.destroy()
        except Exception:
            pass
        self.on_logout_cb()

    def _center(self):
        try:
            self.update_idletasks()
            h = max(self.winfo_reqheight(), 700)
            sh = self.winfo_screenheight()
            if h > sh - 40:
                h = sh - 40
            center_toplevel(self, 380, h)
        except Exception:
            center_toplevel(self, 380, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)


class SettingsWindow(ctk.CTkToplevel):
    def __init__(self, master, on_account_settings,
                 on_toggle_notifications, notifications_enabled,
                 on_pick_language, on_interface_settings,
                 on_about):
        super().__init__(master)
        self.title(t('settings'))
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_account_settings_cb = on_account_settings
        self.on_toggle_notifications_cb = on_toggle_notifications
        self.on_pick_language_cb = on_pick_language
        self.on_interface_settings_cb = on_interface_settings
        self.on_about_cb = on_about

        top = ctk.CTkFrame(self, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.pack(fill="x")
        top.pack_propagate(False)
        ctk.CTkLabel(top, text=t('settings'), text_color=FG_TEXT,
                     font=get_font(16, "bold")
                     ).pack(side="left", padx=15, pady=13)
        ctk.CTkButton(top, text=t('close'), width=90, height=32,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.destroy
                      ).pack(side="right", padx=(5, 15), pady=13)

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      corner_radius=0)
        body.pack(fill="both", expand=True, padx=20, pady=20)

        ctk.CTkButton(body, text=t('account_settings'), height=44,
                      font=get_font(14, "bold"),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_account_settings
                      ).pack(fill="x", pady=(0, 5))

        ctk.CTkFrame(body, height=2, fg_color=BG_LIGHT
                     ).pack(fill="x", pady=15)

        ctk.CTkButton(body, text=t('interface_settings'), height=42,
                      font=get_font(14),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_interface_settings
                      ).pack(fill="x", pady=5)

        notif_row = ctk.CTkFrame(body, fg_color=BG_DARK)
        notif_row.pack(fill="x", pady=5)
        ctk.CTkLabel(notif_row, text=t('notifications'),
                     text_color=FG_TEXT,
                     font=get_font(14), anchor="w"
                     ).pack(side="left", padx=(5, 10))
        self.notif_switch = ctk.CTkSwitch(
            notif_row, text="",
            font=get_font(14),
            command=self._do_toggle_notifications,
            onvalue=True, offvalue=False,
            progress_color=SWITCH_COLOR)
        self.notif_switch.pack(side="right", padx=5)
        if notifications_enabled:
            self.notif_switch.select()
        else:
            self.notif_switch.deselect()

        lang_row = ctk.CTkFrame(body, fg_color=BG_DARK)
        lang_row.pack(fill="x", pady=5)
        ctk.CTkLabel(lang_row, text=t('language'),
                     text_color=FG_TEXT,
                     font=get_font(14), anchor="w"
                     ).pack(side="left", padx=(5, 10))
        flag, _ = LANGUAGES.get(get_current_lang(),
                                ('🌐', 'Unknown'))
        ctk.CTkButton(lang_row, text=flag, width=60, height=36,
                      font=get_font(22),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_pick_language
                      ).pack(side="right", padx=5)

        ctk.CTkFrame(body, height=2, fg_color=BG_LIGHT
                     ).pack(fill="x", pady=15)

        ctk.CTkButton(body, text="О проекте", height=42,
                      font=get_font(14),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_about
                      ).pack(fill="x", pady=5)

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        try:
            self.update_idletasks()
            h = max(self.winfo_reqheight(), 500)
            sh = self.winfo_screenheight()
            if h > sh - 40:
                h = sh - 40
            center_toplevel(self, 440, h)
        except Exception:
            center_toplevel(self, 440, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _do_account_settings(self):
        try:
            self.destroy()
        except Exception:
            pass
        self.on_account_settings_cb()

    def _do_toggle_notifications(self):
        enabled = bool(self.notif_switch.get())
        try:
            self.on_toggle_notifications_cb(enabled)
        except Exception as e:
            log_error(f'toggle notifications: {e}')

    def _do_pick_language(self):
        self.on_pick_language_cb(self)

    def _do_interface_settings(self):
        try:
            self.on_interface_settings_cb(self)
        except Exception as e:
            log_error(f'interface settings: {e}')

    def _do_about(self):
        try:
            self.on_about_cb(self)
        except Exception as e:
            log_error(f'about: {e}')


class AboutWindow(ctk.CTkToplevel):
    def __init__(self, master):
        super().__init__(master)
        self.title("О проекте")
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)

        top = ctk.CTkFrame(self, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.pack(fill="x")
        top.pack_propagate(False)
        ctk.CTkLabel(top, text="О проекте", text_color=FG_TEXT,
                     font=get_font(16, "bold")
                     ).pack(side="left", padx=15, pady=13)
        ctk.CTkButton(top, text=t('close'), width=90, height=32,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.destroy
                      ).pack(side="right", padx=(5, 15), pady=13)

        body = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      corner_radius=0)
        body.pack(fill="both", expand=True, padx=25, pady=20)

        ctk.CTkLabel(body, text=ABOUT_TEXT, text_color=FG_TEXT,
                     font=get_font(13), justify="left",
                     anchor="w", wraplength=520
                     ).pack(fill="x")

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 620, 560)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)


class SearchDialog(ctk.CTkToplevel):
    def __init__(self, master, on_search, on_pick, on_manual_ip):
        super().__init__(master)
        self.title(t('search_title'))
        self.configure(fg_color=BG_DARK)
        self.resizable(False, False)
        self.on_search_cb = on_search
        self.on_pick_cb = on_pick
        self.on_manual_ip_cb = on_manual_ip

        ctk.CTkLabel(self, text=t('search_title'),
                     text_color=FG_TEXT,
                     font=get_font(14, "bold")
                     ).pack(pady=(15, 10), padx=15, anchor="w")

        row = ctk.CTkFrame(self, fg_color=BG_DARK)
        row.pack(fill="x", padx=15)
        row.grid_columnconfigure(0, weight=1)
        self.query_entry = ctk.CTkEntry(
            row, placeholder_text=t('search_placeholder'), height=36,
            fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.query_entry.grid(row=0, column=0, sticky="ew",
                              padx=(0, 8))
        self.query_entry.bind("<Return>", lambda e: self._do_search())
        ctk.CTkButton(row, text=t('search_btn'), width=100, height=36,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self._do_search).grid(row=0, column=1)

        self.status = ctk.CTkLabel(self, text="", text_color=FG_DIM,
                                   font=get_font(12))
        self.status.pack(fill="x", padx=15, pady=(10, 5))

        ctk.CTkButton(
            self, text=t('search_ip_btn'), height=36,
            fg_color=BG_LIGHT, hover_color=BG_DARK,
            command=self._do_manual_ip
        ).pack(side="bottom", fill="x", padx=15, pady=(0, 15))

        self.results_frame = ctk.CTkScrollableFrame(
            self, fg_color=BG_MID, height=300)
        self.results_frame.pack(fill="both", expand=True,
                                padx=15, pady=(0, 15))

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(80, self._center)
        self.after(150, lambda: self.query_entry.focus_set())

    def _center(self):
        center_toplevel(self, 460, 520)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def _do_search(self):
        q = self.query_entry.get().strip()
        if not q:
            return
        try:
            self.status.configure(text=t('searching'))
        except Exception:
            pass
        try:
            self.on_search_cb(q)
        except Exception as e:
            log_error(f'Search callback: {e}')

    def _do_manual_ip(self):
        try:
            self.destroy()
        except Exception:
            pass
        try:
            self.on_manual_ip_cb()
        except Exception as e:
            log_error(f'Manual IP callback: {e}')

    def show_results(self, users, query):
        try:
            for w in self.results_frame.winfo_children():
                w.destroy()
        except Exception:
            return
        if not users:
            try:
                self.status.configure(text=t('search_nothing'))
            except Exception:
                pass
            return
        try:
            self.status.configure(
                text=t('search_found', len(users)))
        except Exception:
            pass
        for u in users:
            try:
                if isinstance(u, dict):
                    name = u.get('name', '')
                    online = bool(u.get('online'))
                else:
                    name = str(u)
                    online = False
                label = f"● {name}" if online else f"○ {name}"
                ctk.CTkButton(
                    self.results_frame, text=label, anchor="w",
                    height=36, fg_color="transparent",
                    hover_color=BG_LIGHT, text_color=FG_TEXT,
                    font=get_font(13),
                    command=lambda n=name: self._pick(n)
                ).pack(fill="x", padx=4, pady=2)
            except Exception:
                continue

    def _pick(self, username):
        try:
            self.on_pick_cb(username)
        except Exception as e:
            log_error(f'Pick callback: {e}')
        try:
            self.destroy()
        except Exception:
            pass


class SimpleInputDialog(ctk.CTkToplevel):
    def __init__(self, master, text, title, show=None, initial=''):
        super().__init__(master)
        self.title(title)
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.result = None

        ctk.CTkLabel(self, text=text, text_color=FG_TEXT,
                     font=get_font(13), wraplength=380,
                     justify="center").pack(padx=25, pady=(20, 12))
        self.entry = ctk.CTkEntry(self, width=380, height=30,
                                  fg_color=BG_INPUT, border_width=0,
                                  show=show,
                                  font=get_font(13))
        if initial:
            try:
                self.entry.insert(0, initial)
            except Exception:
                pass
        self.entry.pack(padx=25, pady=(0, 14))
        self.entry.focus_set()
        row = ctk.CTkFrame(self, fg_color=BG_MID)
        row.pack(padx=25, pady=(0, 20))
        ctk.CTkButton(row, text="Ok", width=180, height=34,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.on_ok).pack(side="left",
                                               padx=(0, 8))
        ctk.CTkButton(row, text=t('cancel'), width=180, height=34,
                      fg_color=BG_LIGHT, hover_color=BG_DARK,
                      command=self.on_cancel).pack(side="left")
        self.entry.bind("<Return>",
                        lambda e: (self.on_ok(), "break")[1])
        self.bind("<Escape>", lambda e: self.on_cancel())
        self.protocol("WM_DELETE_WINDOW", self.on_cancel)
        self.transient(master)
        self.grab_set()
        self.after(50, self._center)

    def _center(self):
        center_toplevel(self, 440, None)
        animate_alpha(self, 0.0, 1.0, duration_ms=200, steps=12,
                      ease='back')
        bring_to_front(self)

    def on_ok(self):
        self.result = self.entry.get()
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass

    def on_cancel(self):
        self.result = None
        try:
            self.grab_release()
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


def ask_input(master, text, title, show=None, initial=''):
    try:
        d = SimpleInputDialog(master, text=text, title=title,
                              show=show, initial=initial)
        d.wait_window()
        return d.result
    except Exception as e:
        log_error(f'ask_input: {e}')
        return None


class EmojiPicker(ctk.CTkToplevel):
    def __init__(self, master, on_pick):
        super().__init__(master)
        self.title("Emoji")
        self.configure(fg_color=BG_MID)
        self.resizable(False, False)
        self.on_pick_cb = on_pick

        grid = ctk.CTkScrollableFrame(self, fg_color=BG_DARK,
                                      width=380, height=320)
        grid.pack(padx=15, pady=15)

        for i in range(8):
            grid.grid_columnconfigure(i, weight=1)

        for idx, em in enumerate(EMOJI_LIST):
            r = idx // 8
            c = idx % 8
            try:
                ctk.CTkButton(
                    grid, text=em, width=38, height=38,
                    fg_color="transparent",
                    hover_color=BG_LIGHT,
                    font=get_font(20),
                    command=lambda e=em: self._pick(e)
                ).grid(row=r, column=c, padx=1, pady=1)
            except Exception:
                continue

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(50, self._center)
        self.bind("<Escape>", lambda e: self.destroy())

    def _center(self):
        try:
            self.update_idletasks()
            h = self.winfo_reqheight()
        except Exception:
            h = 380
        if h < 380:
            h = 380
        center_toplevel(self, 420, h)
        animate_alpha(self, 0.0, 1.0, duration_ms=180, steps=12,
                      ease='back')
        bring_to_front(self)

    def _pick(self, emoji):
        try:
            self.on_pick_cb(emoji)
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


class ChatterApp:
    def __init__(self):
        settings = load_settings()
        set_language(settings.get('language', 'ru'))
        set_font_by_code(settings.get('font', 'standard'))
        apply_theme(settings.get('theme', 'black'))

        self.root = ctk.CTk()
        try:
            _apply_global_font_family(_current_font_family)
        except Exception:
            pass

        self.root.title("Chatter")
        self.root.geometry("1100x750")
        self.root.configure(fg_color=BG_DARK)
        self.root.protocol("WM_DELETE_WINDOW", self.on_window_close)

        self._is_fullscreen = False

        self.root.update_idletasks()
        self.root.withdraw()
        self.root.update_idletasks()

        self.my_username = ''
        self.my_first_name = ''
        self.my_last_name = ''
        self.my_avatar_b64 = ''
        self.known_users = []
        self.reply_to = None
        self.conn_state = 'idle'
        self.blocked_users = set()
        self.user_profiles = {}

        self.identity = E2EIdentity()

        self.e2e_verified = set(
            settings.get('e2e_verified', []) or [])

        self.loop = None
        self.reader = None
        self.writer = None
        self.send_queue = None
        self.server_host = None
        self.heartbeat_running = False

        self.my_server = ChatServer()
        self.this_is_server = False
        self.local_users_known = set()

        self._saved_username = None
        self._saved_password = None
        self._pending_new_password = None
        self._auto_reconnect_active = False
        self.manual_server_ip = None
        self._reopen_search_after_connect = False
        self._connecting_ip_display = ''
        self._last_search_query = ''
        self._pending_encrypted = []

        self.audio = AudioEngine()
        self.voice_recorder = VoiceRecorder()
        self.voice_player = VoicePlayer()
        self._voice_recording = False
        self._voice_record_start = 0.0
        self._voice_record_job = None
        self.current_playing_voice = None

        self.call_state = 'idle'
        self.call_id = None
        self.call_peer = None
        self.call_is_outgoing = False
        self.call_window = None
        self.incoming_call_window = None
        self._call_timeout_job = None
        self._pending_peer_ip = None
        self._pending_peer_port = None

        self.chat_picker_dialog = None

        self.notifications_enabled = bool(
            settings.get('notifications', True))
        self.blocked_users = set(settings.get('blocked', []) or [])
        self.my_avatar_b64 = settings.get('avatar', '') or ''
        self.my_first_name = settings.get('first_name', '') or ''
        self.my_last_name = settings.get('last_name', '') or ''

        self.chats = {}
        self.current_chat = None
        self.chat_frames = {}
        self.chat_buttons = {}
        self.chat_avatars = {}
        self.chat_rows = {}
        self.empty_chat_labels = {}

        self.session_id = uuid.uuid4().hex[:6]
        self.msg_counter = 0
        self.msg_widgets = {}
        self.pending_msgs = {}
        self.typing_dm = {}
        self.last_typing_sent = 0.0
        self._typing_phase = 0

        self.gui_queue = queue.Queue()
        self._incoming_bucket = TokenBucket(200.0, 400)
        self.auth_window = None
        self.search_dialog = None
        self.settings_window = None
        self.account_window = None
        self.emoji_picker = None
        self.language_picker = None
        self.font_picker = None
        self.theme_picker = None
        self.interface_window = None
        self.about_window = None
        self._notification_popup = None
        self._pending_attachment = None

        self._build_ui()
        self._poll_queue()
        self._update_typing_label()
        self._status_loop()
        self._bind_hotkeys()

    @property
    def connected(self):
        return self.conn_state == 'connected'

    def _bind_hotkeys(self):
        try:
            self.root.bind('<F11>',
                           lambda e: self._toggle_fullscreen())
            self.root.bind('<Escape>',
                           lambda e: self._exit_fullscreen())
        except Exception:
            pass

    def _toggle_fullscreen(self):
        try:
            if self._is_fullscreen:
                self.root.attributes('-fullscreen', False)
                self._is_fullscreen = False
            else:
                self.root.attributes('-fullscreen', True)
                self._is_fullscreen = True
        except Exception as e:
            log_error(f'toggle fullscreen: {e}')

    def _exit_fullscreen(self):
        try:
            if self._is_fullscreen:
                self.root.attributes('-fullscreen', False)
                self._is_fullscreen = False
        except Exception:
            pass

    def _new_msg_id(self):
        self.msg_counter += 1
        return (f"{self.my_username}-{self.session_id}-"
                f"{self.msg_counter}")

    def _animate_bubble_appear(self, bubble, is_own,
                               duration_ms=340, steps=18):
        start_extra = 34
        interval = max(1, duration_ms // max(1, steps))

        def tick(i):
            try:
                if not bubble.winfo_exists():
                    return
                t = i / float(steps)
                e = ease_out_back(t, 2.6)
                extra = int(start_extra * (1.0 - e))
                if extra < 0:
                    extra = 0
                if is_own:
                    px = (extra + 4, 4)
                else:
                    px = (4, extra + 4)
                r = int(11 * e)
                if r < 0:
                    r = 0
                if r > 18:
                    r = 18
                bubble.pack_configure(padx=px)
                bubble.configure(corner_radius=r)
                if i < steps:
                    bubble.after(interval, lambda: tick(i + 1))
                else:
                    bubble.pack_configure(padx=(4, 4))
                    bubble.configure(corner_radius=10)
            except Exception:
                pass

        try:
            if is_own:
                bubble.pack_configure(padx=(start_extra + 4, 4))
            else:
                bubble.pack_configure(padx=(4, start_extra + 4))
            bubble.configure(corner_radius=0)
            bubble.after(interval, lambda: tick(1))
        except Exception:
            pass

    def _is_creator(self, username):
        try:
            return bool(username) and username == CREATOR_USERNAME
        except Exception:
            return False

    def _make_creator_badge(self, parent, size=15):
        try:
            badge = ctk.CTkLabel(
                parent, text="✓",
                text_color=CREATOR_COLOR,
                font=get_font(size, "bold"),
                fg_color="transparent")
            Tooltip(badge, t('creator_badge'))
            return badge
        except Exception as e:
            log_error(f'_make_creator_badge: {e}')
            return None

    def _get_avatar_for(self, username, size=AVATAR_SIZE_CHAT):
        prof = self.user_profiles.get(username)
        if username == self.my_username:
            b64 = self.my_avatar_b64
            fn = self.my_first_name
            ln = self.my_last_name
        elif prof:
            b64 = prof.get('avatar', '')
            fn = prof.get('first_name', '')
            ln = prof.get('last_name', '')
        else:
            b64 = ''
            fn = ''
            ln = ''
        img = make_avatar_image(b64, size)
        if img is None:
            img = make_initials_avatar(fn, ln, username, size)
        return img

    def _setup_self_chat(self):
        if not self.my_username:
            return
        display = self.my_first_name
        if self.my_last_name:
            display = f"{display} {self.my_last_name}".strip()
        if not display:
            display = self.my_username
        display = f"{display} {t('you_suffix')}"
        if SELF_CHAT_ID not in self.chats:
            self.chats[SELF_CHAT_ID] = {'name': display, 'messages': []}
            self.add_chat_to_list(SELF_CHAT_ID, display)
            self.get_or_create_chat_frame(SELF_CHAT_ID)
        else:
            self.chats[SELF_CHAT_ID]['name'] = display
            b = self.chat_buttons.get(SELF_CHAT_ID)
            if b is not None:
                try:
                    b.configure(text=display)
                except Exception:
                    pass
            self._refresh_chat_avatar(SELF_CHAT_ID)
        try:
            self.update_header()
        except Exception:
            pass

    def _my_public_key(self):
        try:
            if self.identity and self.identity.public_key_b64:
                return self.identity.public_key_b64
        except Exception:
            pass
        return ''

    def _get_peer_pubkey(self, username):
        if not HAS_CRYPTO:
            return None
        if not username or username == self.my_username:
            return None
        if not self.identity or not self.identity.private_key:
            return None
        prof = self.user_profiles.get(username)
        if not prof:
            return None
        pk = prof.get('public_key', '')
        if pk:
            return pk
        return None

    def _is_encrypted_payload(self, obj):
        text = obj.get('text', '')
        if isinstance(text, str) and text.startswith(E2E_PREFIX):
            return True
        att = obj.get('attachment')
        if isinstance(att, dict) and att.get('encrypted'):
            return True
        if obj.get('encrypted'):
            return True
        return False

    def _encrypt_for_peer(self, target, text, attachment):
        if not HAS_CRYPTO:
            return text, attachment, False
        if not self.identity or not self.identity.private_key:
            return text, attachment, False
        if not target or target == SELF_CHAT_ID:
            return text, attachment, False
        peer_pub = self._get_peer_pubkey(target)
        if not peer_pub:
            return text, attachment, False
        shared = self.identity.derive_shared_key(peer_pub)
        if not shared:
            return text, attachment, False

        net_text = text
        if text:
            enc = e2e_encrypt(shared, text.encode('utf-8'))
            if enc:
                net_text = E2E_PREFIX + enc

        net_att = attachment
        if attachment:
            net_att = dict(attachment)
            b64 = attachment.get('data', '')
            if b64:
                try:
                    raw = base64.b64decode(b64)
                    enc = e2e_encrypt(shared, raw)
                    if enc:
                        net_att['data'] = enc
                        net_att['encrypted'] = True
                except Exception as e:
                    log_error(f'_encrypt_for_peer att: {e}')

        return net_text, net_att, True

    def _try_decrypt_dm(self, sender, obj):
        pubkey = self._get_peer_pubkey(sender)
        if pubkey is None:
            return False
        shared = self.identity.derive_shared_key(pubkey)
        if not shared:
            return False

        text = obj.get('text', '')
        if isinstance(text, str) and text.startswith(E2E_PREFIX):
            enc_part = text[len(E2E_PREFIX):]
            dec = e2e_decrypt(shared, enc_part)
            if dec is not None:
                try:
                    obj['text'] = dec.decode('utf-8')
                except Exception:
                    obj['text'] = t('e2e_decrypt_fail')
            else:
                obj['text'] = t('e2e_decrypt_fail')

        att = obj.get('attachment')
        if isinstance(att, dict) and att.get('encrypted'):
            b64 = att.get('data', '')
            if b64:
                dec = e2e_decrypt(shared, b64)
                if dec is not None:
                    att['data'] = base64.b64encode(dec).decode('ascii')
                    att['encrypted'] = False
                else:
                    att['data'] = ''
                    att['name'] = t('e2e_decrypt_fail')

        return True

    def _flush_pending_encrypted(self, username=None):
        if not self._pending_encrypted:
            return
        remaining = []
        for obj in self._pending_encrypted:
            if username and obj.get('from') != username:
                remaining.append(obj)
                continue
            sender = obj.get('from', '')
            if self._get_peer_pubkey(sender) is None:
                remaining.append(obj)
                continue
            if not self._try_decrypt_dm(sender, obj):
                remaining.append(obj)
                continue
            self._process_incoming_dm(obj)
        self._pending_encrypted = remaining

    def _save_e2e_verified(self):
        try:
            st = load_settings()
            st['e2e_verified'] = list(self.e2e_verified)
            save_settings(st)
        except Exception as e:
            log_error(f'_save_e2e_verified: {e}')

    def _show_fingerprint(self, username):
        if not HAS_CRYPTO:
            custom_alert(self.root, t('e2e_title'),
                         t('e2e_unavailable'))
            return
        my_pk = self._my_public_key()
        prof = self.user_profiles.get(username) or {}
        peer_pk = prof.get('public_key', '')
        if not peer_pk:
            self._request_profile(username)
            custom_alert(self.root, t('e2e_title'),
                         t('e2e_wait_key'))
            return
        fp = e2e_fingerprint(my_pk, peer_pk)
        if not fp:
            custom_alert(self.root, t('e2e_title'),
                         t('e2e_unavailable'))
            return
        custom_alert(self.root, t('e2e_title'),
                     t('e2e_fingerprint', username, fp))
        ok = custom_confirm(
            self.root, t('e2e_title'),
            t('e2e_confirm_match'), danger=False)
        if ok:
            if username not in self.e2e_verified:
                self.e2e_verified.add(username)
                self._save_e2e_verified()
            try:
                custom_alert(self.root, t('done'),
                             t('e2e_marked_verified'),
                             auto_close_ms=1500)
            except Exception:
                pass
        else:
            if username in self.e2e_verified:
                self.e2e_verified.discard(username)
                self._save_e2e_verified()
            try:
                custom_alert(self.root, t('done'),
                             t('e2e_marked_unverified'),
                             auto_close_ms=1500)
            except Exception:
                pass
        try:
            self.update_header()
        except Exception:
            pass

    def _build_ui(self):
        self.root.grid_columnconfigure(1, weight=1)
        self.root.grid_rowconfigure(0, weight=1)

        left = ctk.CTkFrame(self.root, width=240, fg_color=BG_MID,
                            corner_radius=0)
        left.grid(row=0, column=0, sticky="nsew")
        left.grid_propagate(False)

        ctk.CTkLabel(left, text=t('chats'),
                     font=get_font(15, "bold"),
                     text_color=FG_TEXT).pack(pady=(18, 6))

        ctk.CTkButton(left, text=t('find_user'),
                      height=32, font=get_font(12),
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.open_search
                      ).pack(fill="x", padx=8, pady=(0, 8))

        self.chats_list = ctk.CTkScrollableFrame(left,
                                                 fg_color=BG_MID)
        self.chats_list.pack(fill="both", expand=True,
                             padx=5, pady=5)

        right = ctk.CTkFrame(self.root, fg_color=BG_DARK,
                             corner_radius=0)
        right.grid(row=0, column=1, sticky="nsew")
        right.grid_rowconfigure(2, weight=1)
        right.grid_columnconfigure(0, weight=1)

        top = ctk.CTkFrame(right, height=58, fg_color=BG_MID,
                           corner_radius=0)
        top.grid(row=0, column=0, sticky="ew")
        top.grid_propagate(False)

        self.header_label = ctk.CTkLabel(
            top, text=t('connecting'), text_color=FG_TEXT,
            font=get_font(14, "bold"))
        self.header_label.pack(side="left", padx=(15, 0))

        self.header_creator_badge = self._make_creator_badge(top, size=15)

        ctk.CTkButton(top, text="⚙", width=40, height=32,
                      font=get_font(16),
                      command=self.open_settings
                      ).pack(side="right", padx=(5, 15), pady=13)

        self.call_btn = ctk.CTkButton(
            top, text="📞", width=40, height=32,
            font=get_font(16),
            fg_color=BG_LIGHT, hover_color=GREEN,
            command=self._on_call_button)
        self.call_btn.pack(side="right", padx=(5, 5), pady=13)
        self.call_btn.pack_forget()

        self.status_bar = ctk.CTkFrame(right, height=20,
                                       fg_color=BG_DARK,
                                       corner_radius=0)
        self.status_bar.grid(row=1, column=0, sticky="ew")
        self.status_bar.grid_propagate(False)

        self.status_label = ctk.CTkLabel(
            self.status_bar, text="", text_color=FG_DIM,
            font=get_font(11), anchor="w")
        self.status_label.pack(side="left", padx=(30, 0))

        self.e2e_label = ctk.CTkLabel(
            self.status_bar, text="", text_color=FG_TEXT,
            font=get_font(10), anchor="center")
        self.e2e_label.pack(side="left", fill="x", expand=True,
                            padx=(0, 30))

        self.chat_container = ctk.CTkFrame(right,
                                           fg_color=BG_DARK,
                                           corner_radius=0)
        self.chat_container.grid(row=2, column=0, sticky="nsew",
                                 padx=5, pady=5)
        self.chat_container.grid_rowconfigure(0, weight=1)
        self.chat_container.grid_columnconfigure(0, weight=1)

        self.empty_label = ctk.CTkLabel(
            self.chat_container,
            text=t('select_chat'),
            font=get_font(18), text_color=FG_DIM)
        self.empty_label.grid(row=0, column=0)

        bottom = ctk.CTkFrame(right, fg_color=BG_MID,
                              corner_radius=0)
        bottom.grid(row=3, column=0, sticky="ew")
        bottom.grid_remove()
        self.bottom_frame = bottom

        self.reply_bar = ctk.CTkFrame(bottom, fg_color=BG_LIGHT,
                                      corner_radius=6)
        self.reply_label = ctk.CTkLabel(
            self.reply_bar, text="", anchor="w",
            text_color=YELLOW, font=get_font(12))
        self.reply_label.pack(side="left", padx=10, pady=6,
                              fill="x", expand=True)
        ctk.CTkButton(self.reply_bar, text="✕", width=30, height=24,
                      fg_color=BG_LIGHT, hover_color=BG_DARK,
                      command=self.cancel_reply
                      ).pack(side="right", padx=6, pady=6)

        self.input_row = ctk.CTkFrame(bottom, fg_color=BG_MID)
        self.input_row.pack(fill="x", padx=10, pady=(8, 0))
        self.input_row.grid_columnconfigure(2, weight=1)

        ctk.CTkButton(self.input_row, text="📎", width=42,
                      height=42, font=get_font(18),
                      fg_color=BG_LIGHT, hover_color=BG_DARK,
                      command=self.on_attach
                      ).grid(row=0, column=0, padx=(0, 8))

        ctk.CTkButton(self.input_row, text="😊", width=42,
                      height=42, font=get_font(18),
                      fg_color=BG_LIGHT, hover_color=BG_DARK,
                      command=self.open_emoji_picker
                      ).grid(row=0, column=1, padx=(0, 8))

        self.msg_entry = ctk.CTkEntry(
            self.input_row,
            placeholder_text=t('input_placeholder'),
            height=42, fg_color=BG_INPUT, border_width=0,
            font=get_font(13))
        self.msg_entry.grid(row=0, column=2, sticky="ew",
                            padx=(0, 8))
        self.msg_entry.bind("<Return>", lambda e: self.on_send())
        self.msg_entry.bind("<KeyRelease>", self._on_typing_key)

        self.voice_btn = ctk.CTkButton(
            self.input_row, text="🎤", width=48,
            height=42, font=get_font(18),
            fg_color=BTN, hover_color=BTN_HOVER,
            command=self.on_voice_click)
        self.voice_btn.grid(row=0, column=3, padx=(0, 8))

        ctk.CTkButton(self.input_row, text=t('send'), width=120,
                      height=42,
                      fg_color=BTN, hover_color=BTN_HOVER,
                      command=self.on_send).grid(row=0, column=4)

        self.attachment_bar = ctk.CTkFrame(bottom, fg_color=BG_LIGHT,
                                           corner_radius=6)
        self.attachment_label = ctk.CTkLabel(
            self.attachment_bar, text="", anchor="w",
            text_color=FG_TEXT, font=get_font(12))
        self.attachment_label.pack(side="left", padx=10, pady=6,
                                   fill="x", expand=True)
        ctk.CTkButton(self.attachment_bar, text="✕", width=30,
                      height=24, fg_color=BG_LIGHT,
                      hover_color=BG_DARK,
                      command=self.cancel_attachment
                      ).pack(side="right", padx=6, pady=6)

        try:
            self.attachment_bar.bind("<Return>",
                                     lambda e: self.on_send())
            self.attachment_label.bind("<Return>",
                                       lambda e: self.on_send())
        except Exception:
            pass

        self.typing_label = ctk.CTkLabel(
            bottom, text="", text_color=FG_DIM, anchor="w",
            font=get_font(12), height=16)
        self.typing_label.pack(fill="x", padx=15, pady=(2, 6))

        self.input_row.pack_forget()

    def on_voice_click(self):
        if not self.connected or self.current_chat is None:
            return
        if self.call_state != 'idle':
            custom_alert(self.root, t('error'),
                         t('call_in_progress'))
            return
        if not HAS_AUDIO:
            custom_alert(self.root, t('error'), t('no_audio_device'))
            return
        if self._voice_recording:
            self._finish_voice_recording()
        else:
            self._start_voice_recording()

    def _start_voice_recording(self):
        if not self.voice_recorder.start():
            custom_alert(self.root, t('error'), t('no_audio_device'))
            return
        self._voice_recording = True
        self._voice_record_start = time.time()
        try:
            self.voice_btn.configure(
                fg_color=RED, hover_color=RED_HOVER, text="⏹")
        except Exception:
            pass
        try:
            self.msg_entry.configure(
                placeholder_text=f"{t('voice_recording')} 0:00 / 1:00")
        except Exception:
            pass
        self._schedule_voice_indicator()

    def _schedule_voice_indicator(self):
        if not self._voice_recording:
            return
        elapsed = time.time() - self._voice_record_start
        try:
            self.msg_entry.configure(
                placeholder_text=(
                    f"{t('voice_recording')} "
                    f"{format_duration(elapsed)} / "
                    f"{format_duration(MAX_VOICE_SECONDS)}"))
        except Exception:
            pass
        if elapsed >= MAX_VOICE_SECONDS:
            self._finish_voice_recording()
            return
        try:
            self._voice_record_job = self.root.after(
                200, self._schedule_voice_indicator)
        except Exception:
            self._voice_record_job = None

    def _cancel_voice_recording(self):
        if not self._voice_recording:
            return
        self._voice_recording = False
        if self._voice_record_job is not None:
            try:
                self.root.after_cancel(self._voice_record_job)
            except Exception:
                pass
            self._voice_record_job = None
        try:
            self.voice_recorder.cancel()
        except Exception:
            pass
        try:
            self.voice_btn.configure(
                fg_color=BTN, hover_color=BTN_HOVER, text="🎤")
        except Exception:
            pass
        try:
            self.msg_entry.configure(
                placeholder_text=t('input_placeholder'))
        except Exception:
            pass

    def _finish_voice_recording(self):
        if not self._voice_recording:
            return
        self._voice_recording = False
        if self._voice_record_job is not None:
            try:
                self.root.after_cancel(self._voice_record_job)
            except Exception:
                pass
            self._voice_record_job = None
        duration = time.time() - self._voice_record_start
        frames = self.voice_recorder.stop()
        try:
            self.voice_btn.configure(
                fg_color=BTN, hover_color=BTN_HOVER, text="🎤")
        except Exception:
            pass
        try:
            self.msg_entry.configure(
                placeholder_text=t('input_placeholder'))
        except Exception:
            pass
        min_bytes = int(AUDIO_SAMPLE_RATE *
                        AUDIO_CHANNELS * 2 * 0.3)
        if len(frames) < min_bytes:
            return
        wav_bytes = self._frames_to_wav(frames)
        b64 = base64.b64encode(wav_bytes).decode('ascii')
        attachment = {
            'name': 'voice.wav',
            'mime': 'audio/wav',
            'data': b64,
            'size': len(wav_bytes),
            'filepath': '',
            'voice': True,
            'duration': duration,
        }

        target = self.current_chat
        if target is None:
            return

        if target == SELF_CHAT_ID:
            msg_id = self._new_msg_id()
            self.add_message(SELF_CHAT_ID, self.my_username, '',
                             True, msg_id=msg_id, show_status=True,
                             attachment=attachment)
            return

        net_text, net_att, _enc = self._encrypt_for_peer(
            target, '', attachment)
        msg_id = self._new_msg_id()
        payload = {'type': 'dm', 'to': target, 'text': net_text,
                   'id': msg_id, 'attachment': net_att,
                   'encrypted': True}
        reply = None
        if self.reply_to:
            reply = {'target': self.reply_to['target'],
                     'quote': self.reply_to['preview']}
            payload['reply'] = reply
        self._send_obj(payload)
        self.add_message(target, self.my_username, '', True,
                         msg_id=msg_id, reply=reply,
                         show_status=True, attachment=attachment)
        self.cancel_reply()

    def _frames_to_wav(self, frames):
        try:
            buf = io.BytesIO()
            with wave.open(buf, 'wb') as wf:
                wf.setnchannels(AUDIO_CHANNELS)
                wf.setsampwidth(2)
                wf.setframerate(AUDIO_SAMPLE_RATE)
                wf.writeframes(frames)
            return buf.getvalue()
        except Exception as e:
            log_error(f'_frames_to_wav: {e}')
            return b''

    def _render_voice_message(self, bubble, attachment, entry_dict):
        try:
            row = ctk.CTkFrame(bubble, fg_color=BG_INPUT,
                               corner_radius=20)
            row.pack(fill="x", padx=12, pady=(4, 8))

            dur = float(attachment.get('duration', 0))
            dur_text = format_duration(dur)

            play_btn = ctk.CTkButton(
                row, text="▶", width=38, height=38,
                corner_radius=19,
                font=get_font(14),
                fg_color=BG_LIGHT, hover_color=BG_DARK,
                command=lambda: self._toggle_voice_play(
                    entry_dict, attachment))
            play_btn.pack(side="left", padx=(6, 8), pady=6)

            info_lbl = ctk.CTkLabel(
                row, text=f"🎤 {dur_text}",
                text_color=FG_TEXT, anchor="w",
                font=get_font(12))
            info_lbl.pack(side="left", fill="x", expand=True, pady=6)

            save_btn = ctk.CTkButton(
                row, text="💾", width=34, height=34,
                corner_radius=17,
                font=get_font(12),
                fg_color=BG_LIGHT, hover_color=BG_DARK,
                command=lambda a=attachment:
                    self._save_attachment(a))
            save_btn.pack(side="right", padx=(4, 6), pady=6)

            entry_dict['voice_play_btn'] = play_btn
            entry_dict['voice_info_lbl'] = info_lbl
            entry_dict['voice_duration'] = dur
        except Exception as e:
            log_error(f'_render_voice_message: {e}')

    def _toggle_voice_play(self, entry_dict, attachment):
        if self.call_state != 'idle':
            custom_alert(self.root, t('error'),
                         t('call_in_progress'))
            return
        if self.current_playing_voice is entry_dict:
            self._stop_voice_playback()
            return
        self._stop_voice_playback()
        wav_bytes = None
        b64 = attachment.get('data', '')
        if b64:
            try:
                wav_bytes = base64.b64decode(b64)
            except Exception:
                wav_bytes = None
        if wav_bytes is None:
            path = attachment.get('filepath', '') or ''
            if path and os.path.exists(path):
                try:
                    with open(path, 'rb') as f:
                        wav_bytes = f.read()
                except Exception:
                    wav_bytes = None
        if wav_bytes is None:
            return

        self.current_playing_voice = entry_dict

        def on_finished():
            self._post(self._on_voice_finished, entry_dict)

        if not self.voice_player.play(wav_bytes,
                                      on_finished=on_finished):
            self.current_playing_voice = None
            return
        try:
            entry_dict['voice_play_btn'].configure(text="⏸")
        except Exception:
            pass

    def _stop_voice_playback(self):
        entry = self.current_playing_voice
        self.current_playing_voice = None
        try:
            self.voice_player.stop()
        except Exception:
            pass
        if entry is not None:
            try:
                entry['voice_play_btn'].configure(text="▶")
            except Exception:
                pass

    def _on_voice_finished(self, entry_dict):
        if self.current_playing_voice is entry_dict:
            self.current_playing_voice = None
        try:
            if entry_dict.get('voice_play_btn') is not None:
                entry_dict['voice_play_btn'].configure(text="▶")
        except Exception:
            pass

    def start_forward(self, entry):
        chats_list = []
        for cid, info in self.chats.items():
            if cid == SELF_CHAT_ID:
                continue
            chats_list.append((cid, info))
        if not chats_list:
            custom_alert(self.root, t('error'),
                         t('forward_no_chats'))
            return

        def sort_key(item):
            cid, info = item
            online = cid in self.known_users
            return (0 if online else 1,
                    (info.get('name', cid) or cid).lower())
        chats_list.sort(key=sort_key)

        try:
            if (self.chat_picker_dialog
                    and self.chat_picker_dialog.winfo_exists()):
                self.chat_picker_dialog.destroy()
        except Exception:
            pass

        def on_pick(target_cid):
            self._do_forward(entry, target_cid)

        try:
            self.chat_picker_dialog = ChatPickerDialog(
                self.root, chats_list, on_pick=on_pick)
        except Exception as e:
            log_error(f'ChatPickerDialog: {e}')

    def _do_forward(self, entry, target_cid):
        if not target_cid or target_cid not in self.chats:
            return
        if not self.connected:
            custom_alert(self.root, t('error'), t('connect_fail'))
            return

        text = entry.get('text', '') or ''
        attachment_src = entry.get('attachment')
        sender = entry.get('sender', '')
        is_own = entry.get('is_own', False)

        attachment = None
        if attachment_src:
            attachment = dict(attachment_src)
            if not attachment.get('data'):
                path = attachment.get('filepath') or ''
                if path and os.path.exists(path):
                    try:
                        with open(path, 'rb') as f:
                            raw = f.read()
                        attachment['data'] = base64.b64encode(
                            raw).decode('ascii')
                    except Exception as e:
                        log_error(f'forward re-encode: {e}')
                if not attachment.get('data'):
                    attachment = None

        if not text and not attachment:
            custom_alert(self.root, t('error'), t('forward_empty'))
            return

        local_attachment = None
        if attachment:
            local_attachment = dict(attachment)
            try:
                p = local_attachment.get('filepath') or ''
                if p and os.path.exists(p):
                    local_attachment['data'] = ''
            except Exception:
                pass

        fwd_from = self.my_username if is_own else sender

        if target_cid == SELF_CHAT_ID:
            net_text = text
            net_att = attachment
            enc_flag = False
        else:
            net_text, net_att, enc_flag = self._encrypt_for_peer(
                target_cid, text, attachment)

        msg_id = self._new_msg_id()
        payload = {
            'type': 'dm',
            'to': target_cid,
            'text': net_text,
            'id': msg_id,
            'forwarded_from': fwd_from,
        }
        if net_att:
            payload['attachment'] = net_att
        if enc_flag:
            payload['encrypted'] = True

        self._send_obj(payload)
        self.add_message(
            target_cid, self.my_username, text, True,
            msg_id=msg_id, show_status=True,
            attachment=local_attachment,
            forwarded_from=fwd_from)

        try:
            custom_alert(self.root, t('done'), t('forwarded'),
                         auto_close_ms=1200)
        except Exception:
            pass

    def _on_call_button(self):
        if self.call_state != 'idle':
            try:
                if (self.call_window
                        and self.call_window.winfo_exists()):
                    self.call_window.lift()
            except Exception:
                pass
            return
        if not self.current_chat or self.current_chat == SELF_CHAT_ID:
            return
        if self.current_chat == self.my_username:
            return
        if not self.connected:
            custom_alert(self.root, t('error'), t('connect_fail'))
            return
        if not HAS_AUDIO:
            custom_alert(self.root, t('error'), t('no_audio_device'))
            return
        peer = self.current_chat
        if peer not in self.known_users:
            custom_alert(self.root, t('error'), t('call_peer_offline'))
            return

        if self._voice_recording:
            self._cancel_voice_recording()
        self._stop_voice_playback()

        if not self.audio.start():
            custom_alert(self.root, t('error'), t('no_audio_device'))
            return

        self.call_id = uuid.uuid4().hex
        self.call_peer = peer
        self.call_is_outgoing = True
        self.call_state = 'calling'

        try:
            self.call_window = CallWindow(
                self.root, peer,
                on_hangup=self._end_call,
                on_toggle_mute=self._toggle_call_mute)
            self.call_window.set_status(t('call_ringing'))
        except Exception as e:
            log_error(f'CallWindow: {e}')

        self._send_obj({
            'type': 'call_signal',
            'action': 'invite',
            'to': peer,
            'call_id': self.call_id,
            'udp_port': self.audio.local_port,
            'ip': get_local_ip()})

        try:
            self._call_timeout_job = self.root.after(
                int(CALL_TIMEOUT_SEC * 1000),
                self._call_timeout)
        except Exception:
            self._call_timeout_job = None

    def _call_timeout(self):
        self._call_timeout_job = None
        if self.call_state not in ('calling', 'ringing'):
            return
        if self.call_state == 'calling' and self.call_peer:
            self._send_obj({
                'type': 'call_signal',
                'action': 'end',
                'to': self.call_peer,
                'call_id': self.call_id})
        self._cleanup_call()
        custom_alert(self.root, t('call_title'),
                     t('call_timeout'), auto_close_ms=2500)

    def _handle_call_signal(self, obj):
        action = obj.get('action') or ''
        sender = obj.get('from') or ''
        call_id = obj.get('call_id') or ''
        udp_port = obj.get('udp_port')
        peer_ip = obj.get('ip')

        if action == 'invite':
            if not valid_username(sender):
                return
            if sender in self.blocked_users:
                self._send_obj({
                    'type': 'call_signal',
                    'action': 'reject',
                    'to': sender,
                    'call_id': call_id,
                    'reason': 'blocked'})
                return
            if self.call_state != 'idle':
                self._send_obj({
                    'type': 'call_signal',
                    'action': 'busy',
                    'to': sender,
                    'call_id': call_id})
                return
            if not HAS_AUDIO:
                self._send_obj({
                    'type': 'call_signal',
                    'action': 'reject',
                    'to': sender,
                    'call_id': call_id,
                    'reason': 'no_audio_device'})
                custom_alert(self.root, t('error'),
                             t('no_audio_device'))
                return

            if self._voice_recording:
                self._cancel_voice_recording()
            self._stop_voice_playback()

            self.call_id = call_id
            self.call_peer = sender
            self.call_is_outgoing = False
            self.call_state = 'ringing'
            self._pending_peer_ip = peer_ip
            self._pending_peer_port = udp_port

            try:
                if (self.incoming_call_window
                        and self.incoming_call_window.winfo_exists()):
                    self.incoming_call_window.destroy()
            except Exception:
                pass
            try:
                self.incoming_call_window = IncomingCallDialog(
                    self.root, sender,
                    on_accept=self._accept_incoming,
                    on_reject=self._reject_incoming)
            except Exception as e:
                log_error(f'IncomingCallDialog: {e}')
                self.call_state = 'idle'
                self.call_peer = None
                return

            try:
                self._call_timeout_job = self.root.after(
                    int(CALL_TIMEOUT_SEC * 1000),
                    self._incoming_timeout)
            except Exception:
                self._call_timeout_job = None

        elif action == 'accept':
            if self.call_state != 'calling':
                return
            if call_id != self.call_id:
                return
            if peer_ip and udp_port:
                try:
                    self.audio.set_peer(peer_ip, udp_port)
                except Exception as e:
                    log_error(f'set_peer accept: {e}')
            self.call_state = 'active'
            self._cancel_call_timeout()
            if self.call_window and self.call_window.winfo_exists():
                self.call_window.mark_active()

        elif action == 'reject':
            if self.call_state not in ('calling', 'ringing'):
                return
            if call_id and self.call_id and call_id != self.call_id:
                return
            reason = obj.get('reason', 'call_rejected')
            self._cleanup_call()
            msg = t('call_rejected')
            if reason == 'call_busy':
                msg = t('call_busy')
            elif reason == 'call_peer_offline':
                msg = t('call_peer_offline')
            custom_alert(self.root, t('call_title'), msg,
                         auto_close_ms=2500)

        elif action == 'busy':
            if self.call_state != 'calling':
                return
            self._cleanup_call()
            custom_alert(self.root, t('call_title'),
                         t('call_busy'), auto_close_ms=2500)

        elif action == 'end':
            if call_id and self.call_id and call_id != self.call_id:
                return
            if self.call_state == 'idle':
                return
            self._cleanup_call()
            custom_alert(self.root, t('call_title'),
                         t('call_ended'), auto_close_ms=2000)

        elif action == 'unreachable':
            if self.call_state != 'calling':
                return
            self._cleanup_call()
            custom_alert(self.root, t('call_title'),
                         t('call_peer_offline'),
                         auto_close_ms=2500)

    def _incoming_timeout(self):
        self._call_timeout_job = None
        if self.call_state != 'ringing':
            return
        if self.call_peer:
            self._send_obj({
                'type': 'call_signal',
                'action': 'reject',
                'to': self.call_peer,
                'call_id': self.call_id,
                'reason': 'call_timeout'})
        self._cleanup_call()

    def _accept_incoming(self):
        if self.call_state != 'ringing':
            return
        if not self.audio.start():
            self._send_obj({
                'type': 'call_signal',
                'action': 'reject',
                'to': self.call_peer,
                'call_id': self.call_id,
                'reason': 'no_audio_device'})
            self._cleanup_call()
            custom_alert(self.root, t('error'),
                         t('no_audio_device'))
            return
        self._cancel_call_timeout()
        self.call_state = 'active'
        self._send_obj({
            'type': 'call_signal',
            'action': 'accept',
            'to': self.call_peer,
            'call_id': self.call_id,
            'udp_port': self.audio.local_port,
            'ip': get_local_ip()})
        try:
            ip = self._pending_peer_ip
            port = self._pending_peer_port
            if ip and port:
                self.audio.set_peer(ip, port)
        except Exception:
            pass

        try:
            self.call_window = CallWindow(
                self.root, self.call_peer,
                on_hangup=self._end_call,
                on_toggle_mute=self._toggle_call_mute)
            self.call_window.mark_active()
        except Exception as e:
            log_error(f'CallWindow accept: {e}')

    def _reject_incoming(self):
        if self.call_state != 'ringing':
            return
        if self.call_peer:
            self._send_obj({
                'type': 'call_signal',
                'action': 'reject',
                'to': self.call_peer,
                'call_id': self.call_id})
        self._cleanup_call()

    def _end_call(self):
        if self.call_state == 'idle':
            return
        if self.call_peer:
            self._send_obj({
                'type': 'call_signal',
                'action': 'end',
                'to': self.call_peer,
                'call_id': self.call_id})
        self._cleanup_call()

    def _toggle_call_mute(self, muted):
        try:
            self.audio.set_muted(muted)
        except Exception as e:
            log_error(f'toggle_call_mute: {e}')

    def _cancel_call_timeout(self):
        if self._call_timeout_job:
            try:
                self.root.after_cancel(self._call_timeout_job)
            except Exception:
                pass
            self._call_timeout_job = None

    def _cleanup_call(self):
        self._cancel_call_timeout()
        try:
            if (self.call_window
                    and self.call_window.winfo_exists()):
                try:
                    self.call_window.force_close()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            if (self.incoming_call_window
                    and self.incoming_call_window.winfo_exists()):
                try:
                    self.incoming_call_window.destroy()
                except Exception:
                    pass
        except Exception:
            pass
        self.call_window = None
        self.incoming_call_window = None
        try:
            self.audio.stop()
        except Exception:
            pass
        try:
            self._stop_voice_playback()
        except Exception:
            pass
        self.call_state = 'idle'
        self.call_id = None
        self.call_peer = None
        self.call_is_outgoing = False
        self._pending_peer_ip = None
        self._pending_peer_port = None

    def open_emoji_picker(self):
        try:
            if (self.emoji_picker
                    and self.emoji_picker.winfo_exists()):
                self.emoji_picker.lift()
                return
        except Exception:
            pass
        try:
            self.emoji_picker = EmojiPicker(
                self.root, on_pick=self._insert_emoji)
            self.emoji_picker.after(100, self.emoji_picker.lift)
        except Exception as e:
            log_error(f'open_emoji_picker: {e}')

    def _insert_emoji(self, emoji):
        try:
            self.msg_entry.insert("insert", emoji)
            try:
                self.msg_entry.focus_set()
            except Exception:
                pass
        except Exception as e:
            log_error(f'insert_emoji: {e}')

    def on_attach(self):
        try:
            path = pick_file()
            if not path:
                return
            size = os.path.getsize(path)
            if size > MAX_ATTACHMENT_SIZE:
                custom_alert(self.root, t('error'), t('file_too_big'))
                return
            name = os.path.basename(path)
            local_path = None
            if size < 100 * 1024 * 1024:
                with open(path, 'rb') as f:
                    local_path = save_file_to_disk(f.read(), name)
            with open(path, 'rb') as f:
                raw = f.read()
            b64 = base64.b64encode(raw).decode('ascii')
            mime, _ = mimetypes.guess_type(path)
            if not mime:
                mime = 'application/octet-stream'
            self._pending_attachment = {
                'name': name, 'mime': mime, 'data': b64,
                'size': size, 'filepath': local_path or ''}
            self.attachment_label.configure(
                text=f"📎 {name} ({human_size(size)})")
            try:
                if self.input_row.winfo_ismapped():
                    self.attachment_bar.pack(fill="x", padx=10,
                                             pady=(8, 0),
                                             before=self.input_row)
                else:
                    self.attachment_bar.pack(fill="x", padx=10,
                                             pady=(8, 0))
            except Exception:
                pass
            try:
                self.msg_entry.focus_set()
            except Exception:
                pass
        except Exception as e:
            log_error(f'on_attach: {e}')
            custom_alert(self.root, t('error'), f'{e}')

    def cancel_attachment(self):
        self._pending_attachment = None
        try:
            self.attachment_bar.pack_forget()
        except Exception:
            pass

    def _toggle_notifications(self, enabled):
        self.notifications_enabled = bool(enabled)
        settings = load_settings()
        settings['notifications'] = self.notifications_enabled
        save_settings(settings)

    def _open_language_picker(self, parent_window):
        try:
            if (self.language_picker
                    and self.language_picker.winfo_exists()):
                self.language_picker.lift()
                return
        except Exception:
            pass
        try:
            self.language_picker = LanguagePicker(
                parent_window, get_current_lang(),
                on_pick=self._apply_language)
        except Exception as e:
            log_error(f'LanguagePicker: {e}')

    def _open_font_picker(self, parent_window):
        try:
            if (self.font_picker
                    and self.font_picker.winfo_exists()):
                self.font_picker.lift()
                return
        except Exception:
            pass
        try:
            self.font_picker = FontPicker(
                parent_window, get_current_font(),
                on_pick=self._apply_font)
        except Exception as e:
            log_error(f'FontPicker: {e}')

    def _open_theme_picker(self, parent_window):
        try:
            if (self.theme_picker
                    and self.theme_picker.winfo_exists()):
                self.theme_picker.lift()
                return
        except Exception:
            pass
        try:
            self.theme_picker = ThemePicker(
                parent_window, get_current_theme(),
                on_pick=self._apply_theme)
        except Exception as e:
            log_error(f'ThemePicker: {e}')

    def _open_interface_settings(self, parent_window):
        try:
            if (self.interface_window
                    and self.interface_window.winfo_exists()):
                self.interface_window.lift()
                return
        except Exception:
            pass
        try:
            self.interface_window = InterfaceSettingsWindow(
                parent_window,
                on_pick_font=self._open_font_picker,
                on_pick_theme=self._open_theme_picker)
        except Exception as e:
            log_error(f'InterfaceSettingsWindow: {e}')

    def _open_about(self, parent_window):
        try:
            if (self.about_window
                    and self.about_window.winfo_exists()):
                self.about_window.lift()
                return
        except Exception:
            pass
        try:
            self.about_window = AboutWindow(parent_window)
        except Exception as e:
            log_error(f'AboutWindow: {e}')

    def _restart_app(self):
        try:
            self.on_window_close()
        except Exception:
            pass
        try:
            time.sleep(0.3)
        except Exception:
            pass

        env = os.environ.copy()
        for k in ('_MEIPASS', '_MEIPASS2',
                  '_PYI_APPLICATION_HOME_DIR',
                  '_PYI_ARCHIVE_FILE',
                  '_PYI_PARENT_PROCESS_LEVEL',
                  '_PYI_SPLASH_IPC'):
            env.pop(k, None)

        try:
            try:
                sys.stdout.flush()
                sys.stderr.flush()
            except Exception:
                pass
            if getattr(sys, 'frozen', False):
                args = [sys.executable] + sys.argv[1:]
                cwd = os.path.dirname(sys.executable)
            else:
                args = [sys.executable] + sys.argv
                cwd = os.path.dirname(os.path.abspath(__file__))

            kwargs = {'env': env, 'close_fds': True, 'cwd': cwd}
            if sys.platform == 'win32':
                DETACHED_PROCESS = 0x00000008
                CREATE_NEW_PROCESS_GROUP = 0x00000200
                kwargs['creationflags'] = (
                    DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP)
            subprocess.Popen(args, **kwargs)
        except Exception as e:
            log_error(f'restart subprocess failed: {e}')

        try:
            time.sleep(1.0)
        except Exception:
            pass
        try:
            os._exit(0)
        except Exception:
            pass

    def _apply_language(self, code):
        if code not in LANGUAGES:
            return
        if code == get_current_lang():
            return
        settings = load_settings()
        settings['language'] = code
        save_settings(settings)
        set_language(code)
        try:
            custom_alert(self.root, t('restart_title'),
                         t('restart_msg'), auto_close_ms=1500)
        except Exception:
            pass
        self._restart_app()

    def _apply_font(self, code):
        if code not in [c for c, _l, _f in FONTS]:
            return
        if code == get_current_font():
            return
        settings = load_settings()
        settings['font'] = code
        save_settings(settings)
        set_font_by_code(code)
        try:
            _apply_ctk_theme_font(_current_font_family)
        except Exception:
            pass
        try:
            _apply_global_font_family(_current_font_family)
        except Exception:
            pass
        try:
            custom_alert(self.root, t('restart_title'),
                         t('restart_msg_font'), auto_close_ms=1500)
        except Exception:
            pass
        self._restart_app()

    def _apply_theme(self, code):
        if code not in THEMES:
            return
        if code == get_current_theme():
            return
        settings = load_settings()
        settings['theme'] = code
        save_settings(settings)
        apply_theme(code)
        try:
            custom_alert(self.root, t('restart_title'),
                         t('restart_msg_theme'), auto_close_ms=1500)
        except Exception:
            pass
        self._restart_app()

    def _should_notify(self, sender):
        if not self.notifications_enabled:
            return False
        if sender in self.blocked_users:
            return False
        if self.current_chat == sender:
            try:
                if self.root.focus_displayof() is not None:
                    return False
            except Exception:
                pass
        return True

    def _play_notification_sound(self):
        if not HAS_WINSOUND:
            return
        try:
            if os.path.exists(NOTIFY_SOUND_PATH):
                winsound.PlaySound(
                    NOTIFY_SOUND_PATH,
                    winsound.SND_FILENAME |
                    winsound.SND_ASYNC |
                    winsound.SND_NODEFAULT)
            else:
                winsound.MessageBeep(winsound.MB_ICONASTERISK)
        except Exception as e:
            log_error(f'winsound: {e}')

    def _show_notification(self, sender, text):
        try:
            if (self._notification_popup
                    and self._notification_popup.winfo_exists()):
                try:
                    self._notification_popup._close()
                except Exception:
                    pass
        except Exception:
            pass

        self._play_notification_sound()

        def on_click():
            try:
                self.open_private_chat(sender)
                try:
                    self.root.deiconify()
                    self.root.lift()
                    self.root.focus_force()
                except Exception:
                    pass
            except Exception as e:
                log_error(f'notif click: {e}')

        try:
            self._notification_popup = NotificationPopup(
                self.root, sender, text, on_click=on_click)
        except Exception as e:
            log_error(f'NotificationPopup: {e}')

    def open_settings(self):
        try:
            if (self.settings_window
                    and self.settings_window.winfo_exists()):
                self.settings_window.lift()
                return
        except Exception:
            pass
        try:
            self.settings_window = SettingsWindow(
                self.root,
                on_account_settings=self.open_account_settings,
                on_toggle_notifications=self._toggle_notifications,
                notifications_enabled=self.notifications_enabled,
                on_pick_language=self._open_language_picker,
                on_interface_settings=self._open_interface_settings,
                on_about=self._open_about)
        except Exception as e:
            log_error(f'open_settings: {e}')

    def open_account_settings(self):
        try:
            if (self.account_window
                    and self.account_window.winfo_exists()):
                self.account_window.lift()
                return
        except Exception:
            pass
        try:
            self.account_window = AccountSettingsWindow(
                self.root, self.my_username,
                self.my_first_name, self.my_last_name,
                self.my_avatar_b64,
                on_save=self._save_profile,
                on_nick_change=self._save_nick,
                on_avatar_pick=pick_file,
                on_change_password=self.on_change_password,
                on_delete_account=self.on_delete_account,
                on_logout=self.on_logout)
        except Exception as e:
            log_error(f'open_account_settings: {e}')

    def _save_profile(self, first_name, last_name, avatar_b64):
        self.my_first_name = first_name
        self.my_last_name = last_name
        self.my_avatar_b64 = avatar_b64
        settings = load_settings()
        settings['first_name'] = first_name
        settings['last_name'] = last_name
        settings['avatar'] = avatar_b64
        save_settings(settings)
        try:
            db_update_profile(self.my_username,
                              first_name=first_name,
                              last_name=last_name,
                              avatar=avatar_b64)
        except Exception as e:
            log_error(f'save_profile db: {e}')
        self._send_obj({
            'type': 'update_profile',
            'first_name': first_name,
            'last_name': last_name,
            'avatar': avatar_b64})
        self._setup_self_chat()
        self.refresh_chat_list_online()
        self.update_header()
        try:
            custom_alert(self.root, t('done'), t('saved'),
                         auto_close_ms=1200)
        except Exception:
            pass

    def _save_nick(self, new_nick):
        if not new_nick or new_nick == self.my_username:
            return
        if not valid_username(new_nick):
            custom_alert(self.root, t('error'), t('fill_all'))
            return
        self._send_obj({'type': 'change_nick', 'new': new_nick})

    def _refresh_chat_avatar(self, chat_id):
        av = self.chat_avatars.get(chat_id)
        if av is None:
            return
        if chat_id == SELF_CHAT_ID:
            img = self._get_avatar_for(self.my_username)
        else:
            img = self._get_avatar_for(chat_id)
        try:
            if img is not None:
                av.configure(image=img, text='')
            else:
                av.configure(text=(chat_id[:1].upper() if chat_id else '?'))
        except Exception:
            pass

    def on_logout(self):
        try:
            self._cleanup_call()
        except Exception:
            pass
        try:
            self._cancel_voice_recording()
        except Exception:
            pass
        try:
            self._stop_voice_playback()
        except Exception:
            pass
        try:
            delete_session()
        except Exception:
            pass
        self._saved_username = None
        self._saved_password = None
        self._pending_new_password = None
        self.my_username = ''
        self.known_users = []
        self.chats.clear()
        self.chat_frames.clear()
        self.chat_buttons.clear()
        self.chat_avatars.clear()
        self.chat_rows.clear()
        self.empty_chat_labels.clear()
        self.msg_widgets.clear()
        self.pending_msgs.clear()
        self.typing_dm.clear()
        for w in list(self.chats_list.winfo_children()):
            try:
                w.destroy()
            except Exception:
                pass
        for w in list(self.chat_container.winfo_children()):
            try:
                w.destroy()
            except Exception:
                pass
        try:
            self.empty_label = ctk.CTkLabel(
                self.chat_container,
                text=t('select_chat'),
                font=get_font(18), text_color=FG_DIM)
            self.empty_label.grid(row=0, column=0)
        except Exception:
            pass
        self.current_chat = None
        try:
            self.status_label.configure(text="")
        except Exception:
            pass
        self.on_reconnect()

    def _on_typing_key(self, event=None):
        if not self.connected or self.current_chat is None:
            return
        if self.current_chat == SELF_CHAT_ID:
            return
        if self._voice_recording:
            return
        try:
            if self.msg_entry.get() == "":
                return
        except Exception:
            return
        now = time.time()
        if now - self.last_typing_sent < TYPING_SEND_INTERVAL:
            return
        self.last_typing_sent = now
        self._send_obj({'type': 'typing', 'to': self.current_chat})

    def _update_typing_label(self):
        try:
            now = time.time()
            for n in list(self.typing_dm.keys()):
                if self.typing_dm[n] <= now:
                    del self.typing_dm[n]

            self._typing_phase = (self._typing_phase + 1) % 4
            dots_map = ['.', '..', '...', '..']
            dots = dots_map[self._typing_phase]

            text = ""
            if (self.conn_state in ('connected', 'reconnecting')
                    and self.current_chat
                    and self.current_chat != SELF_CHAT_ID):
                other = self.current_chat
                if other in self.typing_dm:
                    base = t('typing', other)
                    base = base.rstrip('.').rstrip()
                    text = base + dots
            try:
                if self.typing_label.winfo_exists():
                    self.typing_label.configure(text=text)
            except Exception:
                pass
        except Exception as e:
            log_error(f'typing label: {e}')
        try:
            self.root.after(400, self._update_typing_label)
        except Exception:
            pass

    def _status_loop(self):
        try:
            if (self.connected and self.current_chat
                    and self.current_chat != SELF_CHAT_ID):
                self._request_status(self.current_chat)
        except Exception:
            pass
        try:
            self.root.after(STATUS_REFRESH_MS, self._status_loop)
        except Exception:
            pass

    def _request_status(self, username):
        self._send_obj({'type': 'status', 'user': username})

    def _show_input(self):
        try:
            self.bottom_frame.grid()
        except Exception:
            pass
        try:
            if not self.input_row.winfo_ismapped():
                self.input_row.pack(fill="x", padx=10,
                                    pady=(8, 0),
                                    before=self.typing_label)
        except Exception:
            pass

    def _hide_input(self):
        try:
            if self.input_row.winfo_ismapped():
                self.input_row.pack_forget()
        except Exception:
            pass
        try:
            if self.attachment_bar.winfo_ismapped():
                self.attachment_bar.pack_forget()
        except Exception:
            pass
        self.cancel_reply()
        self.cancel_attachment()
        try:
            self._cancel_voice_recording()
        except Exception:
            pass
        try:
            self.bottom_frame.grid_remove()
        except Exception:
            pass
        try:
            self.typing_label.configure(text="")
        except Exception:
            pass
        self.typing_dm.clear()

    def update_header(self):
        try:
            try:
                show_e2e = (
                    self.connected
                    and self.current_chat is not None
                    and self.current_chat != SELF_CHAT_ID
                    and HAS_CRYPTO)
                if show_e2e:
                    if self.current_chat in self.e2e_verified:
                        self.e2e_label.configure(
                            text=t('e2e_notice'),
                            text_color=FG_TEXT)
                    else:
                        self.e2e_label.configure(
                            text=t('e2e_unverified'),
                            text_color=FG_TEXT)
                else:
                    self.e2e_label.configure(text="")
            except Exception:
                pass

            try:
                show_call = (
                    self.connected
                    and self.current_chat is not None
                    and self.current_chat != SELF_CHAT_ID
                    and self.current_chat != self.my_username
                    and self.current_chat in self.known_users
                    and self.call_state == 'idle')
                if show_call:
                    if not self.call_btn.winfo_ismapped():
                        self.call_btn.pack(side="right",
                                           padx=(5, 5), pady=13,
                                           before=self.header_label)
                else:
                    if self.call_btn.winfo_ismapped():
                        self.call_btn.pack_forget()
            except Exception:
                pass

            try:
                show_badge = False
                if self.connected and self.current_chat is not None:
                    if (self.current_chat == SELF_CHAT_ID
                            and self._is_creator(self.my_username)):
                        show_badge = True
                    elif self._is_creator(self.current_chat):
                        show_badge = True
                if self.header_creator_badge is not None:
                    if show_badge:
                        if not self.header_creator_badge.winfo_ismapped():
                            self.header_creator_badge.pack(
                                side="left", padx=(4, 0))
                    else:
                        if self.header_creator_badge.winfo_ismapped():
                            self.header_creator_badge.pack_forget()
            except Exception:
                pass

            if self.conn_state == 'connected':
                if self.current_chat is None:
                    self.header_label.configure(text="Chatter")
                    self.status_label.configure(text="")
                elif self.current_chat == SELF_CHAT_ID:
                    fn = self.my_first_name
                    ln = self.my_last_name
                    disp = f"{fn} {ln}".strip() or self.my_username
                    self.header_label.configure(
                        text=f"{disp} {t('you_suffix')}")
                    self.status_label.configure(text="")
                elif self.current_chat in self.chats:
                    self.header_label.configure(
                        text=self.chats[self.current_chat]['name'])
                else:
                    self.header_label.configure(
                        text=self.current_chat)
                if self.current_chat is not None:
                    self._show_input()
                else:
                    self._hide_input()
            elif self.conn_state == 'reconnecting':
                self.header_label.configure(text=t('reconnecting'))
                if self.current_chat is not None:
                    self._show_input()
                else:
                    self._hide_input()
            elif self.conn_state in ('disconnected', 'failed'):
                self.header_label.configure(text=t('disconnected'))
                self._hide_input()
            else:
                self.header_label.configure(text=t('connecting'))
                self._hide_input()
        except Exception as e:
            log_error(f'update_header: {e}')

    def add_chat_to_list(self, chat_id, display_name):
        if chat_id in self.chat_buttons:
            return
        row = ctk.CTkFrame(self.chats_list, fg_color="transparent",
                          height=44)
        row.pack(fill="x", padx=2, pady=2)
        row.pack_propagate(False)
        self.chat_rows[chat_id] = row

        av = ctk.CTkLabel(row, text='?', width=AVATAR_SIZE_CHAT,
                          height=AVATAR_SIZE_CHAT,
                          fg_color=BG_LIGHT,
                          corner_radius=AVATAR_SIZE_CHAT // 2,
                          font=get_font(13, "bold"),
                          text_color=FG_TEXT)
        av.pack(side="left", padx=(6, 8), pady=6)
        self.chat_avatars[chat_id] = av

        btn = ctk.CTkButton(
            row, text=display_name, anchor="w",
            height=36, fg_color="transparent",
            hover_color=BG_LIGHT, text_color=FG_TEXT,
            font=get_font(13),
            command=lambda cid=chat_id: self.select_chat(cid))
        btn.pack(side="left", fill="both", expand=True, pady=4)
        self.chat_buttons[chat_id] = btn

        for w in (row, av, btn):
            try:
                w.bind("<Button-3>",
                       lambda e, cid=chat_id:
                           self.show_chat_context_menu(e, cid))
            except Exception:
                pass

        self._refresh_chat_avatar(chat_id)

    def show_chat_context_menu(self, event, chat_id):
        if chat_id == SELF_CHAT_ID:
            return
        menu = Menu(self.root, tearoff=0, bg=BG_LIGHT,
                    fg=FG_TEXT,
                    font=get_font(13),
                    activebackground=BTN,
                    activeforeground="white",
                    borderwidth=0)
        menu.add_command(
            label=t('menu_delete_chat'),
            command=lambda: self.delete_chat(chat_id))
        menu.add_command(
            label=t('menu_block'),
            command=lambda: self._block_user(chat_id))
        if HAS_CRYPTO and chat_id != self.my_username:
            menu.add_command(
                label=t('e2e_verify'),
                command=lambda: self._show_fingerprint(chat_id))
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def delete_chat(self, chat_id):
        if chat_id == SELF_CHAT_ID:
            return
        ok = custom_confirm(
            self.root, t('menu_delete_chat'),
            t('delete_chat_warning', chat_id), danger=True)
        if not ok:
            return
        row = self.chat_rows.pop(chat_id, None)
        if row is not None:
            try:
                row.destroy()
            except Exception:
                pass
        self.chat_buttons.pop(chat_id, None)
        self.chat_avatars.pop(chat_id, None)
        frame = self.chat_frames.pop(chat_id, None)
        if frame is not None:
            try:
                frame.destroy()
            except Exception:
                pass
        self.empty_chat_labels.pop(chat_id, None)
        self.chats.pop(chat_id, None)
        if self.current_chat == chat_id:
            self.current_chat = None
            self.empty_label.grid(row=0, column=0)
            self._hide_input()
            self.update_header()

    def _update_chat_buttons(self):
        for cid, btn in self.chat_buttons.items():
            try:
                if cid == self.current_chat:
                    btn.configure(fg_color=BTN, hover_color=BTN_HOVER,
                                  text_color="white")
                else:
                    btn.configure(fg_color="transparent",
                                  hover_color=BG_LIGHT,
                                  text_color=FG_TEXT)
            except Exception:
                continue

    def get_or_create_chat_frame(self, chat_id):
        if chat_id in self.chat_frames:
            return self.chat_frames[chat_id]
        frame = ctk.CTkScrollableFrame(self.chat_container,
                                       fg_color=BG_DARK,
                                       corner_radius=0)
        frame.grid_columnconfigure(0, weight=1)
        self.chat_frames[chat_id] = frame
        self._update_empty_chat_state(chat_id)
        return frame

    def _update_empty_chat_state(self, chat_id):
        frame = self.chat_frames.get(chat_id)
        if frame is None:
            return
        has_messages = bool(
            self.chats.get(chat_id, {}).get('messages'))
        existing = self.empty_chat_labels.get(chat_id)

        if has_messages:
            if existing is not None:
                try:
                    existing.destroy()
                except Exception:
                    pass
                self.empty_chat_labels.pop(chat_id, None)
            return

        if existing is not None:
            try:
                if existing.winfo_exists():
                    return
            except Exception:
                pass

        try:
            lbl = ctk.CTkLabel(
                frame, text=t('empty_chat'),
                text_color=FG_DIM,
                font=get_font(22, "bold"),
                wraplength=520, justify="center")
            lbl.pack(pady=(90, 0))
            self.empty_chat_labels[chat_id] = lbl
        except Exception as e:
            log_error(f'empty_chat placeholder: {e}')

    def ensure_private_chat(self, username):
        if username in self.chats:
            return
        display = username
        if (username not in self.known_users
                and username != self.my_username):
            display = f"{username} {t('offline_suffix')}"
        self.chats[username] = {'name': display, 'messages': []}
        self.add_chat_to_list(username, display)
        self.get_or_create_chat_frame(username)
        self._request_profile(username)

    def _request_profile(self, username):
        self._send_obj({'type': 'request_profile', 'user': username})

    def refresh_chat_list_online(self):
        for cid, btn in self.chat_buttons.items():
            if cid == SELF_CHAT_ID:
                continue
            online = cid in self.known_users
            base = cid
            prof = self.user_profiles.get(cid)
            if prof and (prof.get('first_name') or prof.get('last_name')):
                base = f"{prof.get('first_name', '')} {prof.get('last_name', '')}".strip()
            display = base if online else f"{base} {t('offline_suffix')}"
            if cid in self.chats:
                self.chats[cid]['name'] = display
            try:
                btn.configure(text=display)
            except Exception:
                pass
            self._refresh_chat_avatar(cid)
        try:
            self.update_header()
        except Exception:
            pass

    def select_chat(self, chat_id):
        if chat_id not in self.chats:
            return
        for f in self.chat_frames.values():
            try:
                f.grid_forget()
            except Exception:
                pass
        try:
            self.empty_label.grid_forget()
        except Exception:
            pass
        frame = self.get_or_create_chat_frame(chat_id)
        frame.grid(row=0, column=0, sticky="nsew")
        self.current_chat = chat_id
        self._update_chat_buttons()
        self.update_header()
        self.cancel_reply()
        self.cancel_attachment()
        if chat_id == SELF_CHAT_ID:
            self.status_label.configure(text="")
        else:
            self.status_label.configure(text="")
            self._request_status(chat_id)
            self._request_profile(chat_id)
        try:
            self.root.after(60,
                            lambda: self._scroll_to_bottom(chat_id))
        except Exception:
            pass

    def _poll_queue(self):
        try:
            while True:
                fn, args, kwargs = self.gui_queue.get_nowait()
                try:
                    fn(*args, **kwargs)
                except Exception as e:
                    log_error(f'GUI callback: {e}\n'
                              f'{traceback.format_exc()}')
        except queue.Empty:
            pass
        except Exception as e:
            log_error(f'poll_queue: {e}')
        try:
            self.root.after(50, self._poll_queue)
        except Exception:
            pass

    def _post(self, fn, *args, **kwargs):
        self.gui_queue.put((fn, args, kwargs))

    def _highlight_original(self, chat_id, target, quote):
        if target != self.my_username:
            return
        msgs = self.chats.get(chat_id, {}).get('messages', [])
        q = quote or ''
        if q.endswith("..."):
            q = q[:-3]
        for entry in reversed(msgs):
            if entry.get('sender') != target:
                continue
            if entry.get('is_own') is not True:
                continue
            text = entry.get('text', '')
            if text.startswith(q) or q.startswith(text[:len(q)]):
                entry['is_mention'] = True
                try:
                    entry['frame'].configure(fg_color=MENTION_BG)
                    entry['sender_lbl'].configure(
                        text_color="#1a1a1a")
                    if entry.get('text_lbl'):
                        entry['text_lbl'].configure(
                            text_color="#1a1a1a")
                except Exception:
                    pass
                break

    def _mark_sent(self, entry):
        sl = entry.get('status_lbl')
        if sl is None:
            return
        try:
            if sl.winfo_exists():
                tt = time.strftime('%H:%M')
                sl.configure(text=t('sent_at', tt),
                             text_color=FG_STATUS)
        except Exception:
            pass

    def _check_delivered(self, msg_id):
        entry = self.pending_msgs.pop(msg_id, None)
        if entry is None:
            return
        sl = entry.get('status_lbl')
        if sl is None:
            return
        try:
            if sl.winfo_exists():
                sl.configure(text=t('not_delivered'),
                             text_color=ERROR_TEXT)
        except Exception:
            pass

    def _mark_all_pending_failed(self):
        for mid, entry in list(self.pending_msgs.items()):
            sl = entry.get('status_lbl')
            if sl is not None:
                try:
                    if sl.winfo_exists():
                        sl.configure(text=t('not_delivered'),
                                     text_color=ERROR_TEXT)
                except Exception:
                    pass
        self.pending_msgs.clear()

    def add_message(self, chat_id, sender, text, is_own,
                    msg_id=None, reply=None, show_status=False,
                    attachment=None, forwarded_from=None):
        if chat_id not in self.chats:
            self.ensure_private_chat(chat_id)
        frame = self.get_or_create_chat_frame(chat_id)

        row = ctk.CTkFrame(frame, fg_color=BG_DARK)
        row.pack(fill="x", padx=4, pady=(4, 0))

        av_side = "right" if is_own else "left"
        bubble_side = av_side

        av_img = self._get_avatar_for(
            self.my_username if is_own else sender)
        av = ctk.CTkLabel(row, text='?', width=AVATAR_SIZE,
                          height=AVATAR_SIZE,
                          fg_color=BG_LIGHT,
                          corner_radius=AVATAR_SIZE // 2,
                          font=get_font(14, "bold"))
        if av_img is not None:
            av.configure(image=av_img, text='')
        else:
            av.configure(text=sender[:1].upper() if sender else '?')
        av.pack(side=av_side, padx=(6, 6), pady=2, anchor="n")

        bubble_holder = ctk.CTkFrame(row, fg_color=BG_DARK)
        bubble_holder.pack(side=bubble_side, fill="x", expand=True)

        bubble_fg = OWN_BUBBLE if is_own else BG_LIGHT
        sender_color = BTN if is_own else SENDER_OTHER

        bubble = ctk.CTkFrame(bubble_holder, fg_color=bubble_fg,
                              corner_radius=10)
        bubble.pack(fill="x", padx=4, pady=0,
                    anchor="e" if is_own else "w")
        try:
            self._animate_bubble_appear(bubble, is_own)
        except Exception as e:
            log_error(f'bubble appear anim: {e}')

        reply_lbl = None
        if reply:
            reply_txt = (f"↳ @{reply.get('target', '')}: "
                         f"{reply.get('quote', '')}")
            if len(reply_txt) > 100:
                reply_txt = reply_txt[:97] + "..."
            reply_lbl = ctk.CTkLabel(
                bubble, text=reply_txt, text_color=FG_DIM,
                anchor="w", justify="left",
                font=get_font(13), wraplength=550)
            reply_lbl.pack(fill="x", padx=12, pady=(8, 0))

        forwarded_lbl = None
        if forwarded_from:
            try:
                forwarded_lbl = ctk.CTkLabel(
                    bubble,
                    text=f"↪ {t('forwarded_from', forwarded_from)}",
                    text_color=YELLOW,
                    anchor="w", justify="left",
                    font=get_font(11),
                    wraplength=550)
                forwarded_lbl.pack(fill="x", padx=12,
                                   pady=(8 if not reply_lbl else 2, 0))
            except Exception as e:
                log_error(f'forwarded label: {e}')
                forwarded_lbl = None

        display_name = sender
        prof = self.user_profiles.get(sender)
        if prof and (prof.get('first_name') or prof.get('last_name')):
            display_name = f"{prof.get('first_name', '')} {prof.get('last_name', '')}".strip()

        sender_row = ctk.CTkFrame(bubble, fg_color="transparent")
        sender_pady_top = 8
        if reply_lbl or forwarded_lbl:
            sender_pady_top = 2
        sender_row.pack(fill="x", padx=12, pady=(sender_pady_top, 0))

        sender_lbl = ctk.CTkLabel(
            sender_row, text=display_name, text_color=sender_color,
            anchor="w", font=get_font(12, "bold"))
        sender_lbl.pack(side="left")

        if self._is_creator(sender):
            try:
                creator_badge = self._make_creator_badge(
                    sender_row, size=12)
                if creator_badge is not None:
                    creator_badge.pack(side="left", padx=(4, 0))
            except Exception as e:
                log_error(f'creator badge in message: {e}')

        entry_dict = {
            'sender': sender, 'text': text, 'is_own': is_own,
            'frame': bubble, 'text_lbl': None,
            'sender_lbl': sender_lbl, 'status_lbl': None,
            'reply_lbl': reply_lbl, 'msg_id': msg_id,
            'chat_id': chat_id, 'is_mention': False,
            'avatar_widget': av, 'row_widget': row,
            'attachment': attachment,
            'forwarded_from': forwarded_from,
            'forwarded_lbl': forwarded_lbl,
            'voice_play_btn': None,
            'voice_info_lbl': None,
            'voice_duration': 0.0,
        }

        if attachment:
            if attachment.get('voice'):
                self._render_voice_message(bubble, attachment,
                                           entry_dict)
            else:
                att_frame = ctk.CTkFrame(bubble, fg_color=BG_INPUT,
                                         corner_radius=8)
                att_frame.pack(fill="x", padx=12, pady=(4, 4))
                att_name = attachment.get('name', 'file')
                att_size = attachment.get('size', 0)
                ctk.CTkLabel(
                    att_frame, text=f"📎 {att_name}",
                    text_color=FG_TEXT, anchor="w",
                    font=get_font(13, "bold")
                ).pack(fill="x", padx=10, pady=(6, 0))
                ctk.CTkLabel(
                    att_frame, text=human_size(att_size),
                    text_color=FG_DIM, anchor="w",
                    font=get_font(11)
                ).pack(fill="x", padx=10, pady=(0, 4))
                att_btns = ctk.CTkFrame(att_frame,
                                        fg_color="transparent")
                att_btns.pack(fill="x", padx=10, pady=(0, 8))
                ctk.CTkButton(
                    att_btns, text=t('open_file'),
                    height=28, font=get_font(12),
                    fg_color=BTN, hover_color=BTN_HOVER,
                    command=lambda a=attachment:
                        self._open_attachment(a)
                ).pack(side="left", fill="x", expand=True, padx=(0, 4))
                ctk.CTkButton(
                    att_btns, text=t('save_file'),
                    height=28, font=get_font(12),
                    fg_color=BTN, hover_color=BTN_HOVER,
                    command=lambda a=attachment:
                        self._save_attachment(a)
                ).pack(side="left", fill="x", expand=True, padx=(4, 0))

        text_lbl = None
        if text:
            text_lbl = ctk.CTkLabel(
                bubble, text=text, text_color=FG_TEXT,
                anchor="w", justify="left", wraplength=550,
                font=get_font(13))
            text_lbl.pack(fill="x", padx=12, pady=(0, 8))
            entry_dict['text_lbl'] = text_lbl

        status_lbl = None
        if show_status and is_own:
            try:
                status_lbl = ctk.CTkLabel(
                    bubble_holder, text=t('sending'),
                    text_color=FG_STATUS,
                    anchor="e", justify="right",
                    font=get_font(11))
                status_lbl.pack(fill="x", padx=20, pady=(0, 4),
                                anchor="e")
            except Exception:
                status_lbl = None
            entry_dict['status_lbl'] = status_lbl

        if msg_id:
            self.msg_widgets[msg_id] = entry_dict

        widgets = [bubble, sender_lbl, reply_lbl, forwarded_lbl]
        if text_lbl is not None:
            widgets.append(text_lbl)
        for w in widgets:
            if w is not None:
                w.bind("<Button-3>",
                       lambda e, d=entry_dict:
                           self.show_context_menu(e, d))

        self.chats[chat_id]['messages'].append(entry_dict)

        if len(self.chats[chat_id]['messages']) > HISTORY_LIMIT:
            old = self.chats[chat_id]['messages'].pop(0)
            oid = old.get('msg_id')
            if oid:
                self.pending_msgs.pop(oid, None)
                self.msg_widgets.pop(oid, None)
            try:
                if old is self.current_playing_voice:
                    self._stop_voice_playback()
                osl = old.get('status_lbl')
                if osl is not None:
                    try:
                        osl.destroy()
                    except Exception:
                        pass
                orow = old.get('row_widget')
                if orow is not None:
                    try:
                        orow.destroy()
                    except Exception:
                        pass
                else:
                    old['frame'].destroy()
            except Exception:
                pass

        if status_lbl is not None:
            if chat_id == SELF_CHAT_ID or not msg_id:
                self._mark_sent(entry_dict)
            else:
                self.pending_msgs[msg_id] = entry_dict
                try:
                    self.root.after(
                        DELIVERY_TIMEOUT_MS,
                        lambda mid=msg_id:
                            self._check_delivered(mid))
                except Exception:
                    pass

        if reply:
            self._highlight_original(chat_id, reply.get('target'),
                                     reply.get('quote'))

        if chat_id == self.current_chat:
            try:
                self.root.after(60,
                                lambda: self._scroll_to_bottom(chat_id))
            except Exception:
                pass

        self._update_empty_chat_state(chat_id)

    def _open_attachment(self, attachment):
        try:
            path = attachment.get('filepath', '') or ''
            if not path or not os.path.exists(path):
                b64 = attachment.get('data', '')
                if b64:
                    try:
                        raw = base64.b64decode(b64)
                        new_path = save_file_to_disk(
                            raw, attachment.get('name', 'file'))
                        if new_path:
                            attachment['filepath'] = new_path
                            attachment['data'] = ''
                            path = new_path
                    except Exception as e:
                        log_error(f'open_attachment decode: {e}')
            if not path or not os.path.exists(path):
                custom_alert(self.root, t('error'),
                             'Файл не найден')
                return
            if sys.platform == 'win32':
                os.startfile(path)
            elif sys.platform == 'darwin':
                subprocess.Popen(['open', path])
            else:
                subprocess.Popen(['xdg-open', path])
        except Exception as e:
            log_error(f'open_attachment: {e}')
            custom_alert(self.root, t('error'), f'{e}')

    def _save_attachment(self, attachment):
        try:
            name = attachment.get('name', 'file')
            if attachment.get('voice'):
                name = 'voice.wav'
            path_src = attachment.get('filepath', '')
            target = filedialog.asksaveasfilename(
                title=t('save_file'), initialfile=name)
            if not target:
                return
            if path_src and os.path.exists(path_src):
                shutil.copy2(path_src, target)
            else:
                data_b64 = attachment.get('data', '')
                if not data_b64:
                    custom_alert(self.root, t('error'),
                                 'Данные вложения недоступны')
                    return
                raw = base64.b64decode(data_b64)
                with open(target, 'wb') as f:
                    f.write(raw)
            custom_alert(self.root, t('done'), t('file_saved'))
        except Exception as e:
            log_error(f'save_attachment: {e}')
            custom_alert(self.root, t('error'), f'{e}')

    def _scroll_to_bottom(self, chat_id=None):
        if chat_id is None:
            chat_id = self.current_chat
        frame = self.chat_frames.get(chat_id)
        if not frame:
            return
        try:
            canvas = frame._parent_canvas
        except Exception:
            return

        try:
            start = canvas.yview()[0]
        except Exception:
            start = 1.0
        target = 1.0
        if start >= 0.999:
            try:
                canvas.yview_moveto(1.0)
            except Exception:
                pass
            return

        steps = 16
        interval = 16

        def tick(i):
            try:
                if not canvas.winfo_exists():
                    return
                t = i / float(steps)
                e = ease_out_back(t, 2.0)
                y = start + (target - start) * e
                if y > 1.0:
                    y = 1.0
                canvas.yview_moveto(y)
                if i < steps:
                    canvas.after(interval, lambda: tick(i + 1))
                else:
                    canvas.yview_moveto(1.0)
            except Exception:
                pass

        try:
            tick(1)
        except Exception:
            try:
                canvas.yview_moveto(1.0)
            except Exception:
                pass

    def remove_entry_local(self, entry):
        if not entry:
            return
        if entry is self.current_playing_voice:
            self._stop_voice_playback()
        sl = entry.get('status_lbl')
        if sl is not None:
            try:
                sl.destroy()
            except Exception:
                pass
        try:
            orow = entry.get('row_widget')
            if orow is not None:
                orow.destroy()
            else:
                entry['frame'].destroy()
        except Exception:
            pass
        cid = entry.get('chat_id')
        if cid and cid in self.chats:
            msgs = self.chats[cid]['messages']
            for i, m in enumerate(msgs):
                if m is entry:
                    msgs.pop(i)
                    break
        mid = entry.get('msg_id')
        if mid:
            self.msg_widgets.pop(mid, None)
            self.pending_msgs.pop(mid, None)
        if cid:
            self._update_empty_chat_state(cid)

    def remove_message_local(self, msg_id):
        e = self.msg_widgets.get(msg_id)
        if e:
            self.remove_entry_local(e)

    def delete_own_message(self, entry):
        if not entry.get('is_own'):
            return
        cid = entry.get('chat_id')
        if cid == SELF_CHAT_ID:
            self.remove_entry_local(entry)
            return
        mid = entry.get('msg_id')
        if not mid:
            return
        self._send_obj({'type': 'delete', 'id': mid})
        self.remove_entry_local(entry)

    def _apply_remote_edit(self, msg_id, new_text):
        entry = self.msg_widgets.get(msg_id)
        if entry is None:
            return
        entry['text'] = new_text
        text_lbl = entry.get('text_lbl')
        if text_lbl is not None:
            try:
                text_lbl.configure(text=new_text)
            except Exception as e:
                log_error(f'_apply_remote_edit configure: {e}')

    def _block_user(self, username):
        if not username:
            return
        ok = custom_confirm(
            self.root, t('menu_block'),
            t('blocked_warning', username), danger=True)
        if not ok:
            return
        self.blocked_users.add(username)
        settings = load_settings()
        settings['blocked'] = list(self.blocked_users)
        save_settings(settings)
        self.refresh_chat_list_online()

    def _unblock_user(self, username):
        if username in self.blocked_users:
            self.blocked_users.discard(username)
            settings = load_settings()
            settings['blocked'] = list(self.blocked_users)
            save_settings(settings)
            self.refresh_chat_list_online()

    def show_context_menu(self, event, entry):
        cid = entry.get('chat_id')
        is_own = entry.get('is_own', False)

        menu = Menu(self.root, tearoff=0, bg=BG_LIGHT,
                    fg=FG_TEXT,
                    font=get_font(13),
                    activebackground=BTN, activeforeground="white",
                    borderwidth=0)

        menu.add_command(
            label=t('forward'),
            command=lambda: self.start_forward(entry))

        if cid and cid != SELF_CHAT_ID:
            menu.add_command(
                label=t('menu_reply'),
                command=lambda: self.start_reply(entry))

        if is_own and entry.get('text'):
            menu.add_command(
                label=t('menu_edit'),
                command=lambda: self.start_edit(cid, entry))

        if is_own:
            if entry.get('msg_id') or cid == SELF_CHAT_ID:
                menu.add_command(
                    label=t('menu_delete'),
                    command=lambda: self.delete_own_message(entry))
        else:
            menu.add_command(
                label=t('menu_delete_local'),
                command=lambda: self.remove_entry_local(entry))

        if not is_own:
            sender = entry.get('sender', '')
            if sender in self.blocked_users:
                menu.add_command(
                    label=t('menu_unblock'),
                    command=lambda: self._unblock_user(sender))
            elif valid_username(sender):
                menu.add_command(
                    label=t('menu_block'),
                    command=lambda: self._block_user(sender))
            if valid_username(sender):
                menu.add_command(
                    label=t('menu_dm'),
                    command=lambda: self.open_private_chat(sender))

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def open_private_chat(self, username):
        if not valid_username(username):
            return
        if username == self.my_username:
            return
        self.ensure_private_chat(username)
        self.select_chat(username)
        try:
            self.msg_entry.focus_set()
        except Exception:
            pass

    def open_search(self):
        try:
            if (self.search_dialog
                    and self.search_dialog.winfo_exists()):
                self.search_dialog.lift()
                return
        except Exception:
            pass
        try:
            self.search_dialog = SearchDialog(
                self.root, on_search=self._send_search,
                on_pick=self.open_private_chat,
                on_manual_ip=self._prompt_manual_ip)
            self.search_dialog.after(100,
                                     self.search_dialog.lift)
        except Exception as e:
            log_error(f'open_search: {e}')

    def _send_search(self, query):
        self._last_search_query = query
        self._send_obj({'type': 'search', 'query': query})

    def _prompt_manual_ip(self):
        value = ask_input(
            self.root,
            text='Введите ник пользователя (или IP сервера):',
            title='Поиск по сети')
        if not value:
            return
        value = value.strip()
        if not value:
            return

        parts = value.split('.')
        is_ip = (len(parts) == 4 and
                 all(p.isdigit() and 0 <= int(p) <= 255
                     for p in parts))
        if is_ip:
            self.manual_server_ip = value
            self._connecting_ip_display = value
            self._reopen_search_after_connect = True
            self._auto_reconnect_active = False
            self.heartbeat_running = False
            try:
                if self.loop and self.send_queue:
                    try:
                        self.loop.call_soon_threadsafe(
                            self.send_queue.put_nowait, None)
                    except Exception:
                        pass
                if self.writer:
                    try:
                        self.writer.close()
                    except Exception:
                        pass
            except Exception:
                pass
            self.conn_state = 'reconnecting'
            self.writer = None
            self.send_queue = None
            self.typing_dm.clear()
            self.pending_msgs.clear()
            self.update_header()
            if not self._auto_reconnect_active:
                self._auto_reconnect_active = True
                threading.Thread(
                    target=self._auto_reconnect_loop,
                    daemon=True).start()
            return

        if not self.connected:
            custom_alert(self.root, t('error'), t('connect_fail'))
            return
        self._last_search_query = value
        self._send_obj({'type': 'search', 'query': value})
        try:
            self.open_search()
        except Exception as e:
            log_error(f'_prompt_manual_ip open_search: {e}')

    def switch_server(self):
        log_error(f'Switching server to {self.manual_server_ip}')
        self._auto_reconnect_active = False
        self.heartbeat_running = False
        try:
            if self.loop and self.send_queue:
                try:
                    self.loop.call_soon_threadsafe(
                        self.send_queue.put_nowait, None)
                except Exception:
                    pass
            if self.writer:
                try:
                    self.writer.close()
                except Exception:
                    pass
        except Exception:
            pass

        self.conn_state = 'reconnecting'
        self.writer = None
        self.send_queue = None
        self.typing_dm.clear()
        self.pending_msgs.clear()
        self.update_header()

        if not self._auto_reconnect_active:
            self._auto_reconnect_active = True
            threading.Thread(
                target=self._auto_reconnect_loop,
                daemon=True).start()

    def start_reply(self, entry):
        if entry.get('chat_id') == SELF_CHAT_ID:
            return
        text_value = entry.get('text', '') or ''
        preview = text_value[:40]
        if len(text_value) > 40:
            preview += "..."
        if not preview and entry.get('attachment'):
            preview = (t('voice_message')
                       if entry['attachment'].get('voice')
                       else t('attachment'))
        self.reply_to = {'target': entry['sender'],
                         'preview': preview}
        try:
            self.reply_label.configure(
                text=t('reply_to', entry["sender"], preview))
        except Exception:
            pass
        try:
            if self.input_row.winfo_ismapped():
                self.reply_bar.pack(fill="x", padx=10,
                                    pady=(8, 0),
                                    before=self.input_row)
            else:
                self.reply_bar.pack(fill="x", padx=10,
                                    pady=(8, 0))
        except Exception:
            pass
        try:
            self.msg_entry.focus_set()
        except Exception:
            pass

    def cancel_reply(self):
        self.reply_to = None
        try:
            self.reply_bar.pack_forget()
        except Exception:
            pass

    def start_edit(self, chat_id, entry):
        old_text = entry.get('text', '') or ''
        new_text = ask_input(self.root,
                             text=t('edit_message'),
                             title=t('edit_message_title'),
                             initial=old_text)
        if not new_text or not new_text.strip():
            return
        new_text = new_text.strip()
        if new_text == old_text:
            return
        body = f"{new_text}{t('changed_suffix')}"

        entry['text'] = body
        text_lbl = entry.get('text_lbl')
        if text_lbl is not None:
            try:
                text_lbl.configure(text=body)
            except Exception as e:
                log_error(f'start_edit configure: {e}')

        if chat_id == SELF_CHAT_ID:
            return

        msg_id = entry.get('msg_id')
        if not msg_id:
            return

        net_text, _na, enc_flag = self._encrypt_for_peer(
            chat_id, body, None)
        payload = {'type': 'edit', 'to': chat_id,
                   'id': msg_id, 'new_text': net_text}
        if enc_flag:
            payload['encrypted'] = True
        self._send_obj(payload)

    def on_send(self):
        if self._voice_recording:
            self._finish_voice_recording()
            return
        if not self.connected or self.current_chat is None:
            return
        try:
            text = self.msg_entry.get().strip()
        except Exception:
            return
        attachment = self._pending_attachment
        if not text and not attachment:
            return
        try:
            self.msg_entry.delete(0, "end")
        except Exception:
            pass

        if self.current_chat == SELF_CHAT_ID:
            msg_id = self._new_msg_id()
            self.add_message(SELF_CHAT_ID, self.my_username,
                             text, True, msg_id=msg_id,
                             show_status=True,
                             attachment=attachment)
            self.cancel_attachment()
            return

        target = self.current_chat
        msg_id = self._new_msg_id()
        net_text, net_att, enc_flag = self._encrypt_for_peer(
            target, text, attachment)
        payload = {'type': 'dm', 'to': target, 'text': net_text,
                   'id': msg_id}
        if net_att:
            payload['attachment'] = net_att
        if enc_flag:
            payload['encrypted'] = True
        reply = None
        if self.reply_to:
            reply = {'target': self.reply_to['target'],
                     'quote': self.reply_to['preview']}
            payload['reply'] = reply
        self._send_obj(payload)
        self.add_message(target, self.my_username, text, True,
                         msg_id=msg_id, reply=reply,
                         show_status=True, attachment=attachment)
        self.cancel_reply()
        self.cancel_attachment()

    def _send_obj(self, obj):
        if self.loop and self.send_queue:
            try:
                self.loop.call_soon_threadsafe(
                    self.send_queue.put_nowait, obj)
            except Exception:
                pass

    def start_auth(self):
        self._show_auth_window()
        session = load_session()
        if session:
            username, password = session
            log_error(f'Auto-login: {username}')
            if (self.auth_window
                    and self.auth_window.winfo_exists()):
                self.auth_window.set_connecting(True)
            try:
                self._authenticate(
                    {'type': 'login', 'username': username,
                     'password': password},
                    username, is_register=False, from_session=True)
            except Exception as e:
                log_error(f'auto-login: {e}')
                if (self.auth_window
                        and self.auth_window.winfo_exists()):
                    self.auth_window.set_connecting(False)

    def _show_auth_window(self):
        def on_login(u, p):
            try:
                self._authenticate(
                    {'type': 'login', 'username': u,
                     'password': p}, u, is_register=False)
            except Exception as e:
                log_error(f'login: {e}\n{traceback.format_exc()}')
                if (self.auth_window
                        and self.auth_window.winfo_exists()):
                    self.auth_window.show_error(f'{e}')

        def on_register(fn, ln, u, p):
            try:
                self._authenticate(
                    {'type': 'register', 'first_name': fn,
                     'last_name': ln, 'username': u,
                     'password': p}, u, is_register=True)
            except Exception as ex:
                log_error(f'register: {ex}\n{traceback.format_exc()}')
                if (self.auth_window
                        and self.auth_window.winfo_exists()):
                    self.auth_window.show_error(f'{ex}')

        def on_cancel():
            self.on_exit()

        try:
            try:
                if (self.auth_window
                        and self.auth_window.winfo_exists()):
                    self.auth_window.destroy()
            except Exception:
                pass
            self.auth_window = AuthWindow(
                self.root, on_login=on_login,
                on_register=on_register, on_cancel=on_cancel)
            self.auth_window.after(100, self.auth_window.lift)
        except Exception as e:
            log_error(f'AuthWindow creation: {e}\n'
                      f'{traceback.format_exc()}')
            raise

    def _authenticate(self, payload, username_hint, is_register,
                      from_session=False):
        if payload.get('type') == 'login':
            self._saved_username = payload.get('username')
            self._saved_password = payload.get('password')

        pk = self._my_public_key()
        if pk:
            payload['public_key'] = pk

        def on_network_error(msg):
            if from_session:
                log_error(f'Auto-login failed: {msg}')
                self._saved_username = None
                self._saved_password = None
                try:
                    delete_session()
                except Exception:
                    pass
                try:
                    if (self.auth_window
                            and self.auth_window.winfo_exists()):
                        self.auth_window.set_connecting(False)
                except Exception:
                    pass
                return
            try:
                if (self.auth_window
                        and self.auth_window.winfo_exists()):
                    self.auth_window.show_error(msg)
            except Exception:
                pass

        def runner():
            loop = None
            try:
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                self.loop = loop
                loop.run_until_complete(self._work_auth(
                    payload, username_hint, is_register,
                    on_network_error))
            except Exception as e:
                log_error(f'Auth runner: {e}\n'
                          f'{traceback.format_exc()}')
                self._post(on_network_error, f'{e}')
            finally:
                if not is_register or from_session:
                    self._post(self._on_network_closed)

        threading.Thread(target=runner, daemon=True).start()

    async def _work_auth(self, payload, username_hint,
                         is_register, on_network_error):
        try:
            host = self._discover_or_become_server()
        except Exception as e:
            log_error(f'discover: {e}')
            self._post(on_network_error, 'error')
            return
        if not host:
            self._post(on_network_error, 'connect_fail')
            return

        try:
            r, w = await asyncio.wait_for(
                asyncio.open_connection(host, TCP_PORT),
                timeout=10)
        except Exception as e:
            log_error(f'connect: {e}')
            self._post(on_network_error, f'{e}')
            return

        if not is_register:
            try:
                local = db_get_user(payload['username'])
                if local and local[0] != 'SYNCED':
                    payload['local_hash'] = local[0]
                    payload['local_salt'] = local[1]
            except Exception:
                pass

        try:
            w.write((json.dumps(payload) + '\n').encode('utf-8'))
            await w.drain()
            line = await asyncio.wait_for(r.readline(),
                                          timeout=15)
        except Exception as e:
            log_error(f'auth write/read: {e}')
            self._post(on_network_error, f'{e}')
            try:
                w.close()
            except Exception:
                pass
            return

        if not line:
            self._post(on_network_error, 'disconnected')
            return

        try:
            resp = json.loads(line.decode('utf-8'))
        except Exception:
            self._post(on_network_error, 'error')
            return

        if resp.get('type') != 'ok':
            self._post(on_network_error,
                       resp.get('text', 'error'))
            try:
                w.close()
            except Exception:
                pass
            return

        try:
            username = payload.get('username')
            password = payload.get('password')
            fn = resp.get('first_name', payload.get('first_name', ''))
            ln = resp.get('last_name', payload.get('last_name', ''))
            av = resp.get('avatar', '')
            if username and password:
                if not db_user_exists(username):
                    ph, salt = hash_password(password)
                    db_add_user(fn, ln, username, ph, salt, av)
                else:
                    db_update_profile(username,
                                      first_name=fn or None,
                                      last_name=ln or None,
                                      avatar=av or None)
                save_session(username, password)
            self.my_first_name = fn or self.my_first_name
            self.my_last_name = ln or self.my_last_name
            if av:
                self.my_avatar_b64 = av
            try:
                st = load_settings()
                st['first_name'] = self.my_first_name
                st['last_name'] = self.my_last_name
                if av:
                    st['avatar'] = av
                save_settings(st)
            except Exception:
                pass
        except Exception as e:
            log_error(f'local save after auth: {e}')

        self.reader = r
        self.writer = w
        self.send_queue = asyncio.Queue()
        self.server_host = host
        self._saved_username = payload.get('username')
        self._saved_password = payload.get('password')
        self._post(self._on_login_ok,
                   resp.get('username', username_hint))

        try:
            await self._sync_local_users()
        except Exception:
            pass
        try:
            self._send_obj({'type': 'request_all_users'})
        except Exception:
            pass

        self.heartbeat_running = True
        asyncio.create_task(self._heartbeat_loop())

        await asyncio.gather(
            self._recv_loop(r),
            self._send_loop(w))

    def _discover_or_become_server(self):
        if self.manual_server_ip:
            ip = self.manual_server_ip
            self.manual_server_ip = None
            return ip
        if OFFICIAL_SERVER:
            return OFFICIAL_SERVER
        try:
            d = DiscoveryClient()
            host = d.find_server(timeout=1.5)
            if host:
                self.this_is_server = False
                return host
            if self.this_is_server:
                return get_local_ip()
            try:
                self.my_server.start()
            except Exception as e:
                log_error(f'server start: {e}')
            time.sleep(1.5)
            if not port_bound(TCP_PORT):
                time.sleep(0.7)
                host = d.find_server(timeout=1.5)
                if host:
                    return host
                return None
            self.this_is_server = True
            return get_local_ip()
        except Exception as e:
            log_error(f'discover_or_become: {e}')
            return None

    async def _sync_local_users(self):
        try:
            users = db_all_users_with_hashes()
            if users:
                self._send_obj({
                    'type': 'sync_users_full',
                    'users': users,
                })
        except Exception as e:
            log_error(f'sync_local_users: {e}')

    async def _heartbeat_loop(self):
        while self.heartbeat_running:
            try:
                await asyncio.sleep(HEARTBEAT_INTERVAL)
            except Exception:
                break
            if not self.heartbeat_running:
                break
            try:
                if self.send_queue is not None:
                    await self.send_queue.put({'type': '__ping__'})
            except Exception:
                break

    async def _recv_loop(self, reader):
        buf = b''
        while True:
            try:
                data = await reader.read(1048576)
                if not data:
                    break
                buf += data
                if len(buf) > MAX_LINE_BYTES and b'\n' not in buf:
                    log_error('Receive buffer overflow, disconnecting')
                    break
                while b'\n' in buf:
                    line, buf = buf.split(b'\n', 1)
                    if len(line) > MAX_LINE_BYTES:
                        continue
                    s = line.decode('utf-8',
                                    errors='replace').strip()
                    if s:
                        try:
                            if not self._incoming_bucket.allow():
                                log_error(
                                    '[DDOS] Server message flood '
                                    'suppressed')
                                continue
                            obj = json.loads(s)
                            if isinstance(obj, dict):
                                if not _json_depth_ok(obj):
                                    continue
                                self._post(
                                    self._handle_server_message,
                                    obj)
                        except Exception:
                            continue
            except Exception:
                break

    async def _send_loop(self, writer):
        while True:
            try:
                obj = await self.send_queue.get()
                if obj is None:
                    break
                data = json.dumps(obj, ensure_ascii=False) + '\n'
                writer.write(data.encode('utf-8'))
                await writer.drain()
            except Exception:
                break

    def _on_login_ok(self, username):
        self.my_username = username
        self.conn_state = 'connected'
        self._connecting_ip_display = ''
        try:
            prof = db_get_profile(username) or {}
            if not self.my_first_name:
                self.my_first_name = prof.get('first_name', '')
            if not self.my_last_name:
                self.my_last_name = prof.get('last_name', '')
            if not self.my_avatar_b64:
                self.my_avatar_b64 = prof.get('avatar', '')
        except Exception:
            pass
        self._setup_self_chat()
        self.update_header()
        try:
            if (self.auth_window
                    and self.auth_window.winfo_exists()):
                try:
                    self.auth_window.grab_release()
                except Exception:
                    pass
                self.auth_window.destroy()
        except Exception:
            pass
        self.auth_window = None
        try:
            self.root.deiconify()
            sw = self.root.winfo_screenwidth()
            sh = self.root.winfo_screenheight()
            w, h = min(1400, sw - 40), min(900, sh - 80)
            x = max(0, (sw - w) // 2)
            y = max(0, (sh - h) // 2)
            self.root.geometry(f"{w}x{h}+{x}+{y}")
            self.root.lift()
            try:
                self.root.focus_force()
            except Exception:
                pass
        except Exception as e:
            log_error(f'on_login_ok: {e}')

    def _on_network_closed(self):
        if self._saved_username and self._saved_password:
            self.conn_state = 'reconnecting'
            try:
                self.update_header()
            except Exception:
                pass
            if not self._auto_reconnect_active:
                self._auto_reconnect_active = True
                threading.Thread(
                    target=self._auto_reconnect_loop,
                    daemon=True).start()
        else:
            self._mark_all_pending_failed()
            if self.conn_state != 'idle':
                self.conn_state = 'disconnected'
                try:
                    self.update_header()
                except Exception:
                    pass

    def _auto_reconnect_loop(self):
        while self._auto_reconnect_active:
            if not self._saved_username or not self._saved_password:
                break
            try:
                time.sleep(2)
            except Exception:
                break
            if not self._auto_reconnect_active:
                break
            try:
                host = self._discover_or_become_server()
            except Exception as e:
                log_error(f'reconnect discover: {e}')
                continue
            if not host:
                continue
            loop = None
            try:
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                pk = self._my_public_key()

                async def try_login():
                    r, w = await asyncio.wait_for(
                        asyncio.open_connection(host, TCP_PORT),
                        timeout=8)
                    pl = {'type': 'login',
                          'username': self._saved_username,
                          'password': self._saved_password}
                    if pk:
                        pl['public_key'] = pk
                    local = db_get_user(self._saved_username)
                    if local and local[0] != 'SYNCED':
                        pl['local_hash'] = local[0]
                        pl['local_salt'] = local[1]
                    w.write((json.dumps(pl) + '\n')
                            .encode('utf-8'))
                    await w.drain()
                    line = await asyncio.wait_for(r.readline(),
                                                  timeout=10)
                    if not line:
                        return None
                    resp = json.loads(line.decode('utf-8'))
                    if resp.get('type') != 'ok':
                        return None
                    return (r, w)

                result = loop.run_until_complete(try_login())
                if not result:
                    loop.close()
                    continue
                r, w = result
                self.loop = loop
                self.reader = r
                self.writer = w
                self.send_queue = asyncio.Queue()
                self.server_host = host
                self.conn_state = 'connected'
                self._connecting_ip_display = ''
                try:
                    loop.run_until_complete(
                        self._sync_local_users())
                except Exception:
                    pass
                try:
                    self._send_obj({'type': 'request_all_users'})
                except Exception:
                    pass
                if self._reopen_search_after_connect:
                    self._reopen_search_after_connect = False
                    self._post(self.open_search)
                try:
                    self._post(self.update_header)
                except Exception:
                    pass
                self.heartbeat_running = True
                asyncio.create_task(self._heartbeat_loop())
                loop.run_until_complete(asyncio.gather(
                    self._recv_loop(r),
                    self._send_loop(w)))
                try:
                    loop.close()
                except Exception:
                    pass
                self.heartbeat_running = False
            except Exception as e:
                log_error(f'reconnect: {e}')
                if loop:
                    try:
                        loop.close()
                    except Exception:
                        pass
                continue

        self._auto_reconnect_active = False

    def _reconnect_failed(self):
        self._mark_all_pending_failed()
        self.conn_state = 'disconnected'
        self._connecting_ip_display = ''
        try:
            self.update_header()
        except Exception:
            pass

    def _process_incoming_dm(self, obj):
        sender = obj.get('from', '')
        text = obj.get('text', '')
        mid = obj.get('id')
        reply = obj.get('reply')
        attachment = obj.get('attachment')
        forwarded_from = obj.get('forwarded_from')
        if not sender:
            return
        if sender in self.blocked_users:
            return
        self.ensure_private_chat(sender)
        if attachment:
            b64 = attachment.get('data', '')
            name = attachment.get('name', 'file')
            if b64:
                try:
                    raw = base64.b64decode(b64)
                    p = save_file_to_disk(raw, name)
                    if p:
                        attachment['filepath'] = p
                        if not attachment.get('voice'):
                            attachment['data'] = ''
                except Exception as e:
                    log_error(f'decode attachment: {e}')
        self.add_message(sender, sender, text, False,
                         msg_id=mid, reply=reply,
                         attachment=attachment,
                         forwarded_from=forwarded_from)
        if self._should_notify(sender):
            if text:
                preview = text
            elif attachment and attachment.get('voice'):
                preview = t('voice_message')
            elif attachment:
                preview = f"📎 {attachment.get('name', '')}"
            else:
                preview = ''
            self._show_notification(sender, preview)

    def _handle_server_message(self, obj):
        if not isinstance(obj, dict):
            return
        t_type = obj.get('type')
        if t_type == 'dm':
            sender = obj.get('from', '')
            if not sender:
                return
            if sender in self.blocked_users:
                return
            if self._is_encrypted_payload(obj):
                if not HAS_CRYPTO:
                    obj['text'] = t('e2e_decrypt_fail')
                    obj['attachment'] = None
                    self._process_incoming_dm(obj)
                    return
                if self._get_peer_pubkey(sender) is None:
                    self._pending_encrypted.append(obj)
                    self._request_profile(sender)
                    return
                if not self._try_decrypt_dm(sender, obj):
                    self._pending_encrypted.append(obj)
                    self._request_profile(sender)
                    return
            self._process_incoming_dm(obj)
        elif t_type == 'edit':
            sender = obj.get('from', '')
            msg_id = obj.get('id')
            new_text = obj.get('new_text', '')
            if not sender or not msg_id:
                return
            if sender in self.blocked_users:
                return
            if obj.get('encrypted') and new_text:
                pub = self._get_peer_pubkey(sender)
                if pub:
                    shared = self.identity.derive_shared_key(pub)
                    if shared and isinstance(new_text, str):
                        if new_text.startswith(E2E_PREFIX):
                            enc_part = new_text[len(E2E_PREFIX):]
                        else:
                            enc_part = new_text
                        dec = e2e_decrypt(shared, enc_part)
                        if dec is not None:
                            try:
                                new_text = dec.decode('utf-8')
                            except Exception:
                                pass
            self._apply_remote_edit(msg_id, new_text)
        elif t_type == 'call_signal':
            self._handle_call_signal(obj)
        elif t_type == 'userlist':
            self.known_users = obj.get('users', [])
            self.refresh_chat_list_online()
            if (self.current_chat
                    and self.current_chat != SELF_CHAT_ID):
                self._request_status(self.current_chat)
        elif t_type == 'all_users_result':
            users = obj.get('users') or []
            for u in users:
                try:
                    if isinstance(u, dict):
                        name = u.get('name', '')
                    else:
                        name = str(u)
                    if not valid_username(name):
                        continue
                    if not db_user_exists(name):
                        db_add_user('', '', name, 'SYNCED', 'SYNCED')
                except Exception as e:
                    log_error(f'all_users_result item: {e}')
        elif t_type == 'profile_result':
            user = obj.get('user', '')
            if not user:
                return
            self.user_profiles[user] = {
                'first_name': obj.get('first_name', ''),
                'last_name': obj.get('last_name', ''),
                'avatar': obj.get('avatar', ''),
                'public_key': obj.get('public_key', '')}
            if user in self.chats:
                online = user in self.known_users
                prof = self.user_profiles[user]
                base = user
                if prof.get('first_name') or prof.get('last_name'):
                    base = f"{prof.get('first_name', '')} {prof.get('last_name', '')}".strip()
                display = (base if online
                           else f"{base} {t('offline_suffix')}")
                self.chats[user]['name'] = display
                btn = self.chat_buttons.get(user)
                if btn is not None:
                    try:
                        btn.configure(text=display)
                    except Exception:
                        pass
                self._refresh_chat_avatar(user)
                if self.current_chat == user:
                    self.update_header()
            self._flush_pending_encrypted(user)
        elif t_type == 'ack':
            mid = obj.get('id')
            e = self.pending_msgs.pop(mid, None)
            if e is not None:
                self._mark_sent(e)
        elif t_type == 'delete':
            self.remove_message_local(obj.get('id'))
        elif t_type == 'typing':
            sender = obj.get('from', '')
            if not sender or sender == self.my_username:
                return
            if sender in self.blocked_users:
                return
            self.typing_dm[sender] = time.time() + TYPING_TIMEOUT
        elif t_type == 'user_registered':
            u = obj.get('username')
            if u and u not in self.local_users_known:
                self.local_users_known.add(u)
        elif t_type == 'status_result':
            user = obj.get('user')
            online = obj.get('online')
            last_seen = obj.get('last_seen', 0)
            if self.current_chat == user:
                if online:
                    self.status_label.configure(text=t('online'))
                elif last_seen > 0:
                    self.status_label.configure(
                        text=t('was_online'))
                else:
                    self.status_label.configure(text="")
        elif t_type == 'error':
            text = obj.get('text', '')
            mid = obj.get('msg_id')
            if mid:
                e = self.pending_msgs.pop(mid, None)
                if e is not None:
                    sl = e.get('status_lbl')
                    if sl is not None:
                        try:
                            if sl.winfo_exists():
                                sl.configure(
                                    text=t('not_delivered'),
                                    text_color=ERROR_TEXT)
                        except Exception:
                            pass
            try:
                cur = TRANSLATIONS.get(_current_lang, {})
                if text in cur:
                    msg_text = t(text)
                elif text in TRANSLATIONS['ru']:
                    msg_text = t(text)
                else:
                    msg_text = str(text)
                custom_alert(self.root, t('error'), msg_text)
            except Exception:
                pass
        elif t_type == 'session_replaced':
            try:
                self._cleanup_call()
            except Exception:
                pass
            self._auto_reconnect_active = False
            self.heartbeat_running = False
            self._saved_username = None
            self._saved_password = None
            self._pending_new_password = None
            try:
                delete_session()
            except Exception:
                pass
            try:
                if self.writer:
                    try:
                        self.writer.close()
                    except Exception:
                        pass
            except Exception:
                pass
            try:
                custom_alert(self.root, t('error'),
                             t('session_replaced'),
                             auto_close_ms=5000)
            except Exception:
                pass
            try:
                self.on_reconnect()
            except Exception:
                pass
        elif t_type == 'search_result':
            try:
                if not (self.search_dialog
                        and self.search_dialog.winfo_exists()):
                    self.open_search()
                if (self.search_dialog
                        and self.search_dialog.winfo_exists()):
                    self.search_dialog.show_results(
                        obj.get('users', []),
                        obj.get('query', ''))
            except Exception as e:
                log_error(f'search_result: {e}')
        elif t_type == 'ok' or t_type == 'action_ok':
            action = obj.get('action')
            if action == 'deleted':
                self._perform_account_deleted()
            elif action == 'nick':
                new_nick = obj.get('username', '')
                if new_nick:
                    old = self._saved_username or self.my_username
                    self._saved_username = new_nick
                    if self._saved_password:
                        save_session(new_nick,
                                     self._saved_password)
                    self.my_username = new_nick
                    try:
                        if old and old != new_nick:
                            db_rename_user(old, new_nick)
                    except Exception:
                        pass
                    self._setup_self_chat()
                    self.refresh_chat_list_online()
                    custom_alert(self.root, t('done'), t('saved'))
            elif action == 'password_changed':
                self._perform_password_changed()
            elif action == 'profile_updated':
                pass

    def on_change_password(self):
        if not self.connected:
            custom_alert(self.root, t('error'), t('connect_fail'))
            return

        old_pwd = ask_input(self.root,
                            text=t('enter_old_password'),
                            title=t('change_password_title'),
                            show="●")
        if not old_pwd:
            return

        new_pwd = ask_input(self.root,
                            text=t('enter_new_password'),
                            title=t('change_password_title'),
                            show="●")
        if not new_pwd:
            return
        if len(new_pwd) < 6:
            custom_alert(self.root, t('error'),
                         t('password_min_6'))
            return

        new_pwd2 = ask_input(self.root,
                             text=t('enter_new_password_again'),
                             title=t('change_password_title'),
                             show="●")
        if not new_pwd2:
            return
        if new_pwd != new_pwd2:
            custom_alert(self.root, t('error'),
                         t('passwords_dont_match'))
            return

        self._pending_new_password = new_pwd
        self._send_obj({
            'type': 'change_password',
            'old_password': old_pwd,
            'new_password': new_pwd,
        })

    def _perform_password_changed(self):
        new_pwd = self._pending_new_password
        self._pending_new_password = None

        if new_pwd and self._saved_username:
            self._saved_password = new_pwd
            try:
                save_session(self._saved_username, new_pwd)
            except Exception as e:
                log_error(f'save_session after pwd change: {e}')
            try:
                ph, salt = hash_password(new_pwd)
                db_add_user(self.my_first_name, self.my_last_name,
                            self._saved_username, ph, salt,
                            self.my_avatar_b64)
            except Exception as e:
                log_error(f'update local db after pwd change: {e}')

        custom_alert(self.root, t('done'), t('password_changed'))

    def on_delete_account(self):
        if not self.connected:
            custom_alert(self.root, t('error'), t('connect_fail'))
            return
        ok = custom_confirm(
            self.root,
            t('delete_account'),
            t('delete_account_warning'),
            danger=True)
        if not ok:
            return
        password = ask_input(self.root,
                             text=t('enter_password_confirm'),
                             title=t('delete_account'),
                             show="●")
        if not password:
            return
        self._send_obj({'type': 'delete_account',
                        'password': password})

    def _perform_account_deleted(self):
        custom_alert(self.root, t('done'),
                     t('account_deleted'),
                     auto_close_ms=5000)
        try:
            self._cleanup_call()
        except Exception:
            pass
        try:
            delete_session()
        except Exception:
            pass
        self._saved_username = None
        self._saved_password = None
        self._pending_new_password = None
        self.my_username = ''
        self.known_users = []
        self.chats.clear()
        self.chat_frames.clear()
        self.chat_buttons.clear()
        self.chat_avatars.clear()
        self.chat_rows.clear()
        self.empty_chat_labels.clear()
        self.msg_widgets.clear()
        self.pending_msgs.clear()
        self.typing_dm.clear()
        for w in list(self.chats_list.winfo_children()):
            try:
                w.destroy()
            except Exception:
                pass
        for w in list(self.chat_container.winfo_children()):
            try:
                w.destroy()
            except Exception:
                pass
        try:
            self.empty_label = ctk.CTkLabel(
                self.chat_container,
                text=t('select_chat'),
                font=get_font(18), text_color=FG_DIM)
            self.empty_label.grid(row=0, column=0)
        except Exception:
            pass
        self.current_chat = None
        try:
            self.status_label.configure(text="")
        except Exception:
            pass
        self.on_reconnect()

    def on_reconnect(self):
        try:
            self._cleanup_call()
        except Exception:
            pass
        try:
            self._cancel_voice_recording()
        except Exception:
            pass
        try:
            self._stop_voice_playback()
        except Exception:
            pass
        self.manual_server_ip = None
        self._reopen_search_after_connect = False
        self._connecting_ip_display = ''
        self._auto_reconnect_active = False
        self.heartbeat_running = False
        try:
            if self.loop and self.send_queue:
                try:
                    self.loop.call_soon_threadsafe(
                        self.send_queue.put_nowait, None)
                except Exception:
                    pass
            if self.writer:
                try:
                    self.writer.close()
                except Exception:
                    pass
        except Exception:
            pass
        self.conn_state = 'idle'
        self.writer = None
        self.send_queue = None
        self.typing_dm.clear()
        self.pending_msgs.clear()
        self._pending_encrypted.clear()
        self.update_header()
        try:
            self.root.withdraw()
        except Exception:
            pass
        try:
            if (self.auth_window
                    and self.auth_window.winfo_exists()):
                self.auth_window.destroy()
        except Exception:
            pass
        self.auth_window = None
        self._saved_username = None
        self._saved_password = None
        self._pending_new_password = None
        self._show_auth_window()

    def on_window_close(self):
        try:
            st = load_settings()
            save_settings(st)
        except Exception as e:
            log_error(f'save settings on close: {e}')
        try:
            self._cleanup_call()
        except Exception:
            pass
        try:
            self._cancel_voice_recording()
        except Exception:
            pass
        try:
            self._stop_voice_playback()
        except Exception:
            pass
        self._auto_reconnect_active = False
        self.heartbeat_running = False
        self.conn_state = 'idle'
        try:
            if self.loop and self.send_queue:
                try:
                    self.loop.call_soon_threadsafe(
                        self.send_queue.put_nowait, None)
                except Exception:
                    pass
            if self.writer:
                try:
                    self.writer.close()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            self.my_server.stop()
        except Exception:
            pass
        try:
            self.root.quit()
            self.root.destroy()
        except Exception:
            pass

    def on_exit(self):
        self.on_window_close()


def _run_server_only():
    print('=' * 60)
    print('  Chatter Server')
    print('=' * 60)
    try:
        init_db()
    except Exception as e:
        log_error(f'DB init failed: {e}\n{traceback.format_exc()}')
        print(f'[!] Не удалось создать БД: {e}')
        return

    try:
        hostname = socket.gethostname()
        local_ip = get_local_ip()
    except Exception:
        hostname = '?'
        local_ip = '?'

    server = ChatServer()
    server.start()
    time.sleep(1.5)

    print(f'  Хост:         {hostname}')
    print(f'  Локальный IP: {local_ip}')
    print(f'  TCP порт:     {TCP_PORT}')
    print(f'  UDP порт:     {UDP_PORT}')
    print()
    print('  Впиши публичный IP этого компьютера в OFFICIAL_SERVER')
    print('  в chatter.py — и клиенты будут подключаться сюда.')
    print()
    print('  Ctrl+C — остановить сервер.')
    print('=' * 60)

    def _on_signal(sig, frame):
        print('\nОстановка сервера...')
        try:
            server.stop()
        except Exception:
            pass
        os._exit(0)

    try:
        signal.signal(signal.SIGINT, _on_signal)
        if hasattr(signal, 'SIGTERM'):
            signal.signal(signal.SIGTERM, _on_signal)
    except Exception:
        pass

    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        _on_signal(None, None)


def main():
    if '--server' in sys.argv[1:]:
        _run_server_only()
        return

    log_error('=== Запуск Chatter ===')
    try:
        try:
            init_db()
            log_error('DB готов')
        except Exception as e:
            log_error(f'DB init failed: {e}\n'
                      f'{traceback.format_exc()}')
            try:
                r = ctk.CTk()
                r.deiconify()
                r.update_idletasks()
                custom_alert(r, "Ошибка Chatter",
                             f"Не удалось создать БД:\n{e}")
                r.destroy()
            except Exception:
                pass
            return

        app = ChatterApp()
        log_error('ChatterApp создан')

        try:
            app.start_auth()
            log_error('Auth запущен')
        except Exception as e:
            log_error(f'start_auth failed: {e}\n'
                      f'{traceback.format_exc()}')
            try:
                try:
                    app.root.deiconify()
                    app.root.update_idletasks()
                except Exception:
                    pass
                custom_alert(app.root, "Ошибка Chatter",
                             f"Не удалось открыть вход:\n{e}")
            except Exception:
                pass
            return

        app.root.mainloop()
        log_error('Mainloop завершён')
    except Exception as e:
        tb = traceback.format_exc()
        log_error(f'FATAL: {e}\n{tb}')
        try:
            r = ctk.CTk()
            r.deiconify()
            r.update_idletasks()
            custom_alert(r, "Ошибка Chatter",
                         f"Программа упала:\n{e}\n\n"
                         f"Лог: {LOG_PATH}")
            r.destroy()
        except Exception:
            pass


if __name__ == "__main__":
    main()
