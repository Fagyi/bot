# -*- coding: utf-8 -*-
"""
KuCoin Universal SDK Bot (SPOT + Margin) — GUI + Symbols Combo + Funds transfer

Függőségek:
  pip install kucoin-universal-sdk pandas matplotlib requests python-dotenv websocket-client

Környezeti változók (privát módhoz):
  KUCOIN_KEY, KUCOIN_SECRET, KUCOIN_PASSPHRASE, [opcionális] KUCOIN_KEY_VERSION=2
Opcionális:
  BOT_PUBLIC_MODE=0|1, BOT_SYMBOL=SOL-USDT, BOT_TIMEFRAME=5m, BOT_SHORT_MA=20, BOT_LONG_MA=50
A program betölti a .env és/vagy key.env fájlokat is a script mappájából (ha vannak).
"""
from __future__ import annotations

import os, sys, time, json, uuid, hmac, base64, hashlib, threading, math, urllib.request
from typing import List, Optional, Literal, Any, Dict, Tuple
from types import SimpleNamespace as NS
from urllib.parse import urlencode
import threading
import datetime
import collections

# -------- 3rd party --------
import requests
import pandas as pd
import numpy as np
import websocket  # websocket-client
import sqlite3

# Tkinter
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
from tkinter import font as tkfont
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext, ROUND_FLOOR, ROUND_CEILING, InvalidOperation
import ttkbootstrap as tb

# Matplotlib
import matplotlib
matplotlib.use('TkAgg')
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.dates as mdates

# KuCoin SDK (opcionális – ha van, logoljuk a service-eket; a működés REST-tel is megy)
SDK_AVAILABLE = True
try:
    from kucoin_universal_sdk.api import DefaultClient as KucoinClient
    from kucoin_universal_sdk.model import ClientOptionBuilder, TransportOptionBuilder
    from kucoin_universal_sdk.model import GLOBAL_API_ENDPOINT, GLOBAL_FUTURES_API_ENDPOINT, GLOBAL_BROKER_API_ENDPOINT
except Exception:
    SDK_AVAILABLE = False

# -------- Pénzügyi számolások precízió --------
# (Egységesen Decimal-t használunk; ez a precízió bőven elég.)
getcontext().prec = 28

# -------- Hasznos Decimal helper --------
def D(x) -> Decimal:
    return x if isinstance(x, Decimal) else Decimal(str(x))

# -------- .env / key.env betöltés --------
try:
    from dotenv import load_dotenv, find_dotenv
    load_dotenv(find_dotenv(usecwd=True))                         # .env
    here = os.path.dirname(os.path.abspath(__file__))
    load_dotenv(os.path.join(here, "key.env"), override=True)     # key.env
except Exception:
    pass

# -------- Konfig --------
DEFAULT_SYMBOL = os.getenv("BOT_SYMBOL", "SOL-USDT")
TIMEFRAME_CHOICES = ["1m","3m","5m","15m","30m","1h","2h","4h","6h","8h","12h","1d","1w"]
DEFAULT_TIMEFRAME = os.getenv("BOT_TIMEFRAME", "5m")
SHORT_MA = int(os.getenv("BOT_SHORT_MA", "20"))
LONG_MA  = int(os.getenv("BOT_LONG_MA", "50"))
LIMIT = int(os.getenv("BOT_LIMIT", "150"))
SLEEP_SECONDS = int(os.getenv("BOT_SLEEP", "30"))
PUBLIC_MODE_DEFAULT = os.getenv("BOT_PUBLIC_MODE", "1") in ("1","true","True")
ACCOUNT_SORT_PRIORITY = {"Main": 0, "Trade": 1, "Cross": 2, "Isolated": 3}
Signal = Literal["buy", "sell", "hold", "error"]

TF_MAP = {
    '1m': '1min','3m':'3min','5m':'5min','15m':'15min','30m':'30min',
    '1h': '1hour','2h':'2hour','4h':'4hour','6h':'6hour','8h':'8hour','12h':'12hour',
    '1d': '1day','1w':'1week'
}
def timeframe_to_sdk_type(tf: str) -> str:
    return TF_MAP.get(tf.lower().strip(), '5min')

def _pair_group_key(row: dict) -> str:
    sym = normalize_symbol(row.get("symbol") or "")
    if sym:
        return f"0-{sym}"           # valódi pár előre
    return f"1-{(row.get('ccy') or '').upper()}"  # „magányos” deviza később

# -------- Szimbólum normalizálás --------
def normalize_symbol(s: str) -> str:
    """
    Egységes pár formátum: 'BASE-QUOTE' nagybetűvel (pl. 'SOL-USDT').
    Elfogad: 'sol/usdt', 'sol-usdt', 'SOL_USDT', 'sol usdt' stb.
    """
    s = (s or "").strip().upper()
    if not s:
        return s
    # gyakori elválasztók egységesítése '-'-re
    for sep in ("/", ":", "_", " "):
        if sep in s:
            s = s.replace(sep, "-")
    return s

def split_symbol(s: str) -> tuple[str, str]:
    """
    Biztonságos BASE, QUOTE bontás a normalizálás után.
    """
    s = normalize_symbol(s)
    if "-" not in s:
        raise ValueError(f"Érvénytelen symbol: '{s}' (várt forma: BASE-QUOTE)")
    base, quote = s.split("-", 1)
    return base, quote

class ConfigManager:
    @staticmethod
    def save_config(filepath: str, config: dict):
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2, ensure_ascii=False)

    @staticmethod
    def load_config(filepath: str) -> dict:
        with open(filepath, 'r', encoding='utf-8') as f:
            return json.load(f)

class BotDatabase:
    def __init__(self, db_name="bot_trades.db"):
        self.db_name = db_name
        self._init_db()

    def _init_db(self):
        """Létrehozza a táblát, ha nem létezik."""
        conn = sqlite3.connect(self.db_name)
        c = conn.cursor()
        # Tároljuk a pozíció minden lényeges adatát.
        # Az 'extra_data' egy JSON mező lesz a flexibilis adatoknak (pl. SL, TP, peak, mgmt mode).
        c.execute('''CREATE TABLE IF NOT EXISTS trades (
                        order_id TEXT PRIMARY KEY,
                        symbol TEXT,
                        side TEXT,
                        entry_price REAL,
                        size REAL,
                        commit_usdt REAL,
                        fee_reserved REAL,
                        status TEXT,
                        timestamp REAL,
                        extra_data TEXT
                    )''')
        conn.commit()
        conn.close()

    def add_position(self, pos: dict):
        """Új nyitott pozíció mentése."""
        conn = sqlite3.connect(self.db_name)
        c = conn.cursor()

        # Kiemeljük a fix mezőket, a többit JSON-be csomagoljuk
        extra = {k: v for k, v in pos.items() if k not in
                 ['oid', 'order_id', 'id', 'symbol', 'side', 'entry', 'size', 'commit_usdt', 'fee_reserved', 'ts']}

        # Biztosítjuk, hogy legyen order_id
        oid = str(pos.get('oid') or pos.get('order_id') or pos.get('id') or f"sim_{pos.get('ts')}")

        try:
            c.execute('''INSERT OR REPLACE INTO trades
                         (order_id, symbol, side, entry_price, size, commit_usdt, fee_reserved, status, timestamp, extra_data)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                      (oid,
                       pos.get('symbol', ''), # Ha nincs a pos-ban symbol, majd update-eljük
                       pos.get('side'),
                       float(pos.get('entry', 0)),
                       float(pos.get('size', 0)),
                       float(pos.get('commit_usdt', 0)),
                       float(pos.get('fee_reserved', 0)),
                       'OPEN',
                       float(pos.get('ts', 0) or 0),
                       json.dumps(extra, ensure_ascii=False, default=str),
                      ))
            conn.commit()
        except Exception as e:
            print(f"DB Error add_position: {e}")
        finally:
            conn.close()

    def close_position(self, order_id: str, exit_price: float, pnl: float, reason: str):
        """Pozíció státuszának frissítése CLOSED-ra."""
        conn = sqlite3.connect(self.db_name)
        c = conn.cursor()

        # Frissítjük a JSON adatot is a zárási infókkal
        try:
            c.execute("SELECT extra_data FROM trades WHERE order_id=?", (str(order_id),))
            row = c.fetchone()
            if row:
                data = json.loads(row[0])
                data.update({'exit_price': exit_price, 'pnl': pnl, 'close_reason': reason, 'closed_at': time.time()})
                c.execute('''UPDATE trades
                             SET status='CLOSED', extra_data=?
                             WHERE order_id=?''', (json.dumps(data, ensure_ascii=False, default=str), str(order_id)))
                conn.commit()
        except Exception as e:
            print(f"DB Error close_position: {e}")
        finally:
            conn.close()

    def get_open_positions(self):
        """Visszaadja az összes OPEN státuszú pozíciót dict listaként."""
        conn = sqlite3.connect(self.db_name)
        conn.row_factory = sqlite3.Row
        c = conn.cursor()
        c.execute("SELECT * FROM trades WHERE status='OPEN'")
        rows = c.fetchall()
        conn.close()

        positions = []
        for row in rows:
            # Visszaépítjük a dict-et a bot számára
            pos = {
                'oid': row['order_id'],
                'symbol': row['symbol'], # Fontos, hogy mentsük a symbolt
                'side': row['side'],
                'entry': row['entry_price'],
                'size': row['size'],
                'commit_usdt': row['commit_usdt'],
                'fee_reserved': row['fee_reserved'],
                'ts': row['timestamp']
            }
            # Extra adatok (sl, tp, peak, mgmt, stb.) visszamergelése
            if row['extra_data']:
                try:
                    extra = json.loads(row['extra_data'])
                    pos.update(extra)
                except:
                    pass
            positions.append(pos)
        return positions

    def update_position_size(self, order_id: str, new_size: float, new_commit: float):
        conn = sqlite3.connect(self.db_name)
        c = conn.cursor()
        try:
            c.execute("UPDATE trades SET size=?, commit_usdt=? WHERE order_id=?",
                      (new_size, new_commit, str(order_id)))
            conn.commit()
        except Exception as e:
            print(f"DB Update Error: {e}")
        finally:
            conn.close()

class KucoinTickerWS:
    """
    Egyszerű KuCoin public ticker websocket:
      - /market/ticker:{symbol}
      - csak last price-et cache-eli
      - reconnectel, ha kapcsolat elszáll
    """
    def __init__(self, symbol: str, log_fn=None):
        self.symbol = normalize_symbol(symbol)
        self._log = log_fn or (lambda *_a, **_k: None)

        self._last_price = 0.0
        self._last_ts_ms = 0
        self._lock = threading.RLock()

        self._running = False
        self._thread: Optional[threading.Thread] = None
        self._ws = None

        # saját HTTP session a bullet-public tokenhez
        self._http = requests.Session()
        self._base_url = "https://api.kucoin.com"

    # --- publikus API a GUI felé ---

    def start(self):
        """Háttérszál indítása (idempotens)."""
        if self._running:
            return
        self._running = True
        self._thread = threading.Thread(
            target=self._run_loop,
            name="KucoinTickerWS",
            daemon=True
        )
        self._thread.start()

    def stop(self):
        """Szál leállítása + websocket lezárása."""
        self._running = False
        ws = self._ws
        if ws is not None:
            try:
                ws.close()
            except Exception:
                pass

    def set_symbol(self, symbol: str):
        """Aktív szimbólum váltása (pl. SOL-USDT → BTC-USDT)."""
        sym = normalize_symbol(symbol)
        with self._lock:
            self.symbol = sym
        # nem kötelező reconnect, a topicot a message.topic alapján szűrjük

    def get_last_price(self) -> float:
        """Legutóbbi last price (ha nincs, 0.0)."""
        with self._lock:
            return float(self._last_price or 0.0)

    # --- belső segédek ---

    def _run_loop(self):
        """Reconnect loop – ha a kapcsolat elszáll, újraépítjük."""
        while self._running:
            try:
                url, ping_int, ping_to = self._get_ws_url()
                self._log(f"🌐 WS connect: {url}\n")

                ws = websocket.WebSocketApp(
                    url,
                    on_open=self._on_open,
                    on_message=self._on_message,
                    on_error=self._on_error,
                    on_close=self._on_close,
                )
                self._ws = ws

                # ping_interval/timeout ms → s
                pi = (ping_int or 20000) / 1000.0
                pt = (ping_to or 10000) / 1000.0

                ws.run_forever(ping_interval=pi, ping_timeout=pt)
            except Exception as e:
                self._log(f"❌ WS hiba (loop): {e}\n")
            finally:
                self._ws = None

            if self._running:
                self._log("🔁 WS reconnect 5s múlva…\n")
                time.sleep(5.0)

    def _get_ws_url(self):
        """
        bullet-public token lehívása (public websocket).
        POST https://api.kucoin.com/api/v1/bullet-public
        """
        r = self._http.post(self._base_url + "/api/v1/bullet-public", timeout=8)
        r.raise_for_status()
        data = (r.json() or {}).get("data", {}) or {}
        token = data.get("token", "")
        inst_list = data.get("instanceServers") or []
        if not inst_list:
            raise RuntimeError("Nincs instanceServers a bullet-public válaszban.")
        inst = inst_list[0]
        endpoint = inst.get("endpoint")
        if not endpoint:
            raise RuntimeError("Nincs endpoint a bullet-public válaszban.")
        ping_interval = inst.get("pingInterval", 20000)
        ping_timeout  = inst.get("pingTimeout", 10000)
        url = f"{endpoint}?token={token}"
        return url, ping_interval, ping_timeout

    # --- websocket callbackek ---

    def _on_open(self, ws):
        try:
            sym = None
            with self._lock:
                sym = self.symbol
            topic = f"/market/ticker:{sym}"
            msg = {
                "id": str(int(time.time() * 1000)),
                "type": "subscribe",
                "topic": topic,
                "privateChannel": False,
                "response": True,
            }
            ws.send(json.dumps(msg))
            self._log(f"✅ WS subscribed: {topic}\n")
        except Exception as e:
            self._log(f"❌ WS on_open hiba: {e}\n")

    def _on_message(self, ws, message: str):
        try:
            data = json.loads(message)
        except Exception:
            return

        if data.get("type") != "message":
            return

        topic = data.get("topic", "") or ""
        # csak az aktuális symbolra figyelünk
        with self._lock:
            cur_sym = self.symbol
        if not topic.endswith(cur_sym):
            return

        d = data.get("data") or {}
        price_s = d.get("price") or d.get("lastPrice") or d.get("last")
        if not price_s:
            return

        try:
            px = float(price_s)
        except Exception:
            return

        ts = d.get("Time") or d.get("time") or d.get("ts") or int(time.time() * 1000)

        with self._lock:
            self._last_price = px
            try:
                self._last_ts_ms = int(ts)
            except Exception:
                self._last_ts_ms = int(time.time() * 1000)

    def _on_error(self, ws, error):
        self._log(f"❌ WS error: {error}\n")

    def _on_close(self, ws, *args):
        self._log("⚠️ WS closed.\n")

class KucoinKlineWS:
    """
    Egyszerű K-Line (gyertya) WebSocket kliens KuCoinhoz.
    - Több TF-et tud figyelni egy szimbólumra
    - A legutóbbi N gyertyát cache-eli tf-enként
    - get_ohlcv(tf, limit) → ccxt-szerű OHLCV lista: [ts_ms, o, h, l, c, v]
    """

    TF_MAP = {
        "1m": "1min",
        "3m": "3min",
        "5m": "5min",
        "15m": "15min",
        "30m": "30min",
        "1h": "1hour",
        "2h": "2hour",
        "4h": "4hour",
        "6h": "6hour",
        "8h": "8hour",
        "12h": "12hour",
        "1d": "1day",
    }

    def __init__(self, symbol: str, tfs: list[str], log_fn=None, depth: int = 300):
        self.symbol = normalize_symbol(symbol)
        self.tfs = sorted(set(tfs))
        self._depth = int(max(50, depth))

        self._log = log_fn or (lambda *a, **k: None)
        self._lock = threading.RLock()
        self._running = False
        self._thread = None
        self._ws = None

        self._http = requests.Session()
        self._base_url = "https://api.kucoin.com"

        self._ping_interval = 20
        self._ping_timeout = 10

        # tf → list[ [ts_ms, o, h, l, c, v] ]
        self._kline: dict[str, list[list[float]]] = {}

    # --- Bullet-public URL ugyanúgy, mint a Ticker WS-ben ---
    def _get_ws_url(self) -> str:
        resp = self._http.post(
            self._base_url + "/api/v1/bullet-public",
            json={},
            timeout=8,
        )
        data = resp.json()
        if not isinstance(data, dict) or str(data.get("code", "")) != "200000":
            raise RuntimeError(f"bullet-public hiba: {data!r}")

        d2 = data.get("data", {}) or {}
        instance_servers = d2.get("instanceServers", []) or []
        if not instance_servers:
            raise RuntimeError("bullet-public: instanceServers üres")

        server = instance_servers[0]
        endpoint = server.get("endpoint")
        if not endpoint:
            raise RuntimeError("bullet-public: endpoint hiányzik")

        token = d2.get("token")
        if not token:
            raise RuntimeError("bullet-public: token hiányzik")

        self._ping_interval = int(server.get("pingInterval", 20000)) / 1000.0
        self._ping_timeout = int(server.get("pingTimeout", 10000)) / 1000.0

        return f"{endpoint}?token={token}"

    def _log_safe(self, msg: str):
        try:
            self._log(msg)
        except Exception:
            pass

    def _build_sub_msg(self, tf: str) -> dict:
        tf_api = self.TF_MAP.get(tf, None)
        if not tf_api:
            raise ValueError(f"Nem támogatott TF: {tf!r}")

        topic = f"/market/candles:{self.symbol}_{tf_api}"
        return {
            "id": str(int(time.time() * 1000)),
            "type": "subscribe",
            "topic": topic,
            "privateChannel": False,
            "response": True,
        }

    def _on_open(self, ws):
        self._log_safe(f"🌐 KLINE WS open: {self.symbol} {self.tfs}\n")
        for tf in self.tfs:
            try:
                sub = self._build_sub_msg(tf)
                ws.send(json.dumps(sub))
                self._log_safe(f"  ↪ subscribed {sub['topic']}\n")
            except Exception as e:
                self._log_safe(f"❌ KLINE subscribe hiba ({tf}): {e}\n")

    def _on_message(self, ws, message: str):
        try:
            d = json.loads(message)
        except Exception:
            return

        if d.get("type") != "message":
            return

        topic = d.get("topic", "") or ""
        if not topic.startswith("/market/candles:"):
            return

        data = d.get("data", {}) or {}
        # KuCoin WS K-line struktúra (docs szerint):
        # data = {
        #    "symbol": "BTC-USDT",
        #    "candles": ["1589968800","9702.7","9711.6","9702.7","9711.6","0.004776","46.3834592"]
        # }
        candles = data.get("candles") or data.get("kline") or data.get("tick")
        if not isinstance(candles, (list, tuple)) or len(candles) < 7:
            return

        try:
            ts_s = float(candles[0])
            o = float(candles[1])
            c = float(candles[2])
            h = float(candles[3])
            l = float(candles[4])
            v = float(candles[5])
        except Exception:
            return

        ts_ms = int(ts_s * 1000)

        # TF visszakeresése a topicból
        try:
            _, pair_tf = topic.split(":", 1)
            # "BTC-USDT_1min" → "1min"
            tf_api = pair_tf.split("_", 1)[1]
            # invert map
            inv = {v: k for k, v in self.TF_MAP.items()}
            tf = inv.get(tf_api)
            if not tf:
                return
        except Exception:
            return

        row = [ts_ms, o, h, l, c, v]

        with self._lock:
            arr = self._kline.setdefault(tf, [])
            # töröljük azonos ts-t, ha volt
            arr = [x for x in arr if x[0] != ts_ms]
            arr.append(row)
            arr.sort(key=lambda x: x[0])
            if len(arr) > self._depth:
                arr = arr[-self._depth :]
            self._kline[tf] = arr

    def _on_error(self, ws, error):
        self._log_safe(f"❌ KLINE WS error: {error}\n")

    def _on_close(self, ws, code, reason):
        self._log_safe(f"🔌 KLINE WS close code={code} reason={reason}\n")

    def _run_loop(self):
        while self._running:
            try:
                url = self._get_ws_url()
                self._log_safe(f"🌐 KLINE WS connect → {url}\n")
                ws = websocket.WebSocketApp(
                    url,
                    on_open=self._on_open,
                    on_message=self._on_message,
                    on_error=self._on_error,
                    on_close=self._on_close,
                )
                self._ws = ws
                pi = max(5, int(self._ping_interval))
                pt = max(5, int(self._ping_timeout))

                ws.run_forever(
                    ping_interval=pi,
                    ping_timeout=pt,
                    skip_utf8_validation=True,
                )
            except Exception as e:
                self._log_safe(f"❌ KLINE WS run_loop hiba: {e}\n")
            finally:
                self._ws = None
                if self._running:
                    time.sleep(5)

    def start(self):
        if self._running:
            return
        self._running = True
        self._thread = threading.Thread(
            target=self._run_loop, daemon=True, name="KucoinKlineWS"
        )
        self._thread.start()

    def stop(self):
        self._running = False
        try:
            if self._ws is not None:
                self._ws.close()
        except Exception:
            pass

    def is_running(self) -> bool:
        return bool(self._running)

    def get_ohlcv(self, tf: str, limit: int = 200) -> list[list[float]]:
        """
        ccxt-szerű OHLCV: [ts_ms, o, h, l, c, v]
        """
        with self._lock:
            arr = list(self._kline.get(tf, []))
        if not arr:
            return []
        if limit <= 0:
            return arr
        return arr[-limit:]

class KucoinPrivateOrderWS:
    """
    Privát KuCoin Spot/Margin order WebSocket manager (/spotMarket/tradeOrdersV2).

    - bullet-private tokennel csatlakozik
    - /spotMarket/tradeOrdersV2 topicra iratkozik fel
    - buffereli az érkező trade/order üzeneteket
    - orderId -> összesített fee + filled size map-et tart fenn
    - hibatűrő reconnect + ping_interval alapján heartbeat (run_forever pinggel)
    """

    def __init__(self, rest_post_func, log_func, max_buf: int = 1000):
        """
        rest_post_func: pl. self._rest_post  (path: str, data: dict|None) -> dict
        log_func:       pl. self._safe_log  (msg: str) -> None
        """
        self._rest_post = rest_post_func
        self._log = log_func

        self._ws = None
        self._running = False
        self._thread = None

        self._lock = threading.Lock()
        self._msg_buf = collections.deque(maxlen=max_buf)
        self._order_info = {}  # orderId -> {"fee": float, "filled": float, "symbol": str, "ts": int}

        self._ws_url = None
        self._ping_interval = 15.0
        self._ping_timeout = 10.0

        self._last_msg_ts = 0.0

    # --- public API ---

    def start(self):
        if self._running:
            return
        self._running = True
        t = threading.Thread(target=self._run, name="KucoinPrivateOrderWS", daemon=True)
        self._thread = t
        t.start()

    def stop(self):
        self._running = False
        ws = self._ws
        if ws is not None:
            try:
                ws.close()
            except Exception:
                pass

    def is_running(self) -> bool:
        return bool(self._running)

    def get_fee_for_order(self, order_id: str):
        if not order_id:
            return None
        with self._lock:
            info = self._order_info.get(str(order_id))
            if not info:
                return None
            return float(info.get("fee", 0.0))

    def wait_for_fee(self, order_id: str, timeout: float = 0.7, poll: float = 0.05):
        """
        Blokkoló, rövid várakozás: megpróbálja megvárni, hogy WS-en megjöjjön a fee.

        timeout: összesen ennyit vár (sec)
        poll:   két próbálkozás között ennyit alszik
        """

        if not order_id:
            return None
        order_id = str(order_id)

        end_ts = time.time() + max(0.0, timeout)
        last_fee = None

        while time.time() < end_ts:
            with self._lock:
                info = self._order_info.get(order_id)
            if info:
                fee = float(info.get("fee", 0.0))
                # ha 0, lehet, hogy még nem jött meg minden fill
                last_fee = fee
                if fee > 0:
                    return fee
            time.sleep(max(0.0, poll))

        return last_fee

    def get_fill_agg(self, order_id: str, timeout: float = 0.7, poll: float = 0.05):
        """
        Egy adott order összesített filled/fee adata WS bufferből, KIS várakozással.

        Visszatérés:
          (filled_base, filled_quote, fee_quote)

        - timeout: összesen ennyit várunk max (sec)
        - poll:   két próbálkozás között ennyit alszunk

        Logika:
          1) Azonnal megnézzük, van-e már info az orderId-re.
          2) Ha nincs vagy filled == 0, rövid ideig poll-oljuk az order buffert.
          3) Ha jön adat (filled > 0 vagy fee > 0), azt adjuk vissza.
          4) Ha semmi értelmes adat nem jön, (0,0,0)-t adunk vissza.
        """

        if not order_id:
            return 0.0, 0.0, 0.0

        oid = str(order_id)

        # összesen eddig várunk
        end_ts = time.time() + max(0.0, float(timeout))
        poll = max(0.0, float(poll))

        last_fb = None
        last_fq = None
        last_fee = None

        while time.time() < end_ts:
            with self._lock:
                info = self._order_info.get(oid)

            if info:
                fb = float(info.get("filled", 0.0) or 0.0)
                fq = float(info.get("filled_quote", 0.0) or 0.0)
                fee = float(info.get("fee", 0.0) or 0.0)

                # eltároljuk az utolsó látott értékeket
                last_fb = fb
                last_fq = fq
                last_fee = fee

                # ha már van érdemi filled (vagy fee), elég jó nekünk
                if fb > 0.0 or fee > 0.0:
                    return float(fb), float(fq), float(fee)

            if poll > 0:
                time.sleep(poll)
            else:
                break  # poll=0 → csak egyszer nézünk rá

        # timeout: ha láttunk már valamit, azt adjuk vissza, egyébként 0-kat
        if last_fb is not None or last_fee is not None:
            return float(last_fb or 0.0), float(last_fq or 0.0), float(last_fee or 0.0)

        return 0.0, 0.0, 0.0

    def get_last_messages(self, limit: int = 50):
        with self._lock:
            return list(self._msg_buf)[-limit:]

    # --- belső rész: ws loop + üzenet feldolgozás ---

    def _run(self):
        backoff = 1.0

        self._log("🔌 Private order WS worker indul...\n")

        while self._running:
            try:
                url = self._get_ws_url()
                if not url:
                    self._log("❌ Private order WS URL nem elérhető (bullet-private). Újrapróbálás...\n")
                    time.sleep(backoff)
                    backoff = min(backoff * 2.0, 60.0)
                    continue

                self._log(f"🔗 Private order WS connect: {url}\n")

                self._ws = websocket.WebSocketApp(
                    url,
                    on_open=self._on_open,
                    on_message=self._on_message,
                    on_error=self._on_error,
                    on_close=self._on_close,
                )

                # run_forever pinggel – a szerver bullet-private pingInterval-ját használjuk
                self._ws.run_forever(
                    ping_interval=self._ping_interval,
                    ping_timeout=self._ping_timeout,
                )

            except Exception as e:
                self._log(f"❌ Private order WS hiba: {e}\n")

            finally:
                self._ws = None

            if not self._running:
                break

            self._log("ℹ️ Private order WS kapcsolat megszakadt, reconnect...\n")
            time.sleep(backoff)
            backoff = min(backoff * 2.0, 60.0)

        self._log("🔌 Private order WS worker leállt.\n")

    def _get_ws_url(self):
        """
        bullet-private token lehívása, endpoint + pingInterval/pingTimeout kinyerése.
        """
        try:
            # ugyanúgy, mint a ticker WS-nél, csak bullet-private
            resp = self._rest_post("/api/v1/bullet-private", {})
        except Exception as e:
            self._log(f"❌ bullet-private hiba: {e}\n")
            return None

        if not isinstance(resp, dict):
            self._log(f"⚠️ bullet-private válasz nem dict: {resp!r}\n")
            return None

        data = resp.get("data") or {}
        token = data.get("token")
        inst_servers = data.get("instanceServers") or []
        if not token or not inst_servers:
            self._log(f"⚠️ bullet-private hiányos válasz: {resp!r}\n")
            return None

        inst = inst_servers[0] or {}
        endpoint = inst.get("endpoint")
        if not endpoint:
            self._log(f"⚠️ bullet-private endpoint hiányzik: {resp!r}\n")
            return None

        ping_interval_ms = inst.get("pingInterval", 20000)
        ping_timeout_ms = inst.get("pingTimeout", 10000)
        try:
            self._ping_interval = max(5.0, float(ping_interval_ms) / 1000.0)
        except Exception:
            self._ping_interval = 15.0
        try:
            self._ping_timeout = max(3.0, float(ping_timeout_ms) / 1000.0)
        except Exception:
            self._ping_timeout = 10.0

        # connectId opcionális, de tehetünk bele egy randomot
        conn_id = str(uuid.uuid4())
        url = f"{endpoint}?token={token}&connectId={conn_id}"
        self._ws_url = url
        return url

    def _on_open(self, ws):
        try:
            sub = {
                "id": str(int(time.time() * 1000)),
                "type": "subscribe",
                "topic": "/spotMarket/tradeOrdersV2",
                "privateChannel": True,
                "response": True,
            }
            ws.send(json.dumps(sub))
            self._log("✅ Private order WS opened, feliratkozás: /spotMarket/tradeOrdersV2\n")
        except Exception as e:
            self._log(f"⚠️ Private order WS on_open hiba: {e}\n")

    def _on_message(self, ws, message: str):
        self._last_msg_ts = time.time()

        try:
            msg = json.loads(message)
        except Exception:
            self._log(f"⚠️ Private order WS: JSON parse hiba: {message!r}\n")
            return

        with self._lock:
            self._msg_buf.append(msg)

        try:
            if msg.get("type") != "message":
                return
            topic = msg.get("topic") or ""
            if "/spotMarket/tradeOrdersV2" not in topic:
                return

            data = msg.get("data") or {}
            order_id = str(data.get("orderId") or data.get("orderid") or "")
            if not order_id:
                return

            # --- fee ---
            fee_raw = data.get("fee", 0.0)
            try:
                fee = float(fee_raw or 0.0)
            except Exception:
                fee = 0.0

            # --- filled (BASE) ---
            match_size_raw = data.get("matchSize", 0.0)
            try:
                match_size = float(match_size_raw or 0.0)
            except Exception:
                match_size = 0.0

            # --- filled_quote (QUOTE) = matchPrice * matchSize ---
            match_price_raw = data.get("matchPrice", 0.0)
            try:
                match_price = float(match_price_raw or 0.0)
            except Exception:
                match_price = 0.0

            filled_quote_inc = match_size * match_price if (match_size and match_price) else 0.0

            symbol = data.get("symbol") or ""
            ts = int(data.get("ts") or 0)

            with self._lock:
                info = self._order_info.get(order_id) or {
                    "fee": 0.0,
                    "filled": 0.0,
                    "filled_quote": 0.0,  # ÚJ: inicializáljuk
                    "symbol": symbol,
                    "ts": ts,
                }

                info["fee"] = float(info.get("fee", 0.0)) + fee
                info["filled"] = float(info.get("filled", 0.0)) + match_size
                info["filled_quote"] = float(info.get("filled_quote", 0.0)) + float(filled_quote_inc or 0.0)
                info["symbol"] = symbol or info.get("symbol", "")
                info["ts"] = ts or info.get("ts", 0)

                self._order_info[order_id] = info

        except Exception as e:
            self._log(f"⚠️ Private order WS üzenet feldolgozás hiba: {e}\n")

    def _on_error(self, ws, error):
        self._log(f"❌ Private order WS error: {error}\n")

    def _on_close(self, ws, status_code, msg):
        self._log(f"ℹ️ Private order WS close: code={status_code} msg={msg}\n")

# ========= KuCoin Wrapper =========
class KucoinSDKWrapper:
    """
    REST + (ha van) SDK. Privát hívások aláírt REST-tel is működnek.
    - Gyors requests.Session, rövid timeoutok
    - /symbols letöltés comboboxhoz
    - Spot/Isolated/Cross funds transfer végpontok
    """

    def __init__(self, public_mode: bool = True, log_fn=None):
        self.public_mode = public_mode
        self._log = (lambda *_: None) if log_fn is None else log_fn

        # Fast HTTP session
        self._http = requests.Session()
        self._http.headers.update({"User-Agent": "kucoin-bot/1.2"})
        self._timeout = (4, 8)

        # Keys
        self._api_key = os.getenv('KUCOIN_KEY', '')
        self._api_secret = os.getenv('KUCOIN_SECRET', '')
        self._api_passphrase = os.getenv('KUCOIN_PASSPHRASE', '')
        self._api_key_version = os.getenv('KUCOIN_KEY_VERSION', '2')

        # SDK objects (optional)
        self._client = None
        self._spot_market = None
        self._spot_account = None
        self._spot_order = None
        self._isolated_api = None
        self._cross_api = None
        self._margin_order_api = None

        # Symbols meta cache (baseInc/quoteInc/priceInc/baseMin/minFunds) per symbol
        self._symbols_meta: Dict[str, Dict[str, Decimal]] = {}

        # Try init SDK and discover services (non-fatal)
        try:
            if SDK_AVAILABLE:
                transport = (TransportOptionBuilder()
                             .set_keep_alive(True)
                             .set_max_pool_size(10)
                             .set_max_connection_per_pool(10)
                             .build())
                opt = (ClientOptionBuilder()
                       .set_key(self._api_key).set_secret(self._api_secret).set_passphrase(self._api_passphrase)
                       .set_spot_endpoint(GLOBAL_API_ENDPOINT)
                       .set_futures_endpoint(GLOBAL_FUTURES_API_ENDPOINT)
                       .set_broker_endpoint(GLOBAL_BROKER_API_ENDPOINT)
                       .set_transport_option(transport)
                       .build())
                self._client = KucoinClient(opt)
                rs = self._client.rest_service()
                spot_srv = getattr(rs, "get_spot_service", lambda: None)()
                if spot_srv:
                    self._spot_market = getattr(spot_srv, "get_market_api", lambda: None)() or getattr(spot_srv, "market_api", None)
                    self._spot_account = getattr(spot_srv, "get_account_api", lambda: None)() or getattr(spot_srv, "account_api", None)
                    self._spot_order = getattr(spot_srv, "get_order_api", lambda: None)() or getattr(spot_srv, "order_api", None)
                margin_srv = getattr(rs, "get_margin_service", lambda: None)()
                if margin_srv:
                    self._margin_order_api = getattr(margin_srv, "get_order_api", lambda: None)()
        except Exception as _e:
            self._log(f"SDK init hiba: {_e}")
            self._client = None
            self._spot_market = self._spot_account = self._spot_order = None
            self._margin_order_api = None

        # Price cache
        self._price_cache = {}
        self._price_ttl = 3.0

    # --- DECIMAL HELPEREK KUCOIN AMOUNT/PRICE FORMÁZÁSHOZ ---
    def _dec_floor(self, x, step: Decimal | None = None) -> Decimal:
        """
        x-et step-re padlózza Decimal-ben. Ha step None vagy <=0 → csak Decimal(x).
        """
        x_dec = D(x)
        if not step or D(step) <= 0:
            return x_dec
        step_dec = D(step)
        return (x_dec // step_dec) * step_dec

    def _dec_str(self, x: Decimal) -> str:
        """
        KuCoin felé küldhető decimális string (felesleges nullák nélkül).
        """
        # normalize → tudja leszedni a fölös nullákat, de nem exponenciális formában küldünk
        x_n = x.normalize()
        return format(x_n, "f")

    # ----- Symbols meta -----
    def _fetch_symbols_meta(self) -> Dict[str, Dict[str, Decimal]]:
        """
        Betölti a KuCoin /api/v2/symbols listát és előkészíti a lépésköz/min adatokat.
        """
        try:
            r = self._rest_get("/api/v2/symbols", {})
            data = r.get("data", []) or []
        except Exception as e:
            self._log(f"/api/v2/symbols hiba: {e}")
            data = []
        out: Dict[str, Dict[str, Decimal]] = {}
        for row in data:
            sym = normalize_symbol(row.get("symbol") or "")
            if not sym:
                continue
            # mezők elnevezése a KuCoin v2 szerint
            baseInc = D(row.get("baseIncrement") or "0.00000001")
            quoteInc = D(row.get("quoteIncrement") or "0.00000001")
            priceInc = D(row.get("priceIncrement") or "0.00000001")
            baseMin = D(row.get("baseMinSize") or "0")
            # minFunds a v2-ben "minFunds" lehet; ha nincs, használjuk 0-t
            minFunds = D(row.get("minFunds") or "0")
            out[sym] = {
                "baseInc": baseInc,
                "quoteInc": quoteInc,
                "priceInc": priceInc,
                "baseMin": baseMin,
                "minFunds": minFunds,
            }
        return out

    def get_symbol_meta(self, symbol: str) -> Dict[str, Decimal]:
        """
        Visszaadja a szimbólum lépésköz/min adatait cache-ből, hiány esetén letölti.
        """
        s = normalize_symbol(symbol)
        meta = self._symbols_meta.get(s)
        if meta:
            return meta
        loaded = self._fetch_symbols_meta()
        # merge cache
        self._symbols_meta.update(loaded)
        meta = self._symbols_meta.get(s)
        if not meta:
            # végső fallback – nagyon kis lépések, hogy legalább ne kerekítsen fel a tőzsde
            meta = {
                "baseInc": D("0.00000001"),
                "quoteInc": D("0.00000001"),
                "priceInc": D("0.00000001"),
                "baseMin": D("0"),
                "minFunds": D("0"),
            }
            self._symbols_meta[s] = meta
        return meta

    def get_margin_order_api(self):
        """Return margin OrderAPIImpl if available, else None."""
        return getattr(self, "_margin_order_api", None)

    # ----- Sign helpers -----
    def _ensure_keys(self):
        if not (self._api_key and self._api_secret and self._api_passphrase):
            raise RuntimeError("Privát REST hívás: hiányzó API kulcsok.")

    def _rest_sign_headers(self, method: str, path: str, query: str = "", body: str = "") -> Dict[str, str]:
        ts = str(int(time.time() * 1000))
        prehash = ts + method.upper() + path + (("?" + query) if query else "") + body
        sig = base64.b64encode(hmac.new(self._api_secret.encode(), prehash.encode(), hashlib.sha256).digest()).decode()
        if self._api_key_version == "2":
            passphrase = base64.b64encode(hmac.new(self._api_secret.encode(), self._api_passphrase.encode(), hashlib.sha256).digest()).decode()
        else:
            passphrase = self._api_passphrase
        return {
            "KC-API-KEY": self._api_key,
            "KC-API-SIGN": sig,
            "KC-API-TIMESTAMP": ts,
            "KC-API-PASSPHRASE": passphrase,
            "KC-API-KEY-VERSION": self._api_key_version,
            "Content-Type": "application/json",
        }

    def _rest_get(self, path: str, params: Optional[dict] = None):
        base = "https://api.kucoin.com"
        params = params or {}
        # public vs signed auto
        is_public_market = path.startswith("/api/v1/market/")
        if is_public_market:
            r = self._http.get(base + path, params=params, timeout=self._timeout)
            r.raise_for_status()
            return r.json()
        if path.startswith("/api/"):
            self._ensure_keys()
            q = urlencode(params)
            headers = self._rest_sign_headers("GET", path, q, "")
            r = self._http.get(base + path, params=params, headers=headers, timeout=self._timeout)
            r.raise_for_status()
            return r.json()
        r = self._http.get(base + path, params=params, timeout=self._timeout)
        r.raise_for_status()
        return r.json()

    def _rest_post(self, path: str, body: dict) -> dict:
        """
        Aláírt KuCoin REST POST (v2) – az osztály-szintű session-t használva.
        """
        self._ensure_keys()  # Biztosítjuk, hogy vannak kulcsok

        base_url = "https://api.kucoin.com"
        url = base_url + path

        # A test-et JSON stringgé alakítjuk
        payload_json = json.dumps(body, separators=(",", ":"))

        # A meglévő aláíró logikát hívjuk, body-val
        headers = self._rest_sign_headers("POST", path, "", payload_json)

        # Az osztály meglévő session-jét használjuk
        r = self._http.post(url, data=payload_json, headers=headers, timeout=self._timeout)
        r.raise_for_status()
        return r.json() if r.text else {}

    def universal_transfer(self,
                           currency: str,
                           amount: float | str,
                           from_type: str,
                           to_type: str,
                           *,
                           symbol: str | None = None,
                           transfer_type: str = "INTERNAL") -> dict:
        """
        Flex Transfer (v3): /api/v3/accounts/universal-transfer

        from_type / to_type: 'MAIN', 'TRADE', 'MARGIN', 'ISOLATED', 'MARGIN_V2', 'ISOLATED_V2'
        symbol: csak ISOLATED/ISOLATED_V2 esetén kötelező (pl. 'SOL-USDT')
        """
        # --- Decimal amount safe ---
        amt_dec = D(amount)
        # 8 tizedes bőven elég a transferhez, lefelé kerekítve
        amt_dec = amt_dec.quantize(D("0.00000001"), rounding=ROUND_DOWN)

        body = {
            "clientOid": uuid.uuid4().hex,
            "type": transfer_type,           # INTERNAL = saját számláid között
            "currency": currency.upper(),
            "amount": self._dec_str(amt_dec),
            "fromAccountType": from_type,
            "toAccountType": to_type,
        }
        # ISOLATED esetén a szimbólumot tag-ben kell átadni
        if from_type in ("ISOLATED", "ISOLATED_V2"):
            if not symbol:
                raise ValueError("Isolated transferhez meg kell adni a symbol-t (pl. 'SOL-USDT').")
            body["fromAccountTag"] = normalize_symbol(symbol)
        if to_type in ("ISOLATED", "ISOLATED_V2"):
            if not symbol:
                raise ValueError("Isolated transferhez meg kell adni a symbol-t (pl. 'SOL-USDT').")
            body["toAccountTag"] = normalize_symbol(symbol)

        # POST /api/v3/accounts/universal-transfer
        return self._rest_post("/api/v3/accounts/universal-transfer", body)

    def transfer_cross_margin(self, currency: str, amount: float, direction: str,
                              *, spot_account: str = "TRADE") -> dict:
        """
        Cross <-> Spot (Flex Transfer)
        direction: 'in' (Spot -> Cross), 'out' (Cross -> Spot)
        spot_account: nálad a spot egyenleg hova könyvelt (legtöbbször TRADE, ritkábban MAIN)
        """
        if direction not in ("in", "out"):
            raise ValueError("direction csak 'in' vagy 'out' lehet")
        if direction == "in":
            # Spot -> Cross
            return self.universal_transfer(currency, amount, spot_account, "MARGIN")
        else:
            # Cross -> Spot
            return self.universal_transfer(currency, amount, "MARGIN", spot_account)

    def transfer_isolated_margin(self, symbol: str, currency: str, amount: float, direction: str,
                                 *, spot_account: str = "TRADE") -> dict:
        """
        Isolated <-> Spot (Flex Transfer)
        direction: 'in' (Spot -> Isolated), 'out' (Isolated -> Spot)
        Megpróbál ISOLATED-tal, ha a számlád V2-es, automatikusan visszavált ISOLATED_V2-re.
        """
        if direction not in ("in", "out"):
            raise ValueError("direction csak 'in' vagy 'out' lehet")

        symbol = normalize_symbol(symbol)

        def _do(from_t: str, to_t: str):
            return self.universal_transfer(currency, amount, from_t, to_t, symbol=symbol)

        try:
            if direction == "in":
                # Spot -> Isolated
                return _do(spot_account, "ISOLATED")
            else:
                # Isolated -> Spot
                return _do("ISOLATED", spot_account)
        except Exception:
            # egyes számlákon ISOLATED_V2 az aktív
            if direction == "in":
                return _do(spot_account, "ISOLATED_V2")
            else:
                return _do("ISOLATED_V2", spot_account)

    # ----- Symbols -----
    def fetch_symbols(self) -> List[str]:
        """KuCoin /symbols (publikus)."""
        try:
            r = self._rest_get("/api/v1/symbols")
            arr = r.get("data", [])
            syms = [normalize_symbol(str(it.get("symbol"))) for it in arr if it.get("symbol")]
            return sorted(set(syms))
        except Exception as e:
            self._log(f"Symbols hiba: {e}")
            return [DEFAULT_SYMBOL]

    # ----- OHLCV -----
    def fetch_ohlcv(self, symbol: str, timeframe: str, limit: int) -> List[List[float]]:
        ktype = timeframe_to_sdk_type(timeframe)
        r = self._http.get(
            "https://api.kucoin.com/api/v1/market/candles",
            params={"symbol": symbol, "type": ktype},
            timeout=self._timeout
        )
        r.raise_for_status()
        rows = r.json().get("data", [])
        out: List[List[float]] = []
        for row in rows:
            ts = int(row[0]); ts = ts*1000 if ts < 10_000_000_000 else ts
            o, c, h, l, v = float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5])
            out.append([ts, o, h, l, c, v])
        return out[-limit:]

    # ----- árak -----
    def _get_cached_price(self, symbol: str) -> Optional[float]:
        item = self._price_cache.get(symbol)
        if not item: return None
        price, ts = item
        if time.time() - ts <= self._price_ttl: return price
        return None

    def fetch_last_prices_bulk(self, symbols: list[str]) -> dict[str, float]:
        out: dict[str, float] = {}
        need: list[str] = []
        now = time.time()
        for s in symbols:
            cp = self._get_cached_price(s)
            if cp is not None: out[s] = cp
            else: need.append(s)
        if need:
            try:
                r = self._http.get("https://api.kucoin.com/api/v1/market/allTickers", timeout=self._timeout)
                r.raise_for_status()
                tickers = (r.json().get("data") or {}).get("ticker") or []
                last_map = {t["symbol"]: float(t.get("last") or 0) for t in tickers if "symbol" in t}
                for s in need[:]:
                    px = last_map.get(s, 0.0)
                    if px > 0:
                        out[s] = px; self._price_cache[s] = (px, now); need.remove(s)
            except Exception:
                pass
        MAX_FALLBACK = 8
        for s in need[:MAX_FALLBACK]:
            try:
                r = self._http.get("https://api.kucoin.com/api/v1/market/orderbook/level1",
                                   params={"symbol": s}, timeout=self._timeout)
                r.raise_for_status()
                px = float((r.json().get("data") or {}).get("price") or 0)
                if px > 0:
                    out[s] = px; self._price_cache[s] = (px, time.time())
                else:
                    out.setdefault(s, 0.0)
            except Exception:
                out.setdefault(s, 0.0)
        for s in need[MAX_FALLBACK:]:
            out.setdefault(s, 0.0)
        return out

    def fetch_last_price(self, symbol: str) -> float:
        """Return last traded price for symbol (e.g. SOL-USDT) with multi-fallback."""
        # 1) SDK single ticker
        try:
            mod = __import__('kucoin_universal_sdk.generate.spot.market', fromlist=['GetTickerReqBuilder'])
            B = getattr(mod, 'GetTickerReqBuilder')
            req = B().set_symbol(symbol).build()
            resp = self._spot_market.get_ticker(req)
            data = getattr(resp, 'data', {}) or {}
            last = data.get('price') or data.get('last') or data.get('lastTradedPrice')
            if last: return float(last)
        except Exception:
            pass
        # 2) SDK all tickers
        try:
            resp = self._spot_market.get_all_tickers({})
            data = getattr(resp, 'data', {}) or {}
            for it in data.get('ticker', []) or []:
                if normalize_symbol(it.get('symbol') or '') == normalize_symbol(symbol):
                    last = it.get('last') or it.get('price')
                    if last: return float(last)
        except Exception:
            pass
        # 3) REST level1
        try:
            url = f"https://api.kucoin.com/api/v1/market/orderbook/level1?symbol={symbol}"
            with urllib.request.urlopen(url, timeout=8) as r:
                data = json.loads(r.read().decode('utf-8'))
                p = (((data or {}).get('data') or {}).get('price') or 0.0)
                p = float(p or 0.0)
                if p > 0: return p
        except Exception:
            pass
        # 4) REST all tickers fallback
        try:
            with urllib.request.urlopen("https://api.kucoin.com/api/v1/market/allTickers", timeout=8) as r:
                data = json.loads(r.read().decode('utf-8'))
                arr = (((data or {}).get('data') or {}).get('ticker') or [])
                for it in arr:
                    if normalize_symbol(it.get('symbol') or '') == normalize_symbol(symbol):
                        p = it.get('last') or it.get('price')
                        p = float(p or 0.0)
                        if p > 0: return p
        except Exception:
            pass
        return 0.0

    # ----- Spot egyenleg -----
    def fetch_spot_balances(self) -> Dict[str, Dict[str, float]]:
        if self.public_mode:
            raise RuntimeError("Privát mód szükséges.")
        r = self._rest_get("/api/v1/accounts", {})
        data = r.get("data", [])
        out: Dict[str, Dict[str, float]] = {}
        for acc in data or []:
            if acc.get('type') not in (None, 'trade', 'main'): continue
            cur = acc.get('currency') or acc.get('currencyName')
            avail = float(acc.get('available') or acc.get('availableBalance') or 0)
            hold  = float(acc.get('holds') or acc.get('holdBalance') or 0)
            if cur: out[cur] = {"available": avail, "holds": hold}
        return out

    # ----- Margin accountok -----
    def fetch_isolated_accounts(self) -> Any:
        if self.public_mode: raise RuntimeError("Privát mód szükséges (isolated).")
        return self._rest_get("/api/v3/isolated/accounts")

    def fetch_cross_accounts(self) -> Any:
        if self.public_mode: raise RuntimeError("Privát mód szükséges (cross).")
        return self._rest_get("/api/v1/margin/account")

    # ----- Spot order -----
    def place_market_order(self, symbol: str, side: str,
                           size_base: Optional[float | str] = None,
                           funds_quote: Optional[float | str] = None) -> Any:
        if self.public_mode: raise RuntimeError("Publikus módban nem küldhető order.")
        if not (size_base or funds_quote):
            raise ValueError("Adj meg legalább 'size_base' vagy 'funds_quote' értéket.")

        meta = self.get_symbol_meta(symbol)
        base_step = meta.get("baseInc", D("0.00000001"))
        quote_step = meta.get("quoteInc", D("0.00000001"))

        body = {
            "clientOid": uuid.uuid4().hex,
            "symbol": symbol,
            "side": side,
            "type": "market",
        }
        if size_base is not None:
            size_dec = self._dec_floor(size_base, base_step)
            if size_dec > 0:
                body["size"] = self._dec_str(size_dec)
        if funds_quote is not None:
            funds_dec = self._dec_floor(funds_quote, quote_step)
            if funds_dec > 0:
                body["funds"] = self._dec_str(funds_dec)
        return self._rest_post("/api/v1/orders", body)

    # ----- Margin order (HF margin endpoint) -----
    def place_margin_market_order(self, mode: Literal['isolated','cross'], symbol: str, side: str,
                                  size_base: Optional[float | str] = None, funds_quote: Optional[float | str] = None,
                                  leverage: Optional[int] = None, auto_borrow: bool = True,
                                  auto_repay: bool = True) -> Any:
        if self.public_mode: raise RuntimeError("Publikus módban nem küldhető margin order.")
        if not (size_base or funds_quote): raise ValueError("Adj meg Size (BASE) vagy Funds (QUOTE) értéket.")
        if mode not in ("isolated", "cross"): raise ValueError("mode: isolated|cross")
        # KuCoin limit: cross max 5x, isolated max 10x
        if leverage is not None:
            if mode == "cross": leverage = min(int(leverage), 5)
            else: leverage = min(int(leverage), 10)

        # --- Symbol meta → lépésközök Decimal-ben ---
        meta = self.get_symbol_meta(symbol)
        base_step: Decimal = meta.get("baseInc", D("0.00000001"))
        quote_step: Decimal = meta.get("quoteInc", D("0.00000001"))

        body: dict[str, Any] = {
            "clientOid": uuid.uuid4().hex,
            "symbol": symbol,
            "side": side,
            "type": "market",
            "isIsolated": (mode == "isolated"),
            "autoBorrow": bool(auto_borrow),
            "autoRepay": bool(auto_repay),
        }

        # --- Size (BASE) padlózása lot_step-re ---
        if size_base is not None:
            size_dec_in = D(size_base)
            size_dec = self._dec_floor(size_dec_in, base_step)
            if size_dec <= 0:
                raise ValueError("A számolt BASE méret 0 vagy negatív a lot_step padlózás után.")
            body["size"] = self._dec_str(size_dec)

        # --- Funds (QUOTE) padlózása quote_step-re ---
        if funds_quote is not None:
            funds_dec_in = D(funds_quote)
            funds_dec = self._dec_floor(funds_dec_in, quote_step)
            if funds_dec <= 0:
                raise ValueError("A számolt QUOTE funds 0 vagy negatív a quote_step padlózás után.")
            body["funds"] = self._dec_str(funds_dec)

        if leverage is not None:
            body["leverage"] = leverage

        return self._rest_post("/api/v3/hf/margin/order", body)

    def get_margin_fills_by_order(
        self,
        order_id: str,
        symbol: Optional[str] = None,
        trade_type: str = "MARGIN_TRADE",
    ) -> list[dict]:
        """
        HF margin trade history egy adott orderId-hoz.
        KuCoin REST: GET /api/v3/hf/margin/fills
        """
        if self.public_mode:
            raise RuntimeError("Publikus módban nem elérhető a margin trade history.")
        if not order_id:
            return []

        params: dict[str, Any] = {"orderId": order_id}
        if symbol:
            params["symbol"] = symbol
        if trade_type:
            params["tradeType"] = trade_type  # pl. MARGIN_TRADE / MARGIN_ISOLATED_TRADE

        r = self._rest_get("/api/v3/hf/margin/fills", params)
        data = r.get("data") or {}
        items = data.get("items") or data.get("list") or []
        # csak dict típusú elemeket engedünk tovább
        return [it for it in items if isinstance(it, dict)]

    # ----- Pozíció zárás helpers -----
    def close_cross_position(self, symbol: str) -> dict:
        acc = self.fetch_cross_accounts()
        data = acc.get("data", acc) or {}
        # A cross account devizánkénti – szimbolikus zárás: ha BASE liability > 0 → buy BASE; ha BASE total > 0 → sell BASE
        base, quote = symbol.split("-")
        accounts = data.get("accounts", []) or data.get("accountList", []) or []
        base_row = next((it for it in accounts if (it.get("currency") or it.get("currencyName","")).upper()==base.upper()), None)
        if not base_row: raise RuntimeError(f"Nincs cross adat {base} devizára.")
        base_li = float(base_row.get("liability", 0) or 0)
        base_tot = float(base_row.get("total", base_row.get("balance", 0)) or 0)
        if base_li > 0: side, size = "buy",  base_li
        elif base_tot > 0: side, size = "sell", base_tot
        else: raise RuntimeError("Nincs zárható cross pozíció ehhez a párhoz.")
        resp = self.place_margin_market_order("cross", symbol, side, size_base=str(size), auto_borrow=True, auto_repay=True)
        return resp if isinstance(resp, dict) else {"data": resp}

    # ----- Funds transfer -----
    def transfer_spot_internal(self, currency: str, amount: float, from_type: str, to_type: str) -> dict:
        """
        Main <-> Trade (spot) közti átvezetés.
        from_type/to_type: 'main' | 'trade'
        """
        amt_dec = D(amount).quantize(D("0.00000001"), rounding=ROUND_DOWN)
        body = {
            "clientOid": uuid.uuid4().hex,
            "currency": currency,
            "amount": self._dec_str(amt_dec),
            "from": from_type,
            "to": to_type,
        }

        return self._rest_post("/api/v2/accounts/inner-transfer", body)

# ========= GUI =========
class CryptoBotApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self._ex_lock = threading.RLock()
        self._ohlcv_lock = threading.RLock()
        self.root.title("KuCoin Universal SDK Bot (SPOT + Margin)")
        self.root.geometry("1280x930")

        self._ohlcv_cache: dict[tuple[str,str], dict[str, object]] = {}
        self._ohlcv_cache_maxlen = 600  # igény szerint (200-nál nagyobb legyen)

        # ---- Funds / Margin cache alapértelmezett állapota ----
        # Így az _mb_refresh_available hívható akkor is, ha még nem volt teljes "Összes egyenleg frissítése".
        self._balance_cache: dict[str, dict] = {
            "spot": {},
            "cross": {},
            "isolated": {},
        }
        self.usdt_avail: float = 0.0

        # === Globális fontok ===
        # A TkDefaultFont-ot használjuk alapnak, hogy minden ttk widget automatikusan ezt vegye át.
        self.base_font = tkfont.nametofont("TkDefaultFont")
        self.base_font.configure(family="Segoe UI", size=10)  # kezdeti érték

        # Félkövér változat kártya címkékhez
        self.bold_font = tkfont.Font(
            family=self.base_font.cget("family"),
            size=self.base_font.cget("size"),
            weight="bold",
        )

        self.is_running = False
        self.exchange: Optional[KucoinSDKWrapper] = None
        self.public_mode = tk.BooleanVar(value=PUBLIC_MODE_DEFAULT)
        self.symbols: list[str] = [DEFAULT_SYMBOL]

        # --- Globális ticker websocket manager (KuCoin public) ---
        self._ticker_ws: Optional[KucoinTickerWS] = None
        self._ticker_ws_symbol: Optional[str] = None

        self._init_styles()

        # Notebook
        self.nb = ttk.Notebook(root); self.nb.pack(fill=tk.BOTH, expand=True)

        # --- Dashboard ---
        self.tab_dash = ttk.Frame(self.nb); self.nb.add(self.tab_dash, text="Dashboard")
        top = ttk.Frame(self.tab_dash, padding=10); top.pack(fill=tk.X)
        ttk.Button(top, text="Start", command=self.start_bot).pack(side=tk.LEFT, padx=5)
        ttk.Button(top, text="Stop", command=self.stop_bot).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(top, text="Publikus mód (nincs API)", variable=self.public_mode).pack(side=tk.RIGHT)
        self.status_lbl = ttk.Label(top, text="Státusz: Leállítva"); self.status_lbl.pack(side=tk.LEFT, padx=10)

        # PanedWindow a fő területeknek (bal: Settings+Log, jobb: Chart)
        self.dash_paned = ttk.PanedWindow(self.tab_dash, orient=tk.HORIZONTAL)
        self.dash_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Bal oldal
        left_panel = ttk.Frame(self.dash_paned)
        self.dash_paned.add(left_panel, weight=1)

        # Jobb oldal
        right_panel = ttk.Frame(self.dash_paned)
        self.dash_paned.add(right_panel, weight=3)

        # Paraméterek (a bal panelbe)
        params = ttk.Labelframe(left_panel, text="Paraméterek", padding=10)
        params.pack(fill=tk.X, padx=0, pady=(0, 10))

        ttk.Label(params, text="Pár:").grid(row=0, column=0, sticky='w')
        self.e_symbol = ttk.Combobox(params, values=self.symbols, width=18, state='readonly')
        self.e_symbol.set(DEFAULT_SYMBOL); self.e_symbol.grid(row=0, column=1, padx=6)
        ttk.Label(params, text="Idősík:").grid(row=0, column=2, sticky='w')
        self.cb_tf = ttk.Combobox(params, values=TIMEFRAME_CHOICES, width=8, state='readonly')
        self.cb_tf.set(DEFAULT_TIMEFRAME if DEFAULT_TIMEFRAME in TIMEFRAME_CHOICES else '5m'); self.cb_tf.grid(row=0, column=3, padx=6)
        ttk.Label(params, text="Short MA:").grid(row=1, column=0, sticky='w')
        self.e_short = ttk.Entry(params, width=8); self.e_short.insert(0, str(SHORT_MA)); self.e_short.grid(row=1, column=1)
        ttk.Label(params, text="Long MA:").grid(row=1, column=2, sticky='w')
        self.e_long  = ttk.Entry(params, width=8); self.e_long.insert(0, str(LONG_MA)); self.e_long.grid(row=1, column=3)
        ttk.Button(params, text="Frissítés most", command=self.tick_once).grid(row=0, column=4, padx=8)

        # Log (a bal panelbe, kitöltve a maradék helyet)
        lf_log = ttk.Labelframe(left_panel, text="Log", padding=10)
        lf_log.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        self.log_area = scrolledtext.ScrolledText(lf_log, wrap=tk.WORD, height=10); self.log_area.pack(fill=tk.BOTH, expand=True)

        # Chart (a jobb panelbe)
        lf_ch = ttk.Labelframe(right_panel, text="Diagram (Close + MA)", padding=10)
        lf_ch.pack(fill=tk.BOTH, expand=True, padx=(10, 0), pady=0)
        self.fig = Figure(figsize=(8,3), dpi=100); self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=lf_ch); self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # --- SPOT (Trade + Balances egy fülön, card stílus) ---
        self.tab_spot = ttk.Frame(self.nb)
        self.nb.add(self.tab_spot, text="SPOT")

        # Külső wrap – grid, hogy felül ticket, alul táblázat legyen
        spot_wrap = ttk.Frame(self.tab_spot)
        spot_wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        spot_wrap.grid_columnconfigure(0, weight=1)
        spot_wrap.grid_rowconfigure(1, weight=1)   # az alsó rész (táblázat) nyúlhat

        # ===== FELSŐ: Kézi SPOT market megbízás (BALRA ZÁRT, CARD stílus) =====
        tf = ttk.Labelframe(
            spot_wrap,
            text="Kézi SPOT market megbízás",
            padding=10,
            style="Card.TLabelframe",   # <<-- cards stílus, Flatly esetén is működik
        )
        # csak balra zárjuk, nem töltjük ki a teljes sort
        tf.grid(row=0, column=0, sticky="w")

        # rugalmasabb layout: az 1-es oszlop kicsit tágulhat
        for c in range(0, 8):
            tf.grid_columnconfigure(c, weight=0)
        tf.grid_columnconfigure(1, weight=1)

        ttk.Label(tf, text="Pár:").grid(row=0, column=0, sticky="w")
        self.trade_symbol = ttk.Combobox(tf, values=self.symbols, width=18, state='readonly')
        self.trade_symbol.set(DEFAULT_SYMBOL)
        self.trade_symbol.grid(row=0, column=1, sticky="w", padx=6)

        ttk.Label(tf, text="Size (BASE):").grid(row=0, column=2, sticky="w")
        self.trade_size = ttk.Entry(tf, width=12)
        self.trade_size.grid(row=0, column=3, sticky="w", padx=6)

        ttk.Label(tf, text="Funds (QUOTE):").grid(row=0, column=4, sticky="w")
        self.trade_funds = ttk.Entry(tf, width=12)
        self.trade_funds.grid(row=0, column=5, sticky="w", padx=6)

        self.btn_spot_buy = ttk.Button(
            tf,
            text="BUY (market)",
            command=lambda: self.market_order('buy')
        )
        self.btn_spot_buy.grid(row=0, column=6, sticky="w", padx=6)

        self.btn_spot_sell = ttk.Button(
            tf,
            text="SELL (market)",
            command=lambda: self.market_order('sell')
        )
        self.btn_spot_sell.grid(row=0, column=7, sticky="w", padx=6)

        # ===== ALSÓ: Balances (SPOT) – card stílus, kitöltve =====
        bf = ttk.Labelframe(
            spot_wrap,
            text="Egyenlegek (SPOT)",
            padding=10,
            style="Card.TLabelframe",   # <<-- ugyanaz a cards stílus
        )
        bf.grid(row=1, column=0, sticky="nsew", pady=(8, 0))

        cols = ("currency", "available", "holds")
        self.tbl_bal = ttk.Treeview(bf, columns=cols, show='headings', height=14)
        for c in cols:
            self.tbl_bal.heading(c, text=c)
            self.tbl_bal.column(c, width=160, anchor='center')
        self.tbl_bal.pack(fill=tk.BOTH, expand=True)

        ttk.Button(
            bf,
            text="Frissítsd egyenlegeket",
            command=self.refresh_balances
        ).pack(pady=6)

        # --- Pozíciók (margin olvasás) ---
        self.tab_positions = ttk.Frame(self.nb); self.nb.add(self.tab_positions, text="Pozíciók")
        spf = ttk.Labelframe(self.tab_positions, text="Margin lekérdezések", padding=10); spf.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # felső vezérlősor
        top = ttk.Frame(spf); top.pack(fill=tk.X)
        self.btn_iso   = ttk.Button(top, text="Isolated accounts", command=self.view_isolated_accounts); self.btn_iso.pack(side=tk.LEFT, padx=6)
        self.btn_cross = ttk.Button(top, text="Cross margin account", command=self.view_cross_accounts); self.btn_cross.pack(side=tk.LEFT, padx=6)
        ttk.Label(top, text="  |  Cross symbol:").pack(side=tk.LEFT, padx=6)
        self.cross_symbol = ttk.Combobox(top, values=self.symbols, width=18, state='readonly')
        self.cross_symbol.set(DEFAULT_SYMBOL); self.cross_symbol.pack(side=tk.LEFT)
        self.btn_cross_snap = ttk.Button(top, text="Snapshot (pair)", command=self.view_cross_for_symbol); self.btn_cross_snap.pack(side=tk.LEFT, padx=6)
        self.btn_cross_close = ttk.Button(top, text="Close this cross", command=self.close_cross_clicked); self.btn_cross_close.pack(side=tk.LEFT, padx=6)
        self.btn_close_selected = ttk.Button(top, text="Close selected (market)", command=self.close_selected_isolated)
        self.btn_close_selected.pack(side=tk.LEFT, padx=6)

        # isolated/cross táblázat (közös)
        tbl_frame = ttk.Frame(spf); tbl_frame.pack(fill=tk.BOTH, expand=True, pady=(8,6))
        cols = ("symbol","side","closable","base","quote","risk")
        self.tbl_iso = ttk.Treeview(tbl_frame, columns=cols, show="headings", height=10, selectmode="browse")
        for c, w in zip(cols, (140,80,160,260,260,140)):
            self.tbl_iso.heading(c, text=c); self.tbl_iso.column(c, width=w, anchor="center")
        self.tbl_iso.pack(fill=tk.BOTH, expand=True)

        # részletes szöveg
        self.txt_positions = scrolledtext.ScrolledText(spf, wrap=tk.WORD, height=12)
        self.txt_positions.pack(fill=tk.BOTH, expand=True, pady=(6,0))

        # === Funds / Átvezetés (ÚJ LAYOUT) ===
        self._build_funds_tab()

        # === Margin Trade (modern ticket) ===
        self.tab_margin = ttk.Frame(self.nb); self.nb.add(self.tab_margin, text="Margin Trade")

        wrap = ttk.Frame(self.tab_margin); wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        wrap.grid_columnconfigure(0, weight=0)
        wrap.grid_columnconfigure(1, weight=1)
        wrap.grid_rowconfigure(1, weight=1)

        # bal: ORDER TICKET
        ticket = ttk.Labelframe(wrap, text="Order ticket", style="Card.TLabelframe")
        ticket.grid(row=0, column=0, rowspan=2, sticky="nsew", padx=(0,10))
        for c in range(0, 4):
            ticket.grid_columnconfigure(c, weight=1)

        # 1) mód + pár
        self.mt_mode = tk.StringVar(value='isolated')
        ttk.Radiobutton(ticket, text='Isolated', variable=self.mt_mode, value='isolated',
                        command=self._mt_on_mode_change).grid(row=0, column=0, sticky="w", pady=(0,6))
        ttk.Radiobutton(ticket, text='Cross',    variable=self.mt_mode, value='cross',
                        command=self._mt_on_mode_change).grid(row=0, column=1, sticky="w", pady=(0,6))
        ttk.Label(ticket, text="Pár").grid(row=0, column=2, sticky="e", padx=(6,2))
        self.mt_symbol = ttk.Combobox(ticket, values=self.symbols, width=18, state='readonly')
        self.mt_symbol.set(DEFAULT_SYMBOL); self.mt_symbol.grid(row=0, column=3, sticky="we")

        # 2) típus + TIF + ár (limitnél)
        ttk.Label(ticket, text="Típus").grid(row=1, column=0, sticky="e")
        self.mt_type = tk.StringVar(value="market")
        ttk.Combobox(ticket, textvariable=self.mt_type, state="readonly",
                     values=["market","limit"], width=10).grid(row=1, column=1, sticky="we", padx=(4,8))
        ttk.Label(ticket, text="TIF").grid(row=1, column=2, sticky="e")
        self.mt_tif = tk.StringVar(value="GTC")
        ttk.Combobox(ticket, textvariable=self.mt_tif, state="readonly",
                     values=["GTC","IOC","FOK"], width=8).grid(row=1, column=3, sticky="we")
        ttk.Label(ticket, text="Ár (limit)").grid(row=2, column=0, sticky="e", pady=(6,0))
        self.mt_price = ttk.Entry(ticket, width=12); self.mt_price.grid(row=2, column=1, sticky="we", pady=(6,0))

        # 3) Auto-borrow + leverage
        self.mt_autobr = tk.BooleanVar(value=True)
        ttk.Checkbutton(ticket, text="Auto-borrow/repay", variable=self.mt_autobr).grid(row=2, column=2, sticky="w", pady=(6,0))
        ttk.Label(ticket, text="Leverage").grid(row=2, column=3, sticky="w", pady=(6,0))
        self.mt_lev = ttk.Spinbox(ticket, from_=1, to=10, width=6); self.mt_lev.delete(0, tk.END); self.mt_lev.insert(0, "10")
        self.mt_lev.grid(row=2, column=3, sticky="e", pady=(6,0))

        ttk.Separator(ticket).grid(row=3, column=0, columnspan=4, sticky="we", pady=8)

        # 4) mennyiség/érték blokk
        self.mt_input_mode = tk.StringVar(value='base')
        ttk.Radiobutton(ticket, text='Mennyiség (BASE)', variable=self.mt_input_mode, value='base',
                        command=self._mt_on_input_change).grid(row=4, column=0, columnspan=2, sticky="w")
        ttk.Radiobutton(ticket, text='Érték (QUOTE)', variable=self.mt_input_mode, value='quote',
                        command=self._mt_on_input_change).grid(row=4, column=2, columnspan=2, sticky="w")

        ttk.Label(ticket, text="Size (BASE)").grid(row=5, column=0, sticky="w", pady=(2,0))
        self.mt_size = ttk.Entry(ticket); self.mt_size.grid(row=5, column=0, columnspan=2, sticky="we", padx=(0,6))
        self.mt_size.bind("<KeyRelease>", lambda e: self._mt_on_input_change())

        ttk.Label(ticket, text="Funds (QUOTE)").grid(row=5, column=2, sticky="w", pady=(2,0))
        self.mt_funds = ttk.Entry(ticket); self.mt_funds.grid(row=5, column=2, columnspan=2, sticky="we", padx=(6,0))
        self.mt_funds.bind("<KeyRelease>", lambda e: self._mt_on_input_change())

        # %-gombok
        pct_bar = ttk.Frame(ticket); pct_bar.grid(row=6, column=0, columnspan=4, sticky="we", pady=(6,0))
        for p in (25, 50, 75, 100):
            ttk.Button(pct_bar, text=f"{p}%", command=lambda v=p: (self.mt_pct.set(v), self._mt_update_for_percent())).pack(side=tk.LEFT, padx=3)

        # slider + MAX gombok
        self.mt_pct = tk.IntVar(value=0)
        scale_widget = ttk.Scale(ticket, from_=0, to=100, orient='horizontal', variable=self.mt_pct)
        scale_widget.grid(row=7, column=0, columnspan=3, sticky="we", pady=(4,0))
        scale_widget.bind("<Button-1>", self._mt_on_slider_press)
        scale_widget.bind("<ButtonRelease-1>", self._mt_on_slider_release)
        actions = ttk.Frame(ticket); actions.grid(row=7, column=3, sticky="e", pady=(4,0))
        ttk.Button(actions, text="Max BUY",  command=lambda: self._mt_fill_max('buy')).pack(side=tk.LEFT, padx=2)
        ttk.Button(actions, text="Max SELL", command=lambda: self._mt_fill_max('sell')).pack(side=tk.LEFT, padx=2)
        ttk.Separator(ticket).grid(row=8, column=0, columnspan=4, sticky="we", pady=8)

        # akció gombok – nagy, színezett
        btn_frame = ttk.Frame(ticket)
        btn_frame.grid(row=9, column=0, columnspan=4, sticky="we", pady=(4,0))
        btn_frame.grid_columnconfigure(0, weight=1)
        btn_frame.grid_columnconfigure(1, weight=1)
        # BUY / SELL gombok
        self.btn_mt_buy = ttk.Button(btn_frame, text="BUY (margin)", style="Buy.TButton",
                                     command=lambda: self._mt_place('buy'))
        self.btn_mt_buy.grid(row=0, column=0, sticky="we", padx=(0,3))

        self.btn_mt_sell = ttk.Button(btn_frame, text="SELL (margin)", style="Sell.TButton",
                                      command=lambda: self._mt_place('sell'))
        self.btn_mt_sell.grid(row=0, column=1, sticky="we", padx=(3,0))

        # jobb: INFO / LOG
        info = ttk.Labelframe(wrap, text="Margin részletek", style="Card.TLabelframe")
        info.grid(row=0, column=1, sticky="nsew")
        info.grid_columnconfigure(1, weight=1)

        ttk.Label(info, text="Élő ár").grid(row=0, column=0, sticky="w")
        self.mt_price_lbl = ttk.Label(info, text="–"); self.mt_price_lbl.grid(row=0, column=1, sticky="w")
        ttk.Label(info, text="Becsült költség/hozam").grid(row=1, column=0, sticky="w")
        self.mt_est_lbl = ttk.Label(info, text="–"); self.mt_est_lbl.grid(row=1, column=1, sticky="w")

        log_frame = ttk.Labelframe(wrap, text="Részletes napló", style="Card.TLabelframe")
        log_frame.grid(row=1, column=1, sticky="nsew", pady=(10,0))
        log_frame.grid_columnconfigure(0, weight=1); log_frame.grid_rowconfigure(0, weight=1)
        self.margin_log = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, height=16)
        self.margin_log.grid(row=0, column=0, sticky="nsew")

        # élő ár frissítés indul
        self._mt_price_job = None
        self._mt_start_price_loop()
        self._mt_on_input_change()

        # Adatbázis kezelés
        self.db = BotDatabase()

        # --- Margin Bot (auto) ---
        self._build_margin_bot_tab()

        # --- Beállítások fül (font) ---
        self._build_settings_tab()

        # Szimbólumok betöltése háttérben
        threading.Thread(target=self._load_symbols_async, daemon=True).start()

        # 4) FONT GLOBÁLIS ALKALMAZÁSA
        self._apply_global_font()

        # 5) Auto-load config ha létezik
        try:
            if os.path.exists("config.json"):
                cfg = ConfigManager.load_config("config.json")
                self.root.after(100, lambda: self._apply_cfg_to_ui(cfg))
                self._safe_log("ℹ️ Auto-loaded config.json\n")
        except Exception as e:
            self._safe_log(f"⚠️ Auto-load error: {e}\n")

        # --- K-Line WS indítása már init-ben (alapértelmezett symbol + TF-ek) ---
        try:
            default_sym = normalize_symbol(DEFAULT_SYMBOL)
            self._ensure_ticker_ws(default_sym)
        except Exception as e:
            # ha bármi gebasz van, ne dőljön el a GUI
            print("Ticker WS init hiba az __init__-ben:", e)

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def _build_funds_tab(self):
        """Funds tab új layout: Bal oldalon táblázat, Jobb oldalon Transfer Wizard, Alul Log."""
        self.tab_funds = ttk.Frame(self.nb)
        self.nb.add(self.tab_funds, text="Funds / Átvezetés")

        # Root grid
        self.tab_funds.grid_rowconfigure(0, weight=1)   # top (balances + transfer)
        self.tab_funds.grid_rowconfigure(1, weight=1)   # log
        self.tab_funds.grid_columnconfigure(0, weight=1)

        top = ttk.Frame(self.tab_funds)
        top.grid(row=0, column=0, sticky="nsew", padx=10, pady=(10, 5))
        top.grid_columnconfigure(0, weight=3)  # balances
        top.grid_columnconfigure(1, weight=1)  # transfer
        top.grid_rowconfigure(0, weight=1)

        # -----------------------------
        # LEFT: Balances (table + actions)
        # -----------------------------
        bf = ttk.Labelframe(top, text="Összesített egyenlegek (Main, Trade, Cross, Isolated)", padding=10)
        bf.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        bf.grid_rowconfigure(1, weight=1)
        bf.grid_columnconfigure(0, weight=1)

        # Action bar (gombok + last update)
        bal_actions = ttk.Frame(bf)
        bal_actions.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        bal_actions.grid_columnconfigure(0, weight=1)
        bal_actions.grid_columnconfigure(1, weight=0)
        bal_actions.grid_columnconfigure(2, weight=0)
        bal_actions.grid_columnconfigure(3, weight=0)

        self.lbl_funds_last_update = ttk.Label(bal_actions, text="Utolsó frissítés: —")
        self.lbl_funds_last_update.grid(row=0, column=0, sticky="w")

        btn_refresh = ttk.Button(bal_actions, text="Frissítés", command=self.refresh_all_funds_balances)
        btn_refresh.grid(row=0, column=1, padx=(8, 0))

        btn_repay = ttk.Button(bal_actions, text="Beragadt kötelezettségek rendezése", command=self.repay_stuck_margin)
        btn_repay.grid(row=0, column=2, padx=(8, 0))

        # Treeview + scrollbar
        cols = ("currency", "account_type", "available", "holds", "value_usd", "liability", "total", "pnl", "symbol")
        tbl_wrap = ttk.Frame(bf)
        tbl_wrap.grid(row=1, column=0, sticky="nsew")
        tbl_wrap.grid_rowconfigure(0, weight=1)
        tbl_wrap.grid_columnconfigure(0, weight=1)

        self.tbl_funds_bal = ttk.Treeview(tbl_wrap, columns=cols, show="headings", height=12)
        vsb = ttk.Scrollbar(tbl_wrap, orient="vertical", command=self.tbl_funds_bal.yview)
        self.tbl_funds_bal.configure(yscrollcommand=vsb.set)

        self.tbl_funds_bal.heading("currency",     text="Deviza");         self.tbl_funds_bal.column("currency", width=70, anchor="center")
        self.tbl_funds_bal.heading("account_type", text="Számla");         self.tbl_funds_bal.column("account_type", width=90, anchor="center")
        self.tbl_funds_bal.heading("available",    text="Elérhető");       self.tbl_funds_bal.column("available", width=140, anchor="e")
        self.tbl_funds_bal.heading("holds",        text="Tartott");        self.tbl_funds_bal.column("holds", width=140, anchor="e")
        self.tbl_funds_bal.heading("value_usd",    text="Érték (USD)");    self.tbl_funds_bal.column("value_usd", width=140, anchor="e", stretch=tk.NO)
        self.tbl_funds_bal.heading("liability",    text="Kötelezettség");  self.tbl_funds_bal.column("liability", width=140, anchor="e")
        self.tbl_funds_bal.heading("total",        text="Nettó Összesen"); self.tbl_funds_bal.column("total", width=140, anchor="e")
        self.tbl_funds_bal.heading("pnl",          text="PNL (USD)");      self.tbl_funds_bal.column("pnl", width=110, anchor="e", stretch=tk.NO)
        self.tbl_funds_bal.heading("symbol",       text="Pár");            self.tbl_funds_bal.column("symbol", width=90, anchor="center")

        self.tbl_funds_bal.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")

        # -----------------------------
        # RIGHT: Transfer Wizard
        # -----------------------------
        tf = ttk.Labelframe(top, text="Átvezetés (Wizard)", padding=10)
        tf.grid(row=0, column=1, sticky="nsew")
        tf.grid_columnconfigure(0, weight=0)
        tf.grid_columnconfigure(1, weight=1)

        # Wizard vars
        self.var_tr_from = tk.StringVar(value="Main")
        self.var_tr_to = tk.StringVar(value="Trade")
        self.var_tr_ccy = tk.StringVar(value="USDT")
        self.var_tr_amt = tk.StringVar(value="10")
        self.var_tr_pair = tk.StringVar(value=DEFAULT_SYMBOL if "DEFAULT_SYMBOL" in globals() else "")

        # Helper: show/hide Pair row if Isolated involved
        def on_from_to_change(*_):
            from_acc = (self.var_tr_from.get() or "").strip().lower()
            to_acc = (self.var_tr_to.get() or "").strip().lower()
            needs_pair = (from_acc == "isolated") or (to_acc == "isolated")

            if needs_pair:
                self.lbl_tr_pair.grid()
                self.cmb_tr_pair.grid()
            else:
                self.lbl_tr_pair.grid_remove()
                self.cmb_tr_pair.grid_remove()

        # Bind changes
        self.var_tr_from.trace_add("write", on_from_to_change)
        self.var_tr_to.trace_add("write", on_from_to_change)

        # Row 0: From
        ttk.Label(tf, text="Honnan").grid(row=0, column=0, sticky="w", pady=(0, 6))
        self.cmb_tr_from = ttk.Combobox(tf, state="readonly", width=14,
                                        values=["Main", "Trade", "Cross", "Isolated"],
                                        textvariable=self.var_tr_from)
        self.cmb_tr_from.grid(row=0, column=1, sticky="ew", pady=(0, 6))

        # Row 1: To
        ttk.Label(tf, text="Hová").grid(row=1, column=0, sticky="w", pady=(0, 6))
        self.cmb_tr_to = ttk.Combobox(tf, state="readonly", width=14,
                                      values=["Main", "Trade", "Cross", "Isolated"],
                                      textvariable=self.var_tr_to)
        self.cmb_tr_to.grid(row=1, column=1, sticky="ew", pady=(0, 6))

        # Row 2: Asset
        ttk.Label(tf, text="Deviza").grid(row=2, column=0, sticky="w", pady=(0, 6))
        self.ent_tr_ccy = ttk.Entry(tf, textvariable=self.var_tr_ccy, width=14)
        self.ent_tr_ccy.grid(row=2, column=1, sticky="ew", pady=(0, 6))

        # Row 3: Amount + Max
        # Szerkezet: Label balra (col 0), Frame jobbra (col 1), benne Entry + Button
        ttk.Label(tf, text="Összeg").grid(row=3, column=0, sticky="w", pady=(0, 6))

        amt_frame = ttk.Frame(tf)
        amt_frame.grid(row=3, column=1, sticky="ew", pady=(0, 6))
        amt_frame.grid_columnconfigure(0, weight=1)  # Entry nyúlik
        amt_frame.grid_columnconfigure(1, weight=0)  # Gomb fix

        self.ent_tr_amt = ttk.Entry(amt_frame, textvariable=self.var_tr_amt, width=14)
        self.ent_tr_amt.grid(row=0, column=0, sticky="ew", padx=(0, 6))

        def _set_max_amount():
            ccy = (self.var_tr_ccy.get() or "").strip().upper()
            if not ccy:
                return

            from_acc = (self.var_tr_from.get() or "").strip().lower()
            pair = (self.var_tr_pair.get() or "").strip().upper()

            try:
                cache = getattr(self, "_balance_cache", None) or {}
                avail = None

                if from_acc in ("main", "trade"):
                    node = ((cache.get("spot") or {}).get(ccy) or {}).get(from_acc)
                    if node and isinstance(node, dict):
                        avail = float(node.get("avail") or 0.0)

                elif from_acc == "cross":
                    node = (cache.get("cross") or {}).get(ccy)
                    if node and isinstance(node, dict):
                        avail = float(node.get("avail") or 0.0)

                elif from_acc == "isolated":
                    iso = (cache.get("isolated") or {}).get(pair)
                    if iso and isinstance(iso, dict):
                        base = iso.get("base") or {}
                        quote = iso.get("quote") or {}
                        if (base.get("ccy") or "").upper() == ccy:
                            avail = float(base.get("avail") or 0.0)
                        elif (quote.get("ccy") or "").upper() == ccy:
                            avail = float(quote.get("avail") or 0.0)

                if avail is not None and avail > 0:
                    # konzervatív: 8 tized, de ne kerekítsen felfelé
                    self.var_tr_amt.set(f"{avail:.8f}".rstrip("0").rstrip("."))
            except Exception:
                return

        ttk.Button(amt_frame, text="Max", command=_set_max_amount).grid(row=0, column=1, sticky="e")

        # Row 4: Pair (only if Isolated involved)
        # Közvetlenül a tf rácsába, így nem csúszik el a címke
        self.lbl_tr_pair = ttk.Label(tf, text="Pár")
        self.lbl_tr_pair.grid(row=4, column=0, sticky="w", pady=(0, 8))

        self.cmb_tr_pair = ttk.Combobox(tf, state="readonly", width=10,
                                        values=getattr(self, "symbols", []),
                                        textvariable=self.var_tr_pair)
        self.cmb_tr_pair.grid(row=4, column=1, sticky="ew", pady=(0, 8))

        # Initial hide/show
        on_from_to_change()

        # Preview label
        self.lbl_tr_preview = ttk.Label(tf, text="Transfer: —")
        self.lbl_tr_preview.grid(row=5, column=0, columnspan=2, sticky="w", pady=(0, 8))

        def _update_preview(*_):
            ccy = (self.var_tr_ccy.get() or "").strip().upper()
            amt = (self.var_tr_amt.get() or "").strip()
            f = (self.var_tr_from.get() or "").strip()
            t = (self.var_tr_to.get() or "").strip()
            pair = (self.var_tr_pair.get() or "").strip().upper()
            if (f.lower() == "isolated") or (t.lower() == "isolated"):
                self.lbl_tr_preview.config(text=f"Transfer: {amt} {ccy} | {f} → {t} | {pair}")
            else:
                self.lbl_tr_preview.config(text=f"Transfer: {amt} {ccy} | {f} → {t}")

        self.var_tr_from.trace_add("write", _update_preview)
        self.var_tr_to.trace_add("write", _update_preview)
        self.var_tr_ccy.trace_add("write", _update_preview)
        self.var_tr_amt.trace_add("write", _update_preview)
        self.var_tr_pair.trace_add("write", _update_preview)
        _update_preview()

        # do_transfer: calls the refactored _do_* functions with explicit args
        def do_transfer():
            if self.public_mode.get():
                messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
                return

            from_acc = (self.var_tr_from.get() or "").strip().lower()
            to_acc = (self.var_tr_to.get() or "").strip().lower()
            ccy = (self.var_tr_ccy.get() or "").strip().upper()

            try:
                amt = float(self.var_tr_amt.get())
                if amt <= 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Hiba", "Érvénytelen összeg.")
                return

            if not ccy:
                messagebox.showerror("Hiba", "Hiányzó deviza (pl. USDT).")
                return

            needs_pair = (from_acc == "isolated") or (to_acc == "isolated")
            pair = ""
            if needs_pair:
                pair = (self.var_tr_pair.get() or "").strip()
                if not pair:
                    messagebox.showerror("Hiba", "Isolated átvezetéshez kötelező a pár kiválasztása.")
                    return

            # ROUTING:
            # Main/Trade = spot internal
            if from_acc in ("main", "trade") and to_acc in ("main", "trade"):
                self._do_spot_transfer(from_acc, to_acc, ccy=ccy, amt=amt)
                return

            # Spot <-> Cross routing
            if (from_acc in ("main", "trade")) and (to_acc == "cross"):
                # spot -> cross == "in"
                self._do_cross_transfer("in", ccy=ccy, amt=amt)
                return

            if (from_acc == "cross") and (to_acc in ("main", "trade")):
                # cross -> spot == "out"
                self._do_cross_transfer("out", ccy=ccy, amt=amt)
                return

            # Spot <-> Isolated routing
            if (from_acc in ("main", "trade")) and (to_acc == "isolated"):
                # isolated transfer supports direction "in"
                # spot_account parameter: allow MAIN if from_acc is main
                spot_account = "MAIN" if from_acc == "main" else "TRADE"
                self._do_isolated_transfer("in", spot_account=spot_account, sym=pair, ccy=ccy, amt=amt)
                return

            if (from_acc == "isolated") and (to_acc in ("main", "trade")):
                # isolated -> spot
                self._do_isolated_transfer("out", sym=pair, ccy=ccy, amt=amt)
                return

            messagebox.showerror("Nem támogatott", f"Ez az átvezetési útvonal nincs kezelve: {from_acc} → {to_acc}")

        # Primary action button
        btn_do = ttk.Button(tf, text="Átvezetés", command=do_transfer)
        btn_do.grid(row=6, column=0, columnspan=2, sticky="ew")

        # Presets (fill wizard only)
        preset_box = ttk.Labelframe(tf, text="Gyors beállítások", padding=8)
        preset_box.grid(row=7, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        preset_box.grid_columnconfigure(0, weight=1)
        preset_box.grid_columnconfigure(1, weight=1)

        def _preset(f, t, ccy="USDT", amt="10"):
            self.var_tr_from.set(f)
            self.var_tr_to.set(t)
            self.var_tr_ccy.set(ccy)
            self.var_tr_amt.set(amt)

        ttk.Button(preset_box, text="Main → Trade", command=lambda: _preset("Main", "Trade")).grid(row=0, column=0, sticky="ew", padx=(0, 6), pady=(0, 6))
        ttk.Button(preset_box, text="Trade → Main", command=lambda: _preset("Trade", "Main")).grid(row=0, column=1, sticky="ew", pady=(0, 6))
        ttk.Button(preset_box, text="Spot → Cross", command=lambda: _preset("Trade", "Cross")).grid(row=1, column=0, sticky="ew", padx=(0, 6), pady=(0, 6))
        ttk.Button(preset_box, text="Cross → Spot", command=lambda: _preset("Cross", "Trade")).grid(row=1, column=1, sticky="ew", pady=(0, 6))
        ttk.Button(preset_box, text="Trade → Isolated", command=lambda: _preset("Trade", "Isolated")).grid(row=2, column=0, sticky="ew", padx=(0, 6))
        ttk.Button(preset_box, text="Main → Isolated", command=lambda: _preset("Main", "Isolated")).grid(row=2, column=1, sticky="ew")

        # -----------------------------
        # BOTTOM: Funds log
        # -----------------------------
        logf = ttk.Labelframe(self.tab_funds, text="Log", padding=8)
        logf.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        logf.grid_rowconfigure(0, weight=1)
        logf.grid_columnconfigure(0, weight=1)

        self.funds_log = scrolledtext.ScrolledText(logf, wrap=tk.WORD, height=8)
        self.funds_log.grid(row=0, column=0, sticky="nsew")

    def _init_styles(self):
        self.style = ttk.Style(self.root)
        style = self.style
        style.configure("TLabel", padding=(2, 2))
        style.configure("TEntry", padding=(2, 2))
        style.configure("TButton", padding=(6, 6))
        style.configure("Card.TLabelframe", padding=12)
        # BUY / SELL gombok
        style.configure("Buy.TButton",  foreground="#0a0a0a", background="#1f9d55")
        style.map("Buy.TButton", background=[("active", "#178246")])
        style.configure("Sell.TButton", foreground="#0a0a0a", background="#d64545")
        style.map("Sell.TButton", background=[("active", "#b93b3b")])

    def _pair_group_key(self, rec: dict) -> str:
        """Egységes rendező kulcs – delegál a modul szintű _pair_group_key-re."""
        return _pair_group_key(rec)

    def _get_balance_row(self, ccy: str, acc_type: str, avail: float, holds: float, liability: float, value: float, pnl: float, symbol: str = "") -> tuple:
        """
        Segédmetódus egyenlegsor formázására és összesítésére.
        value (float): Bruttó érték USD-ben (Elérhető + Tartott) * Árfolyam
        pnl (float): Nettó érték USD-ben (Value - Kötelezettség_USD)
        """

        # Ez a teljes Nettó Darabszám (Quantity) a Kötelezettségek levonása után.
        # Ez a táblázat 'Nettó Összesen' oszlopába kerül.
        total_quantity = avail + holds - liability

        # A sorban a Bevétel (value) és a PNL (pnl) a kapott USD értékek,
        # a többi pedig darabszám.
        return (ccy,
                acc_type,
                f"{avail:,.8f}",     # Elérhető darabszám
                f"{holds:,.8f}",      # Tartott darabszám
                f"{value:,.2f}",      # Bevétel (Value/USD) - BRUTTÓ ÉRTÉK
                f"{liability:,.8f}",  # Kötelezettség darabszám
                f"{total_quantity:,.8f}", # Nettó Összesen darabszám
                f"{pnl:,.2f}",        # PNL (Profit/Loss/USD) - NETTÓ ÉRTÉK
                symbol)

    def _update_funds_balance_table(self, balances: list):
        """
        Frissíti az összesített egyenlegek táblázatot.
        - balances lehet dict-lista (ajánlott) vagy tuple-lista (régi formátum).
        - A végére 'Összesen:' sort illeszt (Bevétel, Kötelezettség, Nettó összesen).
        """
        # tag a félkövér összesen sorhoz (idempotens)
        try:
            self.tbl_funds_bal.tag_configure("total", font=("Segoe UI", 12, "bold"))
        except Exception:
            pass

        # Régi sorok törlése
        for iid in self.tbl_funds_bal.get_children():
            self.tbl_funds_bal.delete(iid)

        value_sum = 0.0     # Bevétel (USD) összege
        liability_sum = 0.0 # Kötelezettség összege

        def _to_float(x, default=0.0):
            try:
                if isinstance(x, (int, float)):
                    return float(x)
                # pl. "1,234.56" → 1234.56
                return float(str(x).replace(",", ""))
            except Exception:
                return default

        for row in balances:
            if isinstance(row, dict):
                currency  = row.get("ccy") or row.get("currency") or ""
                acc_type  = row.get("acc_type") or row.get("account_type") or ""
                avail     = _to_float(row.get("avail", row.get("available", 0.0)))
                holds     = _to_float(row.get("holds", 0.0))
                value_usd = _to_float(row.get("value", row.get("value_usd", 0.0)))
                liability = _to_float(row.get("liability", 0.0))
                # nettó darabszám a táblázat 'Nettó Összesen' oszlopába
                total_qty = _to_float(row.get("total", avail + holds - liability))
                pnl_usd   = _to_float(row.get("pnl", value_usd - liability))
                symbol    = row.get("symbol", "")

                display = (
                    currency,
                    acc_type,
                    f"{avail:,.8f}",
                    f"{holds:,.8f}",
                    f"{value_usd:,.2f}",
                    f"{liability:,.8f}",
                    f"{total_qty:,.8f}",
                    f"{pnl_usd:,.2f}",
                    symbol
                )
            else:
                # tuple/list kompatibilitás: (currency, acc_type, avail, holds, value_usd, liability, total, pnl, symbol)
                display = row
                value_usd = _to_float(row[4] if len(row) > 4 else 0.0)
                liability = _to_float(row[5] if len(row) > 5 else 0.0)

            value_sum   += value_usd
            liability_sum += liability

            self.tbl_funds_bal.insert("", "end", values=display)

        # Összesen sor – a kért mezők összegzése
        net_sum = value_sum - liability_sum
        total_row = ("Összesen:", "", "", "", f"{value_sum:,.2f}", f"{liability_sum:,.2f}", "", f"{net_sum:,.2f}", "")
        self.tbl_funds_bal.insert("", "end", values=total_row, tags=("total",))

        # Log
        self.funds_log.insert(tk.END, f"✅ Összesített egyenlegek frissítve ({len(balances)} sor + Összesen)\n")
        self.funds_log.see(tk.END)

    def refresh_all_funds_balances(self):
        """Összes egyenleg frissítése + USD értékek számítása. Eredményt cache-eljük is."""
        if self.public_mode.get():
            messagebox.showwarning(
                "Privát mód szükséges",
                "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.",
            )
            return

        def worker():
            try:
                ex = getattr(self, "exchange", None)
                if ex is None:
                    raise RuntimeError("Nincs aktív exchange kliens.")

                # cache vödör reset – ugyanazzal a lockkal, mint minden más, ami _balance_cache-et használ
                lock = getattr(self, "_ex_lock", None)
                if lock is not None:
                    with lock:
                        self._balance_cache = {"spot": {}, "cross": {}, "isolated": {}}
                        self.usdt_avail = 0.0
                else:
                    self._balance_cache = {"spot": {}, "cross": {}, "isolated": {}}
                    self.usdt_avail = 0.0

                all_rows: list[dict] = []
                unique_ccy: set[str] = set()

                # ---------- 1) SPOT ----------
                with self._ex_lock:
                    r = ex._rest_get("/api/v1/accounts", {})
                spot_accounts = r.get("data", []) if isinstance(r, dict) else []

                # cache: spot[CCY] = {"main": {...}, "trade": {...}, "futures": {...}}
                spot_cache: dict[str, dict] = {}

                for acc in spot_accounts:
                    acc_type = (acc.get("type") or "main").lower()  # main/trade/futures
                    if acc_type not in ("main", "trade", "futures"):
                        continue
                    ccy = (acc.get("currency") or acc.get("currencyName") or "").upper()
                    avail = float(acc.get("available") or 0.0)
                    holds = float(acc.get("holds") or 0.0)
                    if not ccy:
                        continue

                    spot_cache.setdefault(ccy, {}).setdefault(acc_type, {})
                    spot_cache[ccy][acc_type] = {"avail": avail, "holds": holds}

                    if avail > 0 or holds > 0:
                        all_rows.append(
                            {
                                "ccy": ccy,
                                "acc_type": acc_type.capitalize(),
                                "avail": avail,
                                "holds": holds,
                                "liability": 0.0,
                                "symbol": "",
                            }
                        )
                        unique_ccy.add(ccy)

                # ---------- 2) CROSS ----------
                with self._ex_lock:
                    cross_resp = ex.fetch_cross_accounts()  # type: ignore[union-attr]
                cdata = cross_resp.get("data", {}) if isinstance(cross_resp, dict) else {}
                accounts = (
                    cdata.get("accounts", []) or cdata.get("accountList", []) or []
                )

                # cache: cross[CCY] = {"avail":..., "holds":..., "liability":...}
                cross_cache: dict[str, dict] = {}

                for a in accounts:
                    ccy = (a.get("currency") or a.get("currencyName") or "").upper()
                    if not ccy:
                        continue
                    avail = float(
                        a.get("available", a.get("availableBalance", a.get("free", 0))) or 0
                    )
                    holds = float(a.get("holds", a.get("holdBalance", 0)) or 0)
                    liab = float(a.get("liability", a.get("debt", 0)) or 0)

                    # ha csak 'balance' volt
                    if avail == 0 and "balance" in a:
                        bal = float(a.get("balance") or 0.0)
                        hb = float(a.get("holdBalance") or 0.0)
                        if bal > 0 and bal >= hb:
                            avail = bal - hb
                            holds = hb

                    cross_cache[ccy] = {"avail": avail, "holds": holds, "liability": liab}

                    if avail > 0 or holds > 0 or liab > 0:
                        all_rows.append(
                            {
                                "ccy": ccy,
                                "acc_type": "Cross",
                                "avail": avail,
                                "holds": holds,
                                "liability": liab,
                                "symbol": "",
                            }
                        )
                        unique_ccy.add(ccy)

                # ---------- 3) ISOLATED ----------
                with self._ex_lock:
                    iso_resp = ex.fetch_isolated_accounts()  # type: ignore[union-attr]
                idata = (
                    iso_resp.get("data", {})
                    if isinstance(iso_resp, dict)
                    else getattr(iso_resp, "data", {})
                    or {}
                )
                assets = idata.get("assets", []) or []

                # cache: isolated[SYMBOL] = {"base":{ccy,avail,holds,liability}, "quote":{...}}
                iso_cache: dict[str, dict] = {}

                for asset in assets:
                    symbol = (asset.get("symbol") or "").upper()
                    if not symbol:
                        continue
                    base = asset.get("baseAsset") or {}
                    quote = asset.get("quoteAsset") or {}

                    base_ccy = (base.get("currency") or "").upper()
                    quote_ccy = (quote.get("currency") or "").upper()

                    base_pack = {
                        "ccy": base_ccy,
                        "avail": float(base.get("available") or 0),
                        "holds": float(base.get("holds") or 0),
                        "liability": float(base.get("liability") or 0),
                    }
                    quote_pack = {
                        "ccy": quote_ccy,
                        "avail": float(quote.get("available") or 0),
                        "holds": float(quote.get("holds") or 0),
                        "liability": float(quote.get("liability") or 0),
                    }

                    iso_cache[symbol] = {"base": base_pack, "quote": quote_pack}

                    if base_pack["ccy"] and (
                        base_pack["avail"] > 0
                        or base_pack["holds"] > 0
                        or base_pack["liability"] > 0
                    ):
                        all_rows.append(
                            {
                                "ccy": base_ccy,
                                "acc_type": "Isolated",
                                "avail": base_pack["avail"],
                                "holds": base_pack["holds"],
                                "liability": base_pack["liability"],
                                "symbol": symbol,
                            }
                        )
                        unique_ccy.add(base_ccy)

                    if quote_pack["ccy"] and (
                        quote_pack["avail"] > 0
                        or quote_pack["holds"] > 0
                        or quote_pack["liability"] > 0
                    ):
                        all_rows.append(
                            {
                                "ccy": quote_ccy,
                                "acc_type": "Isolated",
                                "avail": quote_pack["avail"],
                                "holds": quote_pack["holds"],
                                "liability": quote_pack["liability"],
                                "symbol": symbol,
                            }
                        )
                        unique_ccy.add(quote_ccy)

                # --- cache-ek visszaírása LOCK alatt, hogy a reader-ek konzisztens snapshotot lássanak ---
                if lock is not None:
                    with lock:
                        self._balance_cache["spot"] = spot_cache
                        self._balance_cache["cross"] = cross_cache
                        self._balance_cache["isolated"] = iso_cache
                else:
                    self._balance_cache["spot"] = spot_cache
                    self._balance_cache["cross"] = cross_cache
                    self._balance_cache["isolated"] = iso_cache

                # ---------- 4) Árfolyamok – get_best_price használatával ----------
                prices: dict[str, float] = {"USDT": 1.0}

                for ccy in unique_ccy:
                    # USDT alapértelmezésben 1
                    if ccy.upper() == "USDT":
                        continue
                    try:
                        sym = f"{ccy}-USDT"
                        px = self.get_best_price(sym)
                        if self._is_pos_num(px) and px > 0:
                            prices[ccy] = float(px)
                    except Exception:
                        # ha bármi gond van az adott devizával, egyszerűen kihagyjuk
                        continue

                # ---------- 5) USD értékek ----------
                def _pair_key(rec: dict) -> str:
                    sym = rec.get("symbol") or ""
                    return sym if sym else f"{rec.get('ccy', '')}-USDT"

                ACCOUNT_SORT_PRIORITY = {
                    "Main": 0,
                    "Trade": 1,
                    "Cross": 2,
                    "Isolated": 3,
                }

                records: list[dict] = []
                for row in all_rows:
                    ccy = row["ccy"]
                    px = float(prices.get(ccy, 0.0))
                    if px <= 0:
                        px = 0.0
                    value_usd = float(row["avail"]) * px
                    liab_usd = float(row["liability"]) * px
                    pnl_usd = value_usd - liab_usd
                    nrow = dict(row)
                    nrow.update({"value": value_usd, "pnl": pnl_usd})
                    records.append(nrow)

                records.sort(
                    key=lambda r: (
                        ACCOUNT_SORT_PRIORITY.get(r.get("acc_type"), 99),
                        _pair_key(r),
                        (r.get("ccy") or ""),
                    )
                )

                final_rows = [
                    self._get_balance_row(
                        ccy=r["ccy"],
                        acc_type=r["acc_type"],
                        avail=r["avail"],
                        holds=r["holds"],
                        liability=r["liability"],
                        value=r["value"],
                        pnl=r["pnl"],
                        symbol=r["symbol"],
                    )
                    for r in records
                ]

                # ÚJ: timestamp
                ts_str = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

                def _update_ts():
                    lbl = getattr(self, "lbl_funds_last_update", None)
                    if lbl:
                         lbl.configure(text=f"Utolsó frissítés: {ts_str}")

                self.root.after(
                    0,
                    lambda: (
                        self._update_funds_balance_table(final_rows),
                        self._mb_refresh_available(),
                        _update_ts()
                    ),
                )

            except RuntimeError as e:
                self.root.after(
                    0, lambda e=e: messagebox.showwarning("Privát hívás hiba", str(e))
                )
            except Exception as e:
                self.root.after(
                    0,
                    lambda e=e: messagebox.showerror(
                        "Hiba", f"Hiba az egyenlegek frissítésekor: {e}"
                    ),
                )

        threading.Thread(target=worker, daemon=True).start()

    # ---- DASHBOARD LOG ----
    def log(self, msg: str):
        def _append(area, text):
            area.insert(tk.END, text + "\n"); area.see(tk.END)
        self.root.after(0, _append, self.log_area, msg)
        print(msg)

    def set_status(self, s: str):
        self.root.after(0, lambda: self.status_lbl.config(text=f"Státusz: {s}"))

    def _risk_label(self, ratio: float) -> str:
        try:
            r = float(ratio or 0.0)
        except Exception:
            return "-"
        if r < 0.6:
            return f"{r*100:,.2f}%  Low Risk 🟢"
        if r < 0.8:
            return f"{r*100:,.2f}%  Medium Risk 🟡"
        return f"{r*100:,.2f}%  High Risk 🔴"

    # ---- symbols ----
    def _load_symbols_async(self):
        try:
            ex = self.exchange or KucoinSDKWrapper(public_mode=True, log_fn=self.log)
            syms = ex.fetch_symbols()
            if syms:
                # normalizálás + egyediség + rendezés (UI barát)
                syms_norm = sorted({normalize_symbol(s) for s in syms if s})
                self.symbols = syms_norm
                self.root.after(0, self._apply_symbols_to_widgets)
        except Exception as e:
            self.log(f"Symbols betöltési hiba: {e}")

    def _apply_symbols_to_widgets(self):
        """
        Alkalmazza a self.symbols listát az összes Comboboxra, ami a __init__-ben jött létre.
        """
        # Hozzáadtuk az mb_symbol-t (Margin Bot) és a cmb_tr_pair-t (Transfer Wizard)
        # f_iso_sym eltávolítva (régi widget)
        widgets = [
            getattr(self, "e_symbol", None),
            getattr(self, "trade_symbol", None),
            getattr(self, "cross_symbol", None),
            getattr(self, "mt_symbol", None),
            getattr(self, "mb_symbol", None),
            getattr(self, "cmb_tr_pair", None),  # Új wizard widget
        ]

        for cb in widgets:
            if cb is None: continue
            try:
                cb.configure(values=self.symbols)
                # ha a jelenlegi érték nem normalizált, próbáljuk megmenteni
                cur = normalize_symbol(cb.get() or "")
                # ha a jelenlegi érték nem szerepel az új listában, beállítjuk az alapértelmezettre
                cb.set(cur if cur in self.symbols else DEFAULT_SYMBOL)
            except Exception:
                # Csendes hiba, ha a combobox még nem létezik (pl. tesztelés alatt)
                pass

    def pretty_isolated_accounts(self, payload: dict) -> str:
        """
        Isolated margin számlák szépen formázva.
        Optimalizálva: csak azokra a párokra kérünk árat,
        ahol van releváns készlet / tartozás / risk.
        """
        data = payload.get("data", payload) or {}
        assets = data.get("assets", []) or []

        lines = ["Isolated Margin – Részletes nézet", ""]

        # --- Előszűrés: csak releváns eszközök ---
        relevant_assets = []
        for a in assets:
            base = a.get("baseAsset", {}) or {}
            quote = a.get("quoteAsset", {}) or {}

            debt_ratio = float(a.get("debtRatio", 0) or 0)

            base_tot = float(base.get("total", 0) or 0)
            base_li  = float(base.get("liability", 0) or 0)

            quote_tot = float(quote.get("total", 0) or 0)
            quote_li  = float(quote.get("liability", 0) or 0)

            # Csak akkor érdekes, ha van valami nem nulla
            if base_tot > 0 or base_li > 0 or quote_tot > 0 or quote_li > 0 or debt_ratio > 0:
                relevant_assets.append(a)

        # Ha semmi releváns nincs, gyorsan visszaadjuk
        if not relevant_assets:
            lines.append("Nincs releváns izolált eszköz/pozíció.")
            return "\n".join(lines)

        # --- Szimbólumok listája árlekéréshez (csak relevánsak!) ---
        symbols = [a.get("symbol", "").upper() for a in relevant_assets if a.get("symbol")]
        prices: Dict[str, float] = {}

        for sym in symbols:
            try:
                px = self.get_best_price(sym)
                prices[sym] = float(px if (self._is_pos_num(px) and px > 0) else 0.0)
            except Exception:
                prices[sym] = 0.0

        # --- Formázott sorok generálása csak releváns eszközökre ---
        for a in relevant_assets:
            sym = a.get("symbol", "N/A").upper()
            status = a.get("status", "")
            debt_ratio = float(a.get("debtRatio", 0) or 0)

            base = a.get("baseAsset", {}) or {}
            quote = a.get("quoteAsset", {}) or {}

            base_ccy = base.get("currency", "")
            base_tot = float(base.get("total", 0) or 0)
            base_av  = float(base.get("available", 0) or 0)
            base_li  = float(base.get("liability", 0) or 0)

            quote_ccy = quote.get("currency", "")
            quote_tot = float(quote.get("total", 0) or 0)
            quote_av  = float(quote.get("available", 0) or 0)
            quote_li  = float(quote.get("liability", 0) or 0)

            last = float(prices.get(sym, 0.0))

            net_quote = base_tot * last + quote_tot - quote_li if last > 0 else None

            lines.append(f"── {sym}  [{status}]")
            lines.append(f"   Risk: {self._risk_label(debt_ratio)}")

            if last > 0:
                lines.append(f"   Last Price: {last:,.6f} {quote_ccy}")

            lines.append(
                f"   {base_ccy}: total {base_tot:,.6f}  |  available {base_av:,.6f}  |  liability {base_li:,.6f}"
            )
            lines.append(
                f"   {quote_ccy}: total {quote_tot:,.6f} |  available {quote_av:,.6f} | liability {quote_li:,.6f}"
            )

            if net_quote is not None:
                lines.append(f"   Net Value (≈): {net_quote:,.2f} {quote_ccy}")

                side_txt = None
                closable = None
                if base_li > 0:
                    side_txt = "SHORT"
                    closable = base_li
                elif base_tot > 0:
                    side_txt = "LONG"
                    closable = base_tot

                if side_txt and closable is not None:
                    lines.append(
                        f"   Position: {side_txt}  |  Closable size (≈): {closable:,.6f} {base_ccy}"
                    )

            lines.append("")

        return "\n".join(lines)

    def _parse_isolated_rows(self, payload: dict) -> list[dict]:
        data = payload.get('data', payload) or {}
        assets = data.get('assets', []) or []
        rows = []
        for a in assets:
            sym = a.get('symbol', '')
            base = a.get('baseAsset', {}) or {}
            quote = a.get('quoteAsset', {}) or {}
            debt_ratio = float(a.get('debtRatio', 0) or 0)

            base_ccy = base.get('currency', '')
            base_tot = float(base.get('total', 0) or 0)
            base_li  = float(base.get('liability', 0) or 0)

            quote_ccy = quote.get('currency', '')
            quote_tot = float(quote.get('total', 0) or 0)
            quote_li  = float(quote.get('liability', 0) or 0)

            if base_li > 0:
                side = "SHORT"; closable = base_li
            elif base_tot > 0:
                side = "LONG"; closable = base_tot
            else:
                side = "-"; closable = 0.0

            base_txt  = f"{base_ccy}: total {base_tot:,.6f} | liability {base_li:,.6f}"
            quote_txt = f"{quote_ccy}: total {quote_tot:,.6f} | liability {quote_li:,.6f}"
            risk_txt  = self._risk_label(debt_ratio)

            if any([base_tot, base_li, quote_tot, quote_li, debt_ratio]):
                rows.append({
                    "symbol": sym, "side": side, "closable": closable,
                    "base": base_txt, "quote": quote_txt, "risk": risk_txt
                })
        rows.sort(key=lambda r: r["symbol"])
        return rows

    def _cross_currency_map(self, payload: dict) -> dict:
        data = payload.get("data", payload) or {}
        accounts = data.get("accounts", []) or data.get("accountList", []) or data.get("debtList", [])
        curmap = {}
        for it in accounts or []:
            cur = (it.get("currency") or it.get("currencyName") or "").upper()
            if not cur:
                continue
            curmap[cur] = {
                "total": float(it.get("total", it.get("balance", 0)) or 0.0),
                "available": float(it.get("available", it.get("availableBalance", 0)) or 0.0),
                "liability": float(it.get("liability", 0) or 0.0),
            }
        return curmap

    def _parse_cross_rows(self, payload: dict, default_quote: str = "USDT") -> list[dict]:
        curmap = self._cross_currency_map(payload)
        rows = []
        dq = (default_quote or "USDT").upper()
        for base, vals in sorted(curmap.items()):
            if base == dq:
                continue
            base_tot = vals["total"]
            base_li  = vals["liability"]
            qvals = curmap.get(dq, {"total": 0.0, "liability": 0.0})
            quote_tot = qvals["total"]; quote_li = qvals["liability"]

            if base_li > 0:
                side = "SHORT"; closable = base_li
            elif base_tot > 0:
                side = "LONG"; closable = base_tot
            else:
                continue

            symbol = f"{base}-{dq}"
            base_txt  = f"{base}: total {base_tot:,.6f} | liability {base_li:,.6f}"
            quote_txt = f"{dq}: total {quote_tot:,.6f} | liability {quote_li:,.6f}"

            data = payload.get("data", payload) or {}
            risk = data.get("riskRatio") or data.get("debtRatio") or "-"
            if isinstance(risk, (int, float)):
                risk = f"{float(risk)*100:,.2f}%"

            rows.append({
                "symbol": symbol, "side": side, "closable": closable,
                "base": base_txt, "quote": quote_txt, "risk": risk
            })
        return rows

    def pretty_cross_accounts(self, payload: dict, default_quote: str = "USDT") -> str:
        """
        Cross margin számlák szépen formázva.
        Optimalizálva:
          - csak a _parse_cross_rows által már előszűrt (releváns) sorokra kér árfolyamot,
          - ugyanarra a szimbólumra csak egyszer kér árat,
          - robusztus split, ha a szimbólumban nincs '-' (fallback).
        """
        rows = self._parse_cross_rows(payload, default_quote)
        if not rows:
            return "Cross Margin – nincs releváns kitettség."

        # Egyedi szimbólumok a releváns sorokból
        symbols = sorted({r["symbol"] for r in rows})
        prices: dict[str, float] = {}

        # Egységes árlekérés minden releváns szimbólumra: get_best_price (WS → cache → REST)
        for sym in symbols:
            try:
                px = self.get_best_price(sym)
                prices[sym] = float(px if (self._is_pos_num(px) and px > 0) else 0.0)
            except Exception:
                prices[sym] = 0.0

        lines = [f"Cross Margin – Részletes nézet (QUOTE: {default_quote.upper()})", ""]
        for r in rows:
            sym = r["symbol"]
            side = r["side"]
            closable = float(r["closable"])

            # Biztonságos szimbólum-bontás
            parts = str(sym).split("-", 1)
            if len(parts) == 2:
                base_ccy, quote_ccy = parts[0], parts[1]
            else:
                base_ccy, quote_ccy = parts[0], default_quote.upper()

            last = float(prices.get(sym, 0.0) or 0.0)
            est_val = f"{closable * last:,.2f} {quote_ccy}" if last > 0 else "n/a"

            lines.append(f"── {sym}  [{side}]")
            if last > 0:
                lines.append(
                    f"   Last Price: {last:,.6f} {quote_ccy}  |  "
                    f"Closable≈ {closable:,.6f} {base_ccy}  (~{est_val})"
                )
            else:
                lines.append(f"   Closable≈ {closable:,.6f} {base_ccy}")
            lines.append(f"   {r['base']}")
            lines.append(f"   {r['quote']}")
            lines.append(f"   Risk: {r['risk']}")
            lines.append("")

        return "\n".join(lines)

    def _fill_isolated_table(self, rows: list[dict]):
        tv = self.tbl_iso
        for iid in tv.get_children():
            tv.delete(iid)
        tv.configure(displaycolumns=tv["columns"])  # biztosítsd a gyors render utat
        inserts = []
        for r in rows:
            inserts.append(("", tk.END, None, (r["symbol"], r["side"], f"{r['closable']:,.6f}", r["base"], r["quote"], r["risk"])))
        for parent, index, iid, values in inserts:
            tv.insert(parent, index, iid=iid, values=values)

    # ---- WS ----
    def _ensure_ticker_ws(self, symbol: str):
        """
        Gondoskodik arról, hogy fusson egy KucoinTickerWS az adott symbol-ra.
        Egyetlen globális WS kapcsolat, az aktív symbol alapján.
        """
        try:
            sym = normalize_symbol(symbol)
        except Exception:
            return

        # Ha ugyanaz a symbol és már fut, nincs teendő
        if getattr(self, "_ticker_ws", None) is not None and self._ticker_ws_symbol == sym:
            return

        if self._ticker_ws is None:
            try:
                self._ticker_ws = KucoinTickerWS(sym, log_fn=self._safe_log)
                self._ticker_ws.start()
                self._ticker_ws_symbol = sym
                self._safe_log(f"🚀 Ticker WS elindítva: {sym}\n")
            except Exception as e:
                self._safe_log(f"❌ Ticker WS start hiba: {e}\n")
        else:
            try:
                self._ticker_ws.set_symbol(sym)
                self._ticker_ws_symbol = sym
                self._safe_log(f"🔄 Ticker WS symbol váltás: {sym}\n")
            except Exception as e:
                self._safe_log(f"❌ Ticker WS symbol váltás hiba: {e}\n")

    def _ensure_order_ws(self):
        """
        Privát order WebSocket lusta init.

        Csak KuCoin Spot/Margin esetén van értelme, de a bot amúgy is
        erre van kihegyezve, ezért külön ex-típus ellenőrzés nem nagyon kell.
        """
        # Ha már van és fut, nem csinálunk semmit
        ws = getattr(self, "_order_ws", None)
        if ws is not None:
            try:
                if ws.is_running():
                    return
            except Exception:
                # ha valamiért nincs ilyen metódus, újrainitializáljuk
                pass

        # Exchange ellenőrzés
        ex = getattr(self, "exchange", None)
        if ex is None:
            self._safe_log("⚠️ Nincs exchange inicializálva – privát WS nem hozható létre.\n")
            self._order_ws = None
            return

        # Biztonságos REST-wrapper: fix szignó (path, body=None)
        def _rest_post_wrapper(path: str, body: dict | None = None):
            try:
                return ex._rest_post(path, body or {})
            except TypeError:
                # Ha valami nagyon régi signóval futna, próbáljuk meg body nélkül is
                return ex._rest_post(path)

        try:
            self._order_ws = KucoinPrivateOrderWS(
                rest_post_func=_rest_post_wrapper,
                log_func=self._safe_log,
            )
            self._order_ws.start()
            self._safe_log("🔌 Privát order WS elindítva.\n")
        except Exception as e:
            self._safe_log(f"⚠️ Privát order WS init hiba: {e}\n")
            self._order_ws = None

    # --- MarginBot: K-Line WS integráció / közös OHLCV getter -----------------
    def _ensure_kline_ws(self, symbol: str, tfs: list[str]):
        """
        Gondoskodik róla, hogy legyen futó K-Line WS a megadott symbol + TF-ekre.
        Ha a symbol vagy a TF lista változik, újraindítja a WS-t.
        """

        # Normalizáljuk a kért paramétereket
        req_sym = normalize_symbol(symbol)
        req_tfs = sorted(list(set(str(tf) for tf in tfs if tf)))

        if not req_tfs:
            return

        ws = getattr(self, "_mb_kline_ws", None)
        restart_needed = False

        if ws is None or not ws.is_running():
            restart_needed = True
        else:
            cur_sym = getattr(ws, "symbol", "")
            cur_tfs = getattr(ws, "tfs", [])

            if cur_sym != req_sym:
                self._safe_log(f"🔄 K-Line WS váltás: {cur_sym} -> {req_sym}\n")
                restart_needed = True
            elif sorted(cur_tfs) != req_tfs:
                self._safe_log(f"🔄 K-Line WS TF váltás: {cur_tfs} -> {req_tfs}\n")
                restart_needed = True

        if restart_needed:
            if ws is not None:
                try:
                    ws.stop()
                except Exception:
                    pass
                self._mb_kline_ws = None

            try:
                self._safe_log(f"🌐 K-Line WS indítása: {req_sym} {req_tfs}\n")
                self._mb_kline_ws = KucoinKlineWS(
                    symbol=req_sym,
                    tfs=req_tfs,
                    log_fn=self._safe_log,
                    depth=300,
                )
                self._mb_kline_ws.start()
            except Exception as e:
                self._safe_log(f"❌ K-Line WS indítási hiba: {e}\n")
                self._mb_kline_ws = None

    def _ohlcv_merge_into_cache(self, symbol: str, tf: str, new_rows: list[list[float]]):
        symbol = normalize_symbol(symbol)
        key = (symbol, tf)

        if not new_rows:
            return

        # normalizált, ts szerint rendezett bemenet
        new_rows = sorted(new_rows, key=lambda r: int(r[0]))

        with self._ohlcv_lock:
            rec = self._ohlcv_cache.get(key)
            if rec is None:
                rec = {"rows": [], "last_ts": 0}
                self._ohlcv_cache[key] = rec

            rows: list[list[float]] = list(rec["rows"])  # type: ignore[assignment]

            # gyors index ts->pos a meglévőre
            idx = {int(r[0]): i for i, r in enumerate(rows)}

            for r in new_rows:
                ts = int(r[0])
                if ts in idx:
                    rows[idx[ts]] = r  # csere (ugyanaz a candle új értékkel)
                else:
                    rows.append(r)      # új candle

            rows.sort(key=lambda r: int(r[0]))

            # maxlen trim (csak a legrégebbit dobjuk)
            maxlen = int(getattr(self, "_ohlcv_cache_maxlen", 600))
            if maxlen > 0 and len(rows) > maxlen:
                rows = rows[-maxlen:]

            rec["rows"] = rows
            rec["last_ts"] = int(rows[-1][0]) if rows else 0

    def _ohlcv_seed_if_needed(self, symbol: str, tf: str, seed_n: int = 200):
        symbol = normalize_symbol(symbol)
        key = (symbol, tf)

        with self._ohlcv_lock:
            rec = self._ohlcv_cache.get(key)
            if rec and isinstance(rec.get("rows"), list) and len(rec["rows"]) >= seed_n:
                return  # már van elég adat

        # REST seed (csak egyszer)
        try:
            with self._ex_lock:
                rows = self.exchange.fetch_ohlcv(symbol, tf, limit=seed_n)
        except Exception:
            rows = []

        self._ohlcv_merge_into_cache(symbol, tf, rows)

    def _ohlcv_update_from_ws(self, symbol: str, tf: str):
        ws = getattr(self, "_mb_kline_ws", None)
        if ws is None or not ws.is_running():
            return
        try:
            # elég pár utolsó candle a merge-hez
            ws_rows = ws.get_ohlcv(tf, limit=5)
        except Exception:
            ws_rows = []
        self._ohlcv_merge_into_cache(symbol, tf, ws_rows)

    def _get_ohlcv_cached(self, symbol: str, tf: str, limit: int = 200) -> list[list[float]]:
        symbol = normalize_symbol(symbol)

        # 1) seed
        self._ohlcv_seed_if_needed(symbol, tf, seed_n=200)

        # 2) ws merge
        self._ohlcv_update_from_ws(symbol, tf)

        # 3) kiadás cache-ből
        key = (symbol, tf)
        with self._ohlcv_lock:
            rec = self._ohlcv_cache.get(key) or {}
            rows = list(rec.get("rows") or [])

        if limit and limit > 0:
            return rows[-limit:]
        return rows

    def _mb_get_ohlcv(self, symbol: str, tf: str, limit: int = 200):
        return self._get_ohlcv_cached(symbol, tf, limit=limit)

    def _mt_start_price_loop(self):
        if self._mt_price_job:
            self.root.after_cancel(self._mt_price_job)

        # egyszerre csak egy árlekérés fusson
        self._mt_price_inflight = False

        def _tick():
            try:
                # csak aktív fülön frissítünk
                try:
                    if self.nb.tab(self.nb.select(), "text") != "Margin Trade":
                        return
                except Exception:
                    return

                # ha még fut egy előző worker, nem indítunk újat
                if self._mt_price_inflight:
                    return

                sym = normalize_symbol(self.mt_symbol.get())

                # WS előkészítése – ez gyors, maradhat a főszálon
                try:
                    self._ensure_ticker_ws(sym)
                except Exception:
                    pass

                self._mt_price_inflight = True

                # --- háttér thread az árhoz (WS → cache → REST) ---
                def worker(symbol: str):
                    px = 0.0
                    try:
                        try:
                            p = self.get_best_price(symbol)
                            if self._is_pos_num(p) and p > 0:
                                px = float(p)
                        except Exception:
                            px = 0.0
                    finally:
                        # UI frissítés a fő szálon
                        def ui_update():
                            # engedjük el a flaget
                            self._mt_price_inflight = False

                            # közben lehet, hogy elnavigáltál a fülről
                            try:
                                if self.nb.tab(self.nb.select(), "text") != "Margin Trade":
                                    return
                            except Exception:
                                return

                            if px > 0:
                                self.mt_price_lbl.config(text=f"Ár: {px:.6f}")
                            else:
                                self.mt_price_lbl.config(text="Ár: –")

                            # becslés frissítése
                            self._mt_update_estimate(px)

                        try:
                            self.root.after(0, ui_update)
                        except Exception:
                            # ha már meghalt a root, legalább a flaget engedjük el
                            self._mt_price_inflight = False

                threading.Thread(target=worker, args=(sym,), daemon=True).start()

            finally:
                # 1s-enként újrapróbálkozunk – de a hálózati munka már háttérben megy
                self._mt_price_job = self.root.after(1000, _tick)

        _tick()

    def _mt_update_estimate(self, last_price: float):
        sym = normalize_symbol(self.mt_symbol.get())
        quote = sym.split('-')[1] if '-' in sym else 'QUOTE'
        try:
            if self.mt_input_mode.get() == 'base':
                sz = float(self.mt_size.get() or 0)
                est = sz * last_price if last_price > 0 else 0
                txt = f"~ {est:,.2f} {quote}" if est > 0 else "–"
            else:
                funds = float(self.mt_funds.get() or 0)
                txt = f"{funds:,.2f} {quote}" if funds > 0 else "–"
            self.mt_est_lbl.config(text=f"Becsült költség/hozam: {txt}")
        except Exception:
            self.mt_est_lbl.config(text="Becsült költség/hozam: –")

    def _mt_on_mode_change(self):
        self.mt_pct.set(0)
        self.mt_size.delete(0, tk.END); self.mt_funds.delete(0, tk.END)
        # enforce leverage bounds
        max_lev = 5 if self.mt_mode.get() == 'cross' else 10
        self.mt_lev.config(from_=1, to=max_lev)
        cur = int(self.mt_lev.get() or "1")
        if cur > max_lev:
            self.mt_lev.delete(0, tk.END); self.mt_lev.insert(0, str(max_lev))
        self._mt_on_input_change()

    def _mt_on_input_change(self):
        if self.mt_input_mode.get() == 'base':
            self.mt_size.config(state=tk.NORMAL)
            self.mt_funds.config(state=tk.DISABLED)
        else:
            self.mt_size.config(state=tk.DISABLED)
            self.mt_funds.config(state=tk.NORMAL)

    def _mt_on_slider_release(self, event):
        """A slider elengedésekor hívódik (kattintás vagy húzás után)."""
        # A %-os érték frissítése a háttérben
        self._mt_update_for_percent()

    def _mt_update_for_percent(self):
        """Elindítja a háttérszálat a slider százalékos értéke alapján."""
        try:
            pct = max(0, min(100, int(self.mt_pct.get())))
            # Indítás külön szálon, hogy a GUI ne fagyjon le
            threading.Thread(target=self._mt_fetch_balances_and_update,
                             args=('percent', pct), daemon=True).start()
        except Exception:
            pass # A worker úgyis kezeli a hibát

    def _mt_fetch_balances_and_update(self, action_type: str, value: Any):
        """
        KÜLÖN SZÁLON FUT: Lekérdezi az árat és egyenleget, majd a fő szálon frissíti a GUI-t.
        action_type: 'percent' (value = 0-100) vagy 'max' (value = 'buy'|'sell')
        """
        try:
            # kurzor állítás a fő szálon
            self.root.after(0, lambda: self.root.config(cursor="watch"))

            # 1. Adatgyűjtés (ez a lassú rész)
            sym = normalize_symbol(self.mt_symbol.get())
            base, quote = split_symbol(sym)

            # --- Egységes élő ár: get_best_price (WS → cache → REST) ---
            try:
                px = self.get_best_price(sym)
                if not self._is_pos_num(px) or px <= 0:
                    px = 0.0
            except Exception:
                px = 0.0

            # Ez a leglassabb hívás – egyenleg lekérés
            avail_base, avail_quote = self._mt_available(base, quote)

            # 2. Értékek számítása
            new_size, new_funds = None, None
            input_mode = self.mt_input_mode.get()

            if action_type == 'percent':
                pct = int(value)
                if input_mode == 'base':
                    new_size = f"{(avail_base * pct / 100.0):.6f}"
                else:  # 'quote'
                    new_funds = f"{(avail_quote * pct / 100.0):.2f}"

            elif action_type == 'max':
                side = str(value)
                if side == 'sell':
                    input_mode = 'base'  # Eladásnál mindig a BASE-t akarjuk kitölteni
                    new_size = f"{avail_base:.6f}"
                else:  # 'buy'
                    input_mode = 'quote'  # Vételnél mindig a QUOTE-t
                    new_funds = f"{avail_quote:.2f}"

            # 3. GUI frissítése a fő szálon (self.root.after)
            def update_ui():
                try:
                    # 'Max' gomb esetén átváltjuk a beviteli módot
                    if action_type == 'max':
                        self.mt_input_mode.set(input_mode)
                        self._mt_on_input_change()  # Ez engedélyezi/letiltja a mezőket
                        self.mt_pct.set(100)
                    # Mindig engedélyezzük a mezőket írásra, kitöltjük, majd visszaállítjuk
                    self.mt_size.config(state=tk.NORMAL)
                    self.mt_funds.config(state=tk.NORMAL)
                    self.mt_size.delete(0, tk.END)
                    self.mt_funds.delete(0, tk.END)

                    if new_size is not None:
                        self.mt_size.insert(0, new_size)
                    if new_funds is not None:
                        self.mt_funds.insert(0, new_funds)

                    # Visszaállítjuk a mezők állapotát az input mód alapján
                    self._mt_on_input_change()

                    # Becslés frissítése (itt már a get_best_price-ből jövő px megy be)
                    self._mt_update_estimate(px)
                except Exception as e:
                    self.margin_log.insert(tk.END, f"❌ GUI frissítési hiba: {e}\n")
                    self.margin_log.see(tk.END)
                finally:
                    self.root.config(cursor="")  # Kurzor visszaállítása itt

            self.root.after(0, update_ui)

        except Exception as e:
            self.root.after(0, lambda e=e: [
                messagebox.showerror("Hiba", f"Nem sikerült az adatok lekérdezése: {e}"),
                self.root.config(cursor="")
            ])

    def _mt_fill_max(self, side: str):
        """A 'Max' gombok ezt hívják. Elindítja a központi worker szálat."""
        # Indítás külön szálon
        threading.Thread(target=self._mt_fetch_balances_and_update,
                         args=('max', side), daemon=True).start()

    def _mt_on_slider_press(self, event):
        """
        Kattintáskor (lenyomáskor) a csúszkát a kattintás helyére ugorja.
        Felülbírálja a "léptető" alapértelmezett viselkedést.
        """
        try:
            widget = event.widget
            width = widget.winfo_width()
            if width <= 0:
                return # Widget még nem látható

            # Vízszintes pozíció kiszámítása (0.0 -> 1.0)
            # Biztosítjuk, hogy a határokon belül maradjon
            clicked_percent = max(0.0, min(1.0, event.x / width))

            from_ = float(widget.cget("from"))
            to_ = float(widget.cget("to"))

            value = from_ + (to_ - from_) * clicked_percent

            # Azonnal beállítjuk a csúszka értékét
            # A 'round' biztosítja, hogy egész számot kapjunk (0-100)
            self.mt_pct.set(int(round(value)))

            # NEM hívunk hálózati frissítést itt,
            # azt majd a ButtonRelease-1 (felengedés) esemény kezeli!
        except Exception:
            pass # Csendes hiba, ha valamiért nem sikerül (pl. widget nem létezik)

    def _mt_available(self, base_ccy: str, quote_ccy: str) -> tuple[float, float]:
        """
        Elérhető BASE/QUOTE a kiválasztott margin mód szerint.
        Cache-first; NEM esik vissza SPOT-ra.
        """
        ab = aq = 0.0
        if not self.exchange or self.public_mode.get():
            return ab, aq

        mode = (self.mt_mode.get() or "isolated").lower()
        try:
            # _balance_cache snapshot olvasása _ex_lock alatt (konzisztencia miatt)
            lock = getattr(self, "_ex_lock", None)
            if lock is not None:
                with lock:
                    bc = dict(getattr(self, "_balance_cache", {}) or {})
            else:
                bc = dict(getattr(self, "_balance_cache", {}) or {})

            if mode == "isolated":
                sym = normalize_symbol(f"{base_ccy}-{quote_ccy}")
                iso = (bc.get("isolated") or {})
                pack = iso.get(sym)
                if pack:
                    if (pack.get("base") or {}).get("ccy") == base_ccy.upper():
                        ab = float((pack["base"].get("avail") or 0.0))
                    if (pack.get("quote") or {}).get("ccy") == quote_ccy.upper():
                        aq = float((pack["quote"].get("avail") or 0.0))
                else:
                    # nincs cache – ne használj spotot; opcionális lassú fallback:
                    try:
                        with self._ex_lock:
                            resp = self.exchange.fetch_isolated_accounts()  # type: ignore[union-attr]
                        data = resp.get("data", {}) if isinstance(resp, dict) else getattr(resp, "data", {}) or {}
                        for a in data.get("assets", []) or []:
                            if (a.get("symbol") or "").upper() == sym:
                                b = a.get("baseAsset", {}) or {}
                                q = a.get("quoteAsset", {}) or {}
                                ab = float(b.get("available") or 0.0)
                                aq = float(q.get("available") or 0.0)
                                break
                    except Exception:
                        pass

            else:  # cross
                cross = (bc.get("cross") or {})
                ab = float((cross.get(base_ccy.upper(), {}) or {}).get("avail", 0.0))
                aq = float((cross.get(quote_ccy.upper(), {}) or {}).get("avail", 0.0))

        except Exception:
            pass
        return ab, aq

    def _mt_place(self, side: str):
        """Margin/spot gyors rendelés a manuális panelről – thread-safe, sanitizer-rel."""
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        # UI lock
        self.root.config(cursor="watch")
        try:
            btn_buy  = getattr(self, "btn_mt_buy",  None)
            btn_sell = getattr(self, "btn_mt_sell", None)
            if btn_buy:  btn_buy.config(state=tk.DISABLED)
            if btn_sell: btn_sell.config(state=tk.DISABLED)
        except Exception:
            pass

        # Paraméterek kiolvasása itt (főszálon), majd átadás a workernek
        try:
            sym   = normalize_symbol(self.mt_symbol.get())
            typ   = (self.mt_type.get() or "market").strip().lower()   # 'market' / 'limit'
            price_s = (self.mt_price.get() or "").strip()
            size_s  = (self.mt_size.get()  or "").strip()
            funds_s = (self.mt_funds.get() or "").strip()

            size  = float(size_s)  if size_s  else None
            funds = float(funds_s) if funds_s else None
            px_ui = float(price_s) if price_s else None

            lev = int(self.mt_lev.get()) if self.mt_lev.get() else 1
            lev = min(max(1, lev), 5 if self.mt_mode.get() == 'cross' else 10)
            auto = bool(self.mt_autobr.get())
            mode = self.mt_mode.get()
        except Exception as e:
            self.margin_log.insert(tk.END, f"⚠ Paraméter hiba: {e}\n"); self.margin_log.see(tk.END)
            self.root.config(cursor="")
            try:
                if btn_buy:  btn_buy.config(state=tk.NORMAL)
                if btn_sell: btn_sell.config(state=tk.NORMAL)
            except Exception:
                pass
            return

        def worker(p_sym, p_side, p_typ, p_px_ui, p_size, p_funds, p_lev, p_auto, p_mode):
            try:
                # Ár előkészítése:
                # - Limitnél KÖTELEZŐ, a usertől jön (p_px_ui)
                # - Marketnél, ha nincs megadva ár, akkor get_best_price (WS → cache → REST)
                px = p_px_ui
                if p_typ == "market" and (px is None or px <= 0):
                    try:
                        px_best = self.get_best_price(p_sym)
                        if self._is_pos_num(px_best) and px_best > 0:
                            px = px_best
                        else:
                            px = None
                    except Exception:
                        px = None

                # Alap validáció
                if p_typ == "limit" and (px is None or px <= 0):
                    raise ValueError("Limit megbízáshoz érvényes ár szükséges.")
                if not (p_size or p_funds):
                    raise ValueError("Adj meg Size (BASE) vagy Funds (QUOTE) értéket.")

                size_to_send = None
                funds_to_send = None

                if p_typ == "market":
                    if p_side == "buy":
                        # BUY market: funds az elsődleges; ha csak size van, a sanitizer konvertál funds-ra (ár kell hozzá)
                        sb, fq = self._mb_sanitize_order(
                            symbol=p_sym, side="buy", price=px,
                            size_base=p_size, funds_quote=p_funds
                        )
                        # Market BUY-nál a küldendő érték: funds
                        if fq is None:
                            raise ValueError("A megbízás a minimum/step feltételek miatt nem küldhető (BUY/funds).")
                        funds_to_send = fq
                    else:
                        # SELL market: size az elsődleges
                        sb, fq = self._mb_sanitize_order(
                            symbol=p_sym, side="sell", price=px,
                            size_base=p_size, funds_quote=p_funds
                        )
                        if sb is None:
                            raise ValueError("A megbízás a minimum/step feltételek miatt nem küldhető (SELL/size).")
                        size_to_send = sb

                    # Küldés – thread-safe
                    with self._ex_lock:
                        resp = self.exchange.place_margin_market_order(  # type: ignore[union-attr]
                            p_mode, p_sym, p_side,
                            size_base=size_to_send,
                            funds_quote=funds_to_send,
                            leverage=p_lev,
                            auto_borrow=p_auto,
                            auto_repay=True
                        )

                else:
                    # LIMIT rendelés
                    if p_side == "buy":
                        # ha funds jön, számoljunk belőle size-t (lépésközre padlózva), majd szaniter
                        if p_size is None and (p_funds and p_funds > 0) and (px and px > 0):
                            lot_step, _ps, _mb, _mf, _qs = self._mb_get_market_steps(p_sym)
                            est_size = float(p_funds) / float(px)
                            p_size = self._mb_floor_to_step_dec(est_size, float(lot_step or 0.0))
                        sb, _ = self._mb_sanitize_order(
                            symbol=p_sym, side="sell",  # size padlózáshoz a SELL ág size_guardja praktikus
                            price=px, size_base=p_size, funds_quote=None
                        )
                        if sb is None or sb <= 0:
                            raise ValueError("Limit BUY: a számolt/kért méret a minimum alatt van.")
                        with self._ex_lock:
                            resp = self.exchange.place_margin_limit_order(  # type: ignore[attr-defined]
                                p_mode, p_sym, p_side, price=str(px),
                                size_base=str(sb), leverage=p_lev,
                                auto_borrow=p_auto, auto_repay=True
                            )
                    else:
                        # Limit SELL – méretet szanitereljük
                        sb, _ = self._mb_sanitize_order(
                            symbol=p_sym, side="sell",
                            price=px, size_base=p_size, funds_quote=None
                        )
                        if sb is None or sb <= 0:
                            raise ValueError("Limit SELL: a kért méret a minimum alatt van.")
                        with self._ex_lock:
                            resp = self.exchange.place_margin_limit_order(  # type: ignore[attr-defined]
                                p_mode, p_sym, p_side, price=str(px),
                                size_base=str(sb), leverage=p_lev,
                                auto_borrow=p_auto, auto_repay=True
                            )

                # UI visszajelzés
                def ok_ui():
                    oid = None
                    try:
                        oid = (getattr(resp, 'orderId', None)
                               or (resp.get('data') or {}).get('orderId')
                               or (resp.get('orderId') if isinstance(resp, dict) else None))
                    except Exception:
                        pass
                    self.margin_log.insert(
                        tk.END,
                        f"✅ {p_mode} {p_typ} {p_side} – {p_sym} | size={size_to_send} funds={funds_to_send} lev={p_lev} auto={p_auto} | orderId={oid}\n"
                    )
                    self.margin_log.see(tk.END)
                    messagebox.showinfo("Margin order",
                                        f"Sikeres {p_side.upper()} ({p_mode}/{p_typ})\nPár: {p_sym}\nOrderId: {oid}")
                self.root.after(0, ok_ui)

            except Exception as e:
                self.root.after(0, lambda e=e: [
                    self.margin_log.insert(tk.END, f"❌ Margin order hiba: {e}\n"),
                    self.margin_log.see(tk.END),
                    messagebox.showerror("Margin order hiba", str(e))
                ])
            finally:
                # UI unlock
                def unlock():
                    try:
                        if btn_buy:  btn_buy.config(state=tk.NORMAL)
                        if btn_sell: btn_sell.config(state=tk.NORMAL)
                    except Exception:
                        pass
                    self.root.config(cursor="")
                self.root.after(0, unlock)

        threading.Thread(
            target=worker,
            args=(sym, side, typ, px_ui, size, funds, lev, auto, mode),
            daemon=True
        ).start()

    # ---- Lifecycle ----
    def start_bot(self):

        if self.is_running:
            return
        try:
            with self._ex_lock:
                self.exchange = KucoinSDKWrapper(public_mode=self.public_mode.get(), log_fn=self.log)
            if self.public_mode.get():
                self.log("ℹ️ Publikus mód: csak piaci adatok")
            else:
                self.log("🔐 Privát mód: spot/margin elérhető")

                # Extra capability dump
                try:
                    moa = None
                    rs = None
                    ms = None
                    if hasattr(self.exchange, "_client") and getattr(self.exchange, "_client") is not None:
                        with self._ex_lock:
                            rs = self.exchange._client.rest_service()
                    if rs:
                        ms = rs.get_margin_service()
                    ms_methods = ", ".join([m for m in dir(ms) if m and m.startswith("get_")]) if ms else "N/A"
                    self.log(f"MarginService methods: {ms_methods}")
                    if ms and hasattr(ms, "get_order_api"):
                        moa = ms.get_order_api()
                    if moa:
                        mo_methods = ", ".join([m for m in dir(moa) if m and not m.startswith("_")])
                        self.log(f"Margin order API dump: {moa.__class__.__name__} -> {mo_methods[:2000]}")
                    self.log(f"Margin order API: {moa.__class__.__name__ if moa else 'N/A'}")
                except Exception as _e:
                    self.log(f"Margin capability dump error: {_e}")
        except Exception as e:
            messagebox.showerror("Inicializálási hiba", str(e))
            return

        self.is_running = True
        self.set_status("Fut")
        try:
            # 1. Egyenleg frissítése (ez magában elindítja a háttérszálat)
            self._mb_refresh_available()

            # 2. Chart frissítése (piaci adat lekérdezése)
            self._mb_draw_chart()
        except Exception as e:
            # Csak logoljuk, ha valamiért itt elhasal, de ne akadályozza a bot indulását
            self.log(f"❌ Automatikus Margin Bot frissítési hiba a start után: {e}")
        threading.Thread(target=self.loop, daemon=True).start()

    def stop_bot(self):
        self.is_running = False
        self.set_status("Leállítva")
        self.log("🛑 Bot leállítva a felhasználó által.")

    # ---- fő ciklus ----
    def loop(self):
        while self.is_running:
            #self.tick_once()
            for _ in range(SLEEP_SECONDS):
                if not self.is_running:
                    break
                time.sleep(1)
        self.log("A bot ciklusa befejeződött.")

    def tick_once(self):
        if getattr(self, "_tick_busy", False):
            self.log("⏳ Frissítés már folyamatban…\n")
            return

        self._tick_busy = True
        self.log("🔄 Frissítés indul…\n")

        try:
            symbol = normalize_symbol(self.e_symbol.get())
            tf     = self.cb_tf.get().strip()
            short  = int(self.e_short.get())
            long   = int(self.e_long.get())
        except Exception as e:
            self.log(f"⚠ Paraméter hiba: {e}\n")
            self._tick_busy = False
            return

        def _work(p_symbol, p_tf, p_short, p_long):
            try:
                df = None
                use_cache_df = False

                # --- 1) Ha a MarginBot fut ugyanazon a páron/TF-en, használjuk a cache-elt df-et ---
                try:
                    if getattr(self, "_mb_running", False):
                        mb_cfg = getattr(self, "_mb_cfg", {}) or {}
                        mb_sym = normalize_symbol(mb_cfg.get("symbol", DEFAULT_SYMBOL))
                        mb_tf  = mb_cfg.get("tf", "1m")
                        if (
                            mb_sym == p_symbol
                            and mb_tf == p_tf
                            and hasattr(self, "_mb_last_df")
                        ):
                            base_df = getattr(self, "_mb_last_df", None)
                            if base_df is not None:
                                df = base_df.copy()
                                use_cache_df = True
                except Exception:
                    pass

                # --- 2) Ha nincs használható cache, akkor K-Line WS + REST fallback ---
                if not use_cache_df:
                    try:
                        ohlcv = self._mb_get_ohlcv(p_symbol, p_tf, limit=200)
                    except Exception as _e:
                        ohlcv = []
                        self.log(f"❌ tick_once OHLCV hiba: {_e}\n")

                    if not ohlcv:
                        def _no_data():
                            self.log("⚠ Nincs adat a szervertől.\n")
                            self._tick_busy = False
                        self.root.after(0, _no_data)
                        return

                    df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])

                # --- 3) Győződjünk meg róla, hogy float a close, majd számoljuk az MA-kat ---
                try:
                    df['c'] = df['c'].astype(float)
                except Exception:
                    pass

                df['short'] = df['c'].rolling(p_short, min_periods=1).mean()
                df['long']  = df['c'].rolling(p_long,  min_periods=1).mean()

                # --- 4) UI frissítés főszálon ---
                def _update_ui():
                    try:
                        last = df.iloc[-1]
                        self.log(
                            f"[{p_symbol} {p_tf}] close={last['c']:.6f}, "
                            f"short={last['short']:.6f}, long={last['long']:.6f}\n"
                        )
                        self.draw_chart(df, p_symbol, p_tf)
                    finally:
                        self._tick_busy = False

                self.root.after(0, _update_ui)

            except Exception as e:
                def _err():
                    self.log(f"❌ tick_once hiba: {e}\n")
                    self._tick_busy = False
                self.root.after(0, _err)

        threading.Thread(
            target=_work,
            args=(symbol, tf, short, long),
            daemon=True
        ).start()

    # ---- diagram ----
    def draw_chart(self, df: pd.DataFrame, symbol: str, tf: str):
        # UTC → helyi idő konverzió
        local_tz = datetime.datetime.now().astimezone().tzinfo
        dates = (
            pd.to_datetime(df["ts"], unit="ms", utc=True)  # KuCoin ts ms-ben, UTC
              .dt.tz_convert(local_tz)                     # helyi időzónára váltás
              .dt.tz_localize(None)                        # tz-info eldobása matplotlib miatt
        )

        self.ax.clear()
        self.ax.plot(dates, df['c'], label='close')
        self.ax.plot(dates, df['short'], label=f"MA{int(self.e_short.get())}")
        self.ax.plot(dates, df['long'], label=f"MA{int(self.e_long.get())}")
        self.ax.set_title(f"{symbol} – {tf}")
        self.ax.legend(loc='upper left')
        self.ax.xaxis.set_major_formatter(mdates.DateFormatter('%m-%d %H:%M'))
        self.fig.tight_layout()
        self.canvas.draw_idle()

    # ---- Spot order (thread) ----
    def market_order(self, side: str):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        # --- UI: gombok tiltása, kurzor ---
        self.btn_spot_buy.config(state=tk.DISABLED)
        self.btn_spot_sell.config(state=tk.DISABLED)
        self.root.config(cursor="watch")

        # --- PARAMÉTEREK KIOLVASÁSA A FŐ SZÁLON ---
        try:
            symbol = normalize_symbol(self.trade_symbol.get())
            size_str  = (self.trade_size.get()  or "").strip()
            funds_str = (self.trade_funds.get() or "").strip()
        except Exception as e:
            self.log(f"⚠ Paraméter hiba: {e}")
            return

        # üres → None
        size_str  = size_str  if size_str  else None
        funds_str = funds_str if funds_str else None

        def worker(p_symbol: str, p_side: str, p_size: str | None, p_funds: str | None):
            try:
                send_size: str | None  = None  # BASE
                send_funds: str | None = None  # QUOTE

                # --- Alapelv SPOT-on:
                # BUY: funds az elsődleges; ha csak size van → átszámít funds-ra (last price alapján)
                # SELL: size az elsődleges; ha csak funds van → átszámít size-ra (last price alapján)

                # 1) Élő ár előkészítése – egységes helperrel (WS → cache → REST)
                try:
                    last_px = float(self.get_best_price(p_symbol))
                    if (not self._is_pos_num(last_px)) or last_px <= 0:
                        last_px = None
                except Exception:
                    last_px = None

                # 2) Side-aware paraméter választás
                #    - ha mindkettő meg van adva, a side szerinti preferált mezőt választjuk, a másikat ignoráljuk és logoljuk
                if p_side.lower() == "buy":
                    if p_funds:
                        send_funds = p_funds
                        if p_size:
                            self.log("ℹ BUY: funds megadva, a size-t figyelmen kívül hagyom (SPOT).")
                    elif p_size:
                        # csak size → funds konverzió (ha van ár)
                        if last_px and last_px > 0:
                            try:
                                est_f = float(p_size) * float(last_px)
                                send_funds = f"{est_f:.12g}"
                            except Exception:
                                raise ValueError("BUY: Nem sikerült a size→funds konverzió.")
                        else:
                            # ha nincs ár, küldhetünk size-ot is KuCoin felé, de BUY SPOT-on általában funds az elvárt
                            send_size = p_size
                    else:
                        raise ValueError("Adj meg legalább Funds (QUOTE) értéket BUY-hoz, vagy Size-et konverzióval.")

                else:  # SELL
                    if p_size:
                        send_size = p_size
                        if p_funds:
                            self.log("ℹ SELL: size megadva, a funds-t figyelmen kívül hagyom (SPOT).")
                    elif p_funds:
                        # csak funds → size konverzió (ha van ár)
                        if last_px and last_px > 0:
                            try:
                                est_sz = float(p_funds) / float(last_px)
                                send_size = f"{est_sz:.12g}"
                            except Exception:
                                raise ValueError("SELL: Nem sikerült a funds→size konverzió.")
                        else:
                            # fallback: küldjük funds-ként (KuCoin SPOT BUY-nál standard, SELL-nél size szokott lenni)
                            send_funds = p_funds
                    else:
                        raise ValueError("Adj meg legalább Size (BASE) értéket SELL-hez, vagy Funds-ot konverzióval.")

                # 3) (Opcionális) SZANITER – ha már van kész és szeretnéd SPOT-nál is használni
                try:
                    if hasattr(self, "_mb_sanitize_order"):
                        if p_side.lower() == "buy":
                            _sb, _fq = self._mb_sanitize_order(  # type: ignore[attr-defined]
                                symbol=p_symbol, side="buy",
                                price=(last_px or 0.0) if last_px else None,
                                size_base=None if send_size is None else float(send_size),
                                funds_quote=None if send_funds is None else float(send_funds),
                            )
                            # BUY: a végeredmény funds legyen (a szaniter size→funds-t is tud)
                            if _fq is None and _sb is None:
                                raise ValueError("Sanitizer eldobta a BUY megbízást (min/step).")
                            if _fq is not None:
                                send_size, send_funds = None, f"{_fq:.12g}"
                            elif _sb is not None:
                                send_size, send_funds = f"{_sb:.12g}", None
                        else:
                            _sb, _fq = self._mb_sanitize_order(  # type: ignore[attr-defined]
                                symbol=p_symbol, side="sell",
                                price=(last_px or 0.0) if last_px else None,
                                size_base=None if send_size is None else float(send_size),
                                funds_quote=None if send_funds is None else float(send_funds),
                            )
                            # SELL: a végeredmény size legyen
                            if _sb is None and _fq is None:
                                raise ValueError("Sanitizer eldobta a SELL megbízást (min/step).")
                            if _sb is not None:
                                send_size, send_funds = f"{_sb:.12g}", None
                            elif _fq is not None:
                                send_size, send_funds = None, f"{_fq:.12g}"
                except Exception as se:
                    # ha a szaniterrel gond van, ne dőljön össze a GUI – mehet a nyers érték
                    self.log(f"⚠ Sanitizer hiba (SPOT): {se}. Nyers paraméterekkel küldöm.")

                # Végső guard: legalább az egyik legyen nem-None
                if not (send_size or send_funds):
                    raise ValueError("Nincs küldhető mennyiség (size/funds).")

                # 4) ORDER KÜLDÉS – _ex_lock alatt
                with self._ex_lock:
                    resp = self.exchange.place_market_order(
                        p_symbol, p_side, size_base=send_size, funds_quote=send_funds  # type: ignore[arg-type]
                    )

                # 5) Válasz feldolgozás
                try:
                    oid = None
                    if isinstance(resp, dict):
                        # KuCoin: {"code":"200000","data":{"orderId":"..."}}
                        data = resp.get("data") or {}
                        oid = data.get("orderId") or data.get("id") or data.get("orderid")
                    if not oid:
                        oid = getattr(resp, "orderId", None) or getattr(resp, "id", None) or str(resp)
                except Exception:
                    oid = str(resp)

                self.root.after(0, lambda oid=oid, s=p_side: [
                    self.log(f"✅ Spot market {s.upper()} elküldve – orderId={oid}"),
                    messagebox.showinfo("Order", f"Sikeres {s} order.\nID: {oid}")
                ])

            except Exception as e:
                self.root.after(0, lambda e=e: [
                    self.log(f"❌ Spot order hiba: {e}"),
                    messagebox.showerror("Order hiba", str(e))
                ])
            finally:
                self.root.after(0, lambda: [
                    self.btn_spot_buy.config(state=tk.NORMAL),
                    self.btn_spot_sell.config(state=tk.NORMAL),
                    self.root.config(cursor="")
                ])

        threading.Thread(target=worker, args=(symbol, side, size_str, funds_str), daemon=True).start()

    # ---- SPOT egyenleg (thread) ----
    def refresh_balances(self):
        """SPOT egyenlegek frissítése háttérszálban, üres devizák elrejtésével."""
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és add meg az API kulcsokat.")
            return

        # (opcionális) UI lock
        btn = getattr(self, "btn_refresh_bal", None)
        if btn:
            btn.config(state=tk.DISABLED)
        self.root.config(cursor="watch")

        def worker():
            try:
                # --- EXCHANGE HÍVÁS THREAD-SAFE ---
                with self._ex_lock:
                    balances = self.exchange.fetch_spot_balances()  # type: ignore[union-attr]

                # --- UI FRISSÍTÉS A FŐ SZÁLON ---
                def fill():
                    try:
                        # először ürítjük a táblát
                        for row in self.tbl_bal.get_children():
                            self.tbl_bal.delete(row)

                        # feltöltés (ABC sorrendben, csak nem 0 egyenlegek)
                        for cur, vals in sorted((balances or {}).items()):
                            if not isinstance(vals, dict):
                                continue

                            av = vals.get("available", 0)
                            hd = vals.get("holds", 0)
                            try:
                                av = float(av)
                            except Exception:
                                av = 0.0
                            try:
                                hd = float(hd)
                            except Exception:
                                hd = 0.0

                            # Üres deviza (0.0 / 0.0) → kihagyjuk
                            if av == 0.0 and hd == 0.0:
                                continue

                            self.tbl_bal.insert(
                                "",
                                tk.END,
                                values=(cur, f"{av:.8f}", f"{hd:.8f}")
                            )
                    finally:
                        # UI visszaállítás
                        if btn:
                            btn.config(state=tk.NORMAL)
                        self.root.config(cursor="")

                self.root.after(0, fill)

            except Exception as e:
                def on_err():
                    if btn:
                        btn.config(state=tk.NORMAL)
                    self.root.config(cursor="")
                    messagebox.showerror("Egyenleg hiba", str(e))
                self.root.after(0, on_err)

        threading.Thread(target=worker, daemon=True).start()

    # ---- Isolated accounts (thread) ----
    def view_isolated_accounts(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        self.btn_iso.config(state=tk.DISABLED)
        self.root.config(cursor="watch")
        self.txt_positions.delete("1.0", tk.END)
        self.txt_positions.insert(tk.END, "Töltés…\n")

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.fetch_isolated_accounts()  # type: ignore[union-attr]
                payload = resp if isinstance(resp, dict) else getattr(resp, '__dict__', {}) or {'data': getattr(resp, 'data', {})}
                pretty = self.pretty_isolated_accounts(payload)
                rows = self._parse_isolated_rows(payload)
                def _show():
                    self._fill_isolated_table(rows)
                    self.txt_positions.delete("1.0", tk.END)
                    self.txt_positions.insert(tk.END, pretty + "\n")
                    self.txt_positions.see(tk.END)
                    self._last_positions_mode = "isolated"
                self.root.after(0, _show)
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Isolated accounts hiba", str(e)))
            finally:
                self.root.after(0, lambda: [self.btn_iso.config(state=tk.NORMAL), self.root.config(cursor="")])
        threading.Thread(target=worker, daemon=True).start()

    # ---- Cross account (thread) ----
    def view_cross_accounts(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és add meg az API kulcsokat.")
            return
        self.btn_cross.config(state=tk.DISABLED)
        self.root.config(cursor="watch")
        self.txt_positions.delete("1.0", tk.END)
        self.txt_positions.insert(tk.END, "Töltés…\n")

        csym = normalize_symbol(self.cross_symbol.get() or DEFAULT_SYMBOL)
        _, dq = split_symbol(csym)

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.fetch_cross_accounts()  # type: ignore[union-attr]
                payload = resp if isinstance(resp, dict) else getattr(resp, "__dict__", {}) or {"data": getattr(resp, "data", {})}
                rows = self._parse_cross_rows(payload, dq)
                pretty = self.pretty_cross_accounts(payload, dq)

                def _show():
                    self._fill_isolated_table(rows)
                    self.txt_positions.delete("1.0", tk.END)
                    self.txt_positions.insert(tk.END, pretty + "\n")
                    self.txt_positions.see(tk.END)
                    self._last_positions_mode = "cross"

                self.root.after(0, _show)
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Cross account hiba", str(e)))
            finally:
                self.root.after(0, lambda: [self.btn_cross.config(state=tk.NORMAL), self.root.config(cursor="")])

        threading.Thread(target=worker, daemon=True).start()

    def view_cross_for_symbol(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        symbol = normalize_symbol(self.cross_symbol.get() or "")
        if not symbol or "-" not in symbol:
            messagebox.showerror("Hiba", "Adj meg érvényes szimbólumot (pl. SOL-USDT).")
            return

        self.btn_cross_snap.config(state=tk.DISABLED)
        self.root.config(cursor="watch")
        self.txt_positions.delete("1.0", tk.END)
        self.txt_positions.insert(tk.END, f"Cross snapshot töltése: {symbol} …\n")

        def worker():
            try:
                with self._ex_lock:
                    acc = self.exchange.fetch_cross_accounts()  # type: ignore[union-attr]
                payload = acc if isinstance(acc, dict) else getattr(acc, "__dict__", {}) or {"data": getattr(acc, "data", {})}
                dq = symbol.split("-")[1]
                rows = self._parse_cross_rows(payload, dq)
                row = next((r for r in rows if r["symbol"] == symbol), None)

                def _show():
                    for iid in self.tbl_iso.get_children():
                        self.tbl_iso.delete(iid)
                    if row:
                        self.tbl_iso.insert("", tk.END, values=(row["symbol"], row["side"], f"{row['closable']:,.6f}", row["base"], row["quote"], row["risk"]))
                    pretty = self.pretty_cross_accounts(payload, dq)
                    self.txt_positions.delete("1.0", tk.END)
                    self.txt_positions.insert(tk.END, pretty + "\n")
                    self.txt_positions.see(tk.END)
                    self._last_positions_mode = "cross"

                self.root.after(0, _show)
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Cross snapshot hiba", str(e)))
            finally:
                self.root.after(0, lambda: [self.btn_cross_snap.config(state=tk.NORMAL), self.root.config(cursor="")])

        threading.Thread(target=worker, daemon=True).start()

    # ----- Pozíció zárás (isolated) – szaniterrel egységesítve -----
    def close_isolated_position(self, symbol: str) -> dict:
        """
        Manuális isolated pozíciózárás markettel.
        - Long zárás → SELL (BASE mennyiség küldése)
        - Short zárás → BUY (funds küldése, szaniter végzi a size→funds becslést és ellenőrzést)
        """
        # 1) Isolated számla lekérése és a kiválasztott pár sora
        with self._ex_lock:
            acc = self.exchange.fetch_isolated_accounts()
        data = acc.get("data", acc)
        assets = (data or {}).get("assets", []) or []
        row = next((a for a in assets if (a.get("symbol") or "").upper() == symbol.upper()), None)
        if not row:
            raise RuntimeError(f"Nincs isolated adat a(z) {symbol} párra.")

        base  = row.get("baseAsset", {}) or {}
        quote = row.get("quoteAsset", {}) or {}

        base_tot = float(base.get("total", 0) or 0)          # long méret
        base_li  = float(base.get("liability", 0) or 0)      # short méret (visszavásárolandó)
        quote_li = float(quote.get("liability", 0) or 0)

        # 2) Irány és nyers mennyiség (szaniter előtt)
        if base_li > 0:
            side, raw_size = "buy", base_li      # short zárás → BUY
        elif base_tot > 0:
            side, raw_size = "sell", base_tot    # long zárás → SELL
        elif quote_li > 0 and base_tot > 0:
            side, raw_size = "sell", base_tot
        else:
            raise RuntimeError("Nincs zárható isolated pozíció.")

        # 3) Utolsó ár BUY funds-becsléshez – egységes helperrel (WS → cache → REST)
        try:
            last_px = float(self.get_best_price(symbol))
            if (not self._is_pos_num(last_px)) or last_px <= 0:
                last_px = None
        except Exception:
            last_px = None

        # 4) Szaniter hívása – egységes minimumok/lépésközök
        try:
            sb, fq = self._mb_sanitize_order(
                symbol=symbol,
                side=side,
                price=last_px,          # lehet None is, a szaniter ezt bírja
                size_base=float(raw_size),
                funds_quote=None
            )
        except Exception as e:
            raise RuntimeError(f"Szaniter hiba zárás közben: {e}")

        # 5) Kötelező mezők ellenőrzése oldalanként
        if side == "sell":
            if not sb or sb <= 0:
                raise RuntimeError("Zárási méret a lépésköz/minimum alatt – SELL close eldobva.")
            size_arg, funds_arg = float(sb), None
        else:
            if not fq or fq <= 0:
                raise RuntimeError("BUY close eldobva (minFunds/quote_step/minBase ellenőrzés után).")
            size_arg, funds_arg = None, float(fq)

        # 6) Leverage az UI-ból (ha nincs, 10)
        try:
            lev = max(1, int(self._mb_get_int('mb_leverage', 10)))
        except Exception:
            lev = 10

        # 7) Market close küldése; auto_repay=True, auto_borrow=False
        payload_dbg = {
            "mode": "isolated", "symbol": symbol, "side": side,
            "size_base": size_arg, "funds_quote": funds_arg,
            "leverage": lev, "auto_borrow": False, "auto_repay": True
        }
        self._safe_log(f"🐞 SEND MANUAL CLOSE: {self._mb_pp(payload_dbg)}\n")

        with self._ex_lock:
            resp = self.exchange.place_margin_market_order(
                "isolated", symbol, side,
                size_base=size_arg,
                funds_quote=funds_arg,
                leverage=lev,
                auto_borrow=False,
                auto_repay=True
            )

        self._safe_log(f"🐞 RECV MANUAL CLOSE: {self._mb_pp(resp)}\n")
        return resp if isinstance(resp, dict) else {"data": resp}

    def close_selected_isolated(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        sel = self.tbl_iso.selection()
        if not sel:
            messagebox.showwarning("Nincs kiválasztás", "Válassz ki egy sort a táblázatban.")
            return
        symbol = self.tbl_iso.item(sel[0], "values")[0]
        mode = getattr(self, "_last_positions_mode", "isolated")

        btn = self.btn_close_selected
        btn.config(state=tk.DISABLED)
        self.root.config(cursor="watch")

        def worker():
            try:
                if mode == "cross":
                    # marad a wrapperes cross close, ha van
                    with self._ex_lock:
                        resp = self.exchange.close_cross_position(symbol)  # type: ignore[union-attr]
                    refreshed = self.view_cross_accounts
                    ok_title = "Close cross"
                else:
                    # MOSTANTÓL a saját (CryptoBotApp) isolated close-t hívjuk,
                    # hogy a szaniter biztosan ugyanaz legyen, mint a workerben
                    resp = self.close_isolated_position(symbol)
                    refreshed = self.view_isolated_accounts
                    ok_title = "Close isolated"

                data = (resp.get("data", {}) or {}) if isinstance(resp, dict) else {}
                oid = data.get("orderId") or data.get("id") or data.get("orderid") or data.get("clientOid")

                self.root.after(0, lambda oid=oid, s=symbol, ok_title=ok_title: [
                    self.log(f"✅ {ok_title} – {s} – orderId={oid}"),
                    messagebox.showinfo(ok_title, f"Sikeres zárás: {s}\nOrderId: {oid}"),
                    refreshed()
                ])
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Pozíció zárás hiba", str(e)))
            finally:
                self.root.after(0, lambda: [btn.config(state=tk.NORMAL), self.root.config(cursor="")])

        threading.Thread(target=worker, daemon=True).start()

    def close_cross_clicked(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        symbol = normalize_symbol(self.cross_symbol.get() or "")
        if not symbol or "-" not in symbol:
            messagebox.showerror("Hiba", "Adj meg érvényes szimbólumot (pl. SOL-USDT).")
            return

        self.btn_cross_close.config(state=tk.DISABLED)
        self.root.config(cursor="watch")

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.close_cross_position(symbol)  # type: ignore[union-attr]
                oid = (resp.get("data", {}) or {}).get("orderId")
                self.root.after(0, lambda oid=oid, s=symbol: [
                    self.log(f"✅ Cross pozíció zárva ({s}) – orderId={oid}"),
                    messagebox.showinfo("Close cross", f"Sikeres zárás: {s}\nOrderId: {oid}"),
                    self.view_cross_for_symbol()
                ])
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Cross zárás hiba", str(e)))
            finally:
                self.root.after(0, lambda: [self.btn_cross_close.config(state=tk.NORMAL),
                                             self.root.config(cursor="")])

        threading.Thread(target=worker, daemon=True).start()

    # ---- Funds actions ----
    def _do_spot_transfer(self, from_type: str, to_type: str, ccy: str = None, amt: float = None):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        # Fallback régi widgetekre
        if ccy is None and hasattr(self, 'f_spot_ccy'):
            ccy = self.f_spot_ccy.get().strip().upper()
        if amt is None and hasattr(self, 'f_spot_amt'):
            try:
                amt = float(self.f_spot_amt.get())
            except:
                pass

        if not ccy:
            messagebox.showerror("Hiba", "Hiányzó deviza."); return
        try:
            if amt is None or float(amt) <= 0: raise ValueError
            amt = float(amt)
        except Exception:
            messagebox.showerror("Hiba", "Érvénytelen összeg."); return

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.transfer_spot_internal(ccy, amt, from_type, to_type)  # type: ignore[union-attr]
                self.root.after(0, lambda: [self.funds_log.insert(tk.END, f"✅ Spot transfer {from_type}→{to_type} {amt} {ccy}\n"),
                                             self.funds_log.see(tk.END)])
            except Exception as e:
                self.root.after(0, lambda e=e: [self.funds_log.insert(tk.END, f"❌ Spot transfer hiba: {e}\n"),
                                                self.funds_log.see(tk.END),
                                                messagebox.showerror("Transfer hiba", str(e))])
        threading.Thread(target=worker, daemon=True).start()

    def _do_cross_transfer(self, direction: str, ccy: str = None, amt: float = None):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        if ccy is None and hasattr(self, 'f_cross_ccy'):
            ccy = self.f_cross_ccy.get().strip().upper()
        if amt is None and hasattr(self, 'f_cross_amt'):
            try:
                amt = float(self.f_cross_amt.get())
            except:
                pass

        if not ccy:
            messagebox.showerror("Hiba", "Hiányzó deviza."); return
        try:
            if amt is None or float(amt) <= 0: raise ValueError
            amt = float(amt)
        except Exception:
            messagebox.showerror("Hiba", "Érvénytelen összeg."); return

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.transfer_cross_margin(ccy, amt, direction)  # ← EZT hívjuk
                self.root.after(0, lambda: [
                    self.funds_log.insert(tk.END, f"✅ Cross transfer {direction} {amt} {ccy}\n"),
                    self.funds_log.see(tk.END)
                ])
            except Exception as e:
                self.root.after(0, lambda e=e: [
                    self.funds_log.insert(tk.END, f"❌ Cross transfer hiba: {e}\n"),
                    self.funds_log.see(tk.END),
                    messagebox.showerror("Transfer hiba", str(e))
                ])
        threading.Thread(target=worker, daemon=True).start()

    def _do_isolated_transfer(self, direction: str, spot_account: str = "TRADE", sym: str = None, ccy: str = None, amt: float = None):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        if sym is None and hasattr(self, 'f_iso_sym'):
            sym = normalize_symbol(self.f_iso_sym.get())
        else:
            sym = normalize_symbol(sym)

        if ccy is None and hasattr(self, 'f_iso_ccy'):
            ccy = self.f_iso_ccy.get().strip().upper()
        if amt is None and hasattr(self, 'f_iso_amt'):
            try:
                amt = float(self.f_iso_amt.get())
            except:
                pass

        if not sym:
             messagebox.showerror("Hiba", "Hiányzó szimbólum."); return
        if not ccy:
             messagebox.showerror("Hiba", "Hiányzó deviza."); return
        try:
            if amt is None or float(amt) <= 0: raise ValueError
            amt = float(amt)
        except Exception:
            messagebox.showerror("Hiba", "Érvénytelen összeg."); return

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.transfer_isolated_margin(sym, ccy, amt, direction, spot_account=spot_account)
                self.root.after(0, lambda: [
                    self.funds_log.insert(tk.END, f"✅ Isolated transfer {direction} {amt} {ccy}  ({sym})\n"),
                    self.funds_log.see(tk.END)
                ])
            except Exception as e:
                self.root.after(0, lambda e=e: [
                    self.funds_log.insert(tk.END, f"❌ Isolated transfer hiba: {e}\n"),
                    self.funds_log.see(tk.END),
                    messagebox.showerror("Transfer hiba", str(e))
                ])
        threading.Thread(target=worker, daemon=True).start()

    # ==================== MARGIN TRADE BOT (fejlesztett) ====================
    def _build_margin_bot_tab(self):
        """Margin Bot fül – bal: form (scrollozható), jobb: napló + mini-diagram."""
        # fül
        self.tab_mbot = ttk.Frame(self.nb)
        self.nb.add(self.tab_mbot, text="Margin Bot")
        root = self.tab_mbot
        root.grid_columnconfigure(0, weight=0, minsize=800)  # bal: form
        root.grid_columnconfigure(1, weight=1)              # jobb: history+chart
        root.grid_rowconfigure(0, weight=1)

        # ===== bal oszlop: SCROLL-OZHATÓ konténer =====
        left_container = ttk.Frame(root)
        left_container.grid(row=0, column=0, sticky="nsew", padx=(10, 6), pady=10)
        left_container.grid_columnconfigure(0, weight=1)
        left_container.grid_rowconfigure(0, weight=1)

        canvas = tk.Canvas(left_container, highlightthickness=0, borderwidth=0)
        vscroll = ttk.Scrollbar(left_container, orient="vertical", command=canvas.yview)
        canvas.grid(row=0, column=0, sticky="nsew")
        vscroll.grid(row=0, column=1, sticky="ns")
        canvas.configure(yscrollcommand=vscroll.set)

        # A valódi form egy frame-ben ül a canvasban
        scroll_frame = ttk.Frame(canvas)
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")

        # Scrollregion frissítés
        def _on_scroll_frame_config(_event):
            canvas.configure(scrollregion=canvas.bbox("all"))
        scroll_frame.bind("<Configure>", _on_scroll_frame_config)

        # Egérgörgő görgetés – csak bal panel, ne léptesse a Spinboxokat
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            return "break"

        def _bind_mousewheel_recursively(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            for child in widget.winfo_children():
                _bind_mousewheel_recursively(child)

        # ===== bal oszlop: beállítások (form) =====
        form = ttk.Labelframe(
            scroll_frame,
            text="Margin bot – beállítások",
            padding=10,
            style="Card.TLabelframe",
        )
        form.grid(row=0, column=0, sticky="nwe")
        form.grid_columnconfigure(0, weight=1)

        # --- ÚJ: belső fülek (Alap / Haladó) ---
        cfg_nb = ttk.Notebook(form)
        cfg_nb.grid(row=0, column=0, sticky="we")

        tab_basic = ttk.Frame(cfg_nb)
        tab_adv = ttk.Frame(cfg_nb)
        cfg_nb.add(tab_basic, text="Alap beállítások")
        cfg_nb.add(tab_adv, text="Haladó beállítások")

        for i in range(2):
            tab_basic.grid_columnconfigure(i, weight=1)
            tab_adv.grid_columnconfigure(i, weight=1)

        basic = tab_basic
        adv = tab_adv

        r = 0
        r_adv = 0

        # ====== ALAP BEÁLLÍTÁSOK (basic) ======

        # mód választó
        self.mb_mode = tk.StringVar(value="isolated")
        mrow = ttk.Frame(basic)
        mrow.grid(row=r, column=0, columnspan=2, sticky="w")
        ttk.Radiobutton(
            mrow, text="Isolated", variable=self.mb_mode, value="isolated",
            command=lambda: (self._mb_sync_lev_cap(), self._mb_refresh_available())
        ).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Radiobutton(
            mrow, text="Cross", variable=self.mb_mode, value="cross",
            command=lambda: (self._mb_sync_lev_cap(), self._mb_refresh_available())
        ).pack(side=tk.LEFT)
        r += 1

        ttk.Label(basic, text="Pár").grid(row=r, column=0, sticky="w", pady=(4, 0))
        row_pair = ttk.Frame(basic)
        row_pair.grid(row=r, column=1, pady=(4, 0), sticky="w")

        self.mb_symbol = ttk.Combobox(row_pair, values=self.symbols, width=12, state="readonly")
        self.mb_symbol.set(DEFAULT_SYMBOL)
        self.mb_symbol.pack(side="left")

        ttk.Label(row_pair, text="  Max pozíció:").pack(side="left")
        self.mb_max_open = ttk.Spinbox(row_pair, from_=0, to=999, width=6)
        self.mb_max_open.pack(side="left", padx=(4, 0))
        self.mb_max_open.delete(0, "end")
        self.mb_max_open.insert(0, "0")

        self.mb_symbol.bind("<<ComboboxSelected>>", self._mb_refresh_available)
        r += 1

        # Idősík
        ttk.Label(basic, text="Idősík").grid(row=r, column=0, sticky="w", pady=(4, 0))
        self.mb_tf = ttk.Combobox(
            basic, state="readonly", width=10,
            values=["1m", "3m", "5m", "15m", "30m", "1h", "4h", "1d"],
        )
        self.mb_tf.set("1m")
        self.mb_tf.grid(row=r, column=1, sticky="w", pady=(4, 0))

        self.root.after(50, self._mb_refresh_available)
        r += 1

        # --- Strategy Selector ---
        ttk.Label(basic, text="Stratégia").grid(row=r, column=0, sticky="w", pady=(4, 0))
        self.mb_strategy = tk.StringVar(value="EMA")
        self.mb_strategy_cb = ttk.Combobox(
            basic, textvariable=self.mb_strategy, state="readonly", width=15,
            values=["EMA", "Z-Score", "Bollinger Squeeze", "Supertrend"]
        )
        self.mb_strategy_cb.grid(row=r, column=1, sticky="w", pady=(4, 0))
        self.mb_strategy_cb.bind("<<ComboboxSelected>>", self._mb_on_strategy_change)
        r += 1

        # EMA (rövid/hosszú)
        ttk.Label(basic, text="EMA (rövid / hosszú)").grid(row=r, column=0, sticky="w", pady=(2, 0))
        ema_row = ttk.Frame(basic)
        ema_row.grid(row=r, column=1, sticky="w", pady=(2, 0))

        self.mb_ma_fast = ttk.Spinbox(ema_row, from_=2, to=500, width=6)
        self.mb_ma_fast.delete(0, tk.END)
        self.mb_ma_fast.insert(0, "12")
        self.mb_ma_fast.pack(side=tk.LEFT)

        ttk.Label(ema_row, text=" ").pack(side=tk.LEFT)

        self.mb_ma_slow = ttk.Spinbox(ema_row, from_=3, to=1000, width=6)
        self.mb_ma_slow.delete(0, tk.END)
        self.mb_ma_slow.insert(0, "26")
        self.mb_ma_slow.pack(side=tk.LEFT)

        ttk.Label(ema_row, text="   ").pack(side=tk.LEFT)
        self.mb_invert_ema = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            ema_row,
            text="Invert EMA jel-logika",
            variable=self.mb_invert_ema,
        ).pack(side=tk.LEFT, padx=(4, 0))
        r += 1

        # EMA Hysteresis
        ttk.Label(basic, text="EMA Hysteresis (Zajszűrés):").grid(row=r, column=0, sticky="w", pady=(6, 0))
        ema_f_row = ttk.Frame(basic)
        ema_f_row.grid(row=r, column=1, sticky="w", pady=(6, 0))

        self.mb_ema_hyst_pct = ttk.Spinbox(ema_f_row, from_=0.0, to=100, width=6)
        self.mb_ema_hyst_pct.delete(0, tk.END)
        self.mb_ema_hyst_pct.insert(0, "1.00")
        self.mb_ema_hyst_pct.pack(side=tk.LEFT)
        r += 1

        # Tőkeáttét
        ttk.Label(basic, text="Tőkeáttét").grid(row=r, column=0, sticky="w", pady=(6, 0))
        self.mb_leverage = ttk.Spinbox(basic, from_=1, to=10, width=6)
        self.mb_leverage.delete(0, tk.END)
        self.mb_leverage.insert(0, "10")
        self.mb_leverage.grid(row=r, column=1, sticky="w", pady=(6, 0))
        self.mb_lev = self.mb_leverage
        r += 1

        # Méret % + input mód
        ttk.Label(basic, text="Méret (%, QUOTE/BASE szerint)").grid(row=r, column=0, sticky="w", pady=(6, 0))
        size_row = ttk.Frame(basic)
        size_row.grid(row=r, column=1, sticky="w", pady=(6, 0))

        self.mb_size_pct = ttk.Spinbox(size_row, from_=1, to=100, width=6)
        self.mb_size_pct.delete(0, tk.END)
        self.mb_size_pct.insert(0, "25")
        self.mb_size_pct.pack(side=tk.LEFT)

        ttk.Label(size_row, text="  mód:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_input_mode = ttk.Combobox(size_row, state="readonly", width=7, values=["quote", "base"])
        self.mb_input_mode.set("quote")
        self.mb_input_mode.pack(side=tk.LEFT)
        r += 1

        ttk.Label(basic, text="Keret (QUOTE) – opcionális").grid(row=r, column=0, sticky="w", pady=(2, 0))
        _row_budget = ttk.Frame(basic)
        _row_budget.grid(row=r, column=1, sticky="w", pady=(2, 0))

        self.mb_budget = ttk.Entry(_row_budget, width=12)
        self.mb_budget.pack(side=tk.LEFT)

        ttk.Label(_row_budget, text="  Elérhető:").pack(side=tk.LEFT, padx=(8, 2))
        self.mb_avail_var = tk.StringVar(value="–")
        self.mb_avail_lbl = ttk.Label(_row_budget, textvariable=self.mb_avail_var)
        self.mb_avail_lbl.pack(side=tk.LEFT)
        r += 1

        # Dupla / túl közeli azonos irányú nyitások tiltó zóna
        ttk.Label(basic, text="Dupla / túl közeli azonos irányú nyitások tiltó zóna (%):").grid(row=r, column=0, sticky="w", pady=(6, 0))
        if not hasattr(self, 'mb_dup_tol_pct_var'):
            self.mb_dup_tol_pct_var = tk.DoubleVar(value=0.5)

        tol_spin = ttk.Spinbox(
            basic,
            from_=0.0,
            to=5.0,
            increment=0.05,
            width=6,
            textvariable=self.mb_dup_tol_pct_var,
            format="%.2f"
        )
        tol_spin.grid(row=r, column=1, sticky="w", pady=(6, 0))
        r += 1

        # checkboxok
        ch = ttk.Frame(basic)
        ch.grid(row=r, column=0, columnspan=2, sticky="w", pady=(8, 0))

        self.mb_autob = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Auto-borrow/repay", variable=self.mb_autob).pack(side=tk.LEFT, padx=(10))

        self.mb_allow_short = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Short engedélyezése", variable=self.mb_allow_short).pack(side=tk.LEFT, padx=(10))

        self.mb_pause_new = tk.BooleanVar(value=False)
        ttk.Checkbutton(ch, text="Új nyitás szünetel", variable=self.mb_pause_new).pack(side=tk.LEFT, padx=(10))

        self.mb_dry = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Dry-run (nem küld ordert)", variable=self.mb_dry).pack(side=tk.LEFT, padx=(10))
        r += 1

        # Start / Stop
        btns = ttk.Frame(basic)
        btns.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10, 0))
        self.mb_start_btn = ttk.Button(btns, text="Start bot", command=self.mb_start)
        self.mb_start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        self.mb_stop_btn = ttk.Button(btns, text="Stop bot", command=self.mb_stop, state=tk.DISABLED)
        self.mb_stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        r += 1

        apply_btn = ttk.Button(
            basic,
            text="Beállítások frissítése / paraméterek állítása ( futó botra )",
            command=self.mb_reload_cfg,
        )
        apply_btn.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10, 0))

        # Config Save/Load
        r += 1
        cfg_btns = ttk.Frame(basic)
        cfg_btns.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10, 0))
        ttk.Button(cfg_btns, text="Mentés (Config)", command=self._save_cfg_to_file).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        ttk.Button(cfg_btns, text="Betöltés (Config)", command=self._load_cfg_from_file).pack(side=tk.LEFT, fill=tk.X, expand=True)

        # ====== HALADÓ BEÁLLÍTÁSOK (adv): Z-score -> Cooldown ======
        z_title_lbl = ttk.Label(
            adv,
            text="Z-score beállítások",
            font=self.bold_font,
        )
        z_box = ttk.Labelframe(adv, labelwidget=z_title_lbl, padding=6)
        z_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))

        z_row1 = ttk.Frame(z_box)
        z_row1.pack(anchor="w")

        # (Korábbi checkbox eltávolítva - a Stratégia választó vezérli)
        # Dummy variable, hogy a config ne haljon el, ha még hivatkozik rá valahol
        self.mb_use_zscore = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            z_row1,
            text="Z-score filter használata",
            variable=self.mb_use_zscore,
            command=self._mb_toggle_zscore_widgets,
        ).pack(side=tk.LEFT)

        z_row2 = ttk.Frame(z_box)
        z_row2.pack(anchor="w", pady=(4, 0))

        ttk.Label(z_row2, text="Hossz:").pack(side=tk.LEFT)
        self.mb_z_len = ttk.Spinbox(z_row2, from_=10, to=200, width=6)
        self.mb_z_len.delete(0, tk.END)
        self.mb_z_len.insert(0, "40")
        self.mb_z_len.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(z_row2, text="Pontok:").pack(side=tk.LEFT, padx=(4, 2))
        self.mb_z_points = ttk.Spinbox(z_row2, from_=20, to=500, width=6)
        self.mb_z_points.delete(0, tk.END)
        self.mb_z_points.insert(0, "100")
        self.mb_z_points.pack(side=tk.LEFT)

        def _mb_test_zscore():
            symbol = normalize_symbol(self.mb_symbol.get())
            tf = self.mb_tf.get().strip() or "1m"
            try:
                length = int(self.mb_z_len.get())
            except Exception:
                length = 40
            try:
                points = int(self.mb_z_points.get())
            except Exception:
                points = 100

            sig, quad = self._compute_zscore_signal(symbol, tf, length=length, data_points=points)
            txt_map = {1: "LONG", -1: "SHORT", 0: "HOLD"}
            txt = txt_map.get(sig, "ismeretlen")

            extra = ""
            if quad:
                extra = (
                    f" | Q1:{quad['quad1']} Q2:{quad['quad2']} "
                    f"Q3:{quad['quad3']} Q4:{quad['quad4']} "
                    f"CurQ:{quad['current_quadrant']}"
                )
            self.mb_z_label.configure(text=f"Z-score jelzés: {txt}{extra}")

        ttk.Button(z_row2, text="Z-score teszt", command=_mb_test_zscore).pack(side=tk.LEFT, padx=(10, 0))

        self.mb_z_label = ttk.Label(z_row2, text="Z-score jelzés: n/a")
        self.mb_z_label.pack(side=tk.LEFT)
        r_adv += 1

        # Bollinger Squeeze beállítások
        sqz_title_lbl = ttk.Label(
            adv, 
            text="Bollinger Squeeze beállítások",
            font=self.bold_font,
        )
        sqz_box = ttk.Labelframe(adv, labelwidget=sqz_title_lbl, padding=6)
        sqz_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))

        sqz_row1 = ttk.Frame(sqz_box)
        sqz_row1.pack(anchor="w")

        # Checkbox a filterhez
        self.mb_use_sqz_filter = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            sqz_row1,
            text="Használd Filterként (ha más a stratégia)",
            variable=self.mb_use_sqz_filter,
            command=self._mb_on_strategy_change,
        ).pack(side=tk.LEFT)

        ttk.Label(sqz_row1, text="Hossz:").pack(side=tk.LEFT)
        self.mb_sqz_len = ttk.Spinbox(sqz_row1, from_=5, to=200, width=6)
        self.mb_sqz_len.delete(0, tk.END)
        self.mb_sqz_len.insert(0, "20")
        self.mb_sqz_len.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(sqz_row1, text="BB Mult:").pack(side=tk.LEFT)
        self.mb_sqz_bb_mult = ttk.Spinbox(sqz_row1, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_sqz_bb_mult.delete(0, tk.END)
        self.mb_sqz_bb_mult.insert(0, "2.0")
        self.mb_sqz_bb_mult.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(sqz_row1, text="KC Mult:").pack(side=tk.LEFT)
        self.mb_sqz_kc_mult = ttk.Spinbox(sqz_row1, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_sqz_kc_mult.delete(0, tk.END)
        self.mb_sqz_kc_mult.insert(0, "1.5")
        self.mb_sqz_kc_mult.pack(side=tk.LEFT, padx=(2, 0))
        r_adv += 1

        # Supertrend beállítások (Stratégia / Filter)
        st_title_lbl = ttk.Label(
            adv, 
            text="Supertrend (Stratégia / Filter)",
            font=self.bold_font,
        )

        st_box = ttk.Labelframe(adv, labelwidget=st_title_lbl, padding=6)
        st_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))

        st_row1 = ttk.Frame(st_box)
        st_row1.pack(anchor="w")

        # Checkbox a filterhez
        self.mb_use_st_filter = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            st_row1,
            text="Használd Filterként (ha más a stratégia)",
            variable=self.mb_use_st_filter,
            command=self._mb_on_strategy_change,
        ).pack(side=tk.LEFT)

        ttk.Label(st_row1, text="ATR Hossz:").pack(side=tk.LEFT)
        self.mb_st_period = ttk.Spinbox(st_row1, from_=1, to=100, width=6)
        self.mb_st_period.delete(0, tk.END)
        self.mb_st_period.insert(0, "10")
        self.mb_st_period.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(st_row1, text="Multiplier:").pack(side=tk.LEFT)
        self.mb_st_mult = ttk.Spinbox(st_row1, from_=0.1, to=10.0, increment=0.1, width=5)
        self.mb_st_mult.delete(0, tk.END)
        self.mb_st_mult.insert(0, "3.0")
        self.mb_st_mult.pack(side=tk.LEFT, padx=(2, 0))
        r_adv += 1

        # Fix SL / TP / Trailing – opcionális (ATR nélkül)
        fixed_title_lbl = ttk.Label(
            adv,
            text="Fix SL / TP / Trailing (ATR nélkül)",
            font=self.bold_font,
        )

        fixed_box = ttk.Labelframe(adv, labelwidget=fixed_title_lbl, padding=6)
        fixed_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))
        fixed_row1 = ttk.Frame(fixed_box)
        fixed_row1.pack(anchor="w")

        self.mb_use_fixed = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            fixed_row1,
            text="Fix menedzsment használata",
            variable=self.mb_use_fixed,
            command=self._mb_on_fixed_changed,
        ).pack(side=tk.LEFT)

        ttk.Label(fixed_row1, text="SL %").pack(side=tk.LEFT)
        self.mb_sl_pct = ttk.Spinbox(fixed_row1, from_=0, to=50, increment=0.1, width=6)
        self.mb_sl_pct.delete(0, tk.END)
        self.mb_sl_pct.insert(0, "5.0")
        self.mb_sl_pct.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(fixed_row1, text="TP %").pack(side=tk.LEFT)
        self.mb_tp_pct = ttk.Spinbox(fixed_row1, from_=0, to=50, increment=0.1, width=6)
        self.mb_tp_pct.delete(0, tk.END)
        self.mb_tp_pct.insert(0, "1.0")
        self.mb_tp_pct.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(fixed_row1, text="Trailing %").pack(side=tk.LEFT)
        self.mb_trail_pct = ttk.Spinbox(fixed_row1, from_=0, to=20, increment=0.1, width=6)
        self.mb_trail_pct.delete(0, tk.END)
        self.mb_trail_pct.insert(0, "0")
        self.mb_trail_pct.pack(side=tk.LEFT, padx=(2, 0))
        r_adv += 1

        # LIVE kitörés / shock (intra-bar)
        live_title_lbl = ttk.Label(
            adv,
            text="LIVE kitörés / shock (intra-bar",
            font=self.bold_font,
        )

        live_box = ttk.Labelframe(adv, labelwidget=live_title_lbl, padding=6)
        live_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))
        live_row1 = ttk.Frame(live_box)
        live_row1.pack(anchor="w")

        self.mb_use_live = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            live_row1,
            text="Élő ár figyelése (breakout/shock)",
            variable=self.mb_use_live,
            command=self._mb_toggle_live_widgets,
        ).pack(side=tk.LEFT)

        ttk.Label(live_row1, text="  Shock %:").pack(side=tk.LEFT, padx=(10, 2))
        self.mb_live_shock_pct = ttk.Spinbox(live_row1, from_=0.0, to=10.0, increment=0.05, width=6)
        self.mb_live_shock_pct.delete(0, tk.END)
        self.mb_live_shock_pct.insert(0, "1.00")
        self.mb_live_shock_pct.pack(side=tk.LEFT)

        ttk.Label(live_row1, text="  Shock ATR×:").pack(side=tk.LEFT, padx=(10, 2))
        self.mb_live_shock_atr = ttk.Spinbox(live_row1, from_=0.0, to=5.0, increment=0.05, width=6)
        self.mb_live_shock_atr.delete(0, tk.END)
        self.mb_live_shock_atr.insert(0, "1.20")
        self.mb_live_shock_atr.pack(side=tk.LEFT)

        ttk.Label(live_row1, text="  Max Drift %:").pack(side=tk.LEFT, padx=(10, 2))
        self.mb_drift_max_pct = ttk.Spinbox(live_row1, from_=0.0, to=5.0, increment=0.05, width=6)
        self.mb_drift_max_pct.delete(0, tk.END)
        self.mb_drift_max_pct.insert(0, "0.0")
        self.mb_drift_max_pct.pack(side=tk.LEFT)
        r_adv += 1

        # Breakout (kitörés)
        brk_title_lbl = ttk.Label(
            adv,
            text="Breakout (kitörés)",
            font=self.bold_font,
        )

        brk_box = ttk.Labelframe(adv, labelwidget=brk_title_lbl, padding=6)
        brk_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))
        brk_row1 = ttk.Frame(brk_box)
        brk_row1.pack(anchor="w")

        self.mb_use_brk = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            brk_row1,
            text="Breakout használata",
            variable=self.mb_use_brk,
            command=lambda: self._mb_toggle_brk_widgets(),
        ).pack(side=tk.LEFT)

        ttk.Label(brk_row1, text="  Lookback:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_brk_n = ttk.Spinbox(brk_row1, from_=5, to=200, width=6)
        self.mb_brk_n.delete(0, tk.END)
        self.mb_brk_n.insert(0, "20")
        self.mb_brk_n.pack(side=tk.LEFT)

        ttk.Label(brk_row1, text="  Puffer %:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_brk_buf = ttk.Spinbox(brk_row1, from_=0.0, to=2.0, increment=0.01, width=6)
        self.mb_brk_buf.delete(0, tk.END)
        self.mb_brk_buf.insert(0, "0.10")
        self.mb_brk_buf.pack(side=tk.LEFT)

        self.mb_brk_with_trend = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            brk_row1,
            text="Csak HTF trend irányába",
            variable=self.mb_brk_with_trend,
        ).pack(side=tk.LEFT, padx=(10, 0))
        r_adv += 1

        # RSI szűrő
        rsi_title_lbl = ttk.Label(
            adv,
            text="RSI szűrő",
            font=self.bold_font,
        )

        rsi_box = ttk.Labelframe(adv, labelwidget=rsi_title_lbl, padding=6)
        rsi_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))

        rsi_row1 = ttk.Frame(rsi_box)
        rsi_row1.pack(anchor="w")
        self.mb_use_rsi = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            rsi_row1,
            text="RSI használata",
            variable=self.mb_use_rsi,
            command=self._mb_toggle_rsi_widgets,
        ).pack(side=tk.LEFT)

        ttk.Label(rsi_row1, text="  RSI len:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_rsi_len = ttk.Spinbox(rsi_row1, from_=5, to=50, width=6)
        self.mb_rsi_len.delete(0, tk.END)
        self.mb_rsi_len.insert(0, "14")
        self.mb_rsi_len.pack(side=tk.LEFT)

        rsi_row2 = ttk.Frame(rsi_box)
        rsi_row2.pack(anchor="w", pady=(4, 0))

        ttk.Label(rsi_row2, text="BUY zóna [min,max]").pack(side=tk.LEFT)
        self.mb_rsi_buy_min = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_buy_min.delete(0, tk.END)
        self.mb_rsi_buy_min.insert(0, "45")
        self.mb_rsi_buy_min.pack(side=tk.LEFT, padx=(4, 2))

        self.mb_rsi_buy_max = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_buy_max.delete(0, tk.END)
        self.mb_rsi_buy_max.insert(0, "70")
        self.mb_rsi_buy_max.pack(side=tk.LEFT, padx=(2, 12))

        ttk.Label(rsi_row2, text="SELL zóna [min,max]").pack(side=tk.LEFT)
        self.mb_rsi_sell_min = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_sell_min.delete(0, tk.END)
        self.mb_rsi_sell_min.insert(0, "30")
        self.mb_rsi_sell_min.pack(side=tk.LEFT, padx=(4, 2))

        self.mb_rsi_sell_max = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_sell_max.delete(0, tk.END)
        self.mb_rsi_sell_max.insert(0, "55")
        self.mb_rsi_sell_max.pack(side=tk.LEFT, padx=(2, 0))
        r_adv += 1

        # ADX trend szűrő
        adx_title_lbl = ttk.Label(
            adv,
            text="ADX trend szűrő (oldalazás ellen)",
            font=self.bold_font,
        )

        adx_box = ttk.Labelframe(adv, labelwidget=adx_title_lbl, padding=6)
        adx_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))
        adx_row = ttk.Frame(adx_box)
        adx_row.pack(anchor="w")

        self.mb_use_adx = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            adx_row,
            text="ADX filter bekapcsolása (csak ha ADX > küszöb)",
            variable=self.mb_use_adx,
            command=self._mb_toggle_adx_widgets,
        ).pack(side=tk.LEFT)

        ttk.Label(adx_row, text="ADX periódus:").pack(side=tk.LEFT, padx=(12, 2))
        self.mb_adx_len = ttk.Spinbox(adx_row, from_=5, to=50, increment=1, width=6)
        self.mb_adx_len.delete(0, tk.END)
        self.mb_adx_len.insert(0, "14")
        self.mb_adx_len.pack(side=tk.LEFT, padx=(0, 10))

        ttk.Label(adx_row, text="Min ADX küszöb:").pack(side=tk.LEFT, padx=(0, 2))
        self.mb_adx_min = ttk.Spinbox(adx_row, from_=5, to=60, increment=1, width=6)
        self.mb_adx_min.delete(0, tk.END)
        self.mb_adx_min.insert(0, "20")
        self.mb_adx_min.pack(side=tk.LEFT)

        r_adv += 1
        self._mb_toggle_adx_widgets()

        # HTF trend filter
        htf_title_lbl = ttk.Label(
            adv,
            text="HTF trend filter (EMA alapú)",
            font=self.bold_font,
        )
        htf_box = ttk.Labelframe(adv, labelwidget=htf_title_lbl, padding=6)
        htf_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))
        htf_row = ttk.Frame(htf_box)
        htf_row.pack(anchor="w")

        self.mb_use_htf = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            htf_row,
            text="HTF filter használata",
            variable=self.mb_use_htf,
            command=self._mb_toggle_htf_widgets,
        ).pack(side=tk.LEFT)

        ttk.Label(htf_row, text="  HTF TF:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_htf_tf = ttk.Combobox(
            htf_row,
            state="readonly",
            width=6,
            values=["15m", "30m", "1h", "4h", "1d"],
        )
        self.mb_htf_tf.set("15m")
        self.mb_htf_tf.pack(side=tk.LEFT)
        r_adv += 1

        # ATR menedzsment
        atr_title_lbl = ttk.Label(
            adv,
            text="ATR alapú menedzsment (TP1/TP2 + trailing)",
            font=self.bold_font,
        )

        atr_box = ttk.Labelframe(adv, labelwidget=atr_title_lbl, padding=6)
        atr_box.grid(row=r_adv, column=0, columnspan=2, sticky="we", pady=(8, 0))

        atr_row1 = ttk.Frame(atr_box)
        atr_row1.pack(anchor="w")

        self.mb_use_atr = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            atr_row1,
            text="ATR menedzsment használata",
            command=self._mb_on_atr_changed,
            variable=self.mb_use_atr,
        ).pack(side=tk.LEFT)

        ttk.Label(atr_row1, text="  ATR n:").pack(side=tk.LEFT, padx=(6, 2))
        self.mb_atr_n = ttk.Spinbox(atr_row1, from_=5, to=50, width=6)
        self.mb_atr_n.delete(0, tk.END)
        self.mb_atr_n.insert(0, "14")
        self.mb_atr_n.pack(side=tk.LEFT)

        atr_row2 = ttk.Frame(atr_box)
        atr_row2.pack(anchor="w", pady=(4, 0))

        ttk.Label(atr_row2, text="SL×").pack(side=tk.LEFT)
        self.mb_atr_mul_sl = ttk.Spinbox(atr_row2, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_atr_mul_sl.delete(0, tk.END)
        self.mb_atr_mul_sl.insert(0, "1.0")
        self.mb_atr_mul_sl.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(atr_row2, text="TP1×").pack(side=tk.LEFT)
        self.mb_atr_mul_tp1 = ttk.Spinbox(atr_row2, from_=0.1, to=10.0, increment=0.1, width=5)
        self.mb_atr_mul_tp1.delete(0, tk.END)
        self.mb_atr_mul_tp1.insert(0, "1.5")
        self.mb_atr_mul_tp1.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(atr_row2, text="TP2×").pack(side=tk.LEFT)
        self.mb_atr_mul_tp2 = ttk.Spinbox(atr_row2, from_=0.1, to=20.0, increment=0.1, width=5)
        self.mb_atr_mul_tp2.delete(0, tk.END)
        self.mb_atr_mul_tp2.insert(0, "2.5")
        self.mb_atr_mul_tp2.pack(side=tk.LEFT, padx=(2, 8))

        ttk.Label(atr_row2, text="Trail×").pack(side=tk.LEFT)
        self.mb_atr_mul_trail = ttk.Spinbox(atr_row2, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_atr_mul_trail.delete(0, tk.END)
        self.mb_atr_mul_trail.insert(0, "1.0")
        self.mb_atr_mul_trail.pack(side=tk.LEFT, padx=(2, 0))
        r_adv += 1

        # Cooldown
        ttk.Label(adv, text="Cooldown (s)", font=self.bold_font).grid(row=r_adv, column=0, sticky="w", pady=(8, 0))
        self.mb_cooldown_s = ttk.Spinbox(adv, from_=1, to=600, width=8)
        self.mb_cooldown_s.delete(0, tk.END)
        self.mb_cooldown_s.insert(0, "10")
        self.mb_cooldown_s.grid(row=r_adv, column=1, sticky="w", pady=(8, 0))
        r_adv += 1

        # ===== jobb oszlop: felül fülek (History / Bot napló), alul mini-diagram =====
        right = ttk.Frame(root)
        right.grid(row=0, column=1, sticky="nsew", padx=(6, 10), pady=10)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(0, weight=3)  # notebook (history+log)
        right.grid_rowconfigure(1, weight=2)  # chart

        # --- Fülrendszer: History + Bot napló ---
        right_nb = ttk.Notebook(right)
        right_nb.grid(row=0, column=0, sticky="nsew")

        # 1) Trade History (LIVE) fül
        tab_hist = ttk.Frame(right_nb)
        right_nb.add(tab_hist, text="Trade History (LIVE)")
        tab_hist.grid_columnconfigure(0, weight=1)
        tab_hist.grid_rowconfigure(0, weight=1)

        cols = ("timestamp", "side", "entry", "exit", "size", "lev", "fee", "pnl", "orderId")
        self._mb_hist_tv = ttk.Treeview(tab_hist, columns=cols, show="headings", height=10)
        for c, w, text in (
            ("timestamp", 160, "Időbélyeg"),
            ("side", 70, "Irány"),
            ("entry", 110, "Belépő ár"),
            ("exit", 110, "Kilépő ár"),
            ("size", 110, "Méret"),
            ("lev", 90, "Tőkeáttét"),
            ("fee", 90, "Díj"),
            ("pnl", 90, "PNL"),
            ("orderId", 180, "Order ID"),
        ):
            self._mb_hist_tv.heading(c, text=text)
            self._mb_hist_tv.column(c, width=w, anchor="center")
        self._mb_hist_tv.column("orderId", width=180, anchor="center", stretch=True)

        vsb = ttk.Scrollbar(tab_hist, orient="vertical", command=self._mb_hist_tv.yview)
        self._mb_hist_tv.configure(yscrollcommand=vsb.set)
        self._mb_hist_tv.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")

        # History segéd-struktúrák
        self._mb_hist_rows_by_oid = {}
        self._mb_hist_tv.bind("<Button-3>", self._mb_hist_on_rclick)

        # PnL-alapú sor-színezés (idempotens)
        try:
            self._mb_hist_tv.tag_configure("win", background="#d9ffdb")
            self._mb_hist_tv.tag_configure("loss", background="#ffd9d9")
            self._mb_hist_tv.tag_configure("win_floating", background="#f1fff3")
            self._mb_hist_tv.tag_configure("loss_floating", background="#fff1f1")
        except Exception:
            pass

        # 2) Bot napló fül
        tab_log = ttk.Frame(right_nb)
        right_nb.add(tab_log, text="Bot napló")
        tab_log.grid_columnconfigure(0, weight=1)
        tab_log.grid_rowconfigure(0, weight=1)
        self.mb_log = scrolledtext.ScrolledText(tab_log, wrap=tk.WORD)
        self.mb_log.grid(row=0, column=0, sticky="nsew")

        # --- Mini-diagram az aktuális párról (Dashboardhoz hasonló) ---
        ch_box = ttk.Labelframe(right, text="Diagram (aktuális pár)", padding=6)
        ch_box.grid(row=1, column=0, sticky="nsew", pady=(6, 0))
        self.mb_fig = Figure(figsize=(6, 2.4), dpi=100)
        self.mb_ax = self.mb_fig.add_subplot(111)
        self.mb_canvas = FigureCanvasTkAgg(self.mb_fig, master=ch_box)
        self.mb_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # --- Margin Bot belső flag-ek / állapotok ---
        self._mb_running = False
        self._mb_thread = None
        self._mb_kline_ws = None

        # Jel/cooldown állapot
        self._mb_last_cross_ts = 0
        self._mb_last_signal = "hold"
        self._mb_last_bar_ts = {}  # {(symbol, tf): ts}
        self._mb_lock = threading.Lock()

        # Szimulációs állapotok (ha még nem lettek máshol definiálva)
        if not hasattr(self, "_sim_pnl_usdt"):
            self._sim_pnl_usdt = Decimal("0")
        if not hasattr(self, "_sim_history"):
            self._sim_history = []  # list[dict]

        # kezdő tőkeáttét plafon
        self._mb_sync_lev_cap()

        # SL/TP/Trail init – a kezdeti állapotnak megfelelően
        self._mb_toggle_fixed_widgets()
        self._mb_toggle_atr_widgets()
        self._mb_toggle_brk_widgets()
        self._mb_toggle_live_widgets()
        self._mb_toggle_rsi_widgets()
        self._mb_toggle_htf_widgets()
        self._mb_toggle_zscore_widgets()

        # Chart frissítési intervallum (ms)
        self._mb_chart_interval_ms = 5000  # 5 mp

        # 1 másodperc múlva indul a periódikus frissítés
        self.root.after(1000, self._mb_chart_timer)

        # A szimbólumok betöltését is kicsit késleltetjük (pl. 500ms)
        self.root.after(500, lambda: threading.Thread(target=self._load_symbols_async, daemon=True).start())

        # ha TF vagy pár változik, frissítsünk
        try:
            self.mb_tf.bind("<<ComboboxSelected>>", lambda _e: self._mb_draw_chart())
            self.mb_symbol.bind("<<ComboboxSelected>>", lambda _e: self._mb_draw_chart())
            self.mt_symbol.bind("<<ComboboxSelected>>", lambda _e: self._mb_draw_chart())
        except Exception:
            pass

        # --- itt már MINDEN bal oldali widget létezik ---
        _bind_mousewheel_recursively(scroll_frame)

        if not hasattr(self, "_mb_stopping"):
            self._mb_stopping = False

    def _bg(self, fn, ok, err=None):
        def run():
            try:
                res = fn()
                self.root.after(0, lambda: ok(res))
            except Exception as e:
                if err:
                    self.root.after(0, lambda e=e: err(e))
        threading.Thread(target=run, daemon=True).start()

    ### --- """Minidiagram a Margin Bot fülön: Close + EMA-k + RSI (bot-féle, stabil eleje-vége).""" --- ###
    def _mb_draw_chart(self, lookback: int = 150):
        try:
            # Paraméterek kiolvasása (GUI-ból – EZ FŐSZÁLON FUT)
            symbol = normalize_symbol(self.mb_symbol.get())
            tf     = self.mb_tf.get()
            fa     = int(self.mb_ma_fast.get())
            slw    = int(self.mb_ma_slow.get())

            # --- OHLCV lekérés paraméterei ---
            limit = max(lookback, slw + 5)

            # --- WORKER: csak adatlekérés, MEHET háttérszálba ---
            def worker():
                try:
                    ohlcv = self._mb_get_ohlcv(symbol, tf, limit=limit)
                except Exception:
                    ohlcv = []
                return ohlcv

            # --- on_ok: adat megjött, INNENTŐL CSAK FŐSZÁLON fut (root.after) ---
            def on_ok(ohlcv):
                try:
                    if not ohlcv:
                        return

                    df = pd.DataFrame(ohlcv, columns=["ts", "o", "h", "l", "c", "v"])

                    # idő szerint növekvő sorrend (régi → új)
                    df = df.sort_values("ts").reset_index(drop=True)

                    # --- UTC → helyi idő konverzió ---
                    local_tz = datetime.datetime.now().astimezone().tzinfo
                    df["dt"] = (
                        pd.to_datetime(df["ts"], unit="ms", utc=True)
                          .dt.tz_convert(local_tz)
                          .dt.tz_localize(None)
                    )

                    # Close-ok
                    close_for_rsi = df["c"].astype(float).copy()   # RSI-hez
                    close_for_ema = close_for_rsi.copy()           # EMA + ár rajzhoz

                    # --- Websocket RT ár csak a chart/EMA-ra ---
                    try:
                        tws = getattr(self, "_ticker_ws", None)
                        if tws is not None:
                            rt = float(tws.get_last_price() or 0.0)
                            if rt > 0:
                                close_for_ema.iloc[-1] = rt
                                df.loc[df.index[-1], "c"] = rt
                    except Exception:
                        pass

                    # --- EMA-k ---
                    ema_f = close_for_ema.ewm(span=fa, adjust=False).mean()
                    ema_s = close_for_ema.ewm(span=slw, adjust=False).mean()

                    # --- RSI (bot-féle, stabil eleje + vége) ---
                    try:
                        rsi_len = int(self._mb_cfg.get("rsi_len", 14)
                                      if hasattr(self, "_mb_cfg") else 14)
                    except Exception:
                        rsi_len = 14

                    rsi_raw = None
                    rsi_plot = None
                    try:
                        if len(close_for_rsi) >= rsi_len:
                            rsi_raw = self._mb_rsi(close_for_rsi, n=rsi_len)
                            rsi_raw = pd.Series(rsi_raw.values, index=df.index)

                            rsi_plot = rsi_raw.copy()

                            # --- ELEJE: dinamikus, de konzervatív warmup ---
                            stable_window = 5          # ennyi egymás utáni "normális" RSI kell
                            min_warmup     = rsi_len   # legalább ennyi bar legyen elrejtve

                            warmup_n = len(rsi_raw)    # default: ha semmi nem ok, akkor semmit nem rajzolunk

                            if len(rsi_raw) >= rsi_len:
                                mask_ok = (~np.isnan(rsi_raw)) & (rsi_raw > 5.0) & (rsi_raw < 95.0)

                                found_idx = None
                                # keresünk egy olyan indexet, ahonnan indulva van stable_window db egymásutáni "ok" RSI
                                for i in range(0, len(rsi_raw) - stable_window + 1):
                                    if mask_ok.iloc[i:i+stable_window].all():
                                        found_idx = i
                                        break

                                if found_idx is not None:
                                    warmup_n = max(min_warmup, found_idx + 1)
                                else:
                                    warmup_n = min(rsi_len * 2, len(rsi_raw))

                            warmup_n = min(warmup_n, len(rsi_raw))
                            rsi_plot.iloc[:warmup_n] = np.nan

                            # --- VÉGE: ha akarod, visszarakhatod az aktuális gyertyára a NaN-t ---
                            # rsi_plot.iloc[-1] = np.nan

                            rsi_plot = rsi_plot.clip(0.0, 100.0)
                        else:
                            rsi_raw = None
                            rsi_plot = None
                    except Exception:
                        rsi_raw = None
                        rsi_plot = None

                    # --- Rajzolás (MINDEN Tk / mpl CSAK ITT, FŐSZÁLON!) ---
                    self.mb_ax.clear()

                    (line_close,) = self.mb_ax.plot(df["dt"], close_for_ema, label="Close")
                    (line_ema_f,) = self.mb_ax.plot(df["dt"], ema_f, label=f"EMA({fa})")
                    (line_ema_s,) = self.mb_ax.plot(df["dt"], ema_s, label=f"EMA({slw})")

                    if getattr(self, "mb_rsi_ax", None) is None:
                        self.mb_rsi_ax = self.mb_ax.twinx()
                    else:
                        self.mb_rsi_ax.clear()

                    if rsi_plot is not None:
                        (line_rsi,) = self.mb_rsi_ax.plot(df["dt"], rsi_plot, alpha=0.3, label="RSI")
                        self.mb_rsi_ax.set_ylim(0, 100)
                        self.mb_rsi_ax.axhline(30, linestyle="--", alpha=0.2)
                        self.mb_rsi_ax.axhline(70, linestyle="--", alpha=0.2)
                        self.mb_rsi_ax.set_yticks([])
                    else:
                        line_rsi = None

                    self.mb_ax.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))
                    self.mb_ax.set_title(symbol + " • " + tf)
                    self.mb_ax.grid(True, alpha=0.25)

                    handles = [line_close, line_ema_f, line_ema_s]
                    if line_rsi is not None:
                        handles.append(line_rsi)
                    labels = [h.get_label() for h in handles]
                    self.mb_ax.legend(handles, labels, loc="lower left", fontsize="small")

                    self.mb_canvas.draw_idle()

                except Exception as e:
                    # csendes – ne dobáljon fel ablakot
                    try:
                        self._safe_log(f"Chart hiba: {e}\n")
                    except Exception:
                        pass

            # --- on_err: háttérszál hibája, biztonságos log ---
            def on_err(e):
                try:
                    self._safe_log(f"Chart hiba (bg): {e}\n")
                except Exception:
                    pass

            # Adat a háttérben, rajz a főszálon
            self._bg(worker, on_ok, on_err)

        except Exception as e:
            try:
                self._safe_log(f"Chart hiba (külső): {e}\n")
            except Exception:
                pass

    def _mb_chart_timer(self):
        """MarginBot mini-chart periódikus frissítése a fő szálon."""
        try:
            self._mb_draw_chart()
        except Exception as e:
            # ha akarsz logolni:
            try:
                self.log(f"⚠ Chart frissítés hiba: {e}")
            except Exception:
                pass
        finally:
            # ha nem áll a bot, ütemezzük be a következő frissítést
            if not getattr(self, "_mb_stopping", False):
                self.root.after(
                    getattr(self, "_mb_chart_interval_ms", 5000),
                    self._mb_chart_timer
                )

    # --- Safe helpers: NaN/0 guard minden osztáshoz ---
    def _is_pos_num(self, x) -> bool:
        try:
            xx = float(x)
            return xx > 0 and xx == xx  # not NaN
        except Exception:
            return False

    def _sdiv(self, num: float, den: float, fallback: float = 0.0) -> float:
        """Safe division: ha den <= 0 vagy NaN → fallback."""
        try:
            d = float(den)
            if d <= 0 or d != d:
                return float(fallback)
            return float(num) / d
        except Exception:
            return float(fallback)

    # --- Elérhető egyenleg kijelzés frissítése (UI segédfüggvény) ---
    def _mb_refresh_available(self, _event=None):
        """
        A Margin Bot „Elérhető” címkéjének frissítése.
        - Először a cache-ből próbál olvasni.
        - Ha a cache üres (vagy hiányos), egy háttérszálon
          célzottan lekéri a szükséges margin (isolated/cross) adatot.
        - Nem hívja meg a teljes, lassú `refresh_all_funds_balances`-t.
        """
        try:
            if not getattr(self, "is_running", False):
                self.mb_avail_var.set("Indítsa a botot!")
                return

            if self.public_mode.get():
                self.mb_avail_var.set("N/A (public)")
                return

            # 1. Azonnali UI frissítés "Töltés..."-re
            self.mb_avail_var.set("Töltés...")

            # 2. Paraméterek kiolvasása a fő szálon
            sym = normalize_symbol(self.mb_symbol.get())
            base, quote = split_symbol(sym)
            mode = (self.mb_mode.get() or "isolated").lower()

        except Exception as e:
            self.mb_avail_var.set("Hiba (param)")
            self._safe_log(f"❌ _mb_refresh param hiba: {e}\n")
            return

        def worker():
            avail_quote = None
            try:
                # 3. Próba a cache-ből (gyors út) – OLVASÁS IS LOCK ALATT
                lock = getattr(self, "_ex_lock", None)
                if lock is not None:
                    with lock:
                        bc = dict(getattr(self, "_balance_cache", {}) or {})
                else:
                    bc = dict(getattr(self, "_balance_cache", {}) or {})

                iso_cache = bc.get("isolated", {})
                cross_cache = bc.get("cross", {})

                if mode == "isolated" and sym in iso_cache:
                    pack = iso_cache.get(sym, {})
                    if pack and (pack.get("quote") or {}).get("ccy") == quote.upper():
                        avail_quote = float((pack["quote"].get("avail") or 0.0))

                elif mode == "cross" and quote in cross_cache:
                    avail_quote = float((cross_cache.get(quote, {}) or {}).get("avail", 0.0))

                # 4. Ha a cache-ben volt, frissítjük a UI-t és kész
                if avail_quote is not None:
                    self.root.after(0, self.mb_avail_var.set, f"{avail_quote:.2f} {quote}")
                    return

                # 5. Cache miss: Célzott lekérés
                self._safe_log(
                    f"ℹ️ MarginBot egyenleg: cache miss ({mode}/{sym}), célzott lekérés...\n"
                )

                if mode == "isolated":
                    with self._ex_lock:
                        resp = self.exchange.fetch_isolated_accounts()
                        idata = resp.get("data", {}) if isinstance(resp, dict) else getattr(resp, "data", {}) or {}
                        assets = idata.get("assets", []) or []

                        if not hasattr(self, "_balance_cache"):
                            self._balance_cache = {}
                        if "isolated" not in self._balance_cache:
                            self._balance_cache["isolated"] = {}

                        for asset in assets:
                            symbol_from_asset = (asset.get("symbol") or "").upper()
                            if not symbol_from_asset:
                                continue

                            base_pack = asset.get("baseAsset", {}) or {}
                            quote_pack = asset.get("quoteAsset", {}) or {}

                            self._balance_cache["isolated"][symbol_from_asset] = {
                                "base": {
                                    "ccy": (base_pack.get("currency") or "").upper(),
                                    "avail": float(base_pack.get("available") or 0),
                                    "holds": float(base_pack.get("holds") or 0),
                                    "liability": float(base_pack.get("liability") or 0),
                                },
                                "quote": {
                                    "ccy": (quote_pack.get("currency") or "").upper(),
                                    "avail": float(quote_pack.get("available") or 0),
                                    "holds": float(quote_pack.get("holds") or 0),
                                    "liability": float(quote_pack.get("liability") or 0),
                                },
                            }

                            if symbol_from_asset == sym:
                                avail_quote = float(quote_pack.get("available") or 0.0)

                elif mode == "cross":
                    with self._ex_lock:
                        resp = self.exchange.fetch_cross_accounts()  # type: ignore[union-attr]
                        cdata = resp.get("data", {}) if isinstance(resp, dict) else {}
                        accounts = cdata.get("accounts", []) or cdata.get("accountList", []) or []

                        if not hasattr(self, "_balance_cache"):
                            self._balance_cache = {}
                        if "cross" not in self._balance_cache:
                            self._balance_cache["cross"] = {}

                        for a in accounts:
                            ccy = (a.get("currency") or a.get("currencyName") or "").upper()
                            if not ccy:
                                continue

                            avail = float(a.get("available", a.get("availableBalance", a.get("free", 0))) or 0)
                            holds = float(a.get("holds", a.get("holdBalance", 0)) or 0)
                            liab = float(a.get("liability", a.get("debt", 0)) or 0)

                            self._balance_cache["cross"][ccy] = {
                                "avail": avail,
                                "holds": holds,
                                "liability": liab,
                            }

                            if ccy == quote:
                                avail_quote = avail

                # 6. UI frissítés a lekért adattal
                if avail_quote is None:
                    avail_quote = 0.0
                self.root.after(0, self.mb_avail_var.set, f"{avail_quote:.2f} {quote}")

            except Exception as e:
                self.root.after(0, self.mb_avail_var.set, "Hiba (lekérés)")
                self._safe_log(f"❌ _mb_refresh_available hiba: {e}\n")

        # 7. A worker indítása háttérszálon
        threading.Thread(target=worker, daemon=True).start()

    # ---- Margin "beragadt" kötelezettségek rendezése (cross + isolated) ----
    def repay_stuck_margin(self):
        """
        Funds fülön lévő 'Beragadt margin kötelezettségek rendezése' gombhoz.

        Logika:
          - CROSS:  GET /api/v3/margin/accounts
                    data.accounts[*].{currency, liability, available}
          - ISOLATED: GET /api/v3/isolated/accounts
                      data.assets[*].symbol + baseAsset/quoteAsset.{currency, liability, available}

        Minden olyan sorra, ahol liability > 0 ÉS available > 0,
        repay-t küldünk max. min(liability, available) * 0.999 összeggel.

        Törlesztés:
          POST /api/v3/margin/repay

            Cross:
              {"currency": "USDT", "size": "0.1234"}

            Isolated:
              {"currency": "USDT", "size": "0.1234",
               "isolated": true, "symbol": "SOL-USDT"}
        """
        if self.public_mode.get():
            messagebox.showwarning(
                "Privát mód szükséges",
                "Kapcsold ki a publikus módot és állítsd be az API kulcsokat."
            )
            return

        def worker():
            try:
                ex = getattr(self, "exchange", None)
                if not ex:
                    raise RuntimeError("Nincs aktív exchange kliens.")

                repay_ops = []  # (scope, currency, symbol, liability, available, safe_amt)

                # ---------- 1) CROSS MARGIN: /api/v3/margin/accounts ----------
                try:
                    with self._ex_lock:
                        cross_raw = ex._rest_get(
                            "/api/v3/margin/accounts",
                            {"quoteCurrency": "USDT", "queryType": "MARGIN"},
                        )  # type: ignore[union-attr]

                    if isinstance(cross_raw, dict) and str(cross_raw.get("code", "")) == "200000":
                        data = cross_raw.get("data", {}) or {}
                        accounts = data.get("accounts", []) or []
                        for acc in accounts:
                            ccy = (acc.get("currency") or "").upper()
                            if not ccy:
                                continue
                            try:
                                liab = float(acc.get("liability") or 0.0)
                                avail = float(acc.get("available") or acc.get("availableBalance") or 0.0)
                            except Exception:
                                continue

                            if liab <= 0 or avail <= 0:
                                continue

                            raw_repay = min(liab, avail)
                            eps = 1e-8
                            safe_amt = max(0.0, raw_repay - eps) * 0.999
                            safe_amt = math.floor(safe_amt * 1e8) / 1e8

                            if safe_amt > 0:
                                repay_ops.append(("cross", ccy, None, liab, avail, safe_amt))
                    else:
                        # ha vmi más válasz jött, logoljuk
                        self.root.after(
                            0,
                            lambda r=cross_raw: (
                                self.funds_log.insert(
                                    tk.END,
                                    f"ℹ️ Cross margin account hívás nem 200000: {r!r}\n",
                                ),
                                self.funds_log.see(tk.END),
                            ),
                        )
                except Exception as e:
                    self.root.after(
                        0,
                        lambda e=e: (
                            self.funds_log.insert(
                                tk.END, f"❌ Cross margin account lekérdezés hiba: {e}\n"
                            ),
                            self.funds_log.see(tk.END),
                        ),
                    )

                # ---------- 2) ISOLATED MARGIN: /api/v3/isolated/accounts ----------
                try:
                    with self._ex_lock:
                        iso_raw = ex._rest_get(
                            "/api/v3/isolated/accounts",
                            {"quoteCurrency": "USDT", "queryType": "ISOLATED"},
                        )  # type: ignore[union-attr]

                    if isinstance(iso_raw, dict) and str(iso_raw.get("code", "")) == "200000":
                        data = iso_raw.get("data", {}) or {}
                        assets = data.get("assets", []) or []
                        for asset in assets:
                            sym = asset.get("symbol") or ""
                            if not sym:
                                continue

                            for key in ("baseAsset", "quoteAsset"):
                                node = asset.get(key) or {}
                                ccy = (node.get("currency") or "").upper()
                                if not ccy:
                                    continue
                                try:
                                    liab = float(node.get("liability") or 0.0)
                                    # v3: "available", v1: "availableBalance"
                                    avail = float(node.get("available") or node.get("availableBalance") or 0.0)
                                except Exception:
                                    continue

                                if liab <= 0 or avail <= 0:
                                    continue

                                raw_repay = min(liab, avail)
                                eps = 1e-8
                                safe_amt = max(0.0, raw_repay - eps) * 0.999
                                safe_amt = math.floor(safe_amt * 1e8) / 1e8

                                if safe_amt > 0:
                                    repay_ops.append(("isolated", ccy, sym, liab, avail, safe_amt))
                    else:
                        self.root.after(
                            0,
                            lambda r=iso_raw: (
                                self.funds_log.insert(
                                    tk.END,
                                    f"ℹ️ Isolated margin account hívás nem 200000: {r!r}\n",
                                ),
                                self.funds_log.see(tk.END),
                            ),
                        )
                except Exception as e:
                    self.root.after(
                        0,
                        lambda e=e: (
                            self.funds_log.insert(
                                tk.END, f"❌ Isolated margin account lekérdezés hiba: {e}\n"
                            ),
                            self.funds_log.see(tk.END),
                        ),
                    )

                # ---------- 3) Nincs semmi törleszthető? ----------
                if not repay_ops:
                    self.root.after(
                        0,
                        lambda: (
                            self.funds_log.insert(
                                tk.END,
                                "ℹ️ Nem találtam olyan cross/isolated devizát, "
                                "amelyre liability > 0 és pozitív available lenne. "
                                "Nincs automatikusan törleszthető margin kötelezettség.\n",
                            ),
                            self.funds_log.see(tk.END),
                        ),
                    )
                    return

                # ---------- 4) Repay hívások elküldése ----------
                for scope, ccy, sym, liab, avail, safe_amt in repay_ops:
                    body = {
                        "currency": ccy,
                        "size": f"{safe_amt:.8f}",
                    }
                    if scope == "isolated":
                        body["isIsolated"] = True
                        body["symbol"] = sym

                    try:
                        with self._ex_lock:
                            resp = ex._rest_post("/api/v3/margin/repay", body)  # type: ignore[union-attr]

                        def _log_repay(sc=scope, c=ccy, s=sym, l=liab, a=avail, amt=safe_amt, r=resp):
                            prefix = "Isolated" if sc == "isolated" else "Cross"
                            pair_info = f" [{s}]" if s else ""
                            self.funds_log.insert(
                                tk.END,
                                f"↪ {prefix} repay próbálkozás{pair_info} {c}: "
                                f"liability={l:.8f}, available={a:.8f}, küldött={amt:.8f}\n",
                            )

                            if isinstance(r, dict):
                                code = str(r.get("code", "?"))
                                msg = str(r.get("msg", "")) if r.get("msg") is not None else ""
                                if code == "200000":
                                    self.funds_log.insert(
                                        tk.END,
                                        f"✅ Repay sikeres{pair_info}: {c} {amt:.8f} – code={code}\n",
                                    )
                                elif code == "130203":
                                    self.funds_log.insert(
                                        tk.END,
                                        f"❌ Repay elutasítva{pair_info} {c} {amt:.8f}: 130203 – "
                                        f"Nincs elég margin egyenleg ehhez a törlesztéshez. msg='{msg}'\n",
                                    )
                                else:
                                    self.funds_log.insert(
                                        tk.END,
                                        f"❌ Repay elutasítva{pair_info} {c} {amt:.8f}: code={code} msg='{msg}'\n",
                                    )
                            else:
                                self.funds_log.insert(
                                    tk.END,
                                    f"✅ Repay elküldve (nem standard válasz){pair_info}: {c} {amt:.8f}\n",
                                )
                            self.funds_log.see(tk.END)

                        self.root.after(0, _log_repay)

                    except Exception as e:
                        self.root.after(
                            0,
                            lambda sc=scope, c=ccy, s=sym, e=e: (
                                self.funds_log.insert(
                                    tk.END,
                                    f"❌ Repay hiba "
                                    f"{'Isolated' if sc == 'isolated' else 'Cross'} "
                                    f"{(s + ' ') if s else ''}{c}: {e}\n",
                                ),
                                self.funds_log.see(tk.END),
                            ),
                        )

                # ---------- 5) Végén egyenleg frissítés ----------
                self.root.after(0, self.refresh_all_funds_balances)

            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Repay hiba", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    # --- Thread-safe logoló segéd ---
    def _safe_log(self, text: str):
        # 1. Előkészítés: időbélyeg és formázás
        try:
            now = datetime.datetime.now()
            ts_str = now.strftime("%Y-%m-%d %H:%M:%S")
            # Levágjuk a felesleges whitespace-t a végéről (pl. \n), hogy egységes legyen
            clean_text = text.rstrip()
            if not clean_text:
                return  # Üres sort ne naplózzunk

            # Formázott sor: [Dátum Idő] Üzenet
            log_entry = f"[{ts_str}] {clean_text}"
        except Exception:
            # Ha bármi hiba van a string formázással, fallback az eredetire
            log_entry = text.rstrip()
            now = datetime.datetime.now()

        # 2. Fájlba írás (azonnal, append módban)
        try:
            # Fájlnév: margin_bot_YYYY-MM-DD.log
            filename = f"margin_bot_{now.strftime('%Y-%m-%d')}.log"
            with open(filename, "a", encoding="utf-8") as f:
                f.write(log_entry + "\n")
        except Exception as e:
            print(f"Log file error: {e}")

        # 3. GUI frissítés (főszálon) + 500 soros limit
        try:
            def _gui_update():
                try:
                    # Beszúrás a végére (+ sortörés, mert a log_entry-ben nincs)
                    self.mb_log.insert(tk.END, log_entry + "\n")

                    # Limit ellenőrzése és törlés
                    # 'end-1c' indexe pl. '501.0' -> 501 sor
                    line_count_str = self.mb_log.index('end-1c').split('.')[0]
                    lines = int(line_count_str)

                    limit = 500
                    if lines > limit:
                        # Töröljük a legrégebbi sorokat
                        # lines - limit = hány sort kell törölni
                        # pl. 502 sor van, limit 500 -> 2 sort kell törölni.
                        # delete '1.0' től '3.0' -ig törli az 1. és 2. sort.
                        diff = lines - limit
                        self.mb_log.delete('1.0', f'{diff + 1}.0')

                    self.mb_log.see(tk.END)
                except Exception:
                    pass

            self.root.after(0, _gui_update)
        except Exception:
            pass

    # --- LIVE Trade History helper-ek ---
    def _mb_hist_add_open(self, *, order_id: str | None, side: str, entry: float,
                          size: float, lev: float, fee: float | None,
                          ts: float | None = None, pnl_est: float | None = None):
        """
        Új sor felvétele OPEN-nél.
        - fee: nyitási fee (QUOTE-ban) – becsült VAGY tényleges
        - pnl_est: becsült PnL nyitás után (rt ár alapján), ha None, üresen marad
        """
        try:
            ts = float(ts or time.time())
            ts_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts))
            oid = order_id or "-"
            row = (
                ts_str,                 # Timestamp
                side.upper(),           # Side
                f"{entry:.6f}",         # Entry
                "",                     # Exit (még üres)
                f"{size:.6f}",          # Size
                f"{lev:g}",             # Leverage
                ("" if fee is None else f"{float(fee):.6f}"),    # Fee (open est)
                ("" if pnl_est is None else f"{float(pnl_est):.6f}"),  # PnL (est)
                oid                     # orderId
            )

            def _ins():
                tv = getattr(self, "_mb_hist_tv", None)
                if tv is None:
                    return

                # rows_by_oid csak a GUI-szálon legyen használva
                if not hasattr(self, "_mb_hist_rows_by_oid"):
                    self._mb_hist_rows_by_oid = {}

                # Beszúráskor nincs színezés (nem végleges eredmény)
                iid = tv.insert("", "end", values=row)
                if oid != "-":
                    self._mb_hist_rows_by_oid[oid] = iid

            # worker hívhatja – itt csak GUI callback-et ütemezünk
            self.root.after(0, _ins)
        except Exception:
            pass

    def _mb_hist_update_exit(self, order_id: str | None, exit_px: float,
                             fee_total: float | None = None, pnl_final: float | None = None):
        """
        EXIT frissítése:
        - exit_px kitöltése
        - (opcionális) fee_total → 'Fee' oszlop felülírása a véglegessel
        - (opcionális) pnl_final → 'PnL' oszlop végleges értékre írása

        Hívható bármelyik szálról; a tényleges Treeview-módosítás a Tk főszálon fut.
        """
        try:
            if not order_id:
                return
            oid = str(order_id)
        except Exception:
            return

        def _upd():
            try:
                tv = getattr(self, "_mb_hist_tv", None)
                rows = getattr(self, "_mb_hist_rows_by_oid", {})

                if tv is None or not rows:
                    return

                iid = rows.get(oid)
                if not iid:
                    return

                vals = list(tv.item(iid, "values") or ())

                col = getattr(self, "_mb_hist_col_index", None)
                if not col:
                    # Fallback: klasszikus indexek (Timestamp,Side,Entry,Exit,Size,Leverage,Fee,PnL,orderId)
                    EXIT_IDX, FEE_IDX, PNL_IDX = 3, 6, 7
                else:
                    EXIT_IDX = col.get("exit", 3)
                    FEE_IDX  = col.get("fee", 6)
                    PNL_IDX  = col.get("pnl", 7)

                # biztos ami biztos: legyen elég hosszú a lista
                if len(vals) <= max(EXIT_IDX, FEE_IDX, PNL_IDX):
                    return

                vals[EXIT_IDX] = f"{float(exit_px):.6f}"
                if fee_total is not None:
                    vals[FEE_IDX] = f"{float(fee_total):.6f}"
                if pnl_final is not None:
                    vals[PNL_IDX] = f"{float(pnl_final):.6f}"

                tv.item(iid, values=tuple(vals))
                # PnL tag frissítése (ha van érték)
                try:
                    pnl_txt = vals[PNL_IDX]
                    _p = float(str(pnl_txt).replace(",", "")) if pnl_txt not in ("", None) else 0.0
                    if _p > 0:
                        tv.item(iid, tags=("win",))
                    elif _p < 0:
                        tv.item(iid, tags=("loss",))
                    else:
                        tv.item(iid, tags=())
                except Exception:
                    pass
            except Exception:
                pass

        try:
            # worker-safe
            self.root.after(0, _upd)
        except Exception:
            # ha valamiért nincs root/after, utolsó esély: közvetlen (remélhetőleg főszálon)
            _upd()

    def _mb_hist_apply_pnl(self, rt: float):
        """
        History táblában floating PnL frissítése egy adott realtime árral.
        Ezt a függvényt mindig a Tk főszálról hívd (pl. call_in_main-nal).
        """
        try:
            rt_val = float(rt or 0.0)
        except Exception:
            rt_val = 0.0

        if rt_val <= 0:
            return

        col = getattr(self, "_mb_hist_col_index", {})
        ENTRY_IDX = col.get("entry", 2); EXIT_IDX = col.get("exit", 3)
        SIZE_IDX  = col.get("size", 4);  SIDE_IDX = col.get("side", 1)
        FEE_IDX   = col.get("fee", 6);   PNL_IDX  = col.get("pnl", 7)

        tv = getattr(self, "_mb_hist_tv", None)
        if tv is None:
            return

        for iid in tv.get_children(""):
            vals = list(tv.item(iid, "values"))
            try:
                # zárt pozícióra nem számolunk floating PnL-t
                if vals[EXIT_IDX]:
                    continue

                entry = float(vals[ENTRY_IDX] or "0")
                size  = float(vals[SIZE_IDX]  or "0")
                side  = str(vals[SIDE_IDX]).strip().upper()
                fee_s = (vals[FEE_IDX] or "").strip()
                fee_est = float(fee_s) if fee_s not in ("", None) else 0.0

                gross = (rt_val - entry) * size * (1 if side == "BUY" else -1)
                vals[PNL_IDX] = f"{(gross - fee_est):.6f}"
                tv.item(iid, values=tuple(vals))
                # PnL tag frissítése (floating PnL alapján)
                try:
                    pnl_txt = vals[PNL_IDX]
                    _p = float(str(pnl_txt).replace(",", "")) if pnl_txt not in ("", None) else 0.0
                    if _p > 0:
                        tv.item(iid, tags=("win_floating",))
                    elif _p < 0:
                        tv.item(iid, tags=("loss_floating",))
                    else:
                        tv.item(iid, tags=())
                except Exception:
                    pass
            except Exception:
                continue

    def _mb_hist_on_rclick(self, event):
        """Jobb klikk a LIVE History táblán – kontextusmenü (csak a kattintott sorra)."""
        tv = getattr(self, "_mb_hist_tv", None)
        if tv is None:
            return

        row_id = tv.identify_row(event.y)
        if not row_id:
            return

        # Jelöld ki a sort, amin jobb klikkeltél
        tv.selection_set(row_id)

        vals = tv.item(row_id, "values") or ()
        # Várjuk: (timestamp, side, entry, exit, size, lev, fee, pnl, orderId)
        if len(vals) < 9:
            return

        ts, side, entry, exit_px, size, lev, fee, pnl, oid = vals
        exit_px_s = str(exit_px or "").strip()
        status = "open" if exit_px_s == "" else "closed"

        menu = tk.Menu(tv, tearoff=0)
        menu.add_command(
            label="Részletek…",
            command=lambda row_vals=vals: self._mb_hist_show_details(row_vals)
        )

        # Manuális zárás csak NYITOTT pozícióra legyen elérhető
        if status == "open":
            menu.add_command(
                label="Manuális zárás (LIVE)",
                command=lambda oid=str(oid): self._mb_hist_manual_close(oid)
            )

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _mb_hist_show_details(self, row_vals):
        """Részletek egy history sorhoz – közvetlenül a Treeview értékeiből."""
        try:
            ts, side, entry, exit_px, size, lev, fee, pnl, oid = row_vals
        except Exception:
            messagebox.showinfo("Pozíció részletei", "Nem sikerült beolvasni a sor adatait.")
            return

        exit_s = str(exit_px or "").strip()
        status = "open" if exit_s == "" else "closed"

        lines = [
            f"Időbélyeg: {ts}",
            f"Irány: {side}",
            f"Státusz: {status}",
            f"Belépő ár: {entry}",
            f"Kilépő ár: {exit_s or '-'}",
            f"Méret: {size}",
            f"Tőkeáttét: {lev}",
            f"Díj: {fee}",
            f"PNL: {pnl}",
            f"Order ID: {oid}",
        ]

        messagebox.showinfo("Pozíció részletei", "\n".join(lines))

    def _mb_hist_manual_close(self, oid: str):
        """Manuális LIVE zárás a history táblából jobb klikkre (csak a kijelölt pozíció!)."""
        oid = str(oid)

        # 1) History sorból kinyerünk infot (exit ár alapján eldöntjük, nyitott-e)
        tv = getattr(self, "_mb_hist_tv", None)
        if not tv:
            return

        # Find tree item by oid (orderId oszlop = index 8)
        row_id = None
        for rid in tv.get_children(""):
            vals = tv.item(rid, "values") or ()
            if len(vals) >= 9 and str(vals[8]) == oid:
                row_id = rid
                break

        if not row_id:
            messagebox.showerror("Manuális zárás", f"Nem találom a history sort ehhez az OID-hoz:\n{oid}")
            return

        vals = tv.item(row_id, "values") or ()
        if len(vals) < 9:
            messagebox.showerror("Manuális zárás", "A history sor formátuma nem megfelelő.")
            return

        ts, side_txt, entry_s, exit_s, size_s, lev_s, fee_s, pnl_s, oid_row = vals
        exit_s = str(exit_s or "").strip()
        status = "open" if exit_s == "" else "closed"

        if status != "open":
            messagebox.showinfo("Manuális zárás", "Ez a pozíció már zárva van a history szerint.")
            return

        # 2) Megkeressük a szimulált pozíciót OID alapján – LOCK alatt keressük a listában
        sim_index = None
        sim_side_for_close = None  # 'buy' (long) vagy 'sell' (short)
        sim_pos = None

        with self._mb_lock:
            for lst_name, logical_side in [("_sim_pos_long", "buy"), ("_sim_pos_short", "sell")]:
                lst = getattr(self, lst_name, [])
                for i, pos in enumerate(lst):
                    if str(pos.get("oid")) == oid:
                        sim_index = i
                        sim_side_for_close = logical_side
                        sim_pos = pos
                        break
                if sim_pos is not None:
                    break

        if sim_index is None or sim_side_for_close is None or sim_pos is None:
            messagebox.showerror("Manuális zárás", "Nem találom a szimulált pozíciót ehhez az OID-hoz.")
            return

        # 3) Megerősítés – méret/entry a szimulált poziból (ez már lockon kívül olvasható snapshotként)
        qty = sim_pos.get("size")
        entry = sim_pos.get("entry")

        # Symbol: a MarginBot aktuális párja / cfg-je
        try:
            symbol = normalize_symbol(
                self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL))
            )
        except Exception:
            cfg = getattr(self, "_mb_cfg", {}) or {}
            symbol = cfg.get("symbol") or DEFAULT_SYMBOL

        if not messagebox.askyesno(
            "Manuális zárás (LIVE)",
            f"Biztosan zárod ezt a pozíciót?\n\n"
            f"Symbol: {symbol}\n"
            f"Irány: {sim_side_for_close.upper()}\n"
            f"Méret: {qty}\n"
            f"Entry: {entry}\n\n"
            f"OID: {oid}"
        ):
            return

        # 4) Aktuális ár (px_for_mgmt) – egységes árlekérdezés (WS → cache → REST)
        try:
            last_px = float(self.get_best_price(symbol))
        except Exception as e:
            self._safe_log(f"⚠ Manuális zárás – árlekérdezési hiba: {e}\n")
            messagebox.showerror("Manuális zárás", f"Nem sikerült lekérni az aktuális árat:\n{e}")
            return

        if (not last_px) or not (last_px == last_px) or last_px <= 0:
            self._safe_log("⚠ Manuális zárás – érvénytelen ár (get_best_price 0/NaN).\n")
            messagebox.showerror("Manuális zárás", "Nem sikerült értelmes aktuális árat lekérni.")
            return

        # 5) Margin mód + leverage a cfg-ből
        cfg = getattr(self, "_mb_cfg", {}) or {}
        mode = cfg.get("mode", "isolated")
        lev = int(cfg.get("leverage", 10))

        # 6) LIVE zárás CSAK erre a pozícióra
        ok_live = False
        try:
            ok_live = self._live_close_pos(
                side=sim_side_for_close,  # a POZÍCIÓ eredeti nyitó iránya
                pos=sim_pos,
                close_px=last_px,
                symbol=symbol,
                mode=mode,
                lev=lev,
                is_sl_tp=False,
                is_manual=True,
            )
        except Exception as e:
            self._safe_log(f"❌ Manuális LIVE zárási hiba (history): {e}\n")

        if not ok_live:
            messagebox.showerror("Manuális zárás", "A LIVE zárás nem sikerült. Részletek a logban.")
            return

        # 7) SIM zárás – EGYETLEN pozícióra
        try:
            self._close_sim_by_index(
                side=sim_side_for_close,
                idx=sim_index,
                exit_px=last_px,
                reason="manual_hist_close",
                pos_obj=sim_pos,
            )
        except Exception as e:
            self._safe_log(f"⚠️ Manuális SIM zárás hiba (history): {e}\n")

        messagebox.showinfo("Manuális zárás", "A pozíció zárási megbízása elküldve (LIVE + SIM).")

    # === ORDER SANITIZER: lot_step/price_step/minBase/minFunds + padlózás ===
    def _mb_sanitize_order(
        self, *,
        symbol: str,
        side: str,
        price: float | None,
        size_base: float | None,
        funds_quote: float | None
    ):
        """
        Visszaadja a (size_base, funds_quote) tisztított értékeket, vagy (None, None)-t, ha nem küldhető.
        - size_base: lot_step-re padlózva, és minBase felett
        - funds_quote: quote_step-re padlózva, és minFunds felett
        - BUY-nál, ha price rendelkezésre áll: funds→méret becslés lot_step-re padlózva; ha az < minBase → eldob.
        - Nem emelünk felfelé minimum fölé – ha alatta van, eldobjuk.
        """
        # --- Market lépésközök / min értékek beolvasása ---
        try:
            lot_step_f, price_step_f, min_base_f, min_funds_f, quote_step_f = self._mb_get_market_steps(symbol)
        except Exception:
            lot_step_f = price_step_f = None
            min_base_f = min_funds_f = None
            quote_step_f = 0.01

        # --- float → Decimal normalizálás ---
        def _to_dec_or_none(v):
            if v is None:
                return None
            try:
                return D(v)
            except Exception:
                try:
                    return D(str(v))
                except Exception:
                    return None

        lot_step   = _to_dec_or_none(lot_step_f)   if lot_step_f   else None
        price_step = _to_dec_or_none(price_step_f) if price_step_f else None
        min_base   = _to_dec_or_none(min_base_f)   if min_base_f   else None
        min_funds  = _to_dec_or_none(min_funds_f)  if min_funds_f  else None
        quote_step = _to_dec_or_none(quote_step_f) if quote_step_f else _to_dec_or_none("0.01")

        if lot_step is not None and lot_step <= 0:
            lot_step = None
        if price_step is not None and price_step <= 0:
            price_step = None
        if quote_step is not None and quote_step <= 0:
            quote_step = None

        sb = _to_dec_or_none(size_base)
        fq = _to_dec_or_none(funds_quote)
        px = _to_dec_or_none(price)

        # --- Decimal floor/ceil helper lépésközre ---
        def _floor_dec_dec(x: Decimal | None, step: Decimal | None) -> Decimal | None:
            if x is None:
                return None
            if not step or step <= 0:
                return x
            try:
                q = step
                return (x / q).to_integral_value(rounding=ROUND_FLOOR) * q
            except (InvalidOperation, ZeroDivisionError):
                return None

        def _ceil_dec_dec(x: Decimal | None, step: Decimal | None) -> Decimal | None:
            if x is None:
                return None
            if not step or step <= 0:
                return x
            try:
                q = step
                return (x / q).to_integral_value(rounding=ROUND_CEILING) * q
            except (InvalidOperation, ZeroDivisionError):
                return None

        # --- Safety faktor (Decimal-ben) ---
        safety = D("1.0")
        try:
            s_raw = os.getenv("MB_CLOSE_FUNDS_SAFETY", "1.015")
            safety = D(str(s_raw))
            if safety < D("1"):
                safety = D("1")
        except Exception:
            safety = D("1.015")

        # --- BUY oldali speciális ág: ha nincs funds, de van size és ár → size→funds konverzió záráshoz ---
        #     Cél: Market BUY-hoz a tőzsde funds-ot vár; a worker és a live close size-ot ad át → itt alakítjuk át.
        if side == "buy" and fq is None and sb is not None and px is not None and px > 0:
            try:
                # 1) a size-et előbb lot_step-re padlózzuk
                if lot_step:
                    sb = _floor_dec_dec(sb, lot_step)
                if sb is not None and sb > 0:
                    # 2) funds becslés: size * price * safety, quote_step-re felfelé kerekítve
                    est_f = sb * px * safety
                    fq = _ceil_dec_dec(est_f, quote_step)
                    # 3) minFunds guard
                    if fq is not None and min_funds and fq < min_funds:
                        fq = None
                    # 4) minBase guard visszaellenőrzéssel: (floor(fq/price, lot_step) >= min_base)
                    if fq is not None and lot_step and px is not None and px > 0 and min_base:
                        est_size = _floor_dec_dec(fq / px, lot_step)
                        if est_size is None or est_size < min_base:
                            fq = None
                    # BUY marketnél innentől funds az elsődleges, a size-ot nem küldjük
                    sb = None
            except Exception:
                # ha bármi gond, essünk vissza az eredeti (alább lévő) ágakra
                pass

        # --- BASE (méret) tisztítás (SELL oldali küldéshez) ---
        if sb is not None:
            try:
                if lot_step:
                    sb = _floor_dec_dec(sb, lot_step)
            except Exception:
                sb = None

            # minBase guard – nem emelünk fel, ha alatta van → eldob
            try:
                if sb is None or sb <= 0:
                    sb = None
                elif min_base and sb < min_base:
                    sb = None
            except Exception:
                sb = None

        # --- FUNDS (QUOTE) tisztítás (BUY oldali küldéshez) ---
        if fq is not None:
            try:
                if fq <= 0:
                    fq = None
                else:
                    # exchange szerinti quote_step-re padlózás (nem fix 0.01!)
                    fq = _floor_dec_dec(fq, quote_step)
                    # minFunds guard – ha alatta, eldob
                    if fq is not None and min_funds and fq < min_funds:
                        fq = None
                    # minBase guard a funds→méret becslésével (ha van ár)
                    if fq is not None and px is not None and px > 0 and lot_step:
                        est_size = _floor_dec_dec(fq / px, lot_step)
                        if est_size is not None and min_base and est_size < min_base:
                            fq = None
            except Exception:
                fq = None

        # Ha mindkettő None → nem küldhető
        if sb is None and fq is None:
            return None, None

        # Visszatérés float-ként, hogy a meglévő kódot ne kelljen átírni
        sb_out = float(sb) if sb is not None else None
        fq_out = float(fq) if fq is not None else None
        return sb_out, fq_out

    def mb_start(self):
        """Margin bot indítás (dry-runban is futhat)."""
        self._mb_stopping = False   # biztos ami biztos
        self._mb_summary_done = False
        self._mb_first_cycle = True  # első ciklus ne aludjon same-bar miatt

        # bezárás-kezelés egyszeri bekötése
        try:
            self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        except Exception:
            pass

        if getattr(self, "_mb_running", False):
            self._safe_log("⚠️ A bot már fut.\n")
            return

        if self.exchange is None:
            try:
                with self._ex_lock:
                    self.exchange = KucoinSDKWrapper(public_mode=self.public_mode.get(), log_fn=self.log)
                self.log(
                    f"🔧 MarginBot: exchange inicializálva "
                    f"(dry-run: {self.mb_dry.get()}, public_mode: {self.public_mode.get()})"
                )
            except Exception as e:
                messagebox.showerror("Hiba", f"Exchange nincs inicializálva: {e}")
                return

        # biztosítsuk, hogy legyen lock, mielőtt bármit resetelünk
        if not hasattr(self, "_mb_lock"):
            self._mb_lock = threading.Lock()

        # --- Reset és DB betöltés ---  (LOCK ALATT)
        with self._mb_lock:
            # 1. Lista reset, mint eddig
            self._sim_pos_long = []
            self._sim_pos_short = []
            self._sim_history = []
            self._sim_pnl_usdt = Decimal('0')

            # Pool attribútumok törlése, hogy a worker újraépítse
            try:
                delattr(self, "_pool_balance_quote")
                delattr(self, "_pool_used_quote")
            except Exception:
                pass

            # Egyéb belső állapotok resetje (meglévő kódod)
            if hasattr(self, "_mb_last_bar_ts"):
                self._mb_last_bar_ts = {}
            if hasattr(self, "_mb_last_rt_px"):
                self._mb_last_rt_px = {}

            # 2. ÚJ RÉSZ: Pozíciók betöltése DB-ből (CSAK ÉLES MÓDBAN!)
            used_capital = 0.0
            
            # Ellenőrizzük a Dry Run állapotát a GUI változóból (biztonságos getterrel is lehetne, de mb_dry tk.BooleanVar)
            try:
                is_dry = bool(self.mb_dry.get())
            except Exception:
                is_dry = True

            if not is_dry:
                try:
                    open_trades = self.db.get_open_positions()
                    restored_count = 0

                    # A betöltés előtt olvassuk ki a jelenlegi párt a GUI-ból
                    current_symbol_norm = normalize_symbol(self.mb_symbol.get())

                    for pos in open_trades:
                        # BIZTONSÁGI SZŰRÉS: csak az aktuális párral egyezőeket vesszük fel
                        db_symbol = normalize_symbol(pos.get('symbol', ''))

                        if db_symbol != current_symbol_norm:
                            self._safe_log(
                                f"⚠️ Eltérő pár a DB-ben ({db_symbol}) vs GUI ({current_symbol_norm}) - pozíció kihagyva.\n"
                            )
                            continue

                        side = pos.get('side')
                        if side == 'buy':
                            self._sim_pos_long.append(pos)
                        elif side == 'sell':
                            self._sim_pos_short.append(pos)

                        # Pool számítás korrekció
                        commit = float(pos.get('commit_usdt', 0.0))
                        fee_res = float(pos.get('fee_reserved', 0.0))
                        used_capital += (commit + fee_res)
                        restored_count += 1

                        # --- GUI History frissítése a visszaállított pozíciókkal ---
                        try:
                            # 1) Leverage becslés (ha nincs tárolva)
                            p_size   = float(pos.get('size', 0.0))
                            p_entry  = float(pos.get('entry', 0.0))
                            p_commit = float(pos.get('commit_usdt', 0.0))
                            
                            p_lev = 1.0
                            if p_commit > 0:
                                # lev = notional / margin
                                p_lev = (p_size * p_entry) / p_commit
                            
                            # Kerekítés egészre, ha közel van (pl. 9.99 -> 10)
                            if abs(p_lev - round(p_lev)) < 0.1:
                                p_lev = float(round(p_lev))

                            # 2) Fee meghatározása (actual > est > reserved)
                            p_fee = float(pos.get('fee_open_actual', 0.0))
                            if p_fee <= 0:
                                p_fee = float(pos.get('fee_open_est', 0.0))
                            if p_fee <= 0:
                                p_fee = float(pos.get('fee_reserved', 0.0))

                            # 3) Hozzáadás a history-hoz (PnL még üres/becsült)
                            # A ts lehet float vagy string, kezeljük rugalmasan
                            p_ts = pos.get('ts')
                            
                            self._mb_hist_add_open(
                                order_id=pos.get('oid'),
                                side=side,
                                entry=p_entry,
                                size=p_size,
                                lev=p_lev,
                                fee=p_fee,
                                ts=p_ts,
                                pnl_est=None # Majd a következő árfrissítésnél kiszámolja
                            )
                        except Exception as e:
                            self._safe_log(f"⚠️ History GUI restore hiba ({pos.get('oid')}): {e}\n")

                    if restored_count:
                        self._safe_log(
                            f"♻️ DB-ből visszaállítva: {restored_count} nyitott pozíció ({current_symbol_norm}).\n"
                        )

                except Exception as e:
                    self._safe_log(f"❌ Hiba a DB betöltésekor: {e}\n")
                    used_capital = 0.0  # Fallback
            else:
                self._safe_log("ℹ️ Dry Run mód aktív – DB visszaállítás átugorva.\n")

            # belső állapotok, ha hiányoznának
            if not hasattr(self, "_sim_pnl_usdt"):
                self._sim_pnl_usdt = Decimal('0')
            if not hasattr(self, "_sim_pos_long"):
                self._sim_pos_long = []
            if not hasattr(self, "_sim_pos_short"):
                self._sim_pos_short = []
            if not hasattr(self, "_mb_last_bar_ts"):
                self._mb_last_bar_ts = {}
            if not hasattr(self, "_mb_last_cross_ts"):
                self._mb_last_cross_ts = 0
            if not hasattr(self, "_mb_last_signal"):
                self._mb_last_signal = "hold"

        # lock-on KÍVÜL tároljuk el, hogy a worker fel tudja használni
        self._restored_pool_usage = used_capital

        # --- CFG SNAPSHOT: minden UI-olvasás itt, FŐ SZÁLBAN! ---
        try:
            new_cfg = self._mb_build_cfg()
            # cfg írása is lock alatt, hogy konzisztens legyen a worker _load_cfg()-jével
            with self._mb_lock:
                self._mb_cfg = new_cfg
            self._safe_log(f"🧩 MarginBot cfg snapshot: {self._mb_cfg}\n")
        except Exception as e:
            self._safe_log(f"❌ MarginBot cfg építési hiba: {e}\n")
            messagebox.showerror("Hiba", f"MarginBot beállítások nem olvashatók ki: {e}")
            return

        self._mb_running = True
        self.mb_start_btn.configure(state=tk.DISABLED)
        self.mb_stop_btn.configure(state=tk.NORMAL)
        self._safe_log("▶️ Bot indul…\n")

        def _loop():
            try:
                self._mb_worker()
            except Exception as e:
                self._safe_log(f"❌ Bot hiba: {e}\n")
            finally:
                self._mb_running = False
                self.root.after(
                    0,
                    lambda: (
                        self.mb_start_btn.configure(state=tk.NORMAL),
                        self.mb_stop_btn.configure(state=tk.DISABLED),
                    ),
                )

        self._mb_thread = threading.Thread(target=_loop, daemon=True)
        self._mb_thread.start()

    def mb_stop(self):
        """Margin bot leállítása + biztonságos pozíciózárás (SIM/LIVE – egységesen, központi close használatával)."""
        if not getattr(self, "_mb_running", False):
            self._safe_log("ℹ️ A bot nem fut.\n")
            return

        # manuális leállítás jelző + futás megállítása
        self._mb_stopping = True
        try:
            time.sleep(0.1)
        except Exception:
            pass
        self._mb_running = False

        self._safe_log("⏹️ Bot leállítása folyamatban...\n")

        try:
            sym   = normalize_symbol(self._mb_get_str("mb_symbol", self._mb_get_str("mt_symbol", DEFAULT_SYMBOL)))
            dry   = self._mb_get_bool("mb_dry", True)
            lev   = self._mb_get_int("mb_leverage", 10)
            mode  = self._mb_get_str("mb_mode", "isolated")

            # Utolsó ismert élő ár – egységes helperrel: WS → cache → REST
            last_px = None
            try:
                rt = float(self.get_best_price(sym))
                if self._is_pos_num(rt) and rt > 0:
                    last_px = rt
            except Exception:
                last_px = None

            if last_px is None or last_px <= 0:
                self._safe_log("⚠️ Ár lekérés nem sikerült, fallback az entry/peak alapján.\n")

            # Mindkét oldal zárása egységesen, SNAPSHOT segítségével (race condition elkerülése)
            for side in ("buy", "sell"):
                # snapshot a SIM pozíciókról lock alatt
                with self._mb_lock:
                    if side == "buy":
                        snapshot = list(self._sim_pos_long)
                    else:
                        snapshot = list(self._sim_pos_short)

                for pos in snapshot:
                    try:
                        # ár fallback: last_px -> peak -> entry
                        px = float(
                            last_px
                            if last_px is not None and last_px > 0
                            else pos.get("peak", pos.get("entry", 0.0))
                        )

                        close_side = "sell" if side == "buy" else "buy"
                        self._safe_log(
                            f"🔻 Pozíció zárása ({close_side.upper()}) @ {px:.6f} | dry={dry}\n"
                        )

                        if dry:
                            # SIM: központi záró helperrel (history/pool/fee konzisztensek),
                            # pos_obj alapján keresi meg az aktuális indexet, így nem zavarja a GUI-s törlés
                            try:
                                self._close_sim_by_index(
                                    side=side,
                                    idx=-1,
                                    exit_px=px,
                                    reason="mb_stop",
                                    pos_obj=pos,
                                )
                            except Exception as e:
                                self._safe_log(f"⚠️ SIM stop zárás hiba: {e}\n")
                            continue

                        # LIVE eset – KIZÁRÓLAG a központi _live_close_pos hívódik
                        ok = False
                        try:
                            ok = self._live_close_pos(
                                side=side,
                                pos=pos,
                                close_px=px,
                                symbol=sym,
                                mode=mode,
                                lev=lev,
                                is_sl_tp=False,
                                is_manual=True,
                            )
                        except Exception as e:
                            self._safe_log(f"❌ LIVE zárási hiba (stop): {e}\n")
                            ok = False

                        if ok:
                            # csak sikeres LIVE zárás után tükörzárunk a SIM-ben
                            try:
                                self._close_sim_by_index(
                                    side=side,
                                    idx=-1,
                                    exit_px=px,
                                    reason="mb_stop",
                                    pos_obj=pos,
                                )
                            except Exception as e:
                                self._safe_log(f"⚠️ SIM tükrözés hiba (stop): {e}\n")
                        else:
                            self._safe_log("❗ LIVE zárás sikertelen – a pozíció nyitva marad.\n")

                    except Exception as e:
                        self._safe_log(f"❌ Stop loop hiba (side={side}): {e}\n")
                        continue

            # összegzés (egyszer)
            try:
                self._mb_do_summary_once("mb_stop")
            except Exception as e:
                self._safe_log(f"⚠️ Összegzés hiba (stop): {e}\n")

        except Exception as e:
            self._safe_log(f"❌ Stop során hiba: {e}\n")

        # szál lecsatlakoztatás (ha még él)
        try:
            if hasattr(self, "_mb_thread") and self._mb_thread.is_alive():
                self._mb_thread.join(timeout=1.0)
        except Exception:
            pass

        self._mb_stopping = False

    def mb_reload_cfg(self, silent: bool = False):
        """MarginBot cfg újraépítése futás közben – CSAK fő szálról hívd (UI gomb / callback)."""
        try:
            new_cfg = self._mb_build_cfg()
        except Exception as e:
            # Ha valami nem olvasható ki az UI-ból
            self._safe_log(f"❌ MarginBot cfg újraépítési hiba: {e}\n")
            messagebox.showerror("Hiba", f"MarginBot beállítások újraépítése sikertelen: {e}")
            return

        # Egyszerűen lecseréljük a referenciát – worker a következő ciklusban már ezt fogja látni
        # Írás lock alatt, mert a worker _mb_lock-kal olvassa.
        with self._mb_lock:
            self._mb_cfg = new_cfg

        if not silent:
            self._safe_log("♻️ MarginBot cfg frissítve futás közben.\n")

    def _close_sim_by_index(self, side: str, idx: int, exit_px: float, reason: str = "", pos_obj=None):
        """
        Egy szimulált pozíció lezárása index alapján.
        - side: 'buy' → _sim_pos_long, 'sell' → _sim_pos_short
        - MINDEN lista- és pool/pnl művelet self._mb_lock alatt történik.
        - pos_obj: ha meg van adva, identity alapján ellenőrizzük, hogy tényleg azt a
          pozíciót zárjuk, amit a hívó oldalán kezeltünk. Ha közben a lista
          eltolódott vagy a pozíció már kikerült, akkor csendben return.
        """
        with self._mb_lock:
            lst = self._sim_pos_long if side == 'buy' else self._sim_pos_short

            # Thread-safe ellenőrzés: létezik-e még az index?
            if idx < 0 or idx >= len(lst):
                # Ha van pos_obj, próbáljuk identity alapján megkeresni
                if pos_obj is not None:
                    try:
                        idx = lst.index(pos_obj)
                    except ValueError:
                        # már nincs benne → valaki más bezárta
                        return
                else:
                    # se érvényes index, se objektum → nincs teendő
                    return

            pos = lst[idx]

            # Ha van pos_obj, ellenőrizzük, hogy tényleg ugyanarra mutat-e
            if pos_obj is not None and pos is not pos_obj:
                # még egyszer megpróbálhatjuk identity alapján (óvatosságból),
                # de szigorúan véve ez már opcionális
                try:
                    idx = lst.index(pos_obj)
                    pos = lst[idx]
                except ValueError:
                    return

            entry = float(pos.get('entry', 0.0))
            sz    = float(pos.get('size', 0.0))
            gross = (exit_px - entry) * sz * (1 if side == 'buy' else -1)
            fee_rate = self._mb_get_taker_fee()
            f_open, f_close, f_total = self._mb_sum_fee_actual_or_est(pos, exit_px, fee_rate)

            # Pénzügyi összesítők: Decimal (stabil, nem driftel hosszú futás alatt)
            pnl = (Decimal(str(gross)) - Decimal(str(f_total)))

            self._sim_pnl_usdt       = (Decimal(str(getattr(self, "_sim_pnl_usdt", 0))) + pnl)
            self._pool_balance_quote = (Decimal(str(getattr(self, "_pool_balance_quote", 0))) + pnl)

            used_delta = (Decimal(str(float(pos.get('commit_usdt', 0.0)) or 0.0)) +
                          Decimal(str(float(pos.get('fee_reserved', 0.0)) or 0.0)))
            self._pool_used_quote    = (Decimal(str(getattr(self, "_pool_used_quote", 0))) - used_delta)

            # clamp: ne menjen 0 alá
            if self._pool_used_quote < 0:
                self._pool_used_quote = Decimal('0')

            total_pnl    = float(self._sim_pnl_usdt)
            pool_used    = float(self._pool_used_quote)
            pool_balance = float(self._pool_balance_quote)

            # SYMBOL: ne Tk widgetből, hanem cfg-ből, lock alatt
            try:
                cfg_sym = getattr(self, "_mb_cfg", {}) or {}
                symbol_safe = normalize_symbol(cfg_sym.get("symbol", DEFAULT_SYMBOL))
            except Exception:
                symbol_safe = "UNKNOWN"

            # Mielőtt törlöd a listából (del lst[idx]), mentsd el az OID-t
            try:
                closed_oid = str(pos.get('oid') or pos.get('order_id') or pos.get('id'))
            except Exception:
                closed_oid = None

            try:
                self._sim_history.append({
                    "partial": False,
                    "symbol": symbol_safe,
                    "side": side,
                    "entry": float(entry),
                    "exit": float(exit_px),
                    "size_closed": float(sz),
                    "pnl": float(pnl),
                    "ts": time.time(),
                    "reason": reason or "",
                })
            except Exception:
                pass

            try:
                open_oid = str(pos.get('oid')) if pos.get('oid') else None
            except Exception:
                open_oid = None

            # végül töröljük a pozíciót a listából
            del lst[idx]

            # --- DB frissítés ---
            if closed_oid:
                try:
                    # PNL és exit ár mentése
                    self.db.close_position(closed_oid, exit_px, pnl, reason)
                except Exception as e:
                    self._safe_log(f"⚠️ DB Close Error: {e}\n")

        # --- lockon kívül: log + history exit update ---
        self._safe_log(
            f"🔚 SIM CLOSE {side.upper()} | entry={entry:.6f} → exit={exit_px:.6f} | "
            f"sz={sz:.6f} | GROSS={gross:+.6f} | fee_tot≈{f_total:.6f} | "
            f"PNL={pnl:+.6f} | Total={total_pnl:+.2f} | "
            f"pool used={pool_used:.2f}/{pool_balance:.2f}"
            + (f" | reason={reason}" if reason else "")
            + "\n"
        )

        if open_oid:
            try:
                self._mb_hist_update_exit(open_oid, exit_px, fee_total=f_total, pnl_final=pnl)
            except Exception:
                pass

    def _live_close_pos(self,
                        side: str,           # A pozíció nyitó iránya ('buy' = long, 'sell' = short)
                        pos: dict,           # A pozíció dict-je a _sim_pos_... listából
                        close_px: float,     # Az aktuális (becsült) záróár (px_for_mgmt)
                        *,                   # Innentől keyword-only argumentumok
                        symbol: str,
                        mode: str,
                        lev: int,
                        is_sl_tp: bool = False,
                        is_manual: bool = False) -> bool:

        """
        Piacon keresztül zárja a margin pozíciót.
        A CLOSE order sikeres elküldése (van orderId) → logikai True.
        Fee, PnL, history hibák NEM állítják hamisra a visszatérési értéket.
        """
        sent_ok = False
        oid: Optional[str] = None

        # === 1) ORDER KÜLDÉS (kritikus rész) ===========================================
        try:
            close_side: Literal["buy","sell"] = "sell" if side == "buy" else "buy"

            pos_size = float(pos.get("size", 0.0))
            pos_px   = float(pos.get("entry", 0.0))
            pos_id   = str(pos.get("oid", "N/A"))

            if pos_size <= 0:
                self._safe_log(f"⚠️ LIVE zárási hiba: A pozíció ({pos_id}) mérete nulla. Átugorva.\n")
                return False

            sb, fq = self._mb_sanitize_order(
                symbol=symbol,
                side=close_side,
                price=close_px,
                size_base=pos_size,
                funds_quote=None
            )

            size_to_send = None
            funds_to_send = None

            if close_side == "sell":
                if not sb or sb <= 0:
                    self._safe_log(
                        f"❌ LIVE zárási hiba (SELL): sanitizer 0 méretet adott vissza. Nyers={pos_size}\n"
                    )
                    return False
                size_to_send = str(sb)
            else:
                if not fq or fq <= 0:
                    self._safe_log(
                        f"❌ LIVE zárási hiba (BUY): sanitizer 0 funds-ot adott vissza. Nyers={pos_size} @ {close_px}\n"
                    )
                    return False
                funds_to_send = str(fq)

            # Záráskor engedjük az autoBorrow-t mindkét irányban.
            # KuCoin így tud picit rásegíteni, ha dust hiányzik a base/quote oldalról.
            use_auto_borrow_on_close = True

            _payload_dbg = {
                "mode": mode,
                "symbol": symbol,
                "side": close_side,
                "size_base": size_to_send,
                "funds_quote": funds_to_send,
                "leverage": lev,
                "auto_borrow": use_auto_borrow_on_close,
                "auto_repay": True,
            }

            log_prefix = "🐞 SEND"
            if is_sl_tp: log_prefix += " [SL/TP]"
            if is_manual: log_prefix += " [MANUAL]"

            self._safe_log(f"{log_prefix} CLOSE: {self._mb_pp(_payload_dbg)}\n")

            try:
                with self._ex_lock:
                    resp = self.exchange.place_margin_market_order(
                        mode, symbol, close_side,
                        size_base=size_to_send,
                        funds_quote=funds_to_send,
                        leverage=lev,
                        auto_borrow=use_auto_borrow_on_close,
                        auto_repay=True,
                    )
            except Exception as e:
                self._safe_log(f"❌ LIVE zárási API hiba: {e}\n")
                return False

            self._safe_log(f"🐞 RECV CLOSE: {self._mb_pp(resp)}\n")

            # --- orderId kiolvasás ---
            try:
                if hasattr(resp, "orderId"):
                    oid = str(getattr(resp, "orderId"))
                else:
                    data = resp.get("data") if isinstance(resp, dict) else None
                    if isinstance(data, dict):
                        oid = data.get("orderId") or data.get("orderid")
                    if not oid and isinstance(resp, dict):
                        oid = resp.get("orderId")
                if oid:
                    oid = str(oid)
            except Exception:
                oid = None

            if not oid:
                self._safe_log("❌ LIVE zárási hiba: nincs orderId a válaszban.\n")
                return False

            self._safe_log(f"✅ LIVE záró order elküldve (ID: {oid})\n")
            sent_ok = True

        except Exception as e:
            self._safe_log(f"❌ Kivétel _live_close_pos order küldés közben: {e}\n")
            return False

        if not sent_ok or not oid:
            return bool(sent_ok)

        # === 2) POST-PROCESSING: FEE + PNL + HISTORY ===============================
        fee_close = 0.0

        # --- ÚJ: Private Order WS first, várakozással! ---
        try:
            fee_close = float(self._mb_try_fetch_close_fee(str(oid), wait_ws=True) or 0.0)
        except Exception as e:
            self._safe_log(f"⚠️ Fee lekérés WS/REST hiba: {e}\n")

        total_fee = None
        pnl_final = None

        try:
            if fee_close > 0:
                pos["fee_close_actual"] = float(fee_close)

                fee_rate = self._mb_get_taker_fee()
                f_open, f_close, _ = self._mb_sum_fee_actual_or_est(pos, close_px, fee_rate)
                total_fee = float(f_open + f_close)

                sz = float(pos.get("size", 0.0))
                entry = float(pos.get("entry", 0.0))
                gross = (close_px - entry) * sz * (1 if side == "buy" else -1)
                pnl_final = float(gross - total_fee)

        except Exception as e:
            self._safe_log(f"⚠️ Fee/PnL számítási hiba: {e}\n")

        try:
            self._mb_hist_update_exit(
                pos.get("oid") or pos.get("order_id") or pos.get("id") or str(oid),
                close_px,
                fee_total=total_fee,
                pnl_final=pnl_final
            )
        except Exception as e:
            self._safe_log(f"⚠️ History frissítés hiba: {e}\n")

        return True

    def get_best_price(self, symbol: str) -> float:
        """Egységes árlekérdezés: Ticker WS → worker cache → REST fallback.

        Mindig normalizált szimbólummal dolgozik, és 0.0-t ad vissza, ha semmilyen
        forrásból nem sikerül értelmes árat szerezni.
        """
        try:
            sym = normalize_symbol(symbol)
        except Exception:
            sym = symbol

        # 1) Ticker WS – ha ugyanarra a párra van feliratkozva
        try:
            tws = getattr(self, "_ticker_ws", None)
            if tws is not None and getattr(self, "_ticker_ws_symbol", None) == sym:
                p = float(tws.get_last_price() or 0.0)
                if self._is_pos_num(p) and p > 0:
                    return p
        except Exception:
            pass

        # 2) MarginBot worker cache (realtime ár)
        try:
            with self._mb_lock:
                cache = dict(getattr(self, "_mb_last_rt_px", {}) or {})
            last_rt = float(cache.get(sym, 0.0))
            if self._is_pos_num(last_rt) and last_rt > 0:
                return last_rt
        except Exception:
            pass

        # 3) REST fallback – csak ha minden más kudarcot vallott
        try:
            ex = getattr(self, "exchange", None)
            if ex is not None:
                with self._ex_lock:
                    p = float(ex.fetch_last_price(sym))
                if self._is_pos_num(p) and p > 0:
                    return p
        except Exception:
            pass

        return 0.0

    # === MarginBot – fő ciklus, HTF-filter + ATR menedzsment + RSI szűrő ===
    def _mb_worker(self):
        # --- egyszeri init-ek (ha még nem léteznek) ---
        if not hasattr(self, "_sim_pos_long"):   self._sim_pos_long = []   # list[dict]
        if not hasattr(self, "_sim_pos_short"):  self._sim_pos_short = []  # list[dict]
        if not hasattr(self, "_sim_pnl_usdt"):   self._sim_pnl_usdt = Decimal('0')
        if not hasattr(self, "_sim_history"):    self._sim_history = []
        if not hasattr(self, "_mb_last_bar_ts"): self._mb_last_bar_ts = {}
        if not hasattr(self, "_mb_last_cross_ts"): self._mb_last_cross_ts = 0
        if not hasattr(self, "_mb_last_signal"):   self._mb_last_signal   = "hold"
        if not hasattr(self, "_mb_last_rt_px"):   self._mb_last_rt_px = {}
        if not hasattr(self, "_mb_last_status_log_ts"):  self._mb_last_status_log_ts  = 0
        if not hasattr(self, "_mb_last_status_sig"):     self._mb_last_status_sig     = ""
        if not hasattr(self, "_mb_last_status_px"):      self._mb_last_status_px      = 0.0

        # Dinamikus keret (pool) – induláskor felépítjük
        if not hasattr(self, "_pool_balance_quote") or not hasattr(self, "_pool_used_quote"):
            # _mb_cfg olvasása lock alatt, mert GUI thread is írhatja
            with self._mb_lock:
                cfg0 = getattr(self, "_mb_cfg", {}) or {}
            try:
                symbol0 = normalize_symbol(cfg0.get("symbol", DEFAULT_SYMBOL))
                base0, quote0 = split_symbol(symbol0)
            except Exception:
                base0, quote0 = "", "USDT"

            ui_budget = float(cfg0.get("budget_ui", 0.0) or 0.0)
            dry = bool(cfg0.get("dry", True))

            avail_quote = 0.0
            try:
                if hasattr(self, "_mt_available"):
                    _, avail_quote = self._mt_available(base0, quote0)
            except Exception:
                pass

            if dry:
                init_pool = max(0.0, ui_budget)
            else:
                init_pref = ui_budget if ui_budget > 0 else max(0.0, avail_quote)
                init_pool = min(init_pref, max(0.0, avail_quote))
                if ui_budget > 0 and ui_budget > avail_quote:
                    self._safe_log(
                        f"⚠️ Megadott keret {ui_budget:.2f} {quote0}, de elérhető {avail_quote:.2f} {quote0}. "
                        f"Kezdő keret {init_pool:.2f} {quote0}-ra korlátozva.\n"
                    )
            with self._mb_lock:
                self._pool_balance_quote = Decimal(str(init_pool))
                self._pool_used_quote = Decimal(str(getattr(self, "_restored_pool_usage", 0.0)))

            # Takarítás
            if hasattr(self, "_restored_pool_usage"):
                delattr(self, "_restored_pool_usage")

            self._safe_log(f"🏦 Pool init (reloaded): balance={self._pool_balance_quote:.2f} {quote0}, used={self._pool_used_quote:.2f}\n")

        # --- belső helperek: lista oldalszerint, nyitás/zárás multi, menedzsment per-pozíció ---
        def _pos_list(side: str):
            return self._sim_pos_long if side == "buy" else self._sim_pos_short

        def _safe_now_ts() -> int:
            try:
                return int(time.time())
            except Exception:
                return 0

        def _cooldown_status(last_cross_ts: int | None, cd_s: int) -> tuple[int, bool]:
            """
            Vissza: (cd_left_sec, cd_ok)
            - cd_left_sec: hátralévő cooldown másodperc (min. 0)
            - cd_ok: True, ha már letelt a cooldown
            """
            if not last_cross_ts or cd_s <= 0:
                return 0, True
            now_ts = _safe_now_ts()
            elapsed = now_ts - last_cross_ts
            cd_left = max(0, cd_s - elapsed)
            cd_ok = (elapsed >= cd_s)
            return cd_left, cd_ok

        def _drift_status(drift_pct: float, drift_max_ui: float) -> tuple[bool, str | None]:
            """
            Vissza: (drift_ok, drift_over_txt)
            - drift_ok: True, ha abs(drift_pct) <= drift_max_ui, vagy nincs limit
            - drift_over_txt: pl. 'drift>0.50%' ha túl nagy
            """
            try:
                if drift_max_ui <= 0:
                    return True, None
                if drift_pct != drift_pct:  # NaN
                    return True, None
                if abs(drift_pct) <= drift_max_ui:
                    return True, None
                return False, f"drift>{drift_max_ui:.2f}%"
            except Exception:
                return True, None

        def _build_hold_reasons(
            cd_ok: bool,
            drift_ok: bool,
            drift_over_txt: str | None,
            htf_blocked: bool,
            rsi_blocked: bool,
            zscore_blocked: bool,
            adx_blocked: bool,
            st_blocked: bool,
            sqz_blocked: bool,
            short_disabled_blocked: bool,
            ema_up: bool,
            ema_dn: bool,
            combined_sig_raw: str | None,
        ) -> list[str]:
            reasons: list[str] = []

            # 1. Technikai blokkolók
            if not cd_ok:
                reasons.append("cooldown")
            if drift_over_txt and not drift_ok:
                reasons.append(drift_over_txt)

            # 2. Filter blokkolók (explicit)
            if short_disabled_blocked:
                reasons.append("short_disabled")
            if htf_blocked:
                reasons.append("htf_block")
            if rsi_blocked:
                # RSI blokk irányfüggő lehet, de egyszerűsítve:
                if combined_sig_raw == "buy":
                    reasons.append("rsi_block_buy")
                elif combined_sig_raw == "sell":
                    reasons.append("rsi_block_sell")
                else:
                    reasons.append("rsi_block")

            if zscore_blocked:
                reasons.append("zscore_block")

            if adx_blocked:
                reasons.append("adx_block")

            if st_blocked:
                reasons.append("st_block")

            if sqz_blocked:
                reasons.append("bollinger_block")

            # 3. Egyéb (pl. nincs trend, ha az volt a stratégia alapja)
            # Ha EMA stratégiát használunk és nincs trend, az is egyfajta "hold reason"
            # De itt nem tudjuk biztosan, mi a stratégia.
            # Ha combined_sig_raw is 'hold', akkor lehet, hogy "no_signal" vagy "no_ema_trend".
            if combined_sig_raw == "hold" and not (ema_up or ema_dn):
                reasons.append("no_ema_trend")

            return reasons

        def _build_filters_line(
            use_rsi: bool,
            rsi_bmin: float,
            rsi_bmax: float,
            rsi_smin: float,
            rsi_smax: float,
            use_adx: bool,
            adx_len: int,
            adx_min: float,
            adx_val: float | None,
            use_htf: bool,
            trend_htf: int,
            use_brk: bool,
            use_live: bool,
            use_zscore: bool,
            use_st_filter: bool,
            use_sqz_filter: bool,
            st_trend_dir: int,
            cd_left: int,
        ) -> str:
            parts: list[str] = []

            # RSI filter
            if use_rsi:
                parts.append(
                    f"rsi=ON[buy:{rsi_bmin:.1f}-{rsi_bmax:.1f} "
                    f"sell:{rsi_smin:.1f}-{rsi_smax:.1f}]"
                )
            else:
                parts.append("rsi=OFF")

            # ADX filter formázása: adx=ON(14) 25.7(>20)
            if use_adx:
                val_str = f"{adx_val:.1f}" if adx_val is not None else "n/a"
                parts.append(f"adx=ON({int(adx_len)})(>{float(adx_min):g})")
            else:
                parts.append("adx=OFF")

            # HTF filter formázása: htf=ON(-1)
            if use_htf:
                parts.append(f"htf=ON")
            else:
                parts.append("htf=OFF")

            parts.append(f"brk={'ON' if use_brk else 'OFF'}")
            parts.append(f"live_px={'ON' if use_live else 'OFF'}")

            # Z-score filter formázása: csak ON/OFF (érték fent van)
            parts.append(f"z-score={'ON' if use_zscore else 'OFF'}")

            # Bollinger squeeze
            parts.append(f"Bollinger={'ON' if use_sqz_filter else 'OFF'}")

            # ST filter
            st_icon = "⚪"
            if st_trend_dir == 1: st_icon = "🟢"
            elif st_trend_dir == -1: st_icon = "🔴"
            parts.append(f"st_filter={'ON' if use_st_filter else 'OFF'}({st_icon})")

            parts.append(f"cd_left={cd_left}s")

            # Prefix változott: 'filters:'
            return "filters: " + ", ".join(parts)

        def _log_status_line(
            symbol: str,
            tf: str,
            fa: int,
            slw: int,
            last_px: float,
            last_px_rt: float,
            ef_l: float,
            es_l: float,
            use_htf: bool,
            trend_htf: int,
            use_rsi: bool,
            rsi_len: int,
            rsi_val: float | None,
            use_adx: bool,          # ÚJ PARAMÉTER
            adx_len: int,           # ÚJ PARAMÉTER
            adx_val: float | None,  # ÚJ PARAMÉTER
            use_zscore: bool,       # ÚJ PARAMÉTER
            z_dir: str,             # ÚJ PARAMÉTER (buy/sell/hold szövegesen)
            is_st_strat: bool,      # ÚJ: Supertrend aktív stratégia-e
            st_trend: int,          # ÚJ: Supertrend irány (+1/-1)
            is_sqz_strat: bool,     # ÚJ: Bollinger Squeeze aktív-e
            sqz_is_on: bool,        # ÚJ: Squeeze állapot (True/False)
            sqz_mom: float,         # ÚJ: Momentum érték
            bb_up: float = 0.0,
            bb_dn: float = 0.0,
            kc_up: float = 0.0,
            kc_dn: float = 0.0,
            use_brk: bool = False,
            brk_n: int = 20,
            hh: float = 0.0,
            ll: float = 0.0,
            up_lvl: float = 0.0,
            dn_lvl: float = 0.0,
            drift_pct: float = 0.0,
            open_now: int = 0,
            max_open: int = 0,
            pool_used: float = 0.0,
            pool_balance: float = 0.0,
        ) -> str:
            # Formátum követése: [PÁR TF] Élő ár=... Gyertya ár=...
            parts: list[str] = [
                f"[{symbol} {tf}] Élő ár={last_px_rt:.6f}",
                f"Gyertya ár={last_px:.6f}",
                f"EMA({fa})={ef_l:.4f}/EMA({slw})={es_l:.4f}",
            ]

            # HTF érték megjelenítése a felső logban
            if use_htf:
                parts.append(f"HTF={trend_htf:+d}")

            # RSI érték
            if use_rsi and rsi_val is not None:
                parts.append(f"RSI({rsi_len})={rsi_val:.2f}")

            # ADX érték megjelenítése a felső logban: ADX(14)=25.7
            if use_adx and adx_val is not None:
                parts.append(f"ADX({adx_len})={adx_val:.1f}")

            # Z-score érték (irány) megjelenítése a felső logban
            if use_zscore:
                # z_dir értéke 'buy', 'sell' vagy 'hold' -> konvertáljuk 'LONG', 'SHORT', 'HOLD'-re vagy angolra
                z_display = z_dir.upper() if z_dir != "hold" else "Hold"
                if z_dir == "buy": z_display = "Buy"
                if z_dir == "sell": z_display = "Sell"
                parts.append(f"Z-score={z_display}")

            # Bollinger Squeeze adatok (csak ha aktív a stratégia)
            if is_sqz_strat:
                sqz_state = "Squeezed" if sqz_is_on else "Released"
                sqz_txt = f"SQZ_State={sqz_state} MOM={sqz_mom:.4f}"
                if bb_up > 0:
                    sqz_txt += f" BB=[{bb_dn:.2f}, {bb_up:.2f}]"
                if kc_up > 0:
                    sqz_txt += f" KC=[{kc_dn:.2f}, {kc_up:.2f}]"
                parts.append(sqz_txt)

            # Breakout adatok
            if use_brk and not (math.isnan(hh) or math.isnan(ll)):
                parts.append(
                    f"BRK[{brk_n}] HH={hh:.4f} LL={ll:.4f} ↑{up_lvl:.4f} ↓{dn_lvl:.4f}"
                )

            # Drift és Pool adatok
            if drift_pct == drift_pct:
                parts.append(f"drift={drift_pct:.2f}%")
            parts.append(
                f"POOL used/bal={pool_used:.2f}/{pool_balance:.2f}"
            )
            parts.append(
                f"OPEN={open_now}/{('∞' if max_open == 0 else max_open)}"
            )
            return " ".join(parts)

        def _has_nearby_pos(side: str, px: float, tol_pct: float = 0.1, symbol_filter: str | None = None):
            """
            Van-e már nyitott pozíció ugyanazon az oldalon (buy/sell),
            amelynek entry ára tol_pct %-nál közelebb van az aktuális árhoz.

            Visszaad:
              (found: bool, existing_entry: float | None, diff_pct: float | None)
            """
            try:
                tol = max(0.0, float(tol_pct)) / 100.0
            except Exception:
                tol = 0.001  # fallback = 0.1%

            if not self._is_pos_num(px) or px <= 0:
                return False, None, None

            with self._mb_lock:
                arr = self._sim_pos_long if side == "buy" else self._sim_pos_short
                for pos in arr:
                    if symbol_filter and (pos.get("symbol") != symbol_filter):
                        continue
                    try:
                        e = float(pos.get("entry") or 0.0)
                    except Exception:
                        continue
                    if not self._is_pos_num(e) or e <= 0:
                        continue

                    diff_pct = abs(e - px) / max(e, 1e-12)
                    if diff_pct <= tol:
                        return True, e, diff_pct * 100.0

            return False, None, None

        # --- CFG loader: minden beállítás egy helyen ---
        def _load_cfg() -> NS:
            # config olvasása lock alatt, a GUI szál ugyanígy ugyanazzal a lockkal írja
            with self._mb_lock:
                cfg = dict(getattr(self, "_mb_cfg", {}) or {})

            ns = NS(
                raw=cfg,
                symbol=normalize_symbol(cfg.get("symbol", DEFAULT_SYMBOL)),
                tf=cfg.get("tf", "1m"),
                fa=int(cfg.get("ma_fast", 9)),
                slw=int(cfg.get("ma_slow", 21)),
                sizep=float(cfg.get("size_pct", 50.0)),
                inpm=cfg.get("input_mode", "quote"),
                mode=cfg.get("mode", "isolated"),
                lev=int(cfg.get("leverage", 10)),
                tpct=float(cfg.get("tp_pct", 2.0)),
                spct=float(cfg.get("sl_pct", 1.0)),
                trpct=float(cfg.get("trail_pct", 0.5)),
                cd_s=int(cfg.get("cooldown_s", 30)),
                dry=bool(cfg.get("dry", True)),
                budget_ui=float(cfg.get("budget_ui", 0.0)),

                # RSI / HTF / ATR / FIX / BRK
                use_rsi=bool(cfg.get("use_rsi", False)),
                rsi_len=int(cfg.get("rsi_len", 14)),
                rsi_bmin=float(cfg.get("rsi_bmin", 45.0)),
                rsi_bmax=float(cfg.get("rsi_bmax", 70.0)),
                rsi_smin=float(cfg.get("rsi_smin", 30.0)),
                rsi_smax=float(cfg.get("rsi_smax", 55.0)),

                use_adx=bool(cfg.get("use_adx", False)),
                adx_len=int(cfg.get("adx_len", 14)),
                adx_min=float(cfg.get("adx_min", 20.0)),

                use_htf=bool(cfg.get("use_htf", False)),
                htf_tf=cfg.get("htf_tf", "1h"),

                use_atr=bool(cfg.get("use_atr", False)),
                atr_n=int(cfg.get("atr_n", 14)),
                mul_sl=float(cfg.get("atr_mul_sl", 1.2)),
                mul_tp1=float(cfg.get("atr_mul_tp1", 1.5)),
                mul_tp2=float(cfg.get("atr_mul_tp2", 2.5)),
                mul_tr=float(cfg.get("atr_mul_tr", 0.9)),

                use_fixed=bool(cfg.get("use_fixed", False)),

                use_brk=bool(cfg.get("use_brk", False)),
                brk_n=int(cfg.get("brk_n", 20)),
                brk_buf=float(cfg.get("brk_buf", 0.05)),
                brk_with_trend=bool(cfg.get("brk_with_trend", True)),

                # SuperTrend
                use_st_filter=bool(cfg.get("use_st_filter", False)),
                st_period=int(cfg.get("st_period", 10)),
                st_mult=float(cfg.get("st_mult", 3.0)),

                # Squeeze
                use_sqz_filter=bool(cfg.get("use_sqz_filter", False)),
                sqz_len=int(cfg.get("sqz_len", 20)),
                sqz_bb_mult=float(cfg.get("sqz_bb_mult", 2.0)),
                sqz_kc_mult=float(cfg.get("sqz_kc_mult", 1.5)),

                # Z-score
                use_zscore=bool(cfg.get("use_zscore", False)),
                z_len=int(cfg.get("z_len", 40)),
                z_points=int(cfg.get("z_points", 100)),

                use_live=bool(cfg.get("use_live", True)),
                live_shock_pct=float(cfg.get("live_shock_pct", 1.0)),
                live_shock_atr=float(cfg.get("live_shock_atr", 1.2)),
                drift_max_ui=float(cfg.get("drift_max_pct", 0.0)),
                max_open=int(cfg.get("max_open", 0)),
                pause_new=bool(cfg.get("pause_new", False)),
                auto_borrow=bool(cfg.get("auto_borrow", False)),
                allow_short=bool(cfg.get("allow_short", True)),
                invert_ema=bool(cfg.get("invert_ema", False)),
                ema_hyst_pct=float(cfg.get("ema_hyst_pct", 1.0)),
                dup_tol_pct=float(cfg.get("dup_tol_pct", 0.5)),
                strategy=str(cfg.get("strategy", "EMA")),
            )

            # FIXED vs ATR ütközés feloldása
            if ns.use_fixed and ns.use_atr:
                ns.use_fixed = False

            return ns

        def _manage_positions_for_side(side: str):
            """
            Közös menedzsment BUY / SELL pozikra.

            side: 'buy' → _sim_pos_long
                  'sell' → _sim_pos_short
            """
            list_attr = "_sim_pos_long" if side == "buy" else "_sim_pos_short"

            # Snapshot készítés
            with self._mb_lock:
                positions_snapshot = list(getattr(self, list_attr))

            for pos in positions_snapshot:
                try:
                    # Ha közben (GUI-ból) törölték, ugorjunk
                    with self._mb_lock:
                        if pos not in getattr(self, list_attr):
                            continue

                    need_close = False
                    close_reason = "mgmt_auto"

                    # ATR / FIXED menedzsment (közös long/short logika)
                    if pos.get('mgmt') == 'atr' and atr_val is not None:
                        need_close = _manage_atr_on_pos(pos, px_for_mgmt, atr_val)
                    elif pos.get('mgmt') == 'fixed':
                        need_close = _manage_fixed_on_pos(pos, px_for_mgmt)

                    if not need_close:
                        continue

                    # --- SIM ZÁRÁS ---
                    if dry:
                        try:
                            with self._mb_lock:
                                try:
                                    idx = getattr(self, list_attr).index(pos)
                                except ValueError:
                                    idx = -1
                            if idx >= 0:
                                self._close_sim_by_index(
                                    side,
                                    idx,
                                    px_for_mgmt,
                                    reason=close_reason,
                                    pos_obj=pos,
                                )
                        except Exception as e:
                            self._safe_log(
                                f"❌ SIM {side} zárás hiba: {e}\n"
                            )
                            continue

                    # --- LIVE ZÁRÁS ---
                    else:
                        ok = False
                        try:
                            ok = self._live_close_pos(
                                side,
                                pos,
                                px_for_mgmt,
                                symbol=(pos.get("symbol") or symbol),
                                mode=mode,
                                lev=lev,
                            )
                        except Exception as e:
                            self._safe_log(
                                f"❌ LIVE {side} zárás hiba: {e}\n"
                            )
                            ok = False

                        if ok:
                            # sikeres LIVE után tükörzárás SIM-ben
                            try:
                                with self._mb_lock:
                                    try:
                                        idx = getattr(self, list_attr).index(pos)
                                    except ValueError:
                                        idx = -1
                                if idx >= 0:
                                    self._close_sim_by_index(
                                        side,
                                        idx,
                                        px_for_mgmt,
                                        reason=close_reason,
                                        pos_obj=pos,
                                    )
                            except Exception as e:
                                self._safe_log(
                                    f"❌ SIM tükrözés hiba ({side}): {e}\n"
                                )
                                continue
                        else:
                            self._safe_log(
                                f"❗ LIVE zárás sikertelen – a {side} pozíció nyitva marad.\n"
                            )
                            continue

                except Exception as e:
                    self._safe_log(
                        f"❌ Pozíció menedzsment hiba ({side}): {e}\n"
                    )
                    continue

        def _open_sim(side: str, entry_px: float, size_base: float, commit_usdt: float, atr_pack=None, fixed_pack=None, symbol_for_pos: str | None = None, **extra):
            fee_rate = self._mb_get_taker_fee()
            fee_open_est = self._mb_est_fee_quote(entry_px, size_base, fee_rate)

            # Opcionális override-ok LIVE orderből:
            extra = extra or {}
            fee_open_actual = float(extra.pop("fee_open_actual_override", 0.0) or 0.0)
            fee_reserved_override = extra.pop("fee_reserved_override", None)
            if fee_reserved_override is None:
                fee_reserved = fee_open_est
            else:
                try:
                    fee_reserved = float(fee_reserved_override)
                except Exception:
                    fee_reserved = fee_open_est

            pos = {
                'side': side,
                'entry': float(entry_px),
                'size': float(size_base),
                'peak': float(entry_px),
                'pnl': 0.0,
                'commit_usdt': float(commit_usdt),
                'fee_open_est': float(fee_open_est),      # becsült nyitási díj
                'fee_open_actual': float(fee_open_actual),# ha van tényleges nyitási díj
                'fee_close_actual': 0.0,
                'fee_reserved': float(fee_reserved),      # a pool-ból lefoglalt díj (actual>0 ? actual : est)
                'mgmt': 'none',
                'ts': time.time(),
            }
            pos.update({k: v for k, v in (extra or {}).items()})
            pos['symbol'] = symbol_for_pos or symbol
            if atr_pack is not None:
                mul_sl, mul_tp1, mul_tp2, trail_mul, atr_val = atr_pack
                if side == 'buy':
                    sl  = entry_px - mul_sl*atr_val
                    tp1 = entry_px + mul_tp1*atr_val
                    tp2 = entry_px + mul_tp2*atr_val
                else:
                    sl  = entry_px + mul_sl*atr_val
                    tp1 = entry_px - mul_tp1*atr_val
                    tp2 = entry_px - mul_tp2*atr_val
                pos.update({'sl': sl, 'tp1': tp1, 'tp2': tp2, 'trail_mul': trail_mul, 'half_closed': False, 'mgmt': 'atr'})
            elif fixed_pack is not None:
                tpct, spct, trpct = fixed_pack
                pos.update({'tp_pct': tpct, 'sl_pct': spct, 'trail_pct': trpct, 'mgmt': 'fixed'})
            with self._mb_lock:
                _pos_list(side).append(pos)
                # Javítás: Decimal + float hiba elkerülése
                self._pool_used_quote += Decimal(str(float(commit_usdt))) + Decimal(str(float(fee_reserved)))
                # --- Mentés adatbázisba ---
                try:
                    self.db.add_position(pos)
                except Exception as e:
                    self._safe_log(f"⚠️ DB Save Error: {e}\n")

            fee_log = fee_open_actual if fee_open_actual > 0 else fee_open_est
            self._safe_log(
                f"🧪 SIM OPEN {side.upper()} @ {entry_px:.6f} | sz={size_base:.6f} | "
                f"commit={commit_usdt:.2f} | fee≈{fee_log:.4f} | "
                f"pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

        def _partial_close_50(pos: dict, side: str, px: float):
            if pos.get('half_closed', False):
                return

            entry = float(pos['entry']); sz = float(pos['size'])

            try:
                symbol_safe = normalize_symbol(pos.get("symbol") or DEFAULT_SYMBOL)
            except Exception:
                symbol_safe = None

            try:
                sym = symbol_safe or DEFAULT_SYMBOL
                lot_step, _price_step, _min_base, _min_funds, _quote_step = self._mb_get_market_steps(sym)
            except Exception:
                lot_step = 0.0

            raw_half = sz * 0.5
            close_sz = self._mb_floor_to_step_dec(raw_half, float(lot_step or 0.0))
            if close_sz <= 0:
                return
            if sz <= 0:
                return

            pnl = (px - entry) * close_sz * (1 if side == 'buy' else -1)

            commit_before = float(pos.get('commit_usdt', 0.0))
            try:
                rel_ratio = close_sz / max(sz, 1e-12)
            except Exception:
                rel_ratio = 0.5
            release = commit_before * rel_ratio

            fee_res_before = float(pos.get('fee_reserved', 0.0))
            fee_release = fee_res_before * rel_ratio

            with self._mb_lock:
                # Javítás: Decimal + float hiba elkerülése
                self._sim_pnl_usdt += Decimal(str(pnl))
                self._pool_balance_quote += Decimal(str(pnl))

                pos.update({
                    'size': sz - close_sz,
                    'commit_usdt': max(0.0, commit_before - release),
                    'fee_reserved': max(0.0, fee_res_before - fee_release),
                    'half_closed': True,
                })

                # commit + fee arányos része felszabadul a poolból
                self._pool_used_quote = max(
                    0.0,
                    self._pool_used_quote - (release + fee_release),
                )

            try:
                with self._mb_lock:
                    self._sim_history.append({
                        "partial": True,
                        "symbol": symbol_safe,
                        "side": side,
                        "entry": float(entry),
                        "exit": float(px),
                        "size_closed": float(close_sz),
                        "pnl": float(pnl),
                        "ts": time.time(),
                    })
            except Exception:
                pass

            # DB frissítése a csökkentett mérettel
            try:
                # order_id kinyerése
                oid = str(pos.get('oid') or pos.get('order_id') or pos.get('id'))
                self.db.update_position_size(oid, float(pos['size']), float(pos['commit_usdt']))
            except Exception as e:
                self._safe_log(f"⚠️ DB Update Partial Error: {e}\n")

            self._safe_log(
                f"🔹 PARTIAL 50% | entry={entry:.6f} → exit={px:.6f} | "
                f"zárt={close_sz:.6f} | PnL={pnl:+.2f} | "
                f"pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

        def _manage_atr_on_pos(pos: dict, last_px: float, atr_val: float) -> bool:
            side = pos['side']
            # last_px itt px_for_mgmt, ami WS-alapú, ha elérhető  ### WS-PEAK
            if side == 'buy' and last_px > pos['peak']: pos['peak'] = last_px
            if side == 'sell' and last_px < pos['peak']: pos['peak'] = last_px

            tp1 = pos['tp1']
            if not pos.get('half_closed', False):
                if (side == 'buy' and last_px >= tp1) or (side == 'sell' and last_px <= tp1):
                    _partial_close_50(pos, side, last_px)

            peak = pos['peak']; trail_mul = pos.get('trail_mul', 1.0)
            if side == 'buy':
                trail_px = peak - trail_mul*atr_val
                if last_px <= trail_px: return True
            else:
                trail_px = peak + trail_mul*atr_val
                if last_px >= trail_px: return True

            tp2 = pos['tp2']; sl = pos['sl']
            if (side == 'buy' and (last_px >= tp2 or last_px <= sl)) or \
               (side == 'sell' and (last_px <= tp2 or last_px >= sl)):
                return True
            return False

        def _manage_fixed_on_pos(pos: dict, last_px: float) -> bool:
            side  = pos['side']
            entry = float(pos['entry'])
            # last_px itt is px_for_mgmt → WS-alapú, ha elérhető  ### WS-PEAK
            if side == 'buy' and last_px > pos['peak']: pos['peak'] = float(last_px)
            if side == 'sell' and last_px < pos['peak']: pos['peak'] = float(last_px)

            tpct = float(pos.get('tp_pct', 0.0)); spct = float(pos.get('sl_pct', 0.0)); trpct = float(pos.get('trail_pct', 0.0))
            tp_r = max(0.0, tpct) / 100.0
            sl_r = max(0.0, spct) / 100.0
            tr_r = max(0.0, trpct) / 100.0

            if side == 'buy':
                sl_px = entry * (1.0 - sl_r) if sl_r > 0 else -float('inf')
                tp_px = entry * (1.0 + tp_r) if tp_r > 0 else  float('inf')
                trail_px = pos['peak'] * (1.0 - tr_r) if tr_r > 0 else -float('inf')
                if last_px >= tp_px: return True
                if tr_r > 0 and last_px <= trail_px: return True
                if last_px <= sl_px: return True
            else:
                sl_px = entry * (1.0 + sl_r) if sl_r > 0 else  float('inf')
                tp_px = entry * (1.0 - tp_r) if tp_r > 0 else -float('inf')
                trail_px = pos['peak'] * (1.0 + tr_r) if tr_r > 0 else  float('inf')
                if last_px <= tp_px: return True
                if tr_r > 0 and last_px >= trail_px: return True
                if last_px >= sl_px: return True
            return False

        # --- OPTIMALIZÁCIÓ: Market steps egyszeri lekérése a ciklus előtt ---
        try:
            _pre_cfg = _load_cfg()
            _init_symbol = _pre_cfg.symbol
            _ms_init = self._mb_get_market_steps(_init_symbol)
            lot_step, price_step, min_base, min_funds, quote_step = _ms_init
        except Exception:
            lot_step = price_step = min_base = min_funds = quote_step = 0.0

        try:
            while self._mb_running:
                try:
                    # --- 1) CFG beállítások beolvasása egy helyről ---
                    cfg_ns = _load_cfg()

                    symbol = cfg_ns.symbol
                    tf     = cfg_ns.tf
                    fa     = cfg_ns.fa
                    slw    = cfg_ns.slw
                    sizep  = cfg_ns.sizep
                    inpm   = cfg_ns.inpm
                    mode   = cfg_ns.mode
                    lev    = cfg_ns.lev
                    tpct   = cfg_ns.tpct
                    spct   = cfg_ns.spct
                    trpct  = cfg_ns.trpct
                    cd_s   = cfg_ns.cd_s
                    dry    = cfg_ns.dry
                    budget_ui = cfg_ns.budget_ui

                    use_rsi  = cfg_ns.use_rsi
                    rsi_len  = cfg_ns.rsi_len
                    rsi_bmin = cfg_ns.rsi_bmin
                    rsi_bmax = cfg_ns.rsi_bmax
                    rsi_smin = cfg_ns.rsi_smin
                    rsi_smax = cfg_ns.rsi_smax

                    use_adx = cfg_ns.use_adx
                    adx_len = cfg_ns.adx_len
                    adx_min = cfg_ns.adx_min

                    use_htf = cfg_ns.use_htf
                    htf_tf  = cfg_ns.htf_tf

                    use_atr = cfg_ns.use_atr
                    atr_n   = cfg_ns.atr_n
                    mul_sl  = cfg_ns.mul_sl
                    mul_tp1 = cfg_ns.mul_tp1
                    mul_tp2 = cfg_ns.mul_tp2
                    mul_tr  = cfg_ns.mul_tr

                    use_fixed = cfg_ns.use_fixed

                    use_brk   = cfg_ns.use_brk
                    brk_n     = cfg_ns.brk_n
                    brk_buf   = cfg_ns.brk_buf
                    brk_with_trend = cfg_ns.brk_with_trend

                    use_zscore = cfg_ns.use_zscore
                    z_len      = cfg_ns.z_len
                    z_points   = cfg_ns.z_points

                    # Bollinger
                    use_sqz_filter = cfg_ns.use_sqz_filter
                    sqz_len     = cfg_ns.sqz_len
                    sqz_bb_mult = cfg_ns.sqz_bb_mult
                    sqz_kc_mult = cfg_ns.sqz_kc_mult

                    # Supertrend
                    use_st_filter = cfg_ns.use_st_filter
                    st_period     = cfg_ns.st_period
                    st_mult       = cfg_ns.st_mult

                    use_live       = cfg_ns.use_live
                    live_shock_pct = cfg_ns.live_shock_pct
                    live_shock_atr = cfg_ns.live_shock_atr
                    drift_max_ui   = cfg_ns.drift_max_ui
                    max_open       = cfg_ns.max_open
                    pause_new      = cfg_ns.pause_new
                    auto_borrow    = cfg_ns.auto_borrow
                    allow_short    = cfg_ns.allow_short
                    invert_ema     = cfg_ns.invert_ema
                    ema_hyst_pct   = cfg_ns.ema_hyst_pct
                    dup_tol_pct    = cfg_ns.dup_tol_pct
                    strategy       = cfg_ns.strategy

                    # --- K-Line WS: ÖSSZES szükséges TF egy helyen ---
                    required_tfs = [tf]

                    # HTF TF hozzáadása, ha használod
                    if use_htf and htf_tf:
                        required_tfs.append(htf_tf)

                    # Ha van külön chart TF (pl. GUI comboboxból), azt is belerakhatod:
                    try:
                        tf_chart = None
                        try:
                            tf_chart = self.mb_tf_chart.get().strip()
                        except Exception:
                            tf_chart = None
                        if tf_chart:
                            required_tfs.append(tf_chart)
                    except Exception:
                        pass

                    # duplikátumok kiszedése + rendezés, hogy ne okozzon felesleges restartot
                    required_tfs = sorted(set(required_tfs))

                    try:
                        self._ensure_kline_ws(symbol, required_tfs)
                    except Exception as e:
                        self._safe_log(f"⚠️ K-Line WS indítás hiba: {e}\n")

                    # --- Privát order WS biztosítása (KuCoin) ---
                    try:
                        self._ensure_order_ws()
                    except Exception:
                        pass

                    # --- OHLCV frissítés csak ha új candle jött ---  ### WS-REST-OPT
                    now_ts = _safe_now_ts()

                    # gyertya hossza másodpercben
                    tf_sec = {
                        "1m":60, "3m":180, "5m":300, "15m":900, "30m":1800,
                        "1h":3600, "2h":7200, "4h":14400, "6h":21600,
                        "8h":28800, "12h":43200, "1d":86400
                    }.get(tf, 60)

                    key = (symbol, tf)
                    prev_ts = self._mb_last_bar_ts.get(key, 0)
                    need_refresh = False

                    if prev_ts == 0:
                        # első kör ennél a symbol/tf-nél → kell egy teljes OHLCV
                        need_refresh = True
                    else:
                        # ha túl vagyunk a candle végén → új candle
                        if now_ts >= (prev_ts + tf_sec):
                            need_refresh = True

                    # OHLCV beszerzési limit számítása
                    need_n = max(200, adx_len * 4, z_len * 3 + z_points, slw * 3)

                    # Van-e újrahasznosítható DF?
                    current_df = getattr(self, "_mb_last_df", None)
                    current_df_key = getattr(self, "_mb_last_df_key", None)
                    can_reuse_df = (current_df is not None) and (current_df_key == key)

                    if need_refresh or not can_reuse_df:
                        # OHLCV beszerzés WS-ből, vagy fallback REST-ből
                        try:
                            ohlcv = self._mb_get_ohlcv(symbol, tf, limit=need_n)
                        except Exception:
                            with self._ex_lock:
                                ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=200)

                        if not ohlcv:
                            self._safe_log("⚠️ Nincs candle adat.\n")
                            time.sleep(2)
                            continue

                        if can_reuse_df:
                            # --- OPTIMALIZÁCIÓ: pd.concat ---
                            # Csak az új gyertyákat vesszük hozzá
                            last_known_ts = float(current_df['ts'].iloc[-1])
                            new_candles = [row for row in ohlcv if row[0] > last_known_ts]

                            if new_candles:
                                df_new = pd.DataFrame(new_candles, columns=['ts','o','h','l','c','v'])
                                df = pd.concat([current_df, df_new], ignore_index=True)
                                # Trimelés
                                limit_keep = max(500, need_n)
                                if len(df) > limit_keep:
                                    df = df.iloc[-limit_keep:].copy()
                            else:
                                df = current_df.copy()
                        else:
                            # Első kör / szimbólum váltás: teljes DF építés
                            df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])

                        # Kulcs mentése a következő körhöz
                        self._mb_last_df_key = key

                        last_ts_ms = int(df['ts'].iloc[-1])
                        last_ts_s  = int(last_ts_ms // 1000)
                        self._mb_last_bar_ts[key] = last_ts_s
                        # fontos: itt MÉG nem cache-eljük self._mb_last_df-et,
                        # előbb ráengedjük a realtime (WS) árat a legutóbbi gyertyára
                    else:
                        df = self._mb_last_df.copy()
                        last_ts_ms = int(df["ts"].iloc[-1])
                        last_ts_s  = last_ts_ms // 1000
                        self._mb_last_bar_ts[key] = last_ts_s

                    closes = df['c'].astype(float).tolist()
                    last_px = float(closes[-1])

                    # valós idejű (ticker) ár – default a candle close
                    last_px_rt = last_px
                    if not self._is_pos_num(last_px) or not self._is_pos_num(last_px_rt):
                        self._safe_log("⚠️ Érvénytelen ár (0/NaN) – ciklus kihagyva.\n")
                        time.sleep(2)
                        continue

                    used_ws_price = False  # ### WS-FLAG: True csak akkor, ha a last_px_rt TICKER-WS-ből jött (drift ehhez kötött)

                    # --- indikátor DF (lezárt gyertyák!) ---
                    df_ind = df.copy()

                    # --- Websocket ár preferált, get_best_price csak fallbackként ---  ### WS-PRIMARY
                    try:
                        self._ensure_ticker_ws(symbol)
                    except Exception:
                        pass

                    try:
                        # 1) Ticker WS közvetlenül
                        tws = getattr(self, "_ticker_ws", None)
                        if tws is not None:
                            rt_ws = float(tws.get_last_price() or 0.0)
                            if self._is_pos_num(rt_ws) and rt_ws > 0:
                                last_px_rt = rt_ws
                                used_ws_price = True

                        # 2) Ha nincs használható WS ár → egységes helper (WS/cache/REST kombó)
                        if not used_ws_price:
                            rt_best = float(self.get_best_price(symbol))
                            if self._is_pos_num(rt_best) and rt_best > 0:
                                last_px_rt = rt_best

                    except Exception:
                        pass

                    # cache: CSAK LEZÁRT GYERTYA (itt már megvan a last_px_rt is)
                    self._mb_last_df = df_ind

                    # --- realtime DF (EMA / log / döntés) ---
                    # FONTOS: itt már végleges a last_px_rt
                    df_rt = df_ind.copy()
                    try:
                        if self._is_pos_num(last_px_rt) and float(last_px_rt) > 0:
                            df_rt.at[df_rt.index[-1], "c"] = float(last_px_rt)
                            h0 = float(df_rt.at[df_rt.index[-1], "h"])
                            l0 = float(df_rt.at[df_rt.index[-1], "l"])
                            c0 = float(df_rt.at[df_rt.index[-1], "c"])
                            df_rt.at[df_rt.index[-1], "h"] = max(h0, c0)
                            df_rt.at[df_rt.index[-1], "l"] = min(l0, c0)
                    except Exception:
                        pass

                    # --- cache-eljük a realtime árakat más funkcióknak is (manual close / PnL / history) ---
                    try:
                        if self._is_pos_num(last_px_rt) and last_px_rt > 0:
                            with self._mb_lock:
                                if not hasattr(self, "_mb_last_rt_px"):
                                    self._mb_last_rt_px = {}
                                self._mb_last_rt_px[symbol] = float(last_px_rt)

                            # History floating PnL frissítése ugyanazzal a rt-vel (Tk főszálon)
                            try:
                                self.root.after(0, self._mb_hist_apply_pnl, float(last_px_rt))
                            except Exception:
                                pass
                    except Exception:
                        pass

                    px_for_mgmt = last_px_rt if (self._is_pos_num(last_px_rt) and last_px_rt > 0) else last_px

                    # --- drift csak akkor, ha TÉNYLEG WS árunk van ---  ### WS-DRIFT
                    try:
                        if used_ws_price and self._is_pos_num(last_px):
                            drift_pct = abs(last_px_rt - last_px) / max(last_px, 1e-12) * 100.0
                        else:
                            drift_pct = float("nan")
                    except Exception:
                        drift_pct = float("nan")

                    # pozíciók száma lock alatt, mert GUI is módosíthat
                    with self._mb_lock:
                        open_now = len(self._sim_pos_long) + len(self._sim_pos_short)

                    atr_val = None
                    if use_atr:
                        atr_series = self._mb_atr(df_rt, n=atr_n)
                        atr_val = float(atr_series.iloc[-1])
                        self._mb_last_atr_val = atr_val

                    closes_for_sig = df_rt['c'].astype(float).tolist()
                    # hiszterézis mult kivonva cfg-ből → nincs Tk az _mb_signal_from_ema_live-ben
                    atr_eps_mult = max(0.0, ema_hyst_pct) / 100.0
                    sig_raw, ef_l, es_l = self._mb_signal_from_ema_live(
                        closes_for_sig, fa, slw, last_px_rt,
                        atr_eps_mult=atr_eps_mult,
                        invert=invert_ema,            # <<< invert flag cfg-ből
                    )
                    trend_htf = 0
                    if use_htf:
                        trend_htf = self._mb_trend_filter(
                            symbol, htf_tf, fa, slw,
                            invert=invert_ema           # <<< itt is cfg-ből
                        )

                    sig = sig_raw
                    if use_htf:
                        if (sig_raw == 'buy' and trend_htf < 0) or (sig_raw == 'sell' and trend_htf > 0):
                            sig = 'hold'

                    rsi_val = None
                    if use_rsi:
                        rsi_series = self._mb_rsi(df_rt['c'], n=rsi_len)
                        rsi_val = float(rsi_series.iloc[-1])
                        if sig == 'buy':
                            if not (rsi_bmin <= rsi_val <= rsi_bmax):
                                sig = 'hold'
                        elif sig == 'sell':
                            if not (rsi_smin <= rsi_val <= rsi_smax):
                                sig = 'hold'

                    brk_sig, hh, ll, up_lvl, dn_lvl = ("hold", float("nan"), float("nan"), float("nan"), float("nan"))
                    brk_sig_raw = "hold"
                    if use_brk:
                        # breakout-hoz érdemes a realtime high/low-t használni
                        brk_sig, hh, ll, up_lvl, dn_lvl = self._mb_breakout_signal(df_rt, brk_n, brk_buf)
                        brk_sig_raw = brk_sig
                        if brk_with_trend and use_htf:
                            if (brk_sig == 'buy' and trend_htf < 0) or (brk_sig == 'sell' and trend_htf > 0):
                                brk_sig = 'hold'

                    # Élő ár szűrők, breakout/shock logika cfg-ből
                    try:
                        if use_live:
                            shock_pct = max(0.0, live_shock_pct)
                            shock_atr_mul = max(0.0, live_shock_atr)

                            # Itt már a ciklus eleji last_px_rt-et használjuk.
                            # Ha valamiért 0/NaN → egységes helper-rel pótoljuk (WS/cache/REST).
                            if not self._is_pos_num(last_px_rt):
                                try:
                                    rt_tmp = float(self.get_best_price(symbol))
                                    if self._is_pos_num(rt_tmp) and rt_tmp > 0:
                                        last_px_rt = rt_tmp
                                except Exception:
                                    pass

                            live_break_up = (use_brk and not math.isnan(up_lvl) and last_px_rt >= up_lvl)
                            live_break_dn = (use_brk and not math.isnan(dn_lvl) and last_px_rt <= dn_lvl)

                            chg = last_px_rt - last_px
                            chg_pct = (abs(chg) / max(last_px, 1e-12)) * 100.0
                            shock_hit_pct = (chg_pct >= shock_pct)

                            shock_hit_atr = False
                            if atr_val is not None and shock_atr_mul > 0:
                                shock_hit_atr = (abs(chg) >= (shock_atr_mul * atr_val))

                            shock_up = (chg > 0) and (shock_hit_pct or shock_hit_atr)
                            shock_dn = (chg < 0) and (shock_hit_pct or shock_hit_atr)

                            can_buy  = (not use_htf) or (trend_htf >= 0)
                            can_sell = (not use_htf) or (trend_htf <= 0)

                            if (live_break_up or shock_up) and can_buy:
                                brk_sig = 'buy'
                                self._safe_log(
                                    f"⚡ LIVE breakout/shock BUY: Élő ár={last_px_rt:.6f} "
                                    f"(up={up_lvl:.4f} chg={chg:+.4f}, {chg_pct:.2f}%"
                                    + (f", ATRx≈{abs(chg)/max(atr_val,1e-12):.2f}" if atr_val else "")
                                    + ")\n"
                                )

                            elif (live_break_dn or shock_dn) and can_sell:
                                brk_sig = 'sell'
                                self._safe_log(
                                    f"⚡ LIVE breakout/shock SELL: Élő ár={last_px_rt:.6f} "
                                    f"(dn={dn_lvl:.4f} chg={chg:+.4f}, {chg_pct:.2f}%"
                                    + (f", ATRx≈{abs(chg)/max(atr_val,1e-12):.2f}" if atr_val else "")
                                    + ")\n"
                                )
                    except Exception:
                        pass

                    # --- STRATÉGIA VÁLASZTÁS ÉS ALAPJEL KÉPZÉS ---
                    # 1. Z-Score számítása (mindig fusson)
                    z_dir = "hold"
                    z_quad = None
                    try:
                        z_sig, z_quad = self._compute_zscore_signal(
                            symbol,
                            tf,
                            length=z_len,
                            data_points=z_points,
                            df=df_rt,
                        )
                    except Exception:
                        z_sig, z_quad = 0, None

                    if z_sig == 1:
                        z_dir = "buy"
                    elif z_sig == -1:
                        z_dir = "sell"
                    else:
                        z_dir = "hold"

                    # 2. Bollinger Squeeze számítása (mindig fusson)
                    sqz_sig = "hold"
                    is_sqz = False
                    mom_val = 0.0
                    bb_up = 0.0
                    bb_dn = 0.0
                    kc_up = 0.0
                    kc_dn = 0.0
                    try:
                        sqz_sig, is_sqz, mom_val, bb_up, bb_dn, kc_up, kc_dn = self._mb_squeeze_signal(
                            df_rt, length=sqz_len, bb_mult=sqz_bb_mult, kc_mult=sqz_kc_mult
                        )
                    except Exception:
                        pass

                    # 3. Supertrend számítása (mindig fusson, kellhet szűrőnek)
                    st_trend_series = None
                    st_line_series = None
                    st_trend = 0
                    st_sig = "hold"
                    try:
                        st_trend_series, st_line_series = self._mb_supertrend(df_rt, period=st_period, multiplier=st_mult)
                        if st_trend_series is not None and len(st_trend_series) > 1:
                            st_trend = int(st_trend_series.iloc[-1])
                            prev_st_trend = int(st_trend_series.iloc[-2])

                            # Signal only on flip
                            if prev_st_trend == -1 and st_trend == 1:
                                st_sig = "buy"
                            elif prev_st_trend == 1 and st_trend == -1:
                                st_sig = "sell"
                            else:
                                st_sig = "hold"
                    except Exception:
                        pass

                    # 4. Stratégia alapú elágazás
                    strategy_mode = getattr(cfg_ns, "strategy", "EMA")

                    if strategy_mode == "Z-Score":
                        combined_sig_base = z_dir
                    elif strategy_mode == "Bollinger Squeeze":
                        combined_sig_base = sqz_sig
                    elif strategy_mode == "Supertrend":
                        combined_sig_base = st_sig
                    else:
                        # EMA (Alapértelmezett)
                        combined_sig_base = brk_sig if brk_sig in ("buy", "sell") else sig

                    combined_sig = combined_sig_base
                    combined_sig_raw = combined_sig_base  # Ez a nyers jel a filterek előtt

                    # --- ADX számítása ---
                    adx_val = None
                    adx_ok = True
                    if use_adx:
                        try:
                            adx_val = self._mb_adx(df_rt, length=adx_len)
                            adx_ok = (adx_val is not None and float(adx_val) >= float(adx_min))
                        except Exception:
                            adx_val = None
                            adx_ok = True

                    # --- KÖZÖS FILTEREK (Corrected Logic) ---

                    # 1. LÉPÉS: Inicializálás (Itt nullázunk le mindent EGYETLEN EGYSZER)
                    htf_blocked = False
                    rsi_blocked = False
                    zscore_blocked = False
                    adx_blocked = False
                    st_blocked = False
                    sqz_blocked = False
                    short_disabled_blocked = False

                    # Csak akkor futtatjuk a szűrőket, ha van alapjel (buy/sell)
                    if combined_sig_raw in ("buy", "sell"):

                        # 0. Allow Short check
                        if combined_sig_raw == 'sell' and not allow_short:
                            short_disabled_blocked = True

                        # 1. HTF Filter
                        if use_htf:
                            if (combined_sig_raw == 'buy' and trend_htf < 0) or (combined_sig_raw == 'sell' and trend_htf > 0):
                                htf_blocked = True

                        # 2. RSI Filter
                        if use_rsi and rsi_val is not None:
                            if combined_sig_raw == 'buy' and not (rsi_bmin <= rsi_val <= rsi_bmax):
                                rsi_blocked = True
                            elif combined_sig_raw == 'sell' and not (rsi_smin <= rsi_val <= rsi_smax):
                                rsi_blocked = True

                        # 3. Z-Score Filter (Szigorú / Strict Confirmation - ahogy kérted)
                        # Csak akkor szűr, ha NEM Z-Score a stratégia
                        if use_zscore and strategy_mode != "Z-Score":
                            if combined_sig_raw == 'buy' and z_dir != 'buy':
                                zscore_blocked = True
                            elif combined_sig_raw == 'sell' and z_dir != 'sell':
                                zscore_blocked = True

                        # 4. ADX Filter
                        if use_adx and not adx_ok:
                            adx_blocked = True

                        # 5. Supertrend Filter
                        # Csak akkor szűr, ha NEM Supertrend a stratégia
                        if use_st_filter and strategy_mode != "Supertrend":
                            if combined_sig_raw == "buy" and st_trend == -1: # Trend is Bearish -> Block Buy
                                st_blocked = True
                            elif combined_sig_raw == "sell" and st_trend == 1: # Trend is Bullish -> Block Sell
                                st_blocked = True

                        # 5. Bollinger Filter
                        # Csak akkor szűr, ha NEM Bollinger a stratégia
                        if use_sqz_filter and strategy_mode != "Bollinger Squeeze":
                            if combined_sig_raw == "buy" and sqz_sig  != "buy":
                                sqz_blocked = True
                            elif combined_sig_raw == "sell" and sqz_sig  != "sell":
                                sqz_blocked = True

                    # 2. LÉPÉS: Blokkolók alkalmazása
                    # Ha bármelyik blokkoló aktív, a jel 'hold'-ra vált, DE a változó értéke (True) megmarad a loghoz!
                    if htf_blocked or rsi_blocked or zscore_blocked or adx_blocked or st_blocked or sqz_blocked or short_disabled_blocked:
                        combined_sig = 'hold'

                    # Breakout Override (Force Signal)
                    if (use_brk or use_live) and brk_sig in ("buy", "sell"):
                        combined_sig = brk_sig

                    # --- Cooldown + drift ---
                    cd_left, cd_ok = _cooldown_status(self._mb_last_cross_ts, cd_s)

                    ema_up = (ef_l > es_l)
                    ema_dn = (ef_l < es_l)

                    drift_ok, drift_over_txt = _drift_status(drift_pct, drift_max_ui)

                    # Ha Cooldown vagy Drift blokkol, akkor is hold
                    if combined_sig in ("buy", "sell"):
                        if not cd_ok:
                            combined_sig = "hold"
                        elif not drift_ok:
                            combined_sig = "hold"

                    # HOLD okok (Filterek és technikai blokkolók)
                    reasons = _build_hold_reasons(
                        cd_ok=cd_ok,
                        drift_ok=drift_ok,
                        drift_over_txt=drift_over_txt,
                        htf_blocked=htf_blocked,
                        rsi_blocked=rsi_blocked,
                        zscore_blocked=zscore_blocked,
                        st_blocked=st_blocked,
                        sqz_blocked=sqz_blocked,
                        short_disabled_blocked=short_disabled_blocked,
                        adx_blocked=adx_blocked,
                        ema_up=ema_up,
                        ema_dn=ema_dn,
                        combined_sig_raw=combined_sig_raw,
                    )

                    # --- KIEGÉSZÍTÉS: Stratégia-specifikus várakozó okok ---
                    # Ha az alapjel (combined_sig_raw) 'hold', akkor kiírjuk, mire várunk.
                    if combined_sig_raw == "hold":
                        if strategy_mode == "Bollinger Squeeze":
                            if is_sqz:
                                reasons.insert(0, "HOLD | squeezed_waiting")
                            else:
                                # Ha nincs squeeze, de momentum sincs elég
                                reasons.insert(0, "HOLD | sqz_no_setup")

                        elif strategy_mode == "Z-Score":
                            # Ha Z-Score a stratégia, és a sávon belül vagyunk
                            reasons.insert(0, "HOLD | waiting_for_zscore")

                        elif strategy_mode == "Supertrend":
                            reasons.insert(0, "HOLD | waiting_for_st_flip")

                        elif strategy_mode == "EMA":
                            # Ha EMA a stratégia, és nincs keresztezés
                            reasons.insert(0, "HOLD | waiting_for_ema_cross")

                    # filters összefoglaló sor
                    filters_line = _build_filters_line(
                        use_rsi=use_rsi,
                        rsi_bmin=rsi_bmin,
                        rsi_bmax=rsi_bmax,
                        rsi_smin=rsi_smin,
                        rsi_smax=rsi_smax,
                        use_adx=use_adx,
                        adx_len=adx_len,
                        adx_min=adx_min,
                        adx_val=adx_val,
                        use_htf=use_htf,
                        trend_htf=trend_htf,
                        use_brk=use_brk,
                        use_live=use_live,
                        use_zscore=use_zscore,
                        use_st_filter=use_st_filter,
                        use_sqz_filter=use_sqz_filter,
                        st_trend_dir=st_trend,
                        cd_left=cd_left,
                    )

                    # --- Log sor felépítés ---
                    # pool snapshot loghoz
                    with self._mb_lock:
                        pool_used_for_log = float(self._pool_used_quote)
                        pool_bal_for_log  = float(self._pool_balance_quote)

                    # Felső sor hívása
                    log_line = _log_status_line(
                        symbol=symbol,
                        tf=tf,
                        fa=fa,
                        slw=slw,
                        last_px=last_px,
                        last_px_rt=last_px_rt,
                        ef_l=ef_l,
                        es_l=es_l,
                        use_htf=use_htf,
                        trend_htf=trend_htf,
                        use_rsi=use_rsi,
                        rsi_len=rsi_len,
                        rsi_val=rsi_val,
                        use_adx=use_adx,
                        adx_len=adx_len,
                        adx_val=adx_val,
                        use_zscore=use_zscore,
                        z_dir=z_dir,
                        is_st_strat=(strategy_mode == "Supertrend"),
                        st_trend=st_trend,
                        is_sqz_strat=(strategy_mode == "Bollinger Squeeze"),
                        sqz_is_on=is_sqz,
                        sqz_mom=mom_val,
                        bb_up=bb_up,
                        bb_dn=bb_dn,
                        kc_up=kc_up,
                        kc_dn=kc_dn,
                        use_brk=use_brk,
                        brk_n=brk_n,
                        hh=hh,
                        ll=ll,
                        up_lvl=up_lvl,
                        dn_lvl=dn_lvl,
                        drift_pct=drift_pct,
                        open_now=open_now,
                        max_open=max_open,
                        pool_used=pool_used_for_log,
                        pool_balance=pool_bal_for_log,
                    )

                    # --- Végső sor (Suffix) formázása ---
                    final_suffix = ""

                    # Determine true raw signal for logging
                    true_raw_signal = "hold"
                    if use_brk and brk_sig_raw in ("buy", "sell"):
                        true_raw_signal = brk_sig_raw
                    elif combined_sig_raw in ("buy", "sell"):
                        true_raw_signal = combined_sig_raw
                    elif sig_raw in ("buy", "sell"):
                        true_raw_signal = sig_raw

                    if combined_sig in (None, "", "hold"):
                        reasons_str = ", ".join(reasons) if reasons else ""

                        if true_raw_signal in ("buy", "sell"):
                            # Volt jel, de blokkoltuk -> (ok)
                            if reasons_str:
                                final_suffix = f" | {true_raw_signal} › hold ({reasons_str})"
                            else:
                                final_suffix = f" | {true_raw_signal} › hold"
                        else:
                            # Sima hold (várakozás) -> | ok
                            if reasons_str:
                                final_suffix = f" | {reasons_str}"
                            else:
                                final_suffix = " › hold"
                    else:
                        # Ha van érvényes jel (buy/sell)
                        final_suffix = f"  › {combined_sig}"

                    full_log_string = f"{log_line} | {filters_line}\n{final_suffix}\n"

                    # ================== STÁTUSZ LOG VEZÉRLÉS ==================
                    # A korábbi logika szerint, csak a 'log_line.rstrip() + ...' helyett a 'full_log_string'-et használjuk
                    verbose_on = bool(getattr(self, "_mb_log_verbose", False))
                    last_sig_log = getattr(self, "_mb_last_status_sig", "")
                    last_px_log  = float(getattr(self, "_mb_last_status_px", 0.0) or 0.0)

                    if not verbose_on:
                        if combined_sig in ("buy", "sell"):
                            if combined_sig != last_sig_log:
                                self._safe_log(full_log_string) # Módosított string
                        self._mb_last_status_sig = combined_sig
                        self._mb_last_status_px  = float(last_px_rt or last_px or 0.0)
                    else:
                        # (A verbose logikád marad a régi, csak a kiírt string változik)
                        try:
                            delay_s = int(getattr(self, "_mb_log_delay", 5))
                            if delay_s <= 0: delay_s = 5
                        except Exception: delay_s = 5

                        should_log = True
                        try:
                            now_ts_log = _safe_now_ts()
                            last_ts_log = getattr(self, "_mb_last_status_log_ts", 0)
                            if combined_sig in ("buy", "sell"):
                                should_log = True
                            else:
                                dt = now_ts_log - last_ts_log
                                px_move_pct = 0.0
                                if self._is_pos_num(last_px_log) and self._is_pos_num(last_px_rt) and last_px_rt > 0:
                                    px_move_pct = abs(last_px_rt - last_px_log) / last_px_log * 100.0
                                if dt < delay_s and combined_sig == last_sig_log and px_move_pct < 0.2:
                                    should_log = False
                                else:
                                    should_log = True

                            if should_log:
                                self._mb_last_status_log_ts = now_ts_log
                                self._mb_last_status_sig = combined_sig
                                self._mb_last_status_px = float(last_px_rt or last_px or 0.0)
                        except Exception:
                            should_log = True

                        if should_log:
                            self._safe_log(full_log_string) # Módosított string

                    # BUY / SELL pozíciók közös menedzsmentje
                    _manage_positions_for_side("buy")
                    _manage_positions_for_side("sell")

                    # --- OPEN COUNT frissítés a nyitási döntés ELŐTT ---
                    # (A menedzsment ugyanebben a ciklusban zárhatott pozíciókat,
                    # ezért a korábban számolt open_now elavulhat.)
                    with self._mb_lock:
                        open_now = len(self._sim_pos_long) + len(self._sim_pos_short)

                    # --- ÚJ NYITÁS (cooldown + pool limit) ---
                    now = int(time.time())
                    if combined_sig in ('buy','sell') and (now - self._mb_last_cross_ts >= cd_s):
                        if pause_new:
                            self._safe_log(f"⏸️ Új nyitás szüneteltetve (Checkbox). Jel ({combined_sig}) átugorva.\n")
                            opened = False
                            time.sleep(1)
                            continue
                        if max_open > 0 and open_now >= max_open:
                            self._safe_log(
                                f"⏸ Max pozíció elérve ({open_now}/{max_open}) – új nyitás átugorva.\n"
                            )
                            opened = False
                            time.sleep(1)
                            continue

                        # --- DUPLIKÁLT ÁRSZINT SZŰRŐ (Optimalizált) ---
                        if self._is_pos_num(last_px_rt) and last_px_rt > 0:
                            # Tolerancia olvasása a SNAPSHOT config-ból
                            tol_pct_val = max(0.0, float(cfg_ns.dup_tol_pct))

                            # OPTIMALIZÁCIÓ: Ha 0 a tolerancia, ne is keressen feleslegesen
                            found = False
                            existing_entry = 0.0
                            diff_pct = 0.0

                            if tol_pct_val > 0:
                                found, existing_entry, diff_pct = _has_nearby_pos(
                                    combined_sig,
                                    last_px_rt,
                                    tol_pct=tol_pct_val,
                                    symbol_filter=symbol,
                                )

                            if found:
                                # --- SPAM CSÖKKENTÉS (Szimbólumonként külön!). Csak akkor logolunk, ha verbose aktív és letelt az idő
                                now_ts_skip = int(time.time())

                                # Inicializáljuk a dict-et, ha még nincs (hogy páronként tudjuk követni)
                                if not hasattr(self, "_mb_last_skip_log_map"):
                                    self._mb_last_skip_log_map = {}

                                # Kulcs: symbol + irány (pl. "SOL-USDT_LONG")
                                log_key = f"{symbol}_{combined_sig}"
                                last_skip_ts = self._mb_last_skip_log_map.get(log_key, 0)

                                # Itt állíthatod a ritkítást (most 30 másodperc)
                                if verbose_on and (now_ts_skip - last_skip_ts > 30):
                                    self._safe_log(
                                        f"⏭ {combined_sig.upper()} jel átugorva ({symbol}): már van pozíció "
                                        f"hasonló áron (entry={existing_entry:.5f}, now={last_px_rt:.5f}, "
                                        f"diff={diff_pct:.2f}%, tol={tol_pct_val:.2f}%). [30s]"
                                    )
                                    # Frissítjük az időbélyeget ehhez a kulcshoz
                                    self._mb_last_skip_log_map[log_key] = now_ts_skip
                                continue

                        # friss ticker: WS az első, REST csak ha nincs használható WS ár  ### WS-OPEN
                        if (not self._is_pos_num(last_px_rt)) or last_px_rt <= 0:
                            try:
                                rt = float(self.get_best_price(symbol))
                                if self._is_pos_num(rt) and rt > 0:
                                    last_px_rt = rt
                            except Exception:
                                pass

                        # FONTOS: ha itt frissült a last_px_rt, akkor a nyitáshoz használt ár is frissüljön
                        px_for_mgmt = last_px_rt if (self._is_pos_num(last_px_rt) and last_px_rt > 0) else last_px
                        entry_px = float(px_for_mgmt)

                        # keret snapshot lock alatt
                        with self._mb_lock:
                            _pool_bal = float(self._pool_balance_quote)
                            _pool_used = float(self._pool_used_quote)
                        free_pool = max(0.0, _pool_bal - _pool_used)
                        sizep_to_use = max(0.0, min(100.0, float(sizep)))

                        size = None
                        funds = None
                        open_size = 0.0
                        commit_usdt = 0.0
                        nominal_q = 0.0

                        # KERET: teljes szabad pool – a %-ot _mb_compute_size fogja alkalmazni
                        max_quote_for_trade = free_pool

                        if max_quote_for_trade <= 0.0:
                            self._safe_log("ℹ️ Nincs szabad pool a nyitáshoz (keret limit). Kimarad.\n")
                        else:
                            # Egységes méretszámítás, akár 'quote', akár 'base' módban vagyunk
                            size, funds = self._mb_compute_size(
                                symbol=cfg_ns.symbol,
                                side=combined_sig,
                                price=px_for_mgmt,
                                size_pct=cfg_ns.sizep,
                                input_mode=cfg_ns.inpm,
                                mode=cfg_ns.mode,
                                leverage=cfg_ns.lev,
                                budget_quote=cfg_ns.budget_ui,
                                dry=cfg_ns.dry,
                                auto_borrow=cfg_ns.auto_borrow,
                                lot_step=lot_step,
                                price_step=price_step,
                            )

                            # _mb_compute_size logikája:
                            #   - input_mode='quote' → (size=None, funds>0)
                            #   - input_mode='base'  → (size>0, funds=None)
                            if funds is not None and funds > 0:
                                # QUOTE mód: funds = commit_usdt
                                commit_usdt = float(funds)
                                nominal_q   = commit_usdt * max(1, lev)
                                open_size   = nominal_q / max(px_for_mgmt, 1e-12)
                            elif size is not None and size > 0:
                                # BASE mód: size = darabszám
                                open_size   = float(size)
                                nominal_q   = open_size * px_for_mgmt
                                commit_usdt = nominal_q / max(1, lev)
                            else:
                                open_size = 0.0
                                commit_usdt = 0.0
                                nominal_q = 0.0

                            # --- POOL CLAMP: commit/nominal/size ráhúzása a free_pool-ra ---
                            try:
                                lev_eff = max(1, int(lev))
                                free_pool_eff = max(0.0, float(free_pool))

                                # 1) fee headroom becslés
                                fee_rate = self._mb_get_taker_fee()
                                fee_est = 0.0
                                if self._is_pos_num(open_size) and open_size > 0:
                                    fee_est = float(self._mb_est_fee_quote(entry_px, float(open_size), float(fee_rate)))
                                max_commit = max(0.0, free_pool_eff - max(0.0, fee_est))

                                # 2) commit clamp
                                if self._is_pos_num(commit_usdt) and commit_usdt > max_commit:
                                    commit_usdt = max_commit

                                # 3) újraszámolás
                                nominal_q = float(commit_usdt) * float(lev_eff)
                                open_size = float(nominal_q) / max(float(px_for_mgmt), 1e-12)

                                # 4) lépésre kerekítés után korrekció
                                open_size = self._mb_floor_to_step_dec(open_size, lot_step)

                                # BUY esetén felfelé kerekítjük a funds-ot (quote_step)
                                if combined_sig == 'buy' and quote_step > 0:
                                    raw_nom = float(open_size) * float(px_for_mgmt)
                                    qs = float(quote_step)
                                    nominal_q = math.ceil(raw_nom / qs) * qs
                                else:
                                    nominal_q = float(open_size) * float(px_for_mgmt)

                                commit_usdt = float(nominal_q) / float(lev_eff)
                            except Exception:
                                pass

                            open_size = self._mb_floor_to_step_dec(open_size, lot_step)

                            self._safe_log(
                                f"📈 Jel: {combined_sig.upper()} | price={px_for_mgmt:.6f} | size%={sizep_to_use:.2f} | "
                                f"nominal={nominal_q:.2f} | commit={commit_usdt:.2f} | free_pool={free_pool:.2f} | "
                                f"lev={lev} | mode={mode} dry={dry}\n"
                            )

                            opened = False
                            if commit_usdt <= 0 or (combined_sig == 'sell' and open_size <= 0):
                                self._safe_log("ℹ️ Nulla méret / nincs keret – nincs nyitás.\n")
                            else:
                                # --- EGYSÉGESÍTETT SANITIZER ÉS KÜLDÉS ---
                                is_buy = (combined_sig == 'buy')

                                # Paraméterek a sanitizerhez
                                # BUY: funds_quote kell (nominal_q), size_base = None
                                # SELL: size_base kell (open_size), funds_quote = None
                                req_sz = None
                                req_fu = None
                                if is_buy:
                                    req_fu = float(nominal_q)
                                else:
                                    req_sz = float(open_size)

                                sb, fq = self._mb_sanitize_order(
                                    symbol=symbol, side=combined_sig,
                                    price=px_for_mgmt,
                                    size_base=req_sz,
                                    funds_quote=req_fu
                                )
                                size_to_send, funds_to_send = sb, fq

                                # Sikerült?
                                valid = (funds_to_send is not None) if is_buy else (size_to_send is not None)

                                if not valid:
                                    self._safe_log(f"ℹ️ Sanitizer eldobta a {combined_sig} nyitást (min/step miatt).\n")
                                    opened = False
                                else:
                                    # Commit újraszámítás a végleges értékekből (szimulációhoz)
                                    if is_buy:
                                        sz_sim = float(size_to_send) # Sanitizer visszaadja a becsült size-t is
                                        commit_sim = float(funds_to_send) / max(lev, 1)
                                    else:
                                        sz_sim = float(size_to_send)
                                        commit_sim = (sz_sim * float(px_for_mgmt)) / max(lev, 1)

                                    # Csomagok előkészítése
                                    atr_pack_arg = (mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val) if (use_atr and atr_val) else None
                                    fixed_pack_arg = (tpct, spct, trpct) if use_fixed else None

                                    if dry:
                                        _open_sim(
                                            combined_sig, entry_px, sz_sim, commit_sim,
                                            atr_pack=atr_pack_arg,
                                            fixed_pack=fixed_pack_arg,
                                            symbol_for_pos=symbol
                                        )
                                        opened = True
                                    else:
                                        # LIVE ORDER
                                        _payload = {
                                            "mode": mode, "symbol": symbol, "side": combined_sig,
                                            "size_base": size_to_send, "funds_quote": funds_to_send,
                                            "leverage": lev, "auto_borrow": auto_borrow
                                        }
                                        self._safe_log(f"🐞 SEND OPEN: {self._mb_pp(_payload)}\n")

                                        try:
                                            with self._ex_lock:
                                                resp = self.exchange.place_margin_market_order(**_payload)

                                            self._safe_log(f"🐞 RECV OPEN: {self._mb_pp(resp)}\n")

                                            # Válasz feldolgozása
                                            code = None; data = None
                                            if isinstance(resp, dict):
                                                code = resp.get("code")
                                                data = resp.get("data") or {}
                                            elif hasattr(resp, "code"):
                                                code = getattr(resp, "code", None)
                                                data = getattr(resp, "data", None)

                                            oid = cid = None
                                            if isinstance(data, dict):
                                                oid = data.get("orderId") or data.get("id")
                                                cid = data.get("clientOid") or data.get("clientOrderId")

                                            if code and str(code) != "200000":
                                                self._safe_log(f"❌ LIVE order elutasítva (code={code})\n")
                                                opened = False
                                            elif not oid and not cid:
                                                self._safe_log(f"⚠️ LIVE válasz orderId nélkül\n")
                                                opened = False
                                            else:
                                                order_key = oid or cid
                                                self._safe_log(f"✅ LIVE {combined_sig.upper()} OK | oid={order_key}\n")

                                                # Fill adatok lekérése (Realtime partial fill + fee)
                                                # Itt a már meglévő market steps-et használhatjuk, ha kiemeltük a ciklus elé
                                                # Ha nem, akkor itt lekérjük (bár jobb lenne kint)
                                                try:
                                                    ls_now, _, _, _, _ = self._mb_get_market_steps(symbol)
                                                except: ls_now = 0.0

                                                req_sz_f = float(size_to_send) if size_to_send else None
                                                req_fu_f = float(funds_to_send) if funds_to_send else None

                                                fb, commit_real_ws, fee_open_actual = self._mb_resolve_open_fill(
                                                    order_id=str(order_key),
                                                    side=combined_sig,
                                                    req_price=entry_px,
                                                    req_size=req_sz_f,
                                                    req_funds=req_fu_f,
                                                    lev=lev,
                                                    lot_step=float(ls_now or 0.0),
                                                )

                                                size_now = None; commit_used = None
                                                if fb > 0.0:
                                                    size_now = float(fb)
                                                    commit_used = float(commit_real_ws or 0.0)
                                                else:
                                                    # Fallback becslés
                                                    if funds_to_send:
                                                        commit_used = float(funds_to_send) / max(lev, 1)
                                                        size_now = self._sdiv(float(funds_to_send), px_for_mgmt, 0.0)
                                                    else:
                                                        size_now = float(size_to_send)
                                                        commit_used = self._sdiv(size_now * float(px_for_mgmt), lev, 0.0)

                                                    # Padlózás
                                                    size_now = self._mb_floor_to_step_dec(size_now, float(ls_now or 0.0))

                                                if not commit_used or commit_used <= 0:
                                                    commit_used = float(commit_usdt)

                                                # Fee és PnL becslés
                                                _fee_rate = self._mb_get_taker_fee()
                                                _fee_est = self._mb_est_fee_quote(entry_px, size_now, _fee_rate)
                                                fee_act = float(fee_open_actual or 0.0)
                                                _fee_final = fee_act if fee_act > 0 else _fee_est

                                                pnl_est = None
                                                try:
                                                    rt_now = self.get_best_price(symbol)
                                                    if self._is_pos_num(rt_now) and rt_now > 0:
                                                        gross = (rt_now - entry_px) * size_now * (1 if is_buy else -1)
                                                        pnl_est = gross - float(_fee_final)
                                                except: pass

                                                # History
                                                self._mb_hist_add_open(
                                                    order_id=str(order_key),
                                                    side=combined_sig, entry=entry_px,
                                                    size=size_now, lev=lev, fee=float(_fee_final),
                                                    pnl_est=pnl_est
                                                )

                                                # SIM tükrözés
                                                _open_sim(
                                                    combined_sig, entry_px, size_now, commit_used,
                                                    atr_pack=atr_pack_arg,
                                                    fixed_pack=fixed_pack_arg,
                                                    fee_open_actual_override=fee_act,
                                                    fee_reserved_override=_fee_final,
                                                    oid=str(order_key),
                                                    symbol_for_pos=symbol
                                                )
                                                opened = True

                                        except Exception as e:
                                            self._safe_log(f"❌ LIVE order hiba: {e}\n")
                                            opened = False

                            if opened:
                                self._mb_last_cross_ts = now
                                self._mb_last_signal = combined_sig

                    # --- TF-hez igazított alvás, websocket-tel gyorsítva ---  ### WS-SLEEP
                    if getattr(self, "_ticker_ws", None) is not None:
                        # ha él a realtime WS ár, tickeljünk gyorsabban
                        _sleep_total = 1
                    else:
                        _sleep_total = max(2, min(30, tf_sec // 3))
                    for _ in range(int(_sleep_total)):
                        if not self._mb_running:
                            break
                        time.sleep(1)

                except Exception as e:
                    msg = str(e)
                    if "429" not in msg and "rate" not in msg.lower():
                        self._safe_log(f"❌ Bot hiba: {e}\n")
                    time.sleep(2)

        finally:
            self._mb_running = False
            was_manual = getattr(self, "_mb_stopping", False)

            if not was_manual:
                self._mb_do_summary_once("_mb_worker")
            else:
                self._mb_stopping = False

    def _mb_toggle_fixed_widgets(self):
        try:
            on = bool(self.mb_use_fixed.get())
            # kizárás: ha FIX-et bekapcsolják, kapcsoljuk le az ATR-t
            if on and hasattr(self, "mb_use_atr") and self.mb_use_atr.get():
                self.mb_use_atr.set(False)
                self._mb_toggle_atr_widgets()
                self._safe_log("🔧 FIX aktiválva → ATR kikapcsolva.\n")

            state = "normal" if on else "disabled"
            for w in (self.mb_sl_pct, self.mb_tp_pct, self.mb_trail_pct):
                w.config(state=state)
        except Exception:
            pass

    def _mb_toggle_atr_widgets(self):
        try:
            on = bool(self.mb_use_atr.get())
            # kizárás: ha ATR-t bekapcsolják, kapcsoljuk le a FIX-et
            if on and hasattr(self, "mb_use_fixed") and self.mb_use_fixed.get():
                self.mb_use_fixed.set(False)
                self._mb_toggle_fixed_widgets()
                self._safe_log("🔧 ATR aktiválva → FIX kikapcsolva.\n")

            state = "normal" if on else "disabled"
            for w in (self.mb_atr_n, self.mb_atr_mul_sl, self.mb_atr_mul_tp1, self.mb_atr_mul_tp2, self.mb_atr_mul_trail):
                w.config(state=state)

            # UX: ha ATR ON, szürkítsük a FIX mezőit (de a fenti set(False) miatt úgyis ki lesznek)
            if on:
                for w in (self.mb_sl_pct, self.mb_tp_pct, self.mb_trail_pct):
                    w.config(state="disabled")
            else:
                # FIX widgetek állapota a FIX checkbox alapján
                self._mb_toggle_fixed_widgets()
        except Exception:
            pass

    def _mb_toggle_brk_widgets(self):
        try:
            state = "normal" if self.mb_use_brk.get() else "disabled"
            for w in (self.mb_brk_n, self.mb_brk_buf):
                w.config(state=state)
        except Exception:
            pass

    def _mb_toggle_live_widgets(self):
        """Élő ár figyelése ki/be – a Shock mezők engedélyezése/tiltása."""
        try:
            on = bool(self.mb_use_live.get())
            state = "normal" if on else "disabled"
            for w in (self.mb_live_shock_pct, self.mb_live_shock_atr):
                w.config(state=state)
        except Exception:
            pass

    def _mb_toggle_rsi_widgets(self):
        """RSI használata ki/be – az RSI mezők engedélyezése/tiltása."""
        try:
            on = bool(self.mb_use_rsi.get())
            state = "normal" if on else "disabled"
            for w in (
                self.mb_rsi_len,
                self.mb_rsi_buy_min,
                self.mb_rsi_buy_max,
                self.mb_rsi_sell_min,
                self.mb_rsi_sell_max,
            ):
                w.config(state=state)
        except Exception:
            pass

    def _mb_toggle_adx_widgets(self):
        """ADX filter UI enable/disable."""
        try:
            on = bool(self.mb_use_adx.get())
        except Exception:
            on = False
        st = "normal" if on else "disabled"
        for w in (getattr(self, "mb_adx_len", None), getattr(self, "mb_adx_min", None)):
            try:
                if w is not None:
                    w.configure(state=st)
            except Exception:
                pass

    def _mb_toggle_htf_widgets(self):
        """HTF filter ki/be – a HTF TF combobox engedélyezése/tiltása."""
        try:
            on = bool(self.mb_use_htf.get())
            state = "readonly" if on else "disabled"
            self.mb_htf_tf.config(state=state)
        except Exception:
            pass

    def _mb_on_fixed_changed(self):
        """Ha FIX-t bekapcsolod, ATR-t kikapcsolja (pipa is le), és frissíti a mezők állapotát."""
        if getattr(self, "_mb_toggling", False):
            return
        self._mb_toggling = True
        try:
            if self.mb_use_fixed.get():
                # FIX ON -> ATR OFF
                if self.mb_use_atr.get():
                    self.mb_use_atr.set(False)
            # mezők állapotainak frissítése
            self._mb_toggle_fixed_widgets()
            self._mb_toggle_atr_widgets()
        finally:
            self._mb_toggling = False

    def _mb_on_atr_changed(self):
        """Ha ATR-t bekapcsolod, FIX-et kikapcsolja (pipa is le), és frissíti a mezők állapotát."""
        if getattr(self, "_mb_toggling", False):
            return
        self._mb_toggling = True
        try:
            if self.mb_use_atr.get():
                # ATR ON -> FIX OFF
                if self.mb_use_fixed.get():
                    self.mb_use_fixed.set(False)
            # mezők állapotainak frissítése
            self._mb_toggle_fixed_widgets()
            self._mb_toggle_atr_widgets()
        finally:
            self._mb_toggling = False

    def _mb_toggle_zscore_widgets(self, *_):
        # A régi metódus, amit a checkbox hívott.
        # Most már a _mb_on_strategy_change végzi a munkát.
        self._mb_on_strategy_change()

    def _mb_on_strategy_change(self, *_):
        """Stratégia váltásakor letiltjuk/engedélyezzük a releváns widgeteket."""
        try:
            strat = self.mb_strategy.get()
        except Exception:
            strat = "EMA"

        is_ema = (strat == "EMA")
        is_zscore = (strat == "Z-Score")
        is_sqz = (strat == "Bollinger Squeeze")
        is_st = (strat == "Supertrend")

        # 1) EMA widgetek
        ema_state = "normal" if is_ema else "disabled"
        for w in (getattr(self, "mb_ma_fast", None), getattr(self, "mb_ma_slow", None)):
            if w:
                try: w.configure(state=ema_state)
                except Exception: pass

        # 2) Squeeze widgetek
        sqz_state = "normal" if is_sqz else "disabled"
        for w in (getattr(self, "mb_sqz_len", None), getattr(self, "mb_sqz_bb_mult", None), getattr(self, "mb_sqz_kc_mult", None)):
            if w:
                try: w.configure(state=sqz_state)
                except Exception: pass

    # ============ NEW: Leállításkori / ad-hoc összegzés ============
    def _mb_summary(self):
        """Összegző statisztika (SIM trade-ek alapján)."""
        try:
            with self._mb_lock:
                hist = list(getattr(self, "_sim_history", []) or [])
            if not hist:
                self._safe_log("ℹ️ Nincs lezárt ügylet – nincs összegzés.\n")
                return

            trades = [t for t in hist if not t.get("partial")]  # csak teljes zárások
            if not trades:
                self._safe_log("ℹ️ Csak rész-zárások történtek – nincs teljes ügylet összegzés.\n")
                return

            total_pnl = sum(float(t.get("pnl", 0.0)) for t in trades)
            wins = [t for t in trades if float(t.get("pnl", 0.0)) > 0]
            losses = [t for t in trades if float(t.get("pnl", 0.0)) < 0]
            n = len(trades)
            avg = (total_pnl / n) if n else 0.0
            win_rate = (len(wins) / n * 100.0) if n else 0.0

            sum_win = sum(float(t.get("pnl", 0.0)) for t in wins)
            sum_loss = sum(float(t.get("pnl", 0.0)) for t in losses)

            msg = (
                "\n📊 Összegzés – Bot leállításkor\n"
                f"• Ügyletek száma: {n}\n"
                f"• Nyerő ügyletek: {len(wins)}\n"
                f"• Vesztes ügyletek: {len(losses)}\n"
                f"• Nyertes összeg: {sum_win:+.2f} USDT\n"
                f"• Vesztes összeg: {sum_loss:+.2f} USDT\n"
                f"• Végső eredmény: {total_pnl:+.2f} USDT\n"
                f"• Átlagos PnL: {avg:+.3f} USDT/trade\n"
                f"• Win rate: {win_rate:.1f}%\n"
            )
            self._safe_log(msg)
        except Exception as e:
            self._safe_log(f"⚠️ Összegzés hiba: {e}\n")

    def _mb_do_summary_once(self, origin: str):
        """Összegzést pontosan egyszer írjunk ki, akárhonnan is érkezik a leállás."""
        with self._mb_lock:
            if getattr(self, "_mb_summary_done", False):
                return
            self._mb_summary_done = True
        try:
            self._mb_summary()
        except Exception as e:
            self._safe_log(f"⚠️ Összegzés hiba ({origin}): {e}\n")
        self._safe_log(f"⏹️ Bot leállt. (forrás: {origin})\n")

    def _mb_breakout_signal(self, df, lookback: int = 20, buf_pct: float = 0.05) -> tuple[str, float, float, float, float]:
        """
        Egyszerű HH/LL breakout az UTOLSÓ LEZÁRT gyertyára.
        Vissza: (sig, hh, ll, up_lvl, dn_lvl)
          sig: 'buy' | 'sell' | 'hold'
          hh/ll: lookback legmagasabb/legalacsonyabb (előző gyertyáig)
          up_lvl/dn_lvl: pufferrel igazított szintek
        """
        if len(df) < max(lookback + 2, 10):
            return "hold", float("nan"), float("nan"), float("nan"), float("nan")

        # csak a lezárt gyertyáig számolunk
        h = pd.Series(df['h'], dtype='float64').iloc[:-1]
        l = pd.Series(df['l'], dtype='float64').iloc[:-1]

        hh = float(h.rolling(lookback).max().iloc[-1])
        ll = float(l.rolling(lookback).min().iloc[-1])

        last_px = float(df['c'].iloc[-1])
        buf = max(0.0, float(buf_pct)) / 100.0
        up_lvl = hh * (1.0 + buf)
        dn_lvl = ll * (1.0 - buf)

        if last_px >= up_lvl:
            return "buy", hh, ll, up_lvl, dn_lvl
        if last_px <= dn_lvl:
            return "sell", hh, ll, up_lvl, dn_lvl
        return "hold", hh, ll, up_lvl, dn_lvl

    def _mb_sync_lev_cap(self):
        """A tőkeáttét maximumának automatikus beállítása a mód alapján."""
        try:
            cap = 5 if self.mb_mode.get() == "cross" else 10
            self.mb_lev.config(to=cap)
            cur = int(self.mb_lev.get() or "1")
            if cur > cap:
                self.mb_lev.delete(0, tk.END); self.mb_lev.insert(0, str(cap))
        except Exception:
            pass

    # ---------- Segédfüggvény: Wilder's Smoothing (RMA) ----------
    # A TradingView és a standard technikai elemzés ezt használja RSI-hez és ATR-hez.
    def _rma(self, series, n: int):
        return series.ewm(alpha=1.0 / n, adjust=False).mean()

    # ---------- Jel-generátor: EMA KERESZTEZÉS ----------
    def _mb_signal_from_ema_live(
        self,
        series,
        fast: int,
        slow: int,
        last_px_rt: float | None,
        atr_eps_mult: float | None = None,
        invert: bool | None = None,
    ) -> tuple[str, float, float]:
        """
        EMA jelgenerátor (slope nélkül):
          1) Friss keresztezés detektálása hysteresis sávval.
          2) ATR alapú zajszűrés.
          3) Invertálás (ha kérve van).
        """
        # --- adat ellenőrzés ---
        s = pd.Series(series, dtype="float64").copy()
        if len(s) < max(fast, slow) + 5:
            return "hold", float("nan"), float("nan")

        # --- EMA-k számítása ---
        ema_f = s.ewm(span=fast, adjust=False).mean()
        ema_s = s.ewm(span=slow, adjust=False).mean()

        ef_p, ef_l = float(ema_f.iloc[-2]), float(ema_f.iloc[-1])
        es_p, es_l = float(ema_s.iloc[-2]), float(ema_s.iloc[-1])

        diff_prev = ef_p - es_p
        diff_now  = ef_l - es_l

        # --- hysteresis sáv ---
        if atr_eps_mult is None:
            atr_eps_mult = 0.0

        # ATR az osztályból – ez lehet 0 is, az csak annyit jelent, hogy nincs sáv
        try:
            atr_last = float(getattr(self, "_mb_last_atr_val", 0.0))
        except Exception:
            atr_last = 0.0

        band = atr_last * atr_eps_mult if (atr_last > 0 and atr_eps_mult > 0) else 0.0

        up_th =  band
        dn_th = -band

        # --- keresztezések ---
        crossed_up   = (diff_prev <= up_th) and (diff_now > up_th)
        crossed_down = (diff_prev >= dn_th) and (diff_now < dn_th)

        # --- döntés ---
        if crossed_up:
            sig = "buy"
        elif crossed_down:
            sig = "sell"
        else:
            sig = "hold"

        # --- invertálás ---
        if invert is None:
            invert = False

        if invert:
            if sig == "buy":
                sig = "sell"
            elif sig == "sell":
                sig = "buy"

        return sig, ef_l, es_l

    # ---------- ATR számítás (Javítva: Wilder's Smoothing) ----------
    def _mb_atr(self, df, n: int = 14):
        """
        Valódi ATR számítás (Wilder's Smoothing).
        Ez pontosabb és jobban egyezik a TradingView értékeivel.
        """
        h = df['h'].astype(float)
        l = df['l'].astype(float)
        c = df['c'].astype(float)
        prev_c = c.shift(1)

        # True Range vektorizált számítása
        tr1 = h - l
        tr2 = (h - prev_c).abs()
        tr3 = (l - prev_c).abs()

        tr = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1)

        # Sima EMA (ewm span) helyett RMA (alpha = 1/n)
        atr = self._rma(tr, n)
        return atr

    # ---------- RSI Képlet (Javítva: Wilder's Smoothing) ----------
    def _mb_rsi(self, series, n: int = 14):
        """
        Valódi RSI számítás (Wilder's Smoothing).
        Ez pontosabb és jobban egyezik a TradingView értékeivel.
        """
        s = pd.Series(series, dtype='float64')
        delta = s.diff()

        gain = delta.clip(lower=0.0)
        loss = -delta.clip(upper=0.0)

        # EMA helyett Wilder's Smoothing (RMA)
        avg_gain = self._rma(gain, n)
        avg_loss = self._rma(loss, n)

        rs = avg_gain / avg_loss.replace(0, 1e-12) # Nullával osztás védelem
        rsi = 100 - (100 / (1 + rs))
        return rsi

    def _mb_supertrend(self, df, period=10, multiplier=3.0) -> Tuple[pd.Series, pd.Series]:
        """
        Supertrend számítás.
        Visszaad: (trend_direction, supertrend_line)
        trend_direction: +1 (Bull/Zöld), -1 (Bear/Piros)
        """
        high = df['h'].astype(float)
        low = df['l'].astype(float)
        close = df['c'].astype(float)

        atr = self._mb_atr(df, n=period)

        hl2 = (high + low) / 2
        basic_upper = hl2 + (multiplier * atr)
        basic_lower = hl2 - (multiplier * atr)

        # Inicializálás
        final_upper = pd.Series(index=df.index, dtype='float64')
        final_lower = pd.Series(index=df.index, dtype='float64')
        trend = pd.Series(index=df.index, dtype='int')
        supertrend = pd.Series(index=df.index, dtype='float64')

        # Első értékek (naivan)
        final_upper.iloc[0] = basic_upper.iloc[0]
        final_lower.iloc[0] = basic_lower.iloc[0]
        trend.iloc[0] = 1
        supertrend.iloc[0] = final_lower.iloc[0]

        # Iteratív számítás (sajnos a Supertrend rekurzív természete miatt nehéz vektorizálni teljesen)
        # De mivel a dataframe mérete a botban limitált (cache), ez nem lesz lassú.
        n = len(df)
        bu_vals = basic_upper.values
        bl_vals = basic_lower.values
        close_vals = close.values

        fu_vals = np.zeros(n)
        fl_vals = np.zeros(n)
        trend_vals = np.zeros(n, dtype=int)
        st_vals = np.zeros(n)

        # Első elem inicializálás
        fu_vals[0] = bu_vals[0]
        fl_vals[0] = bl_vals[0]
        trend_vals[0] = 1
        st_vals[0] = fl_vals[0]

        for i in range(1, n):
            # Final Upper Band
            if (bu_vals[i] < fu_vals[i-1]) or (close_vals[i-1] > fu_vals[i-1]):
                fu_vals[i] = bu_vals[i]
            else:
                fu_vals[i] = fu_vals[i-1]

            # Final Lower Band
            if (bl_vals[i] > fl_vals[i-1]) or (close_vals[i-1] < fl_vals[i-1]):
                fl_vals[i] = bl_vals[i]
            else:
                fl_vals[i] = fl_vals[i-1]

            # Trend
            prev_trend = trend_vals[i-1]
            curr_close = close_vals[i]
            curr_fu = fu_vals[i]
            curr_fl = fl_vals[i]

            if prev_trend == 1: # Bull volt
                if curr_close < curr_fl:
                    trend_vals[i] = -1 # Bear lett
                else:
                    trend_vals[i] = 1
            else: # Bear volt
                if curr_close > curr_fu:
                    trend_vals[i] = 1 # Bull lett
                else:
                    trend_vals[i] = -1

            # Supertrend Line
            if trend_vals[i] == 1:
                st_vals[i] = curr_fl
            else:
                st_vals[i] = curr_fu

        # Vissza Series-be
        trend_series = pd.Series(trend_vals, index=df.index)
        st_series = pd.Series(st_vals, index=df.index)

        return trend_series, st_series

    def _mb_adx(self, df, length: int = 14) -> float | None:
        """
        Stabil ADX (Wilder / RMA).
        df oszlopok: 'h','l','c'
        Vissza: utolsó ADX érték vagy None.
        """
        try:
            n = int(max(2, int(length or 14)))
            if df is None or len(df) < n * 2:
                return None

            # --- Biztos numerikus input (float) ---
            high  = pd.to_numeric(df["h"], errors="coerce").astype("float64")
            low   = pd.to_numeric(df["l"], errors="coerce").astype("float64")
            close = pd.to_numeric(df["c"], errors="coerce").astype("float64")

            if high.isna().all() or low.isna().all() or close.isna().all():
                return None

            up   = high.diff()
            down = -low.diff()

            plus_dm  = up.where((up > down) & (up > 0), 0.0).astype("float64")
            minus_dm = down.where((down > up) & (down > 0), 0.0).astype("float64")

            tr1 = (high - low).abs()
            tr2 = (high - close.shift(1)).abs()
            tr3 = (low  - close.shift(1)).abs()
            tr = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1).astype("float64")

            atr = self._rma(tr, n)
            if atr is None or len(atr) == 0:
                return None
            atr = pd.to_numeric(atr, errors="coerce").astype("float64").replace(0.0, np.nan)

            pdi = self._rma(plus_dm, n)
            mdi = self._rma(minus_dm, n)
            if pdi is None or mdi is None:
                return None

            pdi = (100.0 * (pd.to_numeric(pdi, errors="coerce").astype("float64") / atr))
            mdi = (100.0 * (pd.to_numeric(mdi, errors="coerce").astype("float64") / atr))

            denom = (pdi + mdi).replace(0.0, np.nan)

            # --- Itt volt a FutureWarning forrása: tegyük garantáltan numerikussá fillna előtt ---
            dx = (100.0 * (pdi - mdi).abs() / denom)
            dx = dx.replace([np.inf, -np.inf], np.nan)
            dx = pd.to_numeric(dx, errors="coerce").fillna(0.0).astype("float64")

            adx = self._rma(dx, n)
            if adx is None or len(adx) == 0:
                return None

            val = float(pd.to_numeric(adx.iloc[-1], errors="coerce"))
            if not np.isfinite(val):
                return None
            return val

        except Exception as e:
            try:
                if not hasattr(self, "_adx_err_logged"):
                    self._adx_err_logged = True
                    self._safe_log(f"⚠️ ADX számítási hiba: {e}\n")
            except Exception:
                pass
            return None

    # ---------- HTF trend filter (Biztonságosabb) ----------
    def _mb_trend_filter(
        self,
        symbol: str,
        tf: str = "1h",
        fast: int = 20,
        slow: int = 50,
        invert: bool | None = None,
    ) -> int:
        """
        HTF Filter: +1 (Bull), -1 (Bear), 0 (HOLD/Hiba).

        JAVÍTVA:
          - NEM indít WebSocketet, azt a fő worker (_mb_worker) intézi.
          - Itt csak az adatot olvassuk a K-Line WS cache-ből, vagy REST-ről fallback-kel.
        """
        try:
            # A slow EMA-hoz kb 2–3x annyi gyertya elég
            limit = max(100, slow * 3)

            # 1) Megpróbáljuk a K-Line WS cache-ből
            try:
                ohlcv = self._mb_get_ohlcv(symbol, tf, limit=limit)
            except Exception:
                ohlcv = []

            # 2) Ha nincs WS adat → fallback: exchange.fetch_ohlcv
            if not ohlcv:
                with self._ex_lock:
                    ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=limit)

            if not ohlcv or len(ohlcv) < slow + 5:
                return 0

            df = pd.DataFrame(ohlcv, columns=["ts", "o", "h", "l", "c", "v"])
            s = df["c"].astype(float)

            ema_f = s.ewm(span=fast, adjust=False).mean().iloc[-1]
            ema_s = s.ewm(span=slow, adjust=False).mean().iloc[-1]

            # Alap trend irány
            trend = 0
            if ema_f > ema_s:
                trend = +1
            elif ema_f < ema_s:
                trend = -1

            # Invertálás
            if invert is None:
                try:
                    invert = bool(getattr(self, "mb_invert_ema", False).get())
                except Exception:
                    invert = False

            return -trend if invert else trend

        except Exception:
            return 0

    # ---- Z-score függvények ----
    def _mb_ohlcv_to_df(self, ohlcv, tz_unit: str = "ms"):
        """OHLCV listából DataFrame készítése (Gyorsított típuskonverzióval)."""
        if not ohlcv:
            return pd.DataFrame()

        df = pd.DataFrame(ohlcv, columns=["ts", "open", "high", "low", "close", "volume"])

        # Időbélyeg konverzió
        df["ts"] = pd.to_datetime(df["ts"], unit=tz_unit, utc=True)
        df.set_index("ts", inplace=True)

        # Csak a numerikus oszlopokat konvertáljuk float-ra (biztonságosabb)
        numeric_cols = ["open", "high", "low", "close", "volume"]
        df[numeric_cols] = df[numeric_cols].astype(float)

        return df

    def _compute_zscore_signal(
        self,
        symbol: str,
        tf: str,
        length: int = 40,
        data_points: int = 100,
        df=None,
    ):
        """Z-score wrapper hibakezeléssel és automatikus oszlopnevezéssel."""
        try:
            # 1. Adat beszerzés (ha nincs átadva)
            if df is None:
                try:
                    ohlcv = self._mb_get_ohlcv(
                        symbol,
                        tf,
                        limit=max(length * 3, data_points + 50), # Kicsit több puffer
                    )
                except Exception:
                    ohlcv = []
                df = self._mb_ohlcv_to_df(ohlcv)
            else:
                # 2. Ha van adat, másolatot készítünk a biztonság kedvéért
                df = df.copy()

            # 3. Oszlopnevek egységesítése (Rövid -> Hosszú)
            # Ez a map-alapú rename tisztább, mint a sok if
            rename_map = {"c": "close", "o": "open", "h": "high", "l": "low", "v": "volume"}
            df.rename(columns=rename_map, inplace=True)

            # 4. Validáció
            if df.empty or len(df) < length + 2:
                return 0, None

            # 5. Stratégia hívása
            signal, quadrant_info = self.apply_zscore_strategy(
                df, # Már másolat, nyugodtan átadhatjuk
                length=length,
                data_points=data_points,
                source="close",
            )
            return int(signal or 0), quadrant_info

        except Exception as e:
            # Opcionális: Logolhatod a hibát, ha debuggolni kell
            # print(f"Z-Score Error: {e}")
            return 0, None

    def compute_zscore_strategy(
        self,
        df: pd.DataFrame,
        length: int = 40,
        source: str = "close",
    ) -> Tuple[pd.Series, pd.Series]:
        """Statistical Trend Analysis alapú Z-score és Z-change."""
        if df.empty or len(df) < length:
            return pd.Series(dtype=float), pd.Series(dtype=float)

        # Forrás kiválasztása
        if source == "Returns":
            # Százalékos változás stabilabb lehet
            src = df["close"].pct_change() * 100.0
        elif source in df.columns:
            src = df[source]
        else:
            src = df["close"]

        # Rolling számítások
        mean = src.rolling(window=length).mean()
        std = src.rolling(window=length).std(ddof=0) # ddof=0 a population std-hez, ha kell

        # 0 szórás kezelése
        std = std.replace(0, np.nan)

        z_score = (src - mean) / std
        z_change = z_score.diff()

        return z_score, z_change

    def apply_zscore_strategy(
        self,
        df: pd.DataFrame,
        length: int = 40,
        data_points: int = 100,
        source: str = "close",
    ) -> Tuple[int, Dict[str, Any]]:

        z_score, z_change = self.compute_zscore_strategy(df, length=length, source=source)

        # Ha nincs elég adat, azonnal térjünk vissza
        if len(z_score) < data_points:
            return 0, {"error": "Not enough data"}

        # --- OPTIMALIZÁCIÓ: Vektorizált számítás ---
        # Csak az utolsó 'data_points' darab
        recent_z = z_score.iloc[-data_points:].values
        recent_z_ch = z_change.iloc[-data_points:].values

        # NaN szűrés (maszkolással)
        valid_mask = ~np.isnan(recent_z) & ~np.isnan(recent_z_ch)
        z_vals = recent_z[valid_mask]
        ch_vals = recent_z_ch[valid_mask]

        # Kvadránsok számolása numpy-val (ciklus nélkül!)
        pos_z = z_vals > 0
        neg_z = z_vals < 0
        pos_ch = ch_vals > 0
        neg_ch = ch_vals < 0

        quad1 = np.sum(pos_z & pos_ch) # Z > 0, Ch > 0
        quad2 = np.sum(pos_z & neg_ch) # Z > 0, Ch < 0
        quad3 = np.sum(neg_z & neg_ch) # Z < 0, Ch < 0
        quad4 = np.sum(neg_z & pos_ch) # Z < 0, Ch > 0

        total_points = len(z_vals) # vagy quad1+quad2+quad3+quad4

        # Jelenlegi értékek
        curr_z = z_score.iloc[-1]
        curr_ch = z_change.iloc[-1]

        current_quadrant = 0
        if pd.notna(curr_z) and pd.notna(curr_ch):
            if curr_z > 0 and curr_ch > 0: current_quadrant = 1
            elif curr_z > 0 and curr_ch < 0: current_quadrant = 2
            elif curr_z < 0 and curr_ch < 0: current_quadrant = 3
            elif curr_z < 0 and curr_ch > 0: current_quadrant = 4

        # Jelzés logika
        signal = 0
        threshold = 0.3 * total_points # 30%-os szabály

        if total_points > 0:
            # LONG feltételek (Q4 felpattanás VAGY Q1 trend)
            if (current_quadrant == 4 and quad4 > threshold) or \
               (current_quadrant == 1 and quad1 > threshold):
                signal = 1
            # SHORT feltételek (Q2 forduló VAGY Q3 lejtmenet)
            elif (current_quadrant == 2 and quad2 > threshold) or \
                 (current_quadrant == 3 and quad3 > threshold):
                signal = -1

        # DataFrame frissítése (ha szükséges, bár backtesztnél ez lassíthat)
        # Ha csak a signal kell, ezt a részt érdemes kikapcsolni élesben
        df["z_score"] = z_score
        df["z_change"] = z_change
        df["zscore_signal"] = signal

        quadrant_info = {
            "quad1": int(quad1),
            "quad2": int(quad2),
            "quad3": int(quad3),
            "quad4": int(quad4),
            "current_quadrant": current_quadrant,
            "signal": signal,
            "z_score": curr_z if pd.notna(curr_z) else 0.0
        }

        return signal, quadrant_info

    # ---------- BOLLINGER SQUEEZE ----------
    def _mb_linear_regression(self, series, length: int) -> pd.Series:
        """
        Mozgó lineáris regresszió végpontjának becslése (gyorsított).
        Képlet: 3*LWMA - 2*SMA
        """
        n = int(length)
        if len(series) < n:
            return pd.Series([np.nan] * len(series), index=series.index)

        # LWMA: Linear Weighted Moving Average
        # Súlyok: 1, 2, ..., n
        weights = np.arange(1, n + 1)
        sum_w = np.sum(weights)

        def calc_lwma(x):
            return np.dot(x, weights) / sum_w

        # Rolling apply LWMA-ra
        lwma = series.rolling(n).apply(calc_lwma, raw=True)
        sma = series.rolling(n).mean()

        # LinReg Endpoint becslés
        return 3 * lwma - 2 * sma

    def _mb_squeeze_signal(self, df, length=20, bb_mult=2.0, kc_mult=1.5):
        """
        Bollinger Squeeze + Momentum (LinReg) jelzés.
        Vissza: (signal_str, squeeze_on_bool, momentum_val, bb_upper, bb_lower, kc_upper, kc_lower)
        signal_str: 'buy', 'sell', 'hold'
        """
        if len(df) < max(length + 5, 20):
            return "hold", False, 0.0, 0.0, 0.0, 0.0, 0.0

        src = df['c'].astype(float)

        # 1. Bollinger Bands
        basis = src.rolling(length).mean()
        dev = src.rolling(length).std()
        upper_bb = basis + bb_mult * dev
        lower_bb = basis - bb_mult * dev

        # 2. Keltner Channel (ATR alapú)
        # ATR számítása (már van _mb_atr, de az Series-t ad vissza)
        atr = self._mb_atr(df, n=length)
        upper_kc = basis + kc_mult * atr
        lower_kc = basis - kc_mult * atr

        # 3. Squeeze állapot (BB a KC-n belül)
        # lower_bb > lower_kc ÉS upper_bb < upper_kc
        sqz_on = (lower_bb > lower_kc) & (upper_bb < upper_kc)

        # 4. Momentum (LinReg)
        # TTM Squeeze logika: LinReg(Source - Avg, length)
        # Source = Close
        # Avg = (Highest + Lowest + SMA)/3  <-- TTM standard
        # Egyszerűsítve, de közelítve a TTM-hez:

        hi = df['h'].rolling(length).max()
        lo = df['l'].rolling(length).min()
        donchian = (hi + lo) / 2
        avg_tot = (donchian + basis) / 2

        delta = src - avg_tot

        mom = self._mb_linear_regression(delta, length)

        # 5. Signal logika
        # "Volatilitás Kitörés": Amikor NINCS squeeze, és a Momentum iránya diktál.

        is_sqz = bool(sqz_on.iloc[-1])
        last_mom = float(mom.iloc[-1])

        sig = "hold"

        # Ha nincs squeeze, akkor a piac tágul -> trendelhet.
        # JAVÍTÁS: Csak akkor lépünk be, ha az elmúlt X gyertyában VOLT squeeze.
        # Ez biztosítja, hogy a kitörést (breakout) kapjuk el, ne a trend végét.

        if not is_sqz:
            # Megnézzük az elmúlt 5 gyertyát (kivéve a mostanit): volt-e köztük squeeze?
            # sqz_on[-1] a mostani (ami False), ezért [-6:-1]
            was_squeezed_recently = sqz_on.iloc[-6:-1].any()

            if was_squeezed_recently:
                # Friss kitörés -> irány a momentum alapján
                if last_mom > 0:
                    sig = "buy"
                elif last_mom < 0:
                    sig = "sell"
            else:
                # Már régóta nincs squeeze -> valószínűleg késői belépő lenne -> HOLD
                pass

        return (
            sig,
            is_sqz,
            last_mom,
            float(upper_bb.iloc[-1]),
            float(lower_bb.iloc[-1]),
            float(upper_kc.iloc[-1]),
            float(lower_kc.iloc[-1]),
        )

    # ---------- Méret-számítás (budget támogatással) ----------
    def _mb_compute_size(
        self,
        symbol: str | None,
        side: str,
        price: float,                 # régi px helyett
        size_pct: float,
        input_mode: str,              # "quote" vagy "base"
        mode: str,                    # "isolated" / "cross" (margin mód)
        leverage: int,
        *,
        budget_quote: float = 0.0,
        dry: bool,                    # <-- kötelezően átadva cfg-ből
        auto_borrow: bool,            # <-- kötelezően átadva cfg-ből
        lot_step: float = 0.0,        # opcionális
        price_step: float = 0.0,      # opcionális
    ) -> tuple[float | None, float | None]:
        """
        Méret számítás:
          - input_mode == 'quote' → funds (USDT) = (cap_quote * pct), size=None
          - input_mode == 'base'  → size (BASE)  = (avail_base * pct), funds=None

        cap_quote logika:
          - DRY-RUN: cap_quote = budget (ha >0), különben avail_quote
          - LIVE + Auto-borrow: cap_quote = budget (ha >0), különben avail_quote
          - LIVE + NINCS Auto-borrow: cap_quote = min(avail_quote, budget) ha budget>0,
                                      különben avail_quote
        VISSZA:
          (size_base, funds_quote)
        """
        try:
            # tőkeáttét korlát (isolated: max 10, cross: max 5)
            lev_max = 10 if mode == "isolated" else 5
            leverage = int(max(1, min(lev_max, int(leverage or 1))))

            # százalék normálás
            pct = max(0.0, min(100.0, float(size_pct))) / 100.0
            budget_quote = float(budget_quote or 0.0)

            # alapértelmezett készletek
            avail_base = 0.0
            avail_quote = 0.0

            base = ""
            quote = ""

            # ha van szimbólum, próbálunk tényleges készletet kérni
            if symbol:
                base, quote = split_symbol(symbol)
                if hasattr(self, "_mt_available"):
                    try:
                        avail_base, avail_quote = self._mt_available(base, quote)
                    except Exception:
                        avail_base, avail_quote = 0.0, 0.0

            # input mód egységesítés
            input_mode = (input_mode or "quote").lower()
            if input_mode not in ("quote", "base"):
                input_mode = "quote"

            # --- QUOTE mód: funds-t számolunk ---
            if input_mode == "quote":
                # cap_quote választása a docstring logika szerint
                if dry:
                    # DRY: csak szimuláció → budget vagy avail
                    cap_quote = budget_quote if budget_quote > 0 else avail_quote
                else:
                    if auto_borrow:
                        if budget_quote > 0:
                            # AUTO-BORROW + BUDGET → avail_quote teljesen ignorálva
                            cap_quote = budget_quote
                        else:
                            # NINCS budget UI → konzervatív fallback: marad az avail_quote,
                            # a teljes hitelkeretet nem használjuk ki (logoljuk)
                            cap_quote = avail_quote
                            try:
                                self._safe_log(
                                    "ℹ️ AUTO-BORROW aktív, de mb_budget=0. "
                                    "A méretezés csak az elérhető QUOTE egyenleget veszi figyelembe, "
                                    "a teljes hitelkeretet nem.\n"
                                )
                            except Exception:
                                pass
                    else:
                        if budget_quote > 0:
                            cap_quote = min(avail_quote, budget_quote)
                        else:
                            cap_quote = avail_quote

                use_quote = max(0.0, cap_quote * pct)
                if use_quote <= 0:
                    return None, None

                # később itt lehet quote_step padlózás
                return None, float(use_quote)

            # --- BASE mód: darabszámot számolunk az elérhető BASE-ből ---
            size_base = max(0.0, avail_base * pct)

            # opcionális lot_step kerekítés
            if lot_step and hasattr(self, "_mb_floor_to_step_dec"):
                try:
                    size_base = self._mb_floor_to_step_dec(size_base, float(lot_step))
                except Exception:
                    pass

            if size_base <= 0:
                return None, None

            return float(size_base), None

        except Exception:
            # hiba esetén inkább ne nyisson semmit
            return None, None

    def _mb_get_market_steps(self, symbol: str):
        """
        Visszaadja: (lot_step, price_step, min_base, min_funds, quote_step)

        + ÚJ: ha elérhető → quote_step is (pl. KuCoin: "quoteIncrement")
        + Ha nincs, quote_step = 0.01 fallback
        """
        try:
            info = None
            # JAVÍTÁS: A 'get_symbol_meta' függvényt hívjuk, ami a KucoinSDKWrapper-ben létezik (sor 211)
            if hasattr(self.exchange, "get_symbol_meta"):
                with self._ex_lock:
                    info = self.exchange.get_symbol_meta(symbol) # <-- JAVÍTVA

            if isinstance(info, dict):
                # JAVÍTÁS: Kulcsok hozzáigazítva a get_symbol_meta által visszaadott dict-hez (sor 201-206)
                lot_step   = float(info.get("baseInc")  or 0.0)
                price_step = float(info.get("priceInc") or 0.0)
                min_base   = float(info.get("baseMin")  or 0.0) # <-- JAVÍTVA
                min_funds  = float(info.get("minFunds") or 0.0)
                quote_step = float(info.get("quoteInc") or 0.0) # <-- JAVÍTVA

                if quote_step <= 0:
                    quote_step = 0.01   # fallback (legtöbb USDT páron oké)

                return lot_step, price_step, min_base, min_funds, quote_step

        except Exception:
            pass # Hiba esetén a lenti fallback-re esik

        # hiba vagy hiány esetén minden 0, de quote_step kap fallbacket
        return 0.0, 0.0, 0.0, 0.0, 0.01

    def _mb_floor_to_step_dec(self, x: float, step: float) -> float:
        """Decimal-al padlózzuk a mennyiséget a lépésközre (float hibák nélkül)."""
        if step <= 0:
            return float(x)
        q = Decimal(str(step))
        return float((Decimal(str(x)) // q) * q)

    # --- TEMP DEBUG: biztonságos pretty print ---
    def _mb_pp(self, obj) -> str:
        """Debughoz: JSON-szerű string (kulcsok/értékek), default=str fallback-kel."""
        try:
            return json.dumps(obj, ensure_ascii=False, default=str)
        except Exception:
            try:
                return repr(obj)
            except Exception:
                return "<unprintable>"

    def _save_cfg_to_file(self):
        try:
            cfg = self._mb_build_cfg()
            filepath = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON fájlok", "*.json"), ("Minden fájl", "*.*")],
                title="Config mentése"
            )
            if not filepath:
                return
            ConfigManager.save_config(filepath, cfg)
            messagebox.showinfo("Siker", f"Config mentve:\n{filepath}")
        except Exception as e:
            messagebox.showerror("Hiba", f"Mentés sikertelen: {e}")

    def _load_cfg_from_file(self):
        try:
            filepath = filedialog.askopenfilename(
                filetypes=[("JSON fájlok", "*.json"), ("Minden fájl", "*.*")],
                title="Config betöltése"
            )
            if not filepath:
                return
            cfg = ConfigManager.load_config(filepath)
            self._apply_cfg_to_ui(cfg)
            messagebox.showinfo("Siker", f"Config betöltve:\n{filepath}")
        except Exception as e:
            messagebox.showerror("Hiba", f"Betöltés sikertelen: {e}")

    def _set_widget_val(self, widget, val):
        """Helper a különböző widget típusok beállításához."""
        try:
            if isinstance(widget, (ttk.Entry, ttk.Spinbox)):
                # Spinbox/Entry esetén delete + insert
                try:
                    widget.delete(0, tk.END)
                    widget.insert(0, str(val))
                except Exception:
                    pass
            elif isinstance(widget, ttk.Combobox):
                try:
                    widget.set(str(val))
                except Exception:
                    pass
            elif isinstance(widget, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar)):
                try:
                    widget.set(val)
                except Exception:
                    pass
            else:
                # Esetleg Checkbutton/Radiobutton variable nélkül?
                # Általában variable-t használunk, amit a config map-ben adunk meg.
                pass
        except Exception:
            pass

    def _apply_cfg_to_ui(self, cfg: dict):
        """
        A cfg dict értékeit visszaírja a GUI widgetekbe / változókba.
        """
        # Mapping: config_key -> widget vagy variable
        # Figyelem: A _mb_build_cfg kulcsait használjuk.

        mapping = {
            "symbol": self.mb_symbol,
            "tf": self.mb_tf,
            "ma_fast": self.mb_ma_fast,
            "ma_slow": self.mb_ma_slow,
            "size_pct": self.mb_size_pct,
            "input_mode": self.mb_input_mode,
            "mode": self.mb_mode,
            "leverage": self.mb_leverage,
            "tp_pct": self.mb_tp_pct,
            "sl_pct": self.mb_sl_pct,
            "trail_pct": self.mb_trail_pct,
            "cooldown_s": self.mb_cooldown_s,
            "dry": self.mb_dry,
            "budget_ui": self.mb_budget,

            "use_rsi": self.mb_use_rsi,
            "rsi_len": self.mb_rsi_len,
            "rsi_bmin": self.mb_rsi_buy_min,
            "rsi_bmax": self.mb_rsi_buy_max,
            "rsi_smin": self.mb_rsi_sell_min,
            "rsi_smax": self.mb_rsi_sell_max,

            "use_adx": getattr(self, "mb_use_adx", None),
            "adx_len": getattr(self, "mb_adx_len", None),
            "adx_min": getattr(self, "mb_adx_min", None),

            "use_htf": self.mb_use_htf,
            "htf_tf": self.mb_htf_tf,

            "use_atr": self.mb_use_atr,
            "atr_n": self.mb_atr_n,
            "atr_mul_sl": self.mb_atr_mul_sl,
            "atr_mul_tp1": self.mb_atr_mul_tp1,
            "atr_mul_tp2": self.mb_atr_mul_tp2,
            "atr_mul_tr": self.mb_atr_mul_trail,

            "use_fixed": self.mb_use_fixed,

            "use_brk": self.mb_use_brk,
            "brk_n": self.mb_brk_n,
            "brk_buf": self.mb_brk_buf,
            "brk_with_trend": self.mb_brk_with_trend,

            "use_live": self.mb_use_live,
            "live_shock_pct": self.mb_live_shock_pct,
            "live_shock_atr": self.mb_live_shock_atr,
            "drift_max_pct": self.mb_drift_max_pct,

            "use_zscore": self.mb_use_zscore,
            "z_len": self.mb_z_len,
            "z_points": self.mb_z_points,

            "sqz_len": getattr(self, "mb_sqz_len", None),
            "sqz_bb_mult": getattr(self, "mb_sqz_bb_mult", None),
            "sqz_kc_mult": getattr(self, "mb_sqz_kc_mult", None),

            "max_open": self.mb_max_open,
            "pause_new": self.mb_pause_new,

            "auto_borrow": self.mb_autob,
            "allow_short": self.mb_allow_short,
            "invert_ema": getattr(self, "mb_invert_ema", None),
            "ema_hyst_pct": getattr(self, "mb_ema_hyst_pct", None),
            "dup_tol_pct": getattr(self, "mb_dup_tol_pct_var", None),
            "strategy": getattr(self, "mb_strategy", None),
        }

        for key, val in cfg.items():
            target = mapping.get(key)
            if target is not None:
                self._set_widget_val(target, val)

        # Trigger UI updates (pl. enable/disable logika)
        self._mb_toggle_fixed_widgets()
        self._mb_toggle_atr_widgets()
        self._mb_toggle_brk_widgets()
        self._mb_toggle_live_widgets()
        self._mb_toggle_rsi_widgets()
        self._mb_toggle_adx_widgets()
        self._mb_toggle_htf_widgets()
        self._mb_toggle_zscore_widgets()
        self._mb_on_strategy_change()

    def _mb_build_cfg(self) -> dict:
        """Margin bot beállítások snapshot – CSAK fő szálból hívd (pl. mb_start-ban)."""
        # Biztonság kedvéért minden _mb_get_* itt még fő szálon fut → thread-safe.
        symbol = normalize_symbol(
            self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL))
        )

        cfg = {
            # Alap paraméterek
            "symbol": symbol,
            "tf": self._mb_get_str('mb_tf', '1m'),
            "ma_fast": self._mb_get_int('mb_ma_fast', 9),
            "ma_slow": self._mb_get_int('mb_ma_slow', 21),
            "size_pct": self._mb_get_float('mb_size_pct', 50.0),
            "input_mode": self._mb_get_str('mb_input_mode', 'quote'),
            "mode": self._mb_get_str('mb_mode', 'isolated'),
            "leverage": max(1, self._mb_get_int('mb_leverage', 10)),
            "tp_pct": self._mb_get_float('mb_tp_pct', 2.0),
            "sl_pct": self._mb_get_float('mb_sl_pct', 1.0),
            "trail_pct": self._mb_get_float('mb_trail_pct', 0.5),
            "cooldown_s": self._mb_get_int('mb_cooldown_s', 30),
            "dry": self._mb_get_bool('mb_dry', True),
            "budget_ui": self._mb_get_float('mb_budget', 0.0),

            # RSI
            "use_rsi": bool(getattr(self, "mb_use_rsi", tk.BooleanVar(value=False)).get()),
            "rsi_len": self._mb_get_int('mb_rsi_len', 14),
            "rsi_bmin": self._mb_get_float('mb_rsi_buy_min', 45.0),
            "rsi_bmax": self._mb_get_float('mb_rsi_buy_max', 70.0),
            "rsi_smin": self._mb_get_float('mb_rsi_sell_min', 30.0),
            "rsi_smax": self._mb_get_float('mb_rsi_sell_max', 55.0),

            # ADX (oldalazás / trend szűrő)
            "use_adx": bool(getattr(self, "mb_use_adx", tk.BooleanVar(value=False)).get()),
            "adx_len": self._mb_get_int('mb_adx_len', 14),
            "adx_min": self._mb_get_float('mb_adx_min', 20.0),

            # HTF
            "use_htf": bool(getattr(self, "mb_use_htf", tk.BooleanVar(value=False)).get()),
            "htf_tf": self._mb_get_str('mb_htf_tf', '1h'),

            # ATR
            "use_atr": bool(getattr(self, "mb_use_atr", tk.BooleanVar(value=False)).get()),
            "atr_n": self._mb_get_int('mb_atr_n', 14),
            "atr_mul_sl": self._mb_get_float('mb_atr_mul_sl', 1.2),
            "atr_mul_tp1": self._mb_get_float('mb_atr_mul_tp1', 1.5),
            "atr_mul_tp2": self._mb_get_float('mb_atr_mul_tp2', 2.5),
            "atr_mul_tr": self._mb_get_float('mb_atr_mul_trail', 0.9),

            # FIX vs ATR
            "use_fixed": bool(getattr(self, "mb_use_fixed", tk.BooleanVar(value=False)).get()),

            # Breakout
            "use_brk": bool(getattr(self, "mb_use_brk", tk.BooleanVar(value=False)).get()),
            "brk_n": self._mb_get_int('mb_brk_n', 20),
            "brk_buf": self._mb_get_float('mb_brk_buf', 0.05),
            "brk_with_trend": bool(getattr(self, "mb_brk_with_trend", tk.BooleanVar(value=True)).get()),

            # Élő ár “shock” + drift
            "use_live": bool(getattr(self, "mb_use_live", tk.BooleanVar(value=True)).get()),
            "live_shock_pct": self._mb_get_float('mb_live_shock_pct', 1.0),
            "live_shock_atr": self._mb_get_float('mb_live_shock_atr', 1.2),
            "drift_max_pct": self._mb_get_float('mb_drift_max_pct', 0.0),

            # Z-score filter
            "use_zscore": bool(getattr(self, "mb_use_zscore", tk.BooleanVar(value=False)).get()),
            "z_len": self._mb_get_int('mb_z_len', 40),
            "z_points": self._mb_get_int('mb_z_points', 100),

            # Squeeze
            "use_sqz_filter": bool(getattr(self, "mb_use_sqz_filter", tk.BooleanVar(value=False)).get()),
            "sqz_len": self._mb_get_int('mb_sqz_len', 20),
            "sqz_bb_mult": self._mb_get_float('mb_sqz_bb_mult', 2.0),
            "sqz_kc_mult": self._mb_get_float('mb_sqz_kc_mult', 1.5),

            # Supertrend
            "use_st_filter": bool(getattr(self, "mb_use_st_filter", tk.BooleanVar(value=False)).get()),
            "st_period": self._mb_get_int('mb_st_period', 10),
            "st_mult": self._mb_get_float('mb_st_mult', 3.0),

            # Max nyitott, pause new
            "max_open": self._mb_get_int('mb_max_open', 0),
            "pause_new": self._mb_get_bool('mb_pause_new', False),

            # Auto-borrow + EMA invert
            "auto_borrow": bool(getattr(self, "mb_autob", tk.BooleanVar(value=False)).get()),
            "allow_short": bool(getattr(self, "mb_allow_short", tk.BooleanVar(value=True)).get()),
            "invert_ema": bool(getattr(self, "mb_invert_ema", tk.BooleanVar(value=False)).get()),

            # EMA hysteresis %
            "ema_hyst_pct": self._mb_get_float('mb_ema_hyst_pct', 1.0),

            # Duplicate / Nearby tolerance %
            "dup_tol_pct": self._mb_get_float('mb_dup_tol_pct_var', 0.5),

            # Strategy
            "strategy": self._mb_get_str('mb_strategy', 'EMA'),
        }

        # Ütközés-kezelés: ATR vs FIX egyszer eldöntve
        if cfg["use_fixed"] and cfg["use_atr"]:
            cfg["use_fixed"] = False

        return cfg

    # --- MarginBot: biztonságos getterek (változatlanok) ---
    def _mb_get(self, candidates, cast, default):
        for name in candidates:
            try:
                w = getattr(self, name)
                try:
                    val = w.get()
                except Exception:
                    val = w
                if val in (None, ""):
                    continue
                return cast(val)
            except Exception:
                continue
        return default

    def _mb_get_str(self, name: str, default: str) -> str:
        return self._mb_get([name], lambda s: str(s), default)

    def _mb_get_int(self, name: str, default: int) -> int:
        return self._mb_get([name], lambda x: int(float(x)), default)

    def _mb_get_float(self, name: str, default: float) -> float:
        return self._mb_get([name], lambda x: float(x), default)

    def _mb_get_bool(self, name: str, default: bool) -> bool:
        def _cast(v):
            if isinstance(v, str):
                return v.lower() in ("1","true","yes","on")
            return bool(v)
        return self._mb_get([name], _cast, default)

    # ======= ABLAK BEZÁRÁS (piros X) – kulturált leállítás =======
    def on_close(self):
        """
        Piros X-re:
          1) mindkét bot + WS kulturált leállítása,
          2) futó frissítések megvárása nem-blokkoló módon,
          3) végül ablak bezárása.
        """
        if getattr(self, "_closing", False):
            return
        self._closing = True
        try:
            self._safe_log("🧹 Bezárás kérése – botok leállítása…\n")
        except Exception:
            pass

        # 1) MINDKÉT bot leállítása
        try:
            # Dashboard bot leállítása
            if getattr(self, "is_running", False):
                self.stop_bot()
        except Exception as e:
            pass # Hiba esetén is megyünk tovább

        try:
            # Margin bot leállítása
            if getattr(self, "_mb_running", False):
                self.mb_stop()
        except Exception as e:
            try: self._safe_log(f"⚠️ mb_stop hiba: {e}\n")
            except Exception: pass

        try:
            # Websocket ticker kulturált leállítása
            ws = getattr(self, "_ticker_ws", None)
            if ws is not None:
                ws.stop()
        except Exception:
            pass

        try:
            # K-Line WS kulturált leállítása
            kws = getattr(self, "_mb_kline_ws", None)
            if kws is not None:
                kws.stop()
        except Exception:
            pass

        # 2) nem-blokkoló poll amíg minden el nem állt
        try:
            self._poll_shutdown(0)
        except Exception:
            try: self.root.destroy()
            except Exception: pass

    def _poll_shutdown(self, tries: int = 0):
        """
        100 ms-onként ellenőrzi, hogy:
          - a margin bot szála leállt-e (_mb_running == False),
          - nincs-e épp tick/refresh (_tick_busy == False),
        majd csak ezután zárja az ablakot.
        """
        still_mb   = bool(getattr(self, "_mb_running", False))
        still_tick = bool(getattr(self, "_tick_busy", False))
        if still_mb or still_tick:
            if tries % 10 == 0:
                try:
                    self._safe_log("⏳ Leállítás folyamatban… (várok a szálakra)\n")
                except Exception:
                    pass
            try:
                self.root.after(100, lambda: self._poll_shutdown(tries + 1))
            except Exception:
                try: self.root.destroy()
                except Exception: pass
            return

        # opcionális: exchange lezárása, ha van ilyen API
        try:
            ex = getattr(self, "exchange", None)
            if ex and hasattr(ex, "close"):
                ex.close()
        except Exception:
            pass

        try:
            self.root.destroy()
        except Exception:
            pass

    # ===== Fee (taker) – auto API + cache (fallback 0.001) =====
    def _mb_get_taker_fee(self) -> float:
        """
        KuCoin taker fee lekérdezése (cache-elve ~1 órára). Fallback: 0.001 (0.1%).
        """
        try:
            now = time.time()
            cache = getattr(self, "_mb_fee_cache", None)
            if cache and (now - cache.get("ts", 0) < 3600):
                return float(cache.get("taker", 0.001))

            fee = 0.001
            ex = getattr(self, "exchange", None)
            if ex:
                try:
                    # Minden exchange-hívás ugyanazzal a lockkal
                    lock = getattr(self, "_ex_lock", None)
                    if lock is not None:
                        with lock:
                            fee = self._mb__fetch_taker_fee_from_ex(ex, fee)
                    else:
                        fee = self._mb__fetch_taker_fee_from_ex(ex, fee)
                except Exception:
                    pass

            self._mb_fee_cache = {"taker": float(fee), "ts": now}
            return float(fee)
        except Exception:
            return 0.001

    def _mb__fetch_taker_fee_from_ex(self, ex, default_fee: float) -> float:
        """Belső helper: taker fee kiszedése az exchange wrapperből (lockon *belül* fusson)."""
        fee = default_fee
        # próbálkozások különböző wrapper nevekkel
        if hasattr(ex, "get_base_fee"):
            fb = ex.get_base_fee() or {}
            fee = float(fb.get("takerFeeRate", fee) or fee)
        elif hasattr(ex, "fetch_trading_fee"):
            tf = ex.fetch_trading_fee() or {}
            fee = float(tf.get("taker", fee) or fee)
        elif hasattr(ex, "fetch_fee_rates"):
            fr = ex.fetch_fee_rates() or {}
            fee = float(fr.get("taker", fee) or fee)
        return fee

    def _mb_est_fee_quote(self, price: float, size_base: float, fee_rate: float) -> float:
        """Becsült díj QUOTE-ban (USDT), taker fee: price * size * fee."""
        try:
            return max(0.0, float(price) * float(size_base) * max(0.0, float(fee_rate)))
        except Exception:
            return 0.0

    def _mb_sum_fee_actual_or_est(self, pos: dict, exit_px: float, fee_rate: float) -> tuple[float, float, float]:
        """
        (open_fee, close_fee, total) – 'actual' ha van, különben estimált.
        """
        sz = float(pos.get("size", 0.0))
        entry = float(pos.get("entry", 0.0))
        # open
        f_open_act = float(pos.get("fee_open_actual", 0.0))
        f_open_est = float(pos.get("fee_open_est", 0.0))
        open_fee = f_open_act if f_open_act > 0 else (f_open_est if f_open_est > 0 else self._mb_est_fee_quote(entry, sz, fee_rate))
        # close
        f_close_act = float(pos.get("fee_close_actual", 0.0))
        close_fee = f_close_act if f_close_act > 0 else self._mb_est_fee_quote(exit_px, sz, fee_rate)
        return (open_fee, close_fee, open_fee + close_fee)

    def _mb_try_fetch_close_fee(self, close_order_id: str, wait_ws: bool = False) -> float:
        """
        Order fee összeszedése:

        1) Ha van privát order WS, akkor először onnan próbáljuk kiolvasni (wait_ws=True esetén
           rövid ideig várunk is rá).
        2) Ha onnan nem jön értelmes fee, fallback REST alapú fills-lekérésre.

        close_order_id: KuCoin orderId (vagy clientOid, ha az alapján kérsz le).
        """
        if not close_order_id:
            return 0.0

        oid = str(close_order_id)
        fee_ws = 0.0

        # --- 1) Private WS próbálkozás ---
        try:
            ws = getattr(self, "_order_ws", None)
            if ws is not None:
                if wait_ws:
                    r = ws.wait_for_fee(oid, timeout=0.7, poll=0.05)
                else:
                    r = ws.get_fee_for_order(oid)
                if r is not None:
                    fee_ws = float(r or 0.0)
        except Exception as e:
            self._safe_log(f"⚠️ WS fee lekérés hiba ({oid}): {e}\n")
            fee_ws = 0.0

        if fee_ws > 0.0:
            return fee_ws

        # --- 2) REST fallback (fills lekérés) ---
        ex = getattr(self, "exchange", None)
        if ex is None:
            return fee_ws

        fills = []
        try:
            lock = getattr(self, "_ex_lock", None)

            def _fetch_fills():
                local_fills = []
                # KucoinMarginTrader specifikus helper
                if hasattr(ex, "get_margin_fills_by_order"):
                    try:
                        local_fills = ex.get_margin_fills_by_order(oid) or []
                    except Exception:
                        local_fills = []
                # Általánosabb spot/margin helper
                if (not local_fills) and hasattr(ex, "get_order_fills"):
                    try:
                        local_fills = ex.get_order_fills(oid) or []
                    except Exception:
                        local_fills = []
                # ccxt-s fetch_order_trades fallback
                if (not local_fills) and hasattr(ex, "fetch_order_trades"):
                    try:
                        local_fills = ex.fetch_order_trades(oid) or []
                    except Exception:
                        local_fills = []
                return local_fills

            if lock is not None:
                with lock:
                    fills = _fetch_fills()
            else:
                fills = _fetch_fills()

        except Exception as e:
            self._safe_log(f"⚠️ REST fills lekérés hiba ({oid}): {e}\n")
            fills = []

        if not fills:
            return fee_ws

        total_fee = 0.0
        for f in fills:
            if not isinstance(f, dict):
                continue
            fee_val = None
            if "fee" in f:
                fee_val = f.get("fee")
            elif "fees" in f:
                fee_val = f.get("fees")
            elif "feeCost" in f:
                fee_val = f.get("feeCost")

            if isinstance(fee_val, (int, float, str)):
                try:
                    total_fee += float(fee_val)
                except Exception:
                    pass

        return total_fee if total_fee > 0.0 else fee_ws

    def _mb_resolve_open_fill(self,
                              *,
                              order_id: str,
                              side: str,
                              req_price: float,
                              req_size,
                              req_funds,
                              lev: int,
                              lot_step: float = 0.0) -> tuple[float, float, float]:
        """
        Open-order realtime fill / fee feloldása.

        Visszatérés:
          (size_now_base, commit_real_quote, fee_open_actual_quote)

        Priority:
          1) Private Order WS manager (self._order_ws.get_fill_agg) – KIS VÁRAKOZÁSSAL
          2) REST fills (get_margin_fills_by_order / get_fills_by_order / fetch_order_trades)
          3) Ha semmi adat → (0,0,0), a hívó fallback-el a régi becslésre.
        """
        filled_base = 0.0    # tényleges teljesült BASE mennyiség
        filled_quote = 0.0   # opcionális: tényleges QUOTE nominális (ha van)
        fee = 0.0            # tényleges fee QUOTE-ban

        # 1) WS – ha van Private Order WS manager és tud aggregált fillt adni
        try:
            ord_ws = getattr(self, "_order_ws", None)
            if ord_ws is not None and hasattr(ord_ws, "get_fill_agg"):
                try:
                    # új, várakozó verzió – hagyunk időt a fill üzenetnek
                    fb, fq, ff = ord_ws.get_fill_agg(str(order_id), timeout=0.7, poll=0.05)
                except TypeError:
                    # ha valamiért régi szignóval futna
                    fb, fq, ff = ord_ws.get_fill_agg(str(order_id))

                if fb is not None and float(fb) > 0.0:
                    filled_base = float(fb)
                    filled_quote = float(fq or 0.0)
                    fee = float(ff or 0.0)
        except Exception as e:
            self._safe_log(f"⚠️ WS open-fill agg hiba: {e}\n")

        # 2) Ha WS nem adott semmit, próbáljuk REST-ből
        if filled_base <= 0.0 and getattr(self, "exchange", None) is not None:
            try:
                ex = self.exchange
                lock = getattr(self, "_ex_lock", None)

                def _fetch_fills():
                    local_fills = None
                    # KuCoin margin specific
                    if hasattr(ex, "get_margin_fills_by_order"):
                        local_fills = ex.get_margin_fills_by_order(order_id)
                    # KuCoin spot / alt wrapper
                    elif hasattr(ex, "get_fills_by_order"):
                        local_fills = ex.get_fills_by_order(order_id)
                    # ccxt-s stílusú wrapper
                    elif hasattr(ex, "fetch_order_trades"):
                        try:
                            local_fills = ex.fetch_order_trades(order_id)
                        except TypeError:
                            local_fills = ex.fetch_order_trades(order_id, None)
                    return local_fills

                if lock is not None:
                    with lock:
                        fills = _fetch_fills()
                else:
                    fills = _fetch_fills()

                if fills:
                    fb = fq = ff = 0.0

                    for f in fills:
                        if not isinstance(f, dict):
                            continue

                        # base mennyiség
                        sz = (
                            f.get("size")
                            or f.get("amount")
                            or f.get("filledSize")
                            or f.get("filled")
                            or f.get("dealSize")
                        )
                        try:
                            szv = float(sz or 0.0)
                            if szv > 0:
                                fb += szv
                        except Exception:
                            pass

                        # quote nominális (funds / cost / quoteQty / dealFunds / filledValue stb.)
                        fq_raw = (
                            f.get("funds")
                            or f.get("fundsValue")
                            or f.get("cost")
                            or f.get("quoteQty")
                            or f.get("dealFunds")
                            or f.get("filledValue")
                        )
                        try:
                            fqv = float(fq_raw or 0.0)
                            if fqv > 0:
                                fq += fqv
                        except Exception:
                            pass

                        # fee – dict vagy plain value
                        fee_val = 0.0
                        fee_obj = f.get("fee")
                        if isinstance(fee_obj, dict):
                            fee_val = (
                                fee_obj.get("cost")
                                or fee_obj.get("fee")
                                or fee_obj.get("amount")
                                or 0.0
                            )
                        elif fee_obj is not None:
                            fee_val = fee_obj

                        # plusz fallback mezők, ha vannak
                        if not fee_val:
                            for key in ("feeCost", "feeAmount", "feeValue", "takerFee", "makerFee"):
                                if key in f and f.get(key) is not None:
                                    fee_val = f.get(key)
                                    break

                        try:
                            fv = float(fee_val or 0.0)
                            if fv > 0:
                                ff += fv
                        except Exception:
                            pass

                    filled_base = float(fb)
                    filled_quote = float(fq)
                    fee = float(ff)
            except Exception as e:
                self._safe_log(f"⚠️ REST open-fill agg hiba: {e}\n")

        # 3) Ha sikerült bármennyi fillt szerezni → normalizálás
        if filled_base > 0.0:
            if lot_step:
                filled_base = self._mb_floor_to_step_dec(filled_base, float(lot_step or 0.0))

            px = float(req_price) if req_price and req_price > 0 else 1.0
            nominal = filled_quote if filled_quote > 0 else filled_base * px
            commit_real = nominal / max(lev, 1)

            return float(filled_base), float(commit_real), float(fee or 0.0)

        # 4) sem WS, sem REST nem adott értelmes fillt → 0,0,0
        return 0.0, 0.0, 0.0

    ###---    BEÁLLÍTÁSOK FÜL     ---###
    def _build_settings_tab(self):
        self.tab_settings = ttk.Frame(self.nb)
        self.nb.add(self.tab_settings, text="Beállítások")

        # Fő frame a 2 oszlopos elrendezéshez
        main_frame = ttk.Frame(self.tab_settings)
        main_frame.pack(fill="both", expand=True, padx=10, pady=10)
        main_frame.grid_columnconfigure(0, weight=1)
        main_frame.grid_columnconfigure(1, weight=1)

        # --- Megjelenés / betűk (BAL OSZLOP) ---
        box = ttk.Labelframe(main_frame, text="Megjelenés / betűk", padding=10)
        box.grid(row=0, column=0, sticky="nsew", padx=(0, 5), pady=(0, 10))

        box.grid_columnconfigure(1, weight=1)

        # Betűméret
        ttk.Label(box, text="Betűméret:").grid(row=0, column=0, sticky="w")
        self.font_size_var = tk.IntVar(value=self.base_font.cget("size"))
        size_spin = ttk.Spinbox(
            box,
            from_=8,
            to=24,
            width=5,
            textvariable=self.font_size_var
        )
        size_spin.grid(row=0, column=1, sticky="w", padx=4)

        # Betűtípus
        ttk.Label(box, text="Betűtípus:").grid(row=1, column=0, sticky="w", pady=(8, 0))
        self.font_family_var = tk.StringVar(value=self.base_font.cget("family"))
        font_list = sorted(set(tkfont.families()))
        family_cb = ttk.Combobox(
            box,
            textvariable=self.font_family_var,
            values=font_list,
            width=20,
            state="readonly"
        )
        family_cb.grid(row=1, column=1, sticky="w", padx=4, pady=(8, 0))

        def apply_font():
            # értékek beolvasása
            try:
                new_size = int(self.font_size_var.get())
            except (ValueError, tk.TclError):
                new_size = self.base_font.cget("size")

            new_family = self.font_family_var.get() or self.base_font.cget("family")

            # alap + félkövér font frissítése
            self.base_font.configure(size=new_size, family=new_family)
            self.bold_font.configure(size=new_size, family=new_family)

            # Minden ttk stílus + Tk alapfont újrafontozása
            self._apply_global_font()

        ttk.Button(box, text="Alkalmaz", command=apply_font)\
           .grid(row=2, column=0, columnspan=2, pady=(10, 0), sticky="w")

        # --- Logolás + MarginBot (JOBB OSZLOP) ---
        right_box = ttk.Labelframe(main_frame, text="Logolás / MarginBot", padding=10)
        right_box.grid(row=0, column=1, sticky="nsew", padx=(5, 0), pady=(0, 10))
        right_box.grid_columnconfigure(1, weight=1)

        # Részletes státusz log engedélyezése
        self.log_verbose_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            right_box,
            text="Részletes státusz logolás engedélyezése",
            variable=self.log_verbose_var
        ).grid(row=0, column=0, columnspan=2, sticky="w")

        # Késleltetés (mp) a státusz logok között
        ttk.Label(right_box, text="Státusz log késleltetése (mp):")\
           .grid(row=1, column=0, sticky="w", pady=(8, 0))

        self.log_delay_var = tk.IntVar(value=5)  # alap 5 mp
        delay_cb = ttk.Combobox(
            right_box,
            textvariable=self.log_delay_var,
            values=["5", "10", "20", "30"],
            width=5,
            state="readonly"
        )
        delay_cb.grid(row=1, column=1, sticky="w", padx=4, pady=(8, 0))

        # Shadow értékek a workernek (thread-safe attribútumok)
        self._mb_log_verbose = bool(self.log_verbose_var.get())
        self._mb_log_delay   = int(self.log_delay_var.get())

        def _on_log_verbose_changed(*args):
            try:
                self._mb_log_verbose = bool(self.log_verbose_var.get())
            except Exception:
                self._mb_log_verbose = False

        def _on_log_delay_changed(*args):
            try:
                self._mb_log_delay = int(self.log_delay_var.get())
            except Exception:
                self._mb_log_delay = 5

        # Változás figyelése (főszálon fut!)
        self.log_verbose_var.trace_add("write", _on_log_verbose_changed)
        self.log_delay_var.trace_add("write", _on_log_delay_changed)

    def _apply_global_font(self):
        """A base_font-ot ráteszi minden fontos ttk widget stílusra.

        Ezt hívd meg:
          - __init__ végén (miután megvannak a fontok és a Style)
          - betűméret / betűtípus változtatás után (Beállítások fül).
        """
        f = self.base_font
        family = f.cget("family")
        size   = f.cget("size")

        # Font tuple a Tk opció adatbázisnak
        font_tuple = (family, size)

        # --- Tk alapértelmezett fontok frissítése (kritikus a ttk belső részeihez) ---
        try:
            tkfont.nametofont("TkDefaultFont").configure(family=family, size=size)
            tkfont.nametofont("TkTextFont").configure(family=family, size=size)
        except Exception as e:
            # ha valamiért még nem léteznek, nem dől össze a program
            print(f"Hiba a Tk alapértelmezett fontok frissítésekor: {e}")

        # --- Alap ttk stílus ---
        self.style.configure(".", font=f)

        # Gyakran használt stílusok
        for sty in (
            "TLabel",
            "TButton",
            "TEntry",
            "TCombobox",
            "TSpinbox",
            "TCheckbutton",
            "TRadiobutton",
            "Treeview",
        ):
            self.style.configure(sty, font=f)

        # Különleges stílusok
        self.style.configure("Treeview.Heading", font=self.bold_font)
        self.style.configure("Card.TLabelframe.Label", font=self.bold_font)

        # Combobox lenyíló lista + menük
        try:
            self.root.option_add('*TCombobox*Listbox.font', font_tuple)
            self.root.option_add('*Menu.font', font_tuple)
        except Exception:
            pass

        # --- Nem-ttk szövegmezők (ScrolledText, Text) frissítése ---
        for name in ("log_area", "margin_log", "txt_positions", "funds_log", "mb_log"):
            if hasattr(self, name):
                try:
                    getattr(self, name).configure(font=font_tuple)
                except Exception:
                    pass

        # Layout frissítés, hogy minden az új mérethez igazodjon
        self.root.update_idletasks()

# ========= main =========
if __name__ == "__main__":
    root = tb.Window(themename="flatly")
    app = CryptoBotApp(root)
    root.mainloop()
