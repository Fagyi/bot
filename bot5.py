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

import os, sys, time, json, uuid, hmac, base64, hashlib, threading
from typing import List, Optional, Literal, Any, Dict
from urllib.parse import urlencode
import time as _time
import threading

# -------- 3rd party --------
import requests
import pandas as pd
import websocket  # websocket-client

# Tkinter
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
from tkinter import font as tkfont
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext
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
        import requests
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
        import time as _t
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
                _t.sleep(5.0)

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
        import collections

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
        import time as _t

        if not order_id:
            return None
        order_id = str(order_id)

        end_ts = _t.time() + max(0.0, timeout)
        last_fee = None

        while _t.time() < end_ts:
            with self._lock:
                info = self._order_info.get(order_id)
            if info:
                fee = float(info.get("fee", 0.0))
                # ha 0, lehet, hogy még nem jött meg minden fill
                last_fee = fee
                if fee > 0:
                    return fee
            _t.sleep(max(0.0, poll))

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
        import time as _t

        if not order_id:
            return 0.0, 0.0, 0.0

        oid = str(order_id)

        # összesen eddig várunk
        end_ts = _t.time() + max(0.0, float(timeout))
        poll = max(0.0, float(poll))

        last_fb = None
        last_fq = None
        last_fee = None

        while _t.time() < end_ts:
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
                _t.sleep(poll)
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
        import time as _t
        backoff = 1.0

        self._log("🔌 Private order WS worker indul...\n")

        while self._running:
            try:
                url = self._get_ws_url()
                if not url:
                    self._log("❌ Private order WS URL nem elérhető (bullet-private). Újrapróbálás...\n")
                    _t.sleep(backoff)
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
            _t.sleep(backoff)
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
        import time as _t
        self._last_msg_ts = _t.time()

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

            fee_raw = data.get("fee", 0.0)
            try:
                fee = float(fee_raw or 0.0)
            except Exception:
                fee = 0.0

            match_size_raw = data.get("matchSize", 0.0)
            try:
                match_size = float(match_size_raw or 0.0)
            except Exception:
                match_size = 0.0

            symbol = data.get("symbol") or ""
            ts = int(data.get("ts") or 0)

            with self._lock:
                info = self._order_info.get(order_id) or {
                    "fee": 0.0,
                    "filled": 0.0,
                    "symbol": symbol,
                    "ts": ts,
                }
                info["fee"] = float(info.get("fee", 0.0)) + fee
                info["filled"] = float(info.get("filled", 0.0)) + match_size
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
        import requests as _req
        self._http = _req.Session()
        self._http.headers.update({"User-Agent": "kucoin-bot/1.2"})
        self._timeout = (4, 8)

        # Keys
        import os as _os
        self._api_key = _os.getenv('KUCOIN_KEY', '')
        self._api_secret = _os.getenv('KUCOIN_SECRET', '')
        self._api_passphrase = _os.getenv('KUCOIN_PASSPHRASE', '')
        self._api_key_version = _os.getenv('KUCOIN_KEY_VERSION', '2')

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
        import json
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
        body = {
            "clientOid": uuid.uuid4().hex,
            "type": transfer_type,           # INTERNAL = saját számláid között
            "currency": currency.upper(),
            "amount": str(amount),
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
            import json, urllib.request
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
            import json, urllib.request
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
        body = {
            "clientOid": uuid.uuid4().hex,
            "symbol": symbol,
            "side": side,
            "type": "market"
        }
        if size_base is not None:
            body["size"] = str(size_base)
        if funds_quote is not None:
            body["funds"] = str(funds_quote)
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

        body = {
            "clientOid": uuid.uuid4().hex, "symbol": symbol, "side": side, "type": "market",
            "isIsolated": (mode == "isolated"), "autoBorrow": bool(auto_borrow), "autoRepay": bool(auto_repay),
        }
        if size_base is not None:
            body["size"] = str(size_base)
        if funds_quote is not None:
            body["funds"] = str(funds_quote)
        if leverage is not None: body["leverage"] = leverage
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
        body = {"clientOid": uuid.uuid4().hex, "currency": currency, "amount": str(amount),
                "from": from_type, "to": to_type}
        return self._rest_post("/api/v2/accounts/inner-transfer", body)

# ========= GUI =========
class CryptoBotApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self._ex_lock = threading.RLock()
        self.root.title("KuCoin Universal SDK Bot (SPOT + Margin)")
        self.root.geometry("1280x930")

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

        params = ttk.Labelframe(self.tab_dash, text="Paraméterek", padding=10); params.pack(fill=tk.X, padx=10)
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

        # Log
        lf_log = ttk.Labelframe(self.tab_dash, text="Log", padding=10); lf_log.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10,10))
        self.log_area = scrolledtext.ScrolledText(lf_log, wrap=tk.WORD, height=10); self.log_area.pack(fill=tk.BOTH, expand=True)

        # Chart
        lf_ch = ttk.Labelframe(self.tab_dash, text="Diagram (Close + MA)", padding=10)
        lf_ch.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0,10))
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

        # === Funds / Átvezetés ===
        # Modernizált fül: fentről lefelé: Egyenlegek táblázat, Átvezetési vezérlők, Log
        self.tab_funds = ttk.Frame(self.nb); self.nb.add(self.tab_funds, text="Funds / Átvezetés")

        # 1. Balances View (Összesített egyenleg táblázat)
        bf = ttk.Labelframe(self.tab_funds, text="Összesített egyenlegek (Main, Trade, Cross, Isolated)", padding=10)
        bf.pack(fill=tk.X, padx=10, pady=(10, 5))

        # Oszlopok definíciója: Deviza, Számla típusa, Elérhető, Tartott, **Bevétel(USD)**, Kötelezettség, Összesen, **PNL(USD)**, Pár
        cols = ("currency", "account_type", "available", "holds", "value_usd", "liability", "total", "pnl", "symbol")
        self.tbl_funds_bal = ttk.Treeview(bf, columns=cols, show='headings', height=10)

        # Fejlécek és oszlopszélességek beállítása
        self.tbl_funds_bal.heading("currency",     text="Deviza");    self.tbl_funds_bal.column("currency", width=70, anchor='center')
        self.tbl_funds_bal.heading("account_type", text="Számla");     self.tbl_funds_bal.column("account_type", width=90, anchor='center')
        self.tbl_funds_bal.heading("available",    text="Elérhető");    self.tbl_funds_bal.column("available", width=140, anchor='e')
        self.tbl_funds_bal.heading("holds",        text="Tartott");     self.tbl_funds_bal.column("holds", width=140, anchor='e')
        self.tbl_funds_bal.heading("value_usd",    text="Bevétel (USD)"); self.tbl_funds_bal.column("value_usd", width=140, anchor='e', stretch=tk.NO) # ÚJ
        self.tbl_funds_bal.heading("liability",    text="Kötelezettség"); self.tbl_funds_bal.column("liability", width=140, anchor='e')
        self.tbl_funds_bal.heading("total",        text="Nettó Összesen");    self.tbl_funds_bal.column("total", width=140, anchor='e')
        self.tbl_funds_bal.heading("pnl",          text="PNL (USD)");       self.tbl_funds_bal.column("pnl", width=100, anchor='e', stretch=tk.NO) # ÚJ
        self.tbl_funds_bal.heading("symbol",       text="Pár");         self.tbl_funds_bal.column("symbol", width=90, anchor='center')
        self.tbl_funds_bal.pack(fill=tk.BOTH, expand=False, pady=(0, 5))

        # Frissítő gomb
        btn_refresh = ttk.Button(bf, text="Összes egyenleg frissítése", command=self.refresh_all_funds_balances)
        btn_refresh.pack(pady=5)

        # Margin "beragadt" kötelezettségek célzott rendezése
        btn_repay = ttk.Button(
            bf,
            text="Beragadt margin kötelezettségek rendezése",
            command=self.repay_stuck_margin
        )
        btn_repay.pack(pady=(0, 5))

        # 2. Transfers (Átvezetési vezérlők, a régi logika megtartásával)
        ff = ttk.Labelframe(self.tab_funds, text="Átvezetés", padding=10); ff.pack(fill=tk.X, padx=10, pady=5)

        # Spot Main <-> Trade
        ttk.Label(ff, text="Spot belső (Main ⇄ Trade)").grid(row=0, column=0, sticky="w")
        self.f_spot_ccy = ttk.Entry(ff, width=10); self.f_spot_ccy.insert(0, "USDT"); self.f_spot_ccy.grid(row=0, column=1, padx=6)
        self.f_spot_amt = ttk.Entry(ff, width=10); self.f_spot_amt.insert(0, "10"); self.f_spot_amt.grid(row=0, column=2, padx=6)
        ttk.Button(ff, text="Main → Trade", command=lambda: self._do_spot_transfer("main","trade")).grid(row=0, column=3, padx=4)
        ttk.Button(ff, text="Trade → Main", command=lambda: self._do_spot_transfer("trade","main")).grid(row=0, column=4, padx=4)

        # Cross margin
        ttk.Label(ff, text="Cross ⇄ Spot").grid(row=1, column=0, sticky="w", pady=(8,0))
        self.f_cross_ccy = ttk.Entry(ff, width=10); self.f_cross_ccy.insert(0, "USDT"); self.f_cross_ccy.grid(row=1, column=1, padx=6, pady=(8,0))
        self.f_cross_amt = ttk.Entry(ff, width=10); self.f_cross_amt.insert(0, "10"); self.f_cross_amt.grid(row=1, column=2, padx=6, pady=(8,0))
        ttk.Button(ff, text="Spot → Cross", command=lambda: self._do_cross_transfer("in")).grid(row=1, column=3, padx=4, pady=(8,0))
        ttk.Button(ff, text="Cross → Spot", command=lambda: self._do_cross_transfer("out")).grid(row=1, column=4, padx=4, pady=(8,0))

        # Isolated margin
        ttk.Label(ff, text="Isolated ⇄ Spot (pár + deviza)").grid(row=2, column=0, sticky="w", pady=(8,0))
        self.f_iso_sym = ttk.Combobox(ff, values=self.symbols, width=18, state='readonly'); self.f_iso_sym.set(DEFAULT_SYMBOL)
        self.f_iso_sym.grid(row=2, column=1, padx=6, pady=(8,0))
        self.f_iso_ccy = ttk.Entry(ff, width=10); self.f_iso_ccy.insert(0, "USDT"); self.f_iso_ccy.grid(row=2, column=2, padx=6, pady=(8,0))
        self.f_iso_amt = ttk.Entry(ff, width=10); self.f_iso_amt.insert(0, "10"); self.f_iso_amt.grid(row=2, column=3, padx=6, pady=(8,0))
        # Isolated Margin Átvezetés gombjai (két 'in' gomb a forrás kiválasztásához)
        ttk.Button(ff, text="Main → Isolated", command=lambda: self._do_isolated_transfer("in", "MAIN")).grid(row=2, column=4, padx=4, pady=(8,0))
        ttk.Button(ff, text="Trade → Isolated", command=lambda: self._do_isolated_transfer("in")).grid(row=2, column=5, padx=4, pady=(8,0))
        # Isolated -> Spot gomb
        ttk.Button(ff, text="Isolated → Spot", command=lambda: self._do_isolated_transfer("out")).grid(row=2, column=6, padx=4, pady=(8,0))

        # 3. Funds log (Log terület a fül alján)
        self.funds_log = scrolledtext.ScrolledText(self.tab_funds, wrap=tk.WORD, height=8)
        self.funds_log.pack(fill=tk.BOTH, expand=True, padx=10, pady=(5,10))

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
        self._ensure_order_ws()

        # --- Margin Bot (auto) ---
        self._build_margin_bot_tab()

        # --- Beállítások fül (font) ---
        self._build_settings_tab()

        # Szimbólumok betöltése háttérben
        threading.Thread(target=self._load_symbols_async, daemon=True).start()

        # 4) FONT GLOBÁLIS ALKALMAZÁSA
        self._apply_global_font()

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

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
            messagebox.showwarning("Privát mód szükséges",
                                   "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        def worker():
            # cache vödör
            self._balance_cache = {"spot": {}, "cross": {}, "isolated": {}}
            self.usdt_avail = 0.0

            try:
                ex = self.exchange
                all_rows = []
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
                        all_rows.append({
                            "ccy": ccy, "acc_type": acc_type.capitalize(),
                            "avail": avail, "holds": holds, "liability": 0.0, "symbol": ""
                        })
                        unique_ccy.add(ccy)

                self._balance_cache["spot"] = spot_cache

                # ---------- 2) CROSS ----------
                with self._ex_lock:
                    cross_resp = ex.fetch_cross_accounts()  # type: ignore[union-attr]
                cdata = cross_resp.get("data", {}) if isinstance(cross_resp, dict) else {}
                accounts = cdata.get("accounts", []) or cdata.get("accountList", []) or []

                # cache: cross[CCY] = {"avail":..., "holds":..., "liability":...}
                cross_cache: dict[str, dict] = {}

                for a in accounts:
                    ccy = (a.get("currency") or a.get("currencyName") or "").upper()
                    if not ccy:
                        continue
                    avail = float(a.get("available", a.get("availableBalance", a.get("free", 0))) or 0)
                    holds = float(a.get("holds", a.get("holdBalance", 0)) or 0)
                    liab  = float(a.get("liability", a.get("debt", 0)) or 0)

                    # ha csak 'balance' volt
                    if avail == 0 and "balance" in a:
                        bal = float(a.get("balance") or 0.0)
                        hb  = float(a.get("holdBalance") or 0.0)
                        if bal > 0 and bal >= hb:
                            avail = bal - hb
                            holds = hb

                    cross_cache[ccy] = {"avail": avail, "holds": holds, "liability": liab}

                    if avail > 0 or holds > 0 or liab > 0:
                        all_rows.append({
                            "ccy": ccy, "acc_type": "Cross",
                            "avail": avail, "holds": holds, "liability": liab, "symbol": ""
                        })
                        unique_ccy.add(ccy)

                self._balance_cache["cross"] = cross_cache

                # ---------- 3) ISOLATED ----------
                with self._ex_lock:
                    iso_resp = ex.fetch_isolated_accounts()  # type: ignore[union-attr]
                idata = iso_resp.get("data", {}) if isinstance(iso_resp, dict) else getattr(iso_resp, "data", {}) or {}
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

                    if base_pack["ccy"] and (base_pack["avail"] > 0 or base_pack["holds"] > 0 or base_pack["liability"] > 0):
                        all_rows.append({
                            "ccy": base_ccy, "acc_type": "Isolated",
                            "avail": base_pack["avail"], "holds": base_pack["holds"],
                            "liability": base_pack["liability"], "symbol": symbol
                        })
                        unique_ccy.add(base_ccy)

                    if quote_pack["ccy"] and (quote_pack["avail"] > 0 or quote_pack["holds"] > 0 or quote_pack["liability"] > 0):
                        all_rows.append({
                            "ccy": quote_ccy, "acc_type": "Isolated",
                            "avail": quote_pack["avail"], "holds": quote_pack["holds"],
                            "liability": quote_pack["liability"], "symbol": symbol
                        })
                        unique_ccy.add(quote_ccy)

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

                # 4/c) (opcionális) utolsó per-CCY REST fallback már nem nagyon szükséges:
                # ha valami CCY-hez nincs ár, annak az értékét 0-nak vesszük.

                # ---------- 5) USD értékek ----------
                def _pair_key(rec):
                    sym = rec.get("symbol") or ""
                    return sym if sym else f"{rec.get('ccy','')}-USDT"

                ACCOUNT_SORT_PRIORITY = {"Main": 0, "Trade": 1, "Cross": 2, "Isolated": 3}

                records = []
                for row in all_rows:
                    ccy = row["ccy"]
                    px = float(prices.get(ccy, 0.0))
                    if px <= 0:
                        px = 0.0
                    value_usd = float(row["avail"]) * px
                    liab_usd  = float(row["liability"]) * px
                    pnl_usd   = value_usd - liab_usd
                    nrow = dict(row)
                    nrow.update({"value": value_usd, "pnl": pnl_usd})
                    records.append(nrow)

                records.sort(key=lambda r: (
                    ACCOUNT_SORT_PRIORITY.get(r.get("acc_type"), 99),
                    _pair_key(r),
                    (r.get("ccy") or "")
                ))

                final_rows = [
                    self._get_balance_row(
                        ccy=r["ccy"], acc_type=r["acc_type"], avail=r["avail"],
                        holds=r["holds"], liability=r["liability"], value=r["value"],
                        pnl=r["pnl"], symbol=r["symbol"]
                    )
                    for r in records
                ]

                self.root.after(0, lambda: (
                    self._update_funds_balance_table(final_rows),
                    self._mb_refresh_available()
                ))

            except RuntimeError as e:
                self.root.after(0, lambda: messagebox.showwarning("Privát hívás hiba", str(e)))
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("Hiba", f"Hiba az egyenlegek frissítésekor: {e}"))

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
        # Hozzáadtuk az mb_symbol-t (Margin Bot)
        for cb in (self.e_symbol, self.trade_symbol, self.cross_symbol, self.mt_symbol, self.mb_symbol, self.f_iso_sym):
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
        data = payload.get('data', payload)
        assets = data.get('assets', []) or []
        lines = ["Isolated Margin – Részletes nézet", ""]

        # --- Szimbólumok listája az árlekéréshez ---
        symbols = [a.get('symbol', '').upper() for a in assets if a.get('symbol')]
        prices: Dict[str, float] = {}

        # Minden szimbólumhoz get_best_price
        for sym in symbols:
            try:
                px = self.get_best_price(sym)
                prices[sym] = float(px if (self._is_pos_num(px) and px > 0) else 0.0)
            except Exception:
                prices[sym] = 0.0

        # --- Formázott sorok generálása ---
        for a in assets:
            sym = a.get('symbol', 'N/A').upper()
            status = a.get('status', '')
            debt_ratio = float(a.get('debtRatio', 0) or 0)

            base = a.get('baseAsset', {}) or {}
            quote = a.get('quoteAsset', {}) or {}

            base_ccy = base.get('currency', '')
            base_tot = float(base.get('total', 0) or 0)
            base_av  = float(base.get('available', 0) or 0)
            base_li  = float(base.get('liability', 0) or 0)

            quote_ccy = quote.get('currency', '')
            quote_tot = float(quote.get('total', 0) or 0)
            quote_av  = float(quote.get('available', 0) or 0)
            quote_li  = float(quote.get('liability', 0) or 0)

            # ---- Ár = CSUPÁN self.get_best_price ----
            last = float(prices.get(sym, 0.0))

            # Nettó érték számítás (ha van ár)
            net_quote = base_tot * last + quote_tot - quote_li if last > 0 else None

            if (base_tot > 0) or (quote_tot > 0) or (quote_li > 0) or (debt_ratio > 0):
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

                    # Pozíció irány és zárható méret
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

        if len(lines) <= 2:
            lines.append("Nincs releváns izolált eszköz/pozíció.")

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
        rows = self._parse_cross_rows(payload, default_quote)
        if not rows:
            return "Cross Margin – nincs releváns kitettség."

        symbols = [r["symbol"] for r in rows]
        prices: dict[str, float] = {}

        # Egységes árlekérés minden szimbólumra: get_best_price (WS → cache → REST)
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
            closable = r["closable"]
            base_ccy, quote_ccy = sym.split("-")[0], sym.split("-")[1]

            last = float(prices.get(sym, 0.0) or 0.0)
            est_val = f"{closable*last:,.2f} {quote_ccy}" if last > 0 else "n/a"

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
        Csak KuCoin Spot/Margin esetén van értelme.
        """
        # már van és fut
        if getattr(self, "_order_ws", None) is not None:
            try:
                if self._order_ws.is_running():
                    return
            except Exception:
                # ha valamiért nincs ilyen metódus, újrainitializáljuk
                pass

        try:
            # REST POST a KucoinSDKWrapper-ből jön!
            if self.exchange is None:
                with self._ex_lock:
                    # >>> ITT LEGYEN PÉLDÁNYOSÍTÁS, NEM OSZTÁLY HOZZÁRENDELÉS <<<
                    self.exchange = KucoinSDKWrapper(
                        public_mode=self.public_mode.get(),
                        log_fn=self.log,
                    )

            self._order_ws = KucoinPrivateOrderWS(
                rest_post_func=self.exchange._rest_post,
                log_func=self._safe_log,
            )
            self._order_ws.start()
            self._safe_log("🔌 Privát order WS elindítva.\n")
        except Exception as e:
            self._safe_log(f"⚠️ Privát order WS init hiba: {e}\n")
            self._order_ws = None

    def _mt_start_price_loop(self):
        if self._mt_price_job:
            self.root.after_cancel(self._mt_price_job)

        self._mt_price_inflight = False  # egyszerre csak egy kérés fusson

        def _tick():
            try:
                # csak aktív fülön frissítünk
                if self.nb.tab(self.nb.select(), "text") != "Margin Trade":
                    return
                if self._mt_price_inflight:
                    return
                self._mt_price_inflight = True

                sym = normalize_symbol(self.mt_symbol.get())
                try:
                    self._ensure_ticker_ws(sym)
                except Exception:
                    pass
                # ---- egységes árlekérés: WS → cache → REST ----
                try:
                    px = self.get_best_price(sym)
                    if not self._is_pos_num(px) or px <= 0:
                        px = 0.0
                except Exception:
                    px = 0.0

                # ---- UI update ----
                self._mt_price_inflight = False
                if px > 0:
                    self.mt_price_lbl.config(text=f"Ár: {px:.6f}")
                else:
                    self.mt_price_lbl.config(text="Ár: –")

                # becslések frissítése
                self._mt_update_estimate(px)

            finally:
                # 1s-enként polloljuk a websocket/REST kombót (most már get_best_price)
                self._mt_price_job = self.root.after(1000, _tick)

        self._mt_price_job = self.root.after(100, _tick)

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
            self.root.config(cursor="watch")
            
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
            self.root.after(0, lambda: [
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
            bc = getattr(self, "_balance_cache", {}) or {}

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
                import math

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
                self.root.after(0, lambda: [
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
                # Capability log: margin order api
                try:
                    moa = None
                    if hasattr(self.exchange, "get_margin_order_api"):
                        with self._ex_lock:
                            moa = self.exchange.get_margin_order_api()
                    if moa is None and hasattr(self.exchange, "_client"):
                        try:
                            with self._ex_lock:
                                rs = self.exchange._client.rest_service()
                            ms = rs.get_margin_service()
                            if ms and hasattr(ms, "get_order_api"):
                                moa = ms.get_order_api()
                        except Exception:
                            moa = None
                    self.log(f"Margin order API: {moa.__class__.__name__ if moa else 'N/A'}")
                except Exception:
                    self.log("Margin order API: N/A")
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
            self.tick_once()
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
            import pandas as pd
            try:
                # exchange init (public), ha nincs
                if getattr(self, "exchange", None) is None:
                    self.exchange = KucoinSDKWrapper(public_mode=True, log_fn=self.log)

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

                # --- 2) Ha nincs használható cache, akkor REST-ből töltjük az OHLCV-t ---
                if not use_cache_df:
                    with self._ex_lock:
                        ohlcv = self.exchange.fetch_ohlcv(p_symbol, p_tf, limit=200)

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
        dates = pd.to_datetime(df['ts'], unit='ms')
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
                import math
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
    def _do_spot_transfer(self, from_type: str, to_type: str):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        ccy = self.f_spot_ccy.get().strip().upper()
        try:
            amt = float(self.f_spot_amt.get())
            if amt <= 0: raise ValueError
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

    def _do_cross_transfer(self, direction: str):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        ccy = self.f_cross_ccy.get().strip().upper()
        try:
            amt = float(self.f_cross_amt.get()); assert amt > 0
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

    def _do_isolated_transfer(self, direction: str):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        sym = normalize_symbol(self.f_iso_sym.get())
        ccy = self.f_iso_ccy.get().strip().upper()
        try:
            amt = float(self.f_iso_amt.get()); assert amt > 0
        except Exception:
            messagebox.showerror("Hiba", "Érvénytelen összeg."); return

        def worker():
            try:
                with self._ex_lock:
                    resp = self.exchange.transfer_isolated_margin(sym, ccy, amt, direction)  # ← EZT hívjuk
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
        root.grid_columnconfigure(1, weight=1)  # jobb: history+chart
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
        def _on_scroll_frame_config(event):
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

        # ===== bal oszlop: beállítások (form) – IDE jön a régi tartalom =====
        form = ttk.Labelframe(
            scroll_frame,
            text="Margin bot – beállítások",
            padding=10,
            style="Card.TLabelframe",
        )
        form.grid(row=0, column=0, sticky="nwe")
        for i in range(2):
            form.grid_columnconfigure(i, weight=1)
        r = 0

        # mód választó
        self.mb_mode = tk.StringVar(value="isolated")
        mrow = ttk.Frame(form); mrow.grid(row=r, column=0, columnspan=2, sticky="w")
        ttk.Radiobutton(
            mrow, text="Isolated", variable=self.mb_mode, value="isolated",
            command=lambda: (self._mb_sync_lev_cap(), self._mb_refresh_available())
        ).pack(side=tk.LEFT, padx=(0,12))
        ttk.Radiobutton(
            mrow, text="Cross", variable=self.mb_mode, value="cross",
            command=lambda: (self._mb_sync_lev_cap(), self._mb_refresh_available())
        ).pack(side=tk.LEFT)
        r += 1

        ttk.Label(form, text="Pár").grid(row=r, column=0, sticky="w", pady=(4,0))
        # Egy soron belüli konténer, hogy a Pár combó és a Max pozíció egymás mellett legyen
        row_pair = ttk.Frame(form)
        row_pair.grid(row=r, column=1, pady=(4,0), sticky="w")
        # Pár combó
        self.mb_symbol = ttk.Combobox(row_pair, values=self.symbols, width=12, state='readonly')
        self.mb_symbol.set(DEFAULT_SYMBOL)
        self.mb_symbol.pack(side="left")
        # Max pozíció (0 = korlátlan) – KÖZVETLENÜL a Pár mellett
        ttk.Label(row_pair, text="  Max pozíció:").pack(side="left")
        self.mb_max_open = ttk.Spinbox(row_pair, from_=0, to=999, width=6)
        self.mb_max_open.pack(side="left", padx=(4,0))
        # alapértelmezett érték
        self.mb_max_open.delete(0, "end"); self.mb_max_open.insert(0, "0")
        # párváltáskor frissítsük az elérhető egyenleget
        self.mb_symbol.bind("<<ComboboxSelected>>", self._mb_refresh_available)
        r += 1

        # Idősík
        ttk.Label(form, text="Idősík").grid(row=r, column=0, sticky="w", pady=(4,0))
        self.mb_tf = ttk.Combobox(form, state="readonly", width=10,
                                  values=["1m","3m","5m","15m","30m","1h","4h","1d"])
        self.mb_tf.set("1m")
        self.mb_tf.grid(row=r, column=1, sticky="w", pady=(4,0))
        # fül felépítése után egyszer töltsük be az elérhető egyenleget
        self.root.after(50, self._mb_refresh_available)
        r += 1

        # EMA (rövid/hosszú) – a worker mb_ma_fast/mb_ma_slow nevét használja
        ttk.Label(form, text="EMA (rövid / hosszú)").grid(row=r, column=0, sticky="w", pady=(2,0))
        ema_row = ttk.Frame(form); ema_row.grid(row=r, column=1, sticky="w", pady=(2,0))
        self.mb_ma_fast = ttk.Spinbox(ema_row, from_=2, to=500, width=6)
        self.mb_ma_fast.delete(0, tk.END); self.mb_ma_fast.insert(0, "12")
        self.mb_ma_fast.pack(side=tk.LEFT)
        ttk.Label(ema_row, text=" ").pack(side=tk.LEFT)
        self.mb_ma_slow = ttk.Spinbox(ema_row, from_=3, to=1000, width=6)
        self.mb_ma_slow.delete(0, tk.END); self.mb_ma_slow.insert(0, "26")
        self.mb_ma_slow.pack(side=tk.LEFT)

        # Invert checkbox ugyanebben a sorban
        ttk.Label(ema_row, text="   ").pack(side=tk.LEFT)  # kis elválasztó
        self.mb_invert_ema = tk.BooleanVar(value=False)
        ttk.Checkbutton(ema_row, text="Invert EMA jel-logika", variable=self.mb_invert_ema)\
           .pack(side=tk.LEFT, padx=(4,0))
        r += 1  # <-- csak egyszer léptetünk itt

        # EMA jel-szűrő paraméterek – KÖVETKEZŐ SOR (nincs extra r+=1 előtte!)
        ttk.Label(form, text="EMA Hysteresis (Zajszűrés):").grid(row=r, column=0, sticky="w", pady=(6,0))
        ema_f_row = ttk.Frame(form)
        ema_f_row.grid(row=r, column=1, sticky="w", pady=(6,0))
        self.mb_ema_hyst_pct = ttk.Spinbox(ema_f_row, from_=0.0, to=100, width=6)
        self.mb_ema_hyst_pct.delete(0, tk.END); self.mb_ema_hyst_pct.insert(0, "1.00")
        self.mb_ema_hyst_pct.pack(side=tk.LEFT)
        r += 1

        # Tőkeáttét (worker: mb_leverage) + kompat alias a _mb_sync_lev_cap-hez
        ttk.Label(form, text="Tőkeáttét").grid(row=r, column=0, sticky="w", pady=(6,0))
        self.mb_leverage = ttk.Spinbox(form, from_=1, to=10, width=6)
        self.mb_leverage.delete(0, tk.END); self.mb_leverage.insert(0, "10")
        self.mb_leverage.grid(row=r, column=1, sticky="w", pady=(6,0))
        self.mb_lev = self.mb_leverage
        r += 1

        # Méret % és input mód (QUOTE/BASE) + opcionális QUOTE keret
        ttk.Label(form, text="Méret (%, QUOTE/BASE szerint)").grid(row=r, column=0, sticky="w", pady=(6,0))
        size_row = ttk.Frame(form); size_row.grid(row=r, column=1, sticky="w", pady=(6,0))
        self.mb_size_pct = ttk.Spinbox(size_row, from_=1, to=100, width=6)
        self.mb_size_pct.delete(0, tk.END); self.mb_size_pct.insert(0, "25")
        self.mb_size_pct.pack(side=tk.LEFT)
        ttk.Label(size_row, text="  mód:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_input_mode = ttk.Combobox(size_row, state="readonly", width=7, values=["quote","base"])
        self.mb_input_mode.set("quote"); self.mb_input_mode.pack(side=tk.LEFT)
        r += 1

        ttk.Label(form, text="Keret (QUOTE) – opcionális").grid(row=r, column=0, sticky="w", pady=(2,0))
        # mező + elérhető egyenleg egysorban
        _row_budget = ttk.Frame(form); _row_budget.grid(row=r, column=1, sticky="w", pady=(2,0))
        self.mb_budget = ttk.Entry(_row_budget, width=12)  # ha üres: elérhető QUOTE-ot használ
        self.mb_budget.pack(side=tk.LEFT)
        ttk.Label(_row_budget, text="  Elérhető:").pack(side=tk.LEFT, padx=(8,2))
        self.mb_avail_var = tk.StringVar(value="–")
        self.mb_avail_lbl = ttk.Label(_row_budget, textvariable=self.mb_avail_var)
        self.mb_avail_lbl.pack(side=tk.LEFT)
        r += 1

        # Fix SL / TP / Trailing – opcionális (ATR nélkül)
        fixed_box = ttk.Labelframe(form, text="Fix SL / TP / Trailing (ATR nélkül)", padding=6)
        fixed_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        fixed_row1 = ttk.Frame(fixed_box); fixed_row1.pack(anchor="w")

        self.mb_use_fixed = tk.BooleanVar(value=True)  # új kapcsoló
        ttk.Checkbutton(fixed_row1, text="Fix menedzsment használata", variable=self.mb_use_fixed,
                        command=self._mb_on_fixed_changed).pack(side=tk.LEFT)

        fixed_row2 = ttk.Frame(fixed_box); fixed_row2.pack(anchor="w", pady=(4,0))
        ttk.Label(fixed_row2, text="SL %").pack(side=tk.LEFT)
        self.mb_sl_pct = ttk.Spinbox(fixed_row2, from_=0, to=50, increment=0.1, width=6)
        self.mb_sl_pct.delete(0, tk.END); self.mb_sl_pct.insert(0, "5.0")
        self.mb_sl_pct.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(fixed_row2, text="TP %").pack(side=tk.LEFT)
        self.mb_tp_pct = ttk.Spinbox(fixed_row2, from_=0, to=50, increment=0.1, width=6)
        self.mb_tp_pct.delete(0, tk.END); self.mb_tp_pct.insert(0, "1.0")
        self.mb_tp_pct.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(fixed_row2, text="Trailing %").pack(side=tk.LEFT)
        self.mb_trail_pct = ttk.Spinbox(fixed_row2, from_=0, to=20, increment=0.1, width=6)
        self.mb_trail_pct.delete(0, tk.END); self.mb_trail_pct.insert(0, "0")
        self.mb_trail_pct.pack(side=tk.LEFT, padx=(2,0))
        r += 1

        # --- LIVE kitörés / shock (intra-bar) ---
        live_box = ttk.Labelframe(form, text="LIVE kitörés / shock (intra-bar)", padding=6)
        live_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        live_row1 = ttk.Frame(live_box); live_row1.pack(anchor="w")

        self.mb_use_live = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            live_row1,
            text="Élő ár figyelése (breakout/shock)",
            variable=self.mb_use_live,
            command=self._mb_toggle_live_widgets   # <<< ÚJ: állapot váltáskor hívjuk
        ).pack(side=tk.LEFT)

        ttk.Label(live_row1, text="  Shock %:").pack(side=tk.LEFT, padx=(10,2))
        self.mb_live_shock_pct = ttk.Spinbox(live_row1, from_=0.0, to=10.0, increment=0.05, width=6)
        self.mb_live_shock_pct.delete(0, tk.END); self.mb_live_shock_pct.insert(0, "1.00")
        self.mb_live_shock_pct.pack(side=tk.LEFT)

        ttk.Label(live_row1, text="  Shock ATR×:").pack(side=tk.LEFT, padx=(10,2))
        self.mb_live_shock_atr = ttk.Spinbox(live_row1, from_=0.0, to=5.0, increment=0.05, width=6)
        self.mb_live_shock_atr.delete(0, tk.END); self.mb_live_shock_atr.insert(0, "1.20")
        self.mb_live_shock_atr.pack(side=tk.LEFT)
        r += 1

        # --- Breakout (kitörés) detektor – kapcsoló + paraméterek ---
        brk_box = ttk.Labelframe(form, text="Breakout (kitörés)", padding=6)
        brk_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        brk_row1 = ttk.Frame(brk_box); brk_row1.pack(anchor="w")

        self.mb_use_brk = tk.BooleanVar(value=False)
        ttk.Checkbutton(brk_row1, text="Breakout használata", variable=self.mb_use_brk,
                        command=lambda: self._mb_toggle_brk_widgets()).pack(side=tk.LEFT)

        ttk.Label(brk_row1, text="  Lookback:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_brk_n = ttk.Spinbox(brk_row1, from_=5, to=200, width=6)
        self.mb_brk_n.delete(0, tk.END); self.mb_brk_n.insert(0, "20")
        self.mb_brk_n.pack(side=tk.LEFT)

        ttk.Label(brk_row1, text="  Puffer %:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_brk_buf = ttk.Spinbox(brk_row1, from_=0.0, to=2.0, increment=0.01, width=6)
        self.mb_brk_buf.delete(0, tk.END); self.mb_brk_buf.insert(0, "0.10")
        self.mb_brk_buf.pack(side=tk.LEFT)

        self.mb_brk_with_trend = tk.BooleanVar(value=False)
        ttk.Checkbutton(brk_row1, text="Csak HTF trend irányába", variable=self.mb_brk_with_trend).pack(side=tk.LEFT, padx=(10,0))
        r += 1

        # RSI szűrő – kapcsoló + hossz + zónák
        rsi_box = ttk.Labelframe(form, text="RSI szűrő", padding=6)
        rsi_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))

        rsi_row1 = ttk.Frame(rsi_box); rsi_row1.pack(anchor="w")
        self.mb_use_rsi = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            rsi_row1,
            text="RSI használata",
            variable=self.mb_use_rsi,
            command=self._mb_toggle_rsi_widgets      # <-- ÚJ
        ).pack(side=tk.LEFT)

        ttk.Label(rsi_row1, text="  RSI len:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_rsi_len = ttk.Spinbox(rsi_row1, from_=5, to=50, width=6)
        self.mb_rsi_len.delete(0, tk.END); self.mb_rsi_len.insert(0, "14")
        self.mb_rsi_len.pack(side=tk.LEFT)

        rsi_row2 = ttk.Frame(rsi_box); rsi_row2.pack(anchor="w", pady=(4,0))
        ttk.Label(rsi_row2, text="BUY zóna [min,max]").pack(side=tk.LEFT)
        self.mb_rsi_buy_min = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_buy_min.delete(0, tk.END); self.mb_rsi_buy_min.insert(0, "45")
        self.mb_rsi_buy_min.pack(side=tk.LEFT, padx=(4,2))
        self.mb_rsi_buy_max = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_buy_max.delete(0, tk.END); self.mb_rsi_buy_max.insert(0, "70")
        self.mb_rsi_buy_max.pack(side=tk.LEFT, padx=(2,12))

        ttk.Label(rsi_row2, text="SELL zóna [min,max]").pack(side=tk.LEFT)
        self.mb_rsi_sell_min = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_sell_min.delete(0, tk.END); self.mb_rsi_sell_min.insert(0, "30")
        self.mb_rsi_sell_min.pack(side=tk.LEFT, padx=(4,2))
        self.mb_rsi_sell_max = ttk.Spinbox(rsi_row2, from_=0, to=100, increment=0.5, width=6)
        self.mb_rsi_sell_max.delete(0, tk.END); self.mb_rsi_sell_max.insert(0, "55")
        self.mb_rsi_sell_max.pack(side=tk.LEFT, padx=(2,0))
        r += 1

        # HTF trend filter – kapcsoló + HTF TF
        htf_box = ttk.Labelframe(form, text="HTF trend filter (EMA alapú)", padding=6)
        htf_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        htf_row = ttk.Frame(htf_box); htf_row.pack(anchor="w")

        self.mb_use_htf = tk.BooleanVar(value=False)
        ttk.Checkbutton(
            htf_row,
            text="HTF filter használata",
            variable=self.mb_use_htf,
            command=self._mb_toggle_htf_widgets     # <<< ÚJ
        ).pack(side=tk.LEFT)

        ttk.Label(htf_row, text="  HTF TF:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_htf_tf = ttk.Combobox(
            htf_row,
            state="readonly",
            width=6,
            values=["15m","30m","1h","4h","1d"]
        )
        self.mb_htf_tf.set("15m")
        self.mb_htf_tf.pack(side=tk.LEFT)
        r += 1

        # ATR menedzsment – kapcsoló + ATR n + szorzók
        atr_box = ttk.Labelframe(form, text="ATR alapú menedzsment (TP1/TP2 + trailing)", padding=6)
        atr_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        atr_row1 = ttk.Frame(atr_box); atr_row1.pack(anchor="w")
        self.mb_use_atr = tk.BooleanVar(value=False)
        ttk.Checkbutton(atr_row1, text="ATR menedzsment használata", command=self._mb_on_atr_changed, variable=self.mb_use_atr).pack(side=tk.LEFT)
        ttk.Label(atr_row1, text="  ATR n:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_atr_n = ttk.Spinbox(atr_row1, from_=5, to=50, width=6)
        self.mb_atr_n.delete(0, tk.END); self.mb_atr_n.insert(0, "14")
        self.mb_atr_n.pack(side=tk.LEFT)

        atr_row2 = ttk.Frame(atr_box); atr_row2.pack(anchor="w", pady=(4,0))
        ttk.Label(atr_row2, text="SL×").pack(side=tk.LEFT)
        self.mb_atr_mul_sl = ttk.Spinbox(atr_row2, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_atr_mul_sl.delete(0, tk.END); self.mb_atr_mul_sl.insert(0, "1.0"); self.mb_atr_mul_sl.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(atr_row2, text="TP1×").pack(side=tk.LEFT)
        self.mb_atr_mul_tp1 = ttk.Spinbox(atr_row2, from_=0.1, to=10.0, increment=0.1, width=5)
        self.mb_atr_mul_tp1.delete(0, tk.END); self.mb_atr_mul_tp1.insert(0, "1.5"); self.mb_atr_mul_tp1.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(atr_row2, text="TP2×").pack(side=tk.LEFT)
        self.mb_atr_mul_tp2 = ttk.Spinbox(atr_row2, from_=0.1, to=20.0, increment=0.1, width=5)
        self.mb_atr_mul_tp2.delete(0, tk.END); self.mb_atr_mul_tp2.insert(0, "2.5"); self.mb_atr_mul_tp2.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(atr_row2, text="Trail×").pack(side=tk.LEFT)
        self.mb_atr_mul_trail = ttk.Spinbox(atr_row2, from_=0.1, to=5.0, increment=0.1, width=5)
        self.mb_atr_mul_trail.delete(0, tk.END); self.mb_atr_mul_trail.insert(0, "1.0"); self.mb_atr_mul_trail.pack(side=tk.LEFT, padx=(2,0))
        r += 1

        # Cooldown
        ttk.Label(form, text="Cooldown (s)").grid(row=r, column=0, sticky="w", pady=(8,0))
        self.mb_cooldown_s = ttk.Spinbox(form, from_=1, to=600, width=8)
        self.mb_cooldown_s.delete(0, tk.END); self.mb_cooldown_s.insert(0, "10")
        self.mb_cooldown_s.grid(row=r, column=1, sticky="w", pady=(8,0))
        r += 1

        # checkboxok
        ch = ttk.Frame(form); ch.grid(row=r, column=0, columnspan=2, sticky="w", pady=(8,0))
        self.mb_autob = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Auto-borrow/repay", variable=self.mb_autob).pack(side=tk.LEFT, padx=(0.08))
        self.mb_allow_short = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Short engedélyezése", variable=self.mb_allow_short).pack(side=tk.LEFT, padx=(0.08))
        self.mb_pause_new = tk.BooleanVar(value=False)
        ttk.Checkbutton(ch, text="Új nyitás szünetel", variable=self.mb_pause_new).pack(side=tk.LEFT, padx=(0.08))
        self.mb_dry = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Dry-run (nem küld ordert)", variable=self.mb_dry).pack(side=tk.LEFT, padx=(0.08))
        r += 1

        # Start / Stop
        btns = ttk.Frame(form); btns.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10,0))
        self.mb_start_btn = ttk.Button(btns, text="Start bot", command=self.mb_start); self.mb_start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0,6))
        self.mb_stop_btn  = ttk.Button(btns, text="Stop bot",  command=self.mb_stop, state=tk.DISABLED); self.mb_stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        r += 1

        apply_btn = ttk.Button(
            form,
            text="Beállítások frissítése / paraméterek állítása ( futó botra )",
            command=self.mb_reload_cfg,
        )
        apply_btn.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10,0))
        
        # ===== jobb oszlop: felül fülek (History / Bot napló), alul mini-diagram =====
        right = ttk.Frame(root)
        right.grid(row=0, column=1, sticky="nsew", padx=(6,10), pady=10)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(0, weight=3)   # notebook (history+log)
        right.grid_rowconfigure(1, weight=2)   # chart

        # --- Fülrendszer: History + Bot napló ---
        right_nb = ttk.Notebook(right)
        right_nb.grid(row=0, column=0, sticky="nsew")

        # 1) Trade History (LIVE) fül
        tab_hist = ttk.Frame(right_nb)
        right_nb.add(tab_hist, text="Trade History (LIVE)")
        tab_hist.grid_columnconfigure(0, weight=1)
        tab_hist.grid_rowconfigure(0, weight=1)

        cols = ("timestamp","side","entry","exit","size","lev","fee","pnl","orderId")
        self._mb_hist_tv = ttk.Treeview(tab_hist, columns=cols, show="headings", height=10)
        for c, w, text in (
            ("timestamp", 160, "Időbélyeg"),
            ("side",       70,  "Irány"),
            ("entry",      110, "Belépő ár"),
            ("exit",       110, "Kilépő ár"),
            ("size",       110, "Méret"),
            ("lev",         90, "Tőkeáttét"),
            ("fee",         90, "Díj"),
            ("pnl",         90, "PNL"),
            ("orderId",    180, "Order ID"),
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

        # 2) Bot napló fül
        tab_log = ttk.Frame(right_nb)
        right_nb.add(tab_log, text="Bot napló")
        tab_log.grid_columnconfigure(0, weight=1)
        tab_log.grid_rowconfigure(0, weight=1)
        self.mb_log = scrolledtext.ScrolledText(tab_log, wrap=tk.WORD)
        self.mb_log.grid(row=0, column=0, sticky="nsew")

        # --- Mini-diagram az aktuális párról (Dashboardhoz hasonló) ---
        ch_box = ttk.Labelframe(right, text="Diagram (aktuális pár)", padding=6)
        ch_box.grid(row=1, column=0, sticky="nsew", pady=(6,0))
        from matplotlib.figure import Figure
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
        self.mb_fig = Figure(figsize=(6,2.4), dpi=100)
        self.mb_ax  = self.mb_fig.add_subplot(111)
        self.mb_canvas = FigureCanvasTkAgg(self.mb_fig, master=ch_box)
        self.mb_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # --- Margin Bot belső flag-ek / állapotok ---
        self._mb_running = False
        self._mb_thread = None

        # Jel/cooldown állapot
        self._mb_last_cross_ts = 0
        self._mb_last_signal = 'hold'
        self._mb_last_bar_ts = {}   # {(symbol, tf): ts}
        self._mb_lock = threading.Lock()

        # Szimulációs állapotok (ha még nem lettek máshol definiálva)
        if not hasattr(self, '_sim_pnl_usdt'):
            self._sim_pnl_usdt = 0.0          # realizált PnL USDT
        if not hasattr(self, '_sim_history'):
            self._sim_history = []            # list[dict]

        # kezdő tőkeáttét plafon
        self._mb_sync_lev_cap()

        # SL/TP/Trail init – a kezdeti állapotnak megfelelően
        self._mb_toggle_fixed_widgets()
        self._mb_toggle_atr_widgets()
        self._mb_toggle_brk_widgets()
        self._mb_toggle_live_widgets()
        self._mb_toggle_rsi_widgets()
        self._mb_toggle_htf_widgets()

        # a history táblázat létrehozása UTÁN:
        self._mb_hist_start_pnl_loop()

        # első rajz
        self._mb_draw_chart()

        # Margin és spot egyenleg cache. Ezt tölti fel a funds fül, de előre inicializálni kell.
        self._balance_cache: Dict[str, Any] = {}

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

    def _mb_draw_chart(self, lookback: int = 150):
            """Minidiagram a Margin Bot fülön: Close + opcionálisan két EMA a formból."""
            try:
                # Paraméterek kiolvasása
                symbol = normalize_symbol(self.mb_symbol.get())
                tf     = self.mb_tf.get()
                fa     = int(self.mb_ma_fast.get())
                slw    = int(self.mb_ma_slow.get())

                # ----------------------------------------------------
                # ÚJ ELLENŐRZÉS: Exchange objektum inicializálva van-e
                # ----------------------------------------------------
                ex = getattr(self, "exchange", None)
                if ex is None:
                    # Csendes hibajelzés, ha a bot nincs indítva.
                    # Ezzel megelőzzük a 'NoneType' object has no attribute 'fetch_ohlcv' hibát.
                    try: self._safe_log("❌ Chart hiba: Az Exchange objektum nincs inicializálva (nincs futás).\n")
                    except Exception: pass
                    return
                # ----------------------------------------------------

                # Lekérés (most már a biztonságos 'ex' változót használjuk)
                ohlcv = ex.fetch_ohlcv(symbol, tf, limit=max(lookback, slw+5)) # type: ignore
                if not ohlcv:
                    return
                
                import pandas as pd, matplotlib.dates as mdates
                
                df = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
                df["dt"] = pd.to_datetime(df["ts"], unit="ms")

                # EMA-k
                close = df["c"].astype(float)

                # --- Websocket élő ár integráció ---
                try:
                    if getattr(self, "_ticker_ws", None) is not None:
                        rt = float(self._ticker_ws.get_last_price() or 0.0)
                        if rt > 0:
                            # utolsó gyertya záróárát kicseréljük az élő árra
                            close.iloc[-1] = rt
                            df.loc[df.index[-1], "c"] = rt
                except Exception:
                    pass

                ema_f = close.ewm(span=fa, adjust=False).mean()
                ema_s = close.ewm(span=slw, adjust=False).mean()

                # rajz
                self.mb_ax.clear()
                self.mb_ax.plot(df["dt"], close, label="Close")
                self.mb_ax.plot(df["dt"], ema_f, label=f"EMA({fa})")
                self.mb_ax.plot(df["dt"], ema_s, label=f"EMA({slw})")
                self.mb_ax.legend(loc="lower left")
                self.mb_ax.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))
                self.mb_ax.set_title(symbol + " • " + tf)
                self.mb_ax.grid(True, alpha=0.25)
                self.mb_fig.tight_layout()
                self.mb_canvas.draw_idle()
            except Exception as e:
                # csendes – ne dobáljon fel ablakot
                try: self._safe_log(f"Chart hiba: {e}\n")
                except Exception: pass

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
                # JAVÍTÁS: Itt már az új 'self.mb_symbol'-t használjuk (lásd 2. pont)
                sym = normalize_symbol(self.mb_symbol.get()) 
                base, quote = split_symbol(sym)
                mode = (self.mb_mode.get() or "isolated").lower()

                if self.public_mode.get():
                    self.mb_avail_var.set("N/A (public)")
                    return
            except Exception as e:
                self.mb_avail_var.set("Hiba (param)")
                self._safe_log(f"❌ _mb_refresh param hiba: {e}\n")
                return

            def worker():
                avail_quote = None
                try:
                    # 3. Próba a cache-ből (gyors út)
                    bc = getattr(self, "_balance_cache", {})
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
                    self._safe_log(f"ℹ️ MarginBot egyenleg: cache miss ({mode}/{sym}), célzott lekérés...\n")

                    if mode == "isolated":
                        with self._ex_lock:
                            resp = self.exchange.fetch_isolated_accounts() # type: ignore[union-attr]
                        
                        idata = resp.get("data", {}) if isinstance(resp, dict) else getattr(resp, "data", {}) or {}
                        assets = idata.get("assets", []) or []
                        
                        # Biztosítjuk, hogy a cache létezzen
                        if "isolated" not in self._balance_cache:
                            self._balance_cache["isolated"] = {}
                        
                        for asset in assets:
                            symbol_from_asset = (asset.get("symbol") or "").upper()
                            if not symbol_from_asset: continue
                            
                            base_pack = asset.get("baseAsset", {}) or {}
                            quote_pack = asset.get("quoteAsset", {}) or {}
                            
                            # Cache feltöltése a talált adattal
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
                                }
                            }
                            
                            # Ha ez a keresett szimbólum, mentsük el az értéket
                            if symbol_from_asset == sym:
                                avail_quote = float(quote_pack.get("available") or 0.0)

                    elif mode == "cross":
                        with self._ex_lock:
                            resp = self.exchange.fetch_cross_accounts() # type: ignore[union-attr]
                        
                        cdata = resp.get("data", {}) if isinstance(resp, dict) else {}
                        accounts = cdata.get("accounts", []) or cdata.get("accountList", []) or []
                        
                        if "cross" not in self._balance_cache:
                            self._balance_cache["cross"] = {}

                        for a in accounts:
                            ccy = (a.get("currency") or a.get("currencyName") or "").upper()
                            if not ccy: continue
                            
                            avail = float(a.get("available", a.get("availableBalance", a.get("free", 0))) or 0)
                            holds = float(a.get("holds", a.get("holdBalance", 0)) or 0)
                            liab  = float(a.get("liability", a.get("debt", 0)) or 0)
                            
                            # Cache feltöltése
                            self._balance_cache["cross"][ccy] = {"avail": avail, "holds": holds, "liability": liab}
                            
                            if ccy == quote:
                                avail_quote = avail
                    
                    # 6. UI frissítés a lekért adattal
                    if avail_quote is None: avail_quote = 0.0
                    self.root.after(0, self.mb_avail_var.set, f"{avail_quote:.2f} {quote}")

                except Exception as e:
                    self.root.after(0, self.mb_avail_var.set, "Hiba (lekérés)")
                    self._safe_log(f"❌ _mb_refresh_available hiba: {e}\n")

            # 7. A worker indítása háttérszálon
            threading.Thread(target=worker, daemon=True).start()

    # ---- Margin "beragadt" kötelezettségek rendezése (cross margin, KuCoin szerinti maxRepayAmount alapján) ----
    def repay_stuck_margin(self):
        """
        Funds fülön lévő 'Repay' gombhoz.

        Ahelyett, hogy saját magunk számolnánk a törleszthető összeget cross/isolated
        account view-ból, közvetlenül a KuCoin margin account endpointját kérdezzük le:

            GET /api/v3/margin/account

        Ez tartalmazza devizánként:
            - liability        (tartozás)
            - maxRepayAmount   (mennyi törlesztés ENGEDÉLYEZETT)

        A repay hívás pedig:
            POST /api/v3/margin/repay  body = {"currency": "...", "size": "..."}

        => Így elkerüljük a 130203 (Insufficient balance / max borrowing exceeded) hibákat,
           mert csak a maxRepayAmount-ig próbálunk törleszteni.
        """
        if self.public_mode.get():
            messagebox.showwarning(
                "Privát mód szükséges",
                "Kapcsold ki a publikus módot és állítsd be az API kulcsokat."
            )
            return

        def worker():
            import math

            try:
                ex = self.exchange
                if not ex:
                    raise RuntimeError("Nincs aktív exchange kliens.")

                # 1) KuCoin margin account – ez adja a liabilityList + maxRepayAmount mezőket
                with self._ex_lock:
                    acc_raw = ex._rest_get("/api/v3/margin/account", {})  # type: ignore[union-attr]

                if not isinstance(acc_raw, dict) or str(acc_raw.get("code", "")) != "200000":
                    raise RuntimeError(f"Margin account hívás hiba / nem 200000: {acc_raw!r}")

                data = acc_raw.get("data", {}) or {}
                liab_list = data.get("liabilityList", []) or []

                # 2) Devizánként kigyűjtjük a liability + maxRepayAmount adatokat
                repay_ops: list[tuple[str, float, float, float]] = []
                # (ccy, liability, max_repay, safe_amt)

                for item in liab_list:
                    ccy  = (item.get("currency") or "").upper()
                    if not ccy:
                        continue

                    try:
                        liab = float(item.get("liability") or 0.0)
                        max_r = float(item.get("maxRepayAmount") or 0.0)
                    except Exception:
                        continue

                    # Csak akkor érdekes, ha tényleg van tartozás
                    if liab <= 0:
                        continue

                    # Ha a KuCoin szerint maxRepayAmount == 0 → semmit nem enged törleszteni
                    if max_r <= 0:
                        # Logoljuk, hogy értsd miért nincs repay kísérlet
                        self.root.after(0, lambda c=ccy, l=liab: (
                            self.funds_log.insert(
                                tk.END,
                                f"ℹ️ {c}: liability={l:.8f}, de maxRepayAmount=0 – KuCoin jelenleg nem enged repay-t erre a devizára.\n"
                            ),
                            self.funds_log.see(tk.END)
                        ))
                        continue

                    # Alapelv: sose próbáljunk többet törleszteni, mint a liability
                    raw_repay = min(liab, max_r)

                    # Biztonsági margin:
                    # - pici epsilon kivonása (float hibák ellen)
                    # - 0.999 faktor, hogy biztosan a maxRepay alatt maradjunk
                    eps = 1e-8
                    safe_amt = max(0.0, raw_repay - eps) * 0.999

                    # Lefelé kerekítés 8 tizedesre (KuCoin USDT/általános pattern)
                    safe_amt = math.floor(safe_amt * 1e8) / 1e8

                    if safe_amt <= 0:
                        # Ha a biztonságos összeg gyakorlatilag 0-ra kerekedik, akkor ezt a devizát kihagyjuk
                        self.root.after(0, lambda c=ccy, l=liab, mr=max_r: (
                            self.funds_log.insert(
                                tk.END,
                                f"ℹ️ {c}: liability={l:.8f}, maxRepayAmount={mr:.8f}, "
                                f"de a biztonságos repay összeg túl kicsi – kihagyva.\n"
                            ),
                            self.funds_log.see(tk.END)
                        ))
                        continue

                    repay_ops.append((ccy, liab, max_r, safe_amt))

                if not repay_ops:
                    # Semmi olyat nem találtunk, amire KuCoin szerint van törleszthető összeg
                    self.root.after(0, lambda: (
                        self.funds_log.insert(
                            tk.END,
                            "ℹ️ Nem találtam olyan devizát, amelyre a KuCoin maxRepayAmount > 0 lett volna. "
                            "Nincs automatikusan törleszthető margin kötelezettség.\n"
                        ),
                        self.funds_log.see(tk.END)
                    ))
                    return

                # 3) Devizánként repay hívás a KuCoin által engedett safe_amt értékkel
                for ccy, liab, max_r, safe_amt in repay_ops:
                    body = {
                        "currency": ccy,
                        "size": f"{safe_amt:.8f}",
                    }

                    try:
                        with self._ex_lock:
                            resp = ex._rest_post("/api/v3/margin/repay", body)  # type: ignore[union-attr]

                        def _log_repay(c=ccy, l=liab, mr=max_r, a=safe_amt, r=resp):
                            # Diagnosztika: megmutatjuk a liability, maxRepayAmount és küldött összeget
                            self.funds_log.insert(
                                tk.END,
                                f"↪ Repay próbálkozás {c}: liability={l:.8f}, maxRepayAmount={mr:.8f}, küldött={a:.8f}\n"
                            )

                            if isinstance(r, dict):
                                code = str(r.get("code", "?"))
                                msg  = str(r.get("msg", "")) if r.get("msg") is not None else ""

                                if code == "200000":
                                    self.funds_log.insert(
                                        tk.END,
                                        f"✅ Repay sikeres: {c} {a:.8f} – code={code}\n"
                                    )
                                elif code == "130203":
                                    # Insufficient account balance / max borrowing exceeded
                                    self.funds_log.insert(
                                        tk.END,
                                        f"❌ Repay elutasítva {c} {a:.8f}: 130203 – "
                                        f"Nincs elég margin egyenleg ehhez a törlesztéshez (KuCoin szerint). msg='{msg}'\n"
                                    )
                                else:
                                    self.funds_log.insert(
                                        tk.END,
                                        f"❌ Repay elutasítva {c} {a:.8f}: code={code} msg='{msg}'\n"
                                    )
                            else:
                                # nem dict válasz – best-effort log
                                self.funds_log.insert(
                                    tk.END,
                                    f"✅ Repay elküldve (nem standard válasz): {c} {a:.8f}\n"
                                )

                            self.funds_log.see(tk.END)

                        self.root.after(0, _log_repay)

                    except Exception as e:
                        self.root.after(0, lambda c=ccy, e=e: (
                            self.funds_log.insert(tk.END, f"❌ Repay hiba {c}: {e}\n"),
                            self.funds_log.see(tk.END)
                        ))

                # 4) Sikeres kör után frissítjük az összes egyenleget is (Funds táblázat + cache)
                self.root.after(0, self.refresh_all_funds_balances)

            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("Repay hiba", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    # --- Thread-safe logoló segéd ---
    def _safe_log(self, text: str):
        try:
            self.root.after(0, lambda: (self.mb_log.insert(tk.END, text), self.mb_log.see(tk.END)))
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
            import time
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
                iid = self._mb_hist_tv.insert("", "end", values=row)
                if oid != "-":
                    self._mb_hist_rows_by_oid[oid] = iid
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
        """
        try:
            if not order_id:
                return
            iid = self._mb_hist_rows_by_oid.get(order_id)
            if not iid:
                return

            vals = list(self._mb_hist_tv.item(iid, "values"))
            col = getattr(self, "_mb_hist_col_index", None)
            if not col:
                # Fallback: klasszikus indexek (Timestamp,Side,Entry,Exit,Size,Leverage,Fee,PnL,orderId)
                EXIT_IDX, FEE_IDX, PNL_IDX = 3, 6, 7
            else:
                EXIT_IDX = col.get("exit", 3); FEE_IDX = col.get("fee", 6); PNL_IDX = col.get("pnl", 7)

            vals[EXIT_IDX] = f"{float(exit_px):.6f}"
            if fee_total is not None:
                vals[FEE_IDX] = f"{float(fee_total):.6f}"
            if pnl_final is not None:
                vals[PNL_IDX] = f"{float(pnl_final):.6f}"

            def _upd():
                self._mb_hist_tv.item(iid, values=tuple(vals))
            self.root.after(0, _upd)
        except Exception:
            pass

    def _mb_hist_start_pnl_loop(self):
        if getattr(self, "_mb_hist_pnl_job", None):
            return
        self._mb_hist_pnl_inflight = False
        self._mb_hist_pnl_tick()

    def _mb_hist_pnl_tick(self):
        try:
            if getattr(self, "_mb_hist_pnl_inflight", False):
                return
            self._mb_hist_pnl_inflight = True

            try:
                symbol = normalize_symbol(
                    self._mb_get_str("mb_symbol", self._mb_get_str("mt_symbol", DEFAULT_SYMBOL))
                )
            except Exception:
                symbol = None

            def fetch_rt():
                """Utolsó ár a history PnL-hez – egységes helperrel:
                get_best_price: WS → cache → REST.
                """
                if not symbol:
                    return None
                try:
                    rt = float(self.get_best_price(symbol))
                    if (not self._is_pos_num(rt)) or rt <= 0:
                        return None
                    return rt
                except Exception:
                    return None

            def apply(rt):
                self._mb_hist_pnl_inflight = False
                if not rt or rt <= 0:
                    return

                col = getattr(self, "_mb_hist_col_index", {})
                ENTRY_IDX = col.get("entry", 2); EXIT_IDX = col.get("exit", 3)
                SIZE_IDX  = col.get("size", 4);  SIDE_IDX = col.get("side", 1)
                FEE_IDX   = col.get("fee", 6);   PNL_IDX  = col.get("pnl", 7)

                for iid in self._mb_hist_tv.get_children(""):
                    vals = list(self._mb_hist_tv.item(iid, "values"))
                    try:
                        # zárt pozícióra nem számolunk floating PnL-t
                        if vals[EXIT_IDX]:
                            continue

                        entry = float(vals[ENTRY_IDX] or "0")
                        size  = float(vals[SIZE_IDX]  or "0")
                        side  = str(vals[SIDE_IDX]).strip().upper()
                        fee_s = (vals[FEE_IDX] or "").strip()
                        fee_est = float(fee_s) if fee_s not in ("", None) else 0.0

                        gross = (rt - entry) * size * (1 if side == "BUY" else -1)
                        vals[PNL_IDX] = f"{(gross - fee_est):.6f}"
                        self._mb_hist_tv.item(iid, values=tuple(vals))
                    except Exception:
                        continue

            def fail(_e):
                self._mb_hist_pnl_inflight = False

            self._bg(fetch_rt, apply, fail)
        finally:
            # 5 mp múlva újrafrissítjük a floating PnL-t
            self._mb_hist_pnl_job = self.root.after(5000, self._mb_hist_pnl_tick)

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

        import tkinter as tk

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
        from tkinter import messagebox

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
        from tkinter import messagebox

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
            lot_step, price_step, min_base, min_funds, quote_step = self._mb_get_market_steps(symbol)
        except Exception:
            lot_step = price_step = None
            min_base = min_funds = None
            quote_step = 0.01

        # --- Locale-safe Decimal padlózás helper ---
        def _floor_dec(x: float, step: float) -> float:
            if not step or step <= 0:
                return float(x)
            from decimal import Decimal
            q = Decimal(str(step))
            return float((Decimal(str(x)) // q) * q)

        def _ceil_dec(x: float, step: float) -> float:
            if not step or step <= 0:
                return float(x)
            from decimal import Decimal, ROUND_CEILING
            q = Decimal(str(step))
            return float((Decimal(str(x)).quantize(q, rounding=ROUND_CEILING)))

        sb = size_base
        fq = funds_quote

        safety = 1.0
        try:
            import os
            safety = float(os.getenv("MB_CLOSE_FUNDS_SAFETY", "1.015"))  # +1.5% alapértelmezett ráhagyás
            if safety < 1.0:
                safety = 1.0
        except Exception:
            safety = 1.015
 
        # --- BUY oldali speciális ág: ha nincs funds, de van size és ár → size→funds konverzió záráshoz ---
        #     Cél: Market BUY-hoz a tőzsde funds-ot vár; a worker és a live close size-ot ad át → itt alakítjuk át.
        if side == "buy" and fq is None and sb is not None and price and price > 0:
            try:
                # 1) a size-et előbb lot_step-re padlózzuk
                if lot_step:
                    sb = _floor_dec(float(sb), float(lot_step))
                if sb is not None and sb > 0:
                    # 2) funds becslés: size * price * safety, quote_step-re felfelé kerekítve
                    est_f = float(sb) * float(price) * float(safety)
                    fq = _ceil_dec(est_f, float(quote_step or 0.0))
                    # 3) minFunds guard
                    if min_funds and fq < float(min_funds):
                        fq = None
                    # 4) minBase guard visszaellenőrzéssel: (floor(fq/price, lot_step) >= min_base)
                    if fq is not None and lot_step and price and price > 0 and min_base:
                        est_size = _floor_dec(float(fq) / float(price), float(lot_step))
                        if float(est_size) < float(min_base):
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
                    sb = _floor_dec(float(sb), float(lot_step))
                sb = float(sb)
            except Exception:
                sb = None

            # minBase guard – nem emelünk fel, ha alatta van → eldob
            try:
                if sb is None or sb <= 0:
                    sb = None
                elif min_base and float(sb) < float(min_base):
                    sb = None
            except Exception:
                sb = None

        # --- FUNDS (QUOTE) tisztítás (BUY oldali küldéshez) ---
        if fq is not None:
            try:
                fq = float(fq)
                if fq <= 0:
                    fq = None
                else:
                    # exchange szerinti quote_step-re padlózás (nem fix 0.01!)
                    fq = _floor_dec(fq, float(quote_step))
                    # minFunds guard – ha alatta, eldob
                    if min_funds and fq < float(min_funds):
                        fq = None
                    # minBase guard a funds→méret becslésével (ha van ár)
                    if fq is not None and price and price > 0 and lot_step:
                        est_size = _floor_dec(fq / float(price), float(lot_step))
                        if min_base and est_size < float(min_base):
                            fq = None
            except Exception:
                fq = None

        # Ha mindkettő None → nem küldhető
        if sb is None and fq is None:
            return None, None
        return sb, fq

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

        # --- Reset minden futás előtt ---
        self._sim_pos_long = []
        self._sim_pos_short = []
        self._sim_history = []
        self._sim_pnl_usdt = 0.0

        # --- Hard reset minden run előtt (különösen pool és bar state) ---
        # töröljük, hogy a worker ÚJRA építse a keretet
        try:
            delattr(self, "_pool_balance_quote")
        except Exception:
            pass
        try:
            delattr(self, "_pool_used_quote")
        except Exception:
            pass

        # azonnali aktivitás – ne szűrje ki "ugyanaz a gyertya"
        self._mb_last_bar_ts = {}
        # opcionális cache-ek nullázása (ha korábban be lettek vezetve)
        self._mb_last_rt_px = {} if hasattr(self, "_mb_last_rt_px") else {}

        # belső állapotok, ha hiányoznának
        if not hasattr(self, "_sim_pnl_usdt"):
            self._sim_pnl_usdt = 0.0
        if not hasattr(self, "_sim_pos_long"):
            self._sim_pos_long = []
        if not hasattr(self, "_sim_pos_short"):
            self._sim_pos_short = []
        if not hasattr(self, "_mb_last_bar_ts"):
            self._mb_last_bar_ts = {}   # {(symbol, tf): ts}
        if not hasattr(self, "_mb_last_cross_ts"):
            self._mb_last_cross_ts = 0
        if not hasattr(self, "_mb_last_signal"):
            self._mb_last_signal = "hold"
        if not hasattr(self, "_mb_lock"):
            self._mb_lock = threading.Lock()

        # --- CFG SNAPSHOT: minden UI-olvasás itt, FŐ SZÁLBAN! ---
        try:
            self._mb_cfg = self._mb_build_cfg()
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
            import time as _t
            _t.sleep(0.1)
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

            if idx < 0 or idx >= len(lst):
                return

            # Ha a hívó adott konkrét pos_obj-ot, ellenőrizzük, hogy még mindig ugyanaz ül-e ott.
            pos = lst[idx]
            if pos_obj is not None and pos is not pos_obj:
                # Próbáljuk megkeresni identity alapján
                real_idx = None
                for j, p in enumerate(lst):
                    if p is pos_obj:
                        real_idx = j
                        break
                if real_idx is None:
                    # már kikerült a listából → nincs teendő
                    return
                idx = real_idx
                pos = lst[idx]

            entry = float(pos.get('entry', 0.0))
            sz    = float(pos.get('size', 0.0))

            gross = (exit_px - entry) * sz * (1 if side == 'buy' else -1)

            fee_rate = self._mb_get_taker_fee()
            f_open, f_close, f_total = self._mb_sum_fee_actual_or_est(pos, exit_px, fee_rate)

            pnl = gross - f_total

            # pool + összesített PnL frissítése
            self._sim_pnl_usdt       += pnl
            self._pool_balance_quote += pnl
            self._pool_used_quote    -= (float(pos.get('commit_usdt', 0.0)) +
                                         float(pos.get('fee_reserved', 0.0)))
            self._pool_used_quote     = max(0.0, self._pool_used_quote)

            total_pnl    = float(self._sim_pnl_usdt)
            pool_used    = float(self._pool_used_quote)
            pool_balance = float(self._pool_balance_quote)

            try:
                symbol_safe = normalize_symbol(
                    self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL))
                )
            except Exception:
                symbol_safe = "UNKNOWN"

            try:
                import time as _t
                self._sim_history.append({
                    "partial": False,
                    "symbol": symbol_safe,
                    "side": side,
                    "entry": float(entry),
                    "exit": float(exit_px),
                    "size_closed": float(sz),
                    "pnl": float(pnl),
                    "ts": _t.time(),
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

        # --- lockon kívül: log + history exit update (itt már nem piszkáljuk a sim listát) ---
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

        import time
        from typing import Optional, Literal

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

            closing_a_short = (close_side == "buy")

            _payload_dbg = {
                "mode": mode,
                "symbol": symbol,
                "side": close_side,
                "size_base": size_to_send,
                "funds_quote": funds_to_send,
                "leverage": lev,
                "auto_borrow": closing_a_short,
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
                        auto_borrow=closing_a_short,
                        auto_repay=True
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
            last_rt = float((getattr(self, "_mb_last_rt_px", {}) or {}).get(sym, 0.0))
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
        import time, math, pandas as pd, threading

        # --- egyszeri init-ek (ha még nem léteznek) ---
        if not hasattr(self, "_sim_pos_long"):   self._sim_pos_long = []   # list[dict]
        if not hasattr(self, "_sim_pos_short"):  self._sim_pos_short = []  # list[dict]
        if not hasattr(self, "_sim_pnl_usdt"):   self._sim_pnl_usdt = 0.0
        if not hasattr(self, "_sim_history"):    self._sim_history = []
        if not hasattr(self, "_mb_last_bar_ts"): self._mb_last_bar_ts = {}
        if not hasattr(self, "_mb_last_cross_ts"): self._mb_last_cross_ts = 0
        if not hasattr(self, "_mb_last_signal"):   self._mb_last_signal   = "hold"
        if not hasattr(self, "_mb_last_rt_px"):   self._mb_last_rt_px = {}

        # Dinamikus keret (pool) – induláskor felépítjük
        if not hasattr(self, "_pool_balance_quote") or not hasattr(self, "_pool_used_quote"):
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
                self._pool_balance_quote = float(init_pool)
                self._pool_used_quote = 0.0
            self._safe_log(f"🏦 Pool init: balance={self._pool_balance_quote:.2f} {quote0}, used={self._pool_used_quote:.2f}\n")

        # --- belső helperek: lista oldalszerint, nyitás/zárás multi, menedzsment per-pozíció ---
        def _pos_list(side: str):
            return self._sim_pos_long if side == "buy" else self._sim_pos_short

        def _open_sim(side: str, entry_px: float, size_base: float, commit_usdt: float,
                      atr_pack=None, fixed_pack=None, **extra):
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
                'mgmt': 'none'
            }
            pos.update({k: v for k, v in (extra or {}).items()})
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
                self._pool_used_quote += float(commit_usdt) + float(fee_reserved)

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

            # symbol widget helyett cfg-ből
            try:
                cfg_sym = getattr(self, "_mb_cfg", {}) or {}
                symbol_safe = cfg_sym.get("symbol", DEFAULT_SYMBOL)
            except Exception:
                symbol_safe = None

            try:
                lot_step, _price_step, _min_base, _min_funds, _quote_step = self._mb_get_market_steps(
                    normalize_symbol(symbol_safe or "BTC-USDT")
                )
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
                self._sim_pnl_usdt += pnl
                self._pool_balance_quote += pnl

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
                import time as _t
                try:
                    cfg_sym = getattr(self, "_mb_cfg", {}) or {}
                    symbol_safe = normalize_symbol(cfg_sym.get("symbol", DEFAULT_SYMBOL))
                except Exception:
                    symbol_safe = "UNKNOWN"

                self._sim_history.append({
                    "partial": True,
                    "symbol": symbol_safe,
                    "side": side,
                    "entry": float(entry),
                    "exit": float(px),
                    "size_closed": float(close_sz),
                    "pnl": float(pnl),
                    "ts": _t.time(),
                })
            except Exception:
                pass

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
            sz    = float(pos['size'])
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

        try:
            while self._mb_running:
                try:
                    # --- CFG beállítások beolvasása (NEM widget!) ---
                    cfg = getattr(self, "_mb_cfg", {}) or {}

                    symbol = normalize_symbol(cfg.get("symbol", DEFAULT_SYMBOL))
                    tf     = cfg.get("tf", "1m")
                    fa     = int(cfg.get("ma_fast", 9))
                    slw    = int(cfg.get("ma_slow", 21))
                    sizep  = float(cfg.get("size_pct", 50.0))
                    inpm   = cfg.get("input_mode", "quote")
                    mode   = cfg.get("mode", "isolated")
                    lev    = int(cfg.get("leverage", 10))
                    tpct   = float(cfg.get("tp_pct", 2.0))
                    spct   = float(cfg.get("sl_pct", 1.0))
                    trpct  = float(cfg.get("trail_pct", 0.5))
                    cd_s   = int(cfg.get("cooldown_s", 30))
                    dry    = bool(cfg.get("dry", True))
                    budget_ui = float(cfg.get("budget_ui", 0.0))

                    # RSI / HTF / ATR / FIX / BRK
                    use_rsi  = bool(cfg.get("use_rsi", False))
                    rsi_len  = int(cfg.get("rsi_len", 14))
                    rsi_bmin = float(cfg.get("rsi_bmin", 45.0))
                    rsi_bmax = float(cfg.get("rsi_bmax", 70.0))
                    rsi_smin = float(cfg.get("rsi_smin", 30.0))
                    rsi_smax = float(cfg.get("rsi_smax", 55.0))

                    use_htf = bool(cfg.get("use_htf", False))
                    htf_tf  = cfg.get("htf_tf", "1h")

                    use_atr = bool(cfg.get("use_atr", False))
                    atr_n   = int(cfg.get("atr_n", 14))
                    mul_sl  = float(cfg.get("atr_mul_sl", 1.2))
                    mul_tp1 = float(cfg.get("atr_mul_tp1", 1.5))
                    mul_tp2 = float(cfg.get("atr_mul_tp2", 2.5))
                    mul_tr  = float(cfg.get("atr_mul_tr", 0.9))

                    use_fixed = bool(cfg.get("use_fixed", False))

                    use_brk   = bool(cfg.get("use_brk", False))
                    brk_n     = int(cfg.get("brk_n", 20))
                    brk_buf   = float(cfg.get("brk_buf", 0.05))
                    brk_with_trend = bool(cfg.get("brk_with_trend", True))

                    if use_fixed and use_atr:
                        use_fixed = False

                    use_live       = bool(cfg.get("use_live", True))
                    live_shock_pct = float(cfg.get("live_shock_pct", 1.0))
                    live_shock_atr = float(cfg.get("live_shock_atr", 1.2))
                    drift_max_ui   = float(cfg.get("drift_max_pct", 0.0))
                    max_open       = int(cfg.get("max_open", 0))
                    pause_new      = bool(cfg.get("pause_new", False))
                    auto_borrow    = bool(cfg.get("auto_borrow", False))
                    invert_ema     = bool(cfg.get("invert_ema", False))
                    ema_hyst_pct   = float(cfg.get("ema_hyst_pct", 1.0))

                    # --- Privát order WS biztosítása (KuCoin) ---
                    try:
                        self._ensure_order_ws()
                    except Exception:
                        pass

                    # --- OHLCV frissítés csak ha új candle jött ---  ### WS-REST-OPT
                    now_ts = int(time.time())

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
                        if now_ts - prev_ts >= tf_sec:
                            need_refresh = True

                    if need_refresh or not hasattr(self, "_mb_last_df"):
                        with self._ex_lock:
                            ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=200)
                        if not ohlcv:
                            self._safe_log("⚠️ Nincs candle adat.\n")
                            time.sleep(2)
                            continue

                        df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
                        last_ts = int(df['ts'].iloc[-1])
                        self._mb_last_bar_ts[key] = last_ts
                        # fontos: itt MÉG nem cache-eljük self._mb_last_df-et,
                        # előbb ráengedjük a realtime (WS) árat a legutóbbi gyertyára
                    else:
                        df = self._mb_last_df.copy()
                        last_ts = int(df["ts"].iloc[-1])

                    closes = df['c'].astype(float).tolist()
                    last_px = float(closes[-1])

                    # valós idejű (ticker) ár – default a candle close
                    last_px_rt = last_px
                    if not self._is_pos_num(last_px) or not self._is_pos_num(last_px_rt):
                        self._safe_log("⚠️ Érvénytelen ár (0/NaN) – ciklus kihagyva.\n")
                        time.sleep(2)
                        continue

                    used_ws_price = False  # ### WS-FLAG: jelezzük, ha a last_px_rt tényleg websocketből jött

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

                    # --- Élő high/low/close frissítés a legutóbbi gyertyára WS alapján ---  ### WS-HIGH/LOW
                    # Ez MINDEN ciklusban lefut: akár volt REST refresh, akár nem.
                    # Így az indikátorok (EMA/RSI/ATR/BRK) mindig a WS-sel frissített utolsó gyertyára számolódnak.
                    try:
                        if self._is_pos_num(last_px_rt) and last_px_rt > 0:
                            idx_last = df.index[-1]
                            h_last = float(df.loc[idx_last, 'h'])
                            l_last = float(df.loc[idx_last, 'l'])
                            if last_px_rt > h_last:
                                df.loc[idx_last, 'h'] = last_px_rt
                            if last_px_rt < l_last:
                                df.loc[idx_last, 'l'] = last_px_rt
                            # close is menjen a legutolsó tickre
                            df.loc[idx_last, 'c'] = last_px_rt

                        # cache frissítése, hogy a következő körben is a WS-sel módosított df-et kapjuk
                        self._mb_last_df = df.copy()
                    except Exception:
                        pass

                    # --- cache-eljük a realtime árakat más funkcióknak is (manual close / PnL / history) ---
                    try:
                        if self._is_pos_num(last_px_rt) and last_px_rt > 0:
                            if not hasattr(self, "_mb_last_rt_px"):
                                self._mb_last_rt_px = {}
                            self._mb_last_rt_px[symbol] = float(last_px_rt)
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

                    open_now = len(self._sim_pos_long) + len(self._sim_pos_short)

                    atr_val = None
                    if use_atr:
                        atr_series = self._mb_atr(df, n=atr_n)
                        atr_val = float(atr_series.iloc[-1])
                        self._mb_last_atr_val = atr_val 

                    closes_for_sig = df['c'].astype(float).tolist()
                    # hiszterézis mult kivonva cfg-ből → nincs Tk az _mb_signal_from_ema_live-ben
                    atr_eps_mult = max(0.0, ema_hyst_pct) / 100.0
                    sig_raw, ef_l, es_l = self._mb_signal_from_ema_live(
                        closes_for_sig, fa, slw, last_px_rt=None,
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
                        rsi_series = self._mb_rsi(df['c'], n=rsi_len)
                        rsi_val = float(rsi_series.iloc[-1])
                        if sig == 'buy':
                            if not (rsi_bmin <= rsi_val <= rsi_bmax):
                                sig = 'hold'
                        elif sig == 'sell':
                            if not (rsi_smin <= rsi_val <= rsi_smax):
                                sig = 'hold'

                    brk_sig, hh, ll, up_lvl, dn_lvl = ("hold", float("nan"), float("nan"), float("nan"), float("nan"))
                    if use_brk:
                        # _mb_breakout_signal már az élő high/low-val módosított df-et látja  ### WS-HIGH/LOW
                        brk_sig, hh, ll, up_lvl, dn_lvl = self._mb_breakout_signal(df, brk_n, brk_buf)
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

                    combined_sig = brk_sig if brk_sig in ('buy', 'sell') else sig

                    try:
                        now_ts = int(time.time())
                    except Exception:
                        now_ts = 0
                    cd_left = 0
                    try:
                        cd_left = max(0, cd_s - (now_ts - self._mb_last_cross_ts))
                    except Exception:
                        pass

                    filters_line = (
                        f"filters: rsi={'ON' if use_rsi else 'OFF'}"
                        + (f"[buy:{rsi_bmin:.1f}-{rsi_bmax:.1f} sell:{rsi_smin:.1f}-{rsi_smax:.1f}]" if use_rsi else "")
                        + f", htf={'ON' if use_htf else 'OFF'}({trend_htf:+d})"
                        + f", brk={'ON' if use_brk else 'OFF'}"
                        + f", live_px={'ON' if use_live else 'OFF'}"
                        + f", cd_left={cd_left}s"
                    )

                    ema_up = (ef_l > es_l)
                    ema_dn = (ef_l < es_l)
                    rsi_ok_buy = True
                    rsi_ok_sell = True
                    if use_rsi and rsi_val is not None:
                        rsi_ok_buy  = (rsi_bmin <= rsi_val <= rsi_bmax)
                        rsi_ok_sell = (rsi_smin <= rsi_val <= rsi_smax)

                    drift_ok = True
                    drift_over_txt = None
                    try:
                        if drift_max_ui > 0 and drift_pct == drift_pct:
                            drift_ok = (abs(drift_pct) <= drift_max_ui)
                            if not drift_ok:
                                drift_over_txt = f"drift>{drift_max_ui:.2f}%"
                    except Exception:
                        pass

                    cd_ok = True
                    try:
                        now_ts = int(time.time())
                        cd_ok = (now_ts - self._mb_last_cross_ts) >= cd_s
                    except Exception:
                        pass

                    htf_block = (use_htf and sig_raw in ('buy','sell') and (sig == 'hold'))

                    reasons = []
                    if not (ema_up or ema_dn):
                        reasons.append("no_ema_trend")
                    if not cd_ok:
                        reasons.append("cooldown")
                    if drift_over_txt and not drift_ok:
                        reasons.append(drift_over_txt)
                    if ema_up and not rsi_ok_buy:
                        reasons.append("rsi_block_buy")
                    if ema_dn and not rsi_ok_sell:
                        reasons.append("rsi_block_sell")
                    if htf_block:
                        reasons.append("htf_block")

                    log_line = (
                        f"[{symbol} {tf}] Élő ár={last_px_rt:.6f} Gyertya ár={last_px:.6f} "
                        f"EMA({fa})={ef_l:.4f}/EMA({slw})={es_l:.4f}"
                    )
                    if use_htf:
                        log_line += f" HTF={trend_htf:+d}"
                    if use_rsi and rsi_val is not None:
                        log_line += f" RSI({rsi_len})={rsi_val:.2f}"
                    if use_brk and not (math.isnan(hh) or math.isnan(ll)):
                        log_line += f" BRK[{brk_n}] HH={hh:.4f} LL={ll:.4f} ↑{up_lvl:.4f} ↓{dn_lvl:.4f}"
                    if drift_pct == drift_pct:
                        log_line += f" drift={drift_pct:.2f}%"
                    log_line += f" | POOL used/bal={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}"
                    log_line += f" | OPEN={open_now}/{('∞' if max_open==0 else max_open)}"

                    # Naplózás ritkítása: csak akkor írunk, ha eltelt néhány másodperc,
                    # vagy új BUY/SELL jel érkezett.
                    should_log = True
                    try:
                        now_ts_log = int(time.time())
                        last_ts_log = getattr(self, "_mb_last_status_log_ts", 0)
                        if combined_sig not in ("buy", "sell") and (now_ts_log - last_ts_log) < 3:
                            should_log = False
                        else:
                            self._mb_last_status_log_ts = now_ts_log
                    except Exception:
                        should_log = True

                    if should_log:
                        self._safe_log(log_line.rstrip() + f"  → {combined_sig} | {filters_line}\n")
                        if combined_sig in (None, "", "hold") and reasons:
                            self._safe_log("  ↳ hold reasons: " + ",".join(reasons) + "\n")

                    # BUY-ok kezelése – snapshot + lock-olt módosítás, hogy elkerüljük a race condition-t
                    with self._mb_lock:
                        long_positions_snapshot = list(self._sim_pos_long)

                    for pos in long_positions_snapshot:
                        try:
                            # ha közben (GUI-ból) már törölték ezt a pozíciót, ugorjunk
                            with self._mb_lock:
                                if pos not in self._sim_pos_long:
                                    continue

                            need_close = False
                            close_reason = "mgmt_auto"

                            if pos.get('mgmt') == 'atr' and atr_val is not None:
                                need_close = _manage_atr_on_pos(pos, px_for_mgmt, atr_val)
                            elif pos.get('mgmt') == 'fixed':
                                need_close = _manage_fixed_on_pos(pos, px_for_mgmt)

                            if need_close:
                                if dry:
                                    # SIM zárás – csak akkor, ha a pozíció még benne van a listában
                                    try:
                                        with self._mb_lock:
                                            try:
                                                idx = self._sim_pos_long.index(pos)
                                            except ValueError:
                                                idx = -1
                                        if idx >= 0:
                                            self._close_sim_by_index('buy', idx, px_for_mgmt, reason=close_reason, pos_obj=pos)
                                    except Exception as e:
                                        self._safe_log(f"❌ SIM long zárás hiba: {e}\n")
                                        continue
                                else:
                                    # LIVE zárás – API/egyéb hiba itt is lokálisan kezelt
                                    ok = False
                                    try:
                                        ok = self._live_close_pos(
                                            'buy', pos, px_for_mgmt,
                                            symbol=symbol, mode=mode, lev=lev
                                        )
                                    except Exception as e:
                                        self._safe_log(f"❌ LIVE long zárás hiba: {e}\n")
                                        ok = False

                                    if ok:
                                        # csak sikeres LIVE zárás után tükörzárunk SIM-ben,
                                        # de előbb ellenőrizzük, hogy a pozíció még létezik-e
                                        try:
                                            with self._mb_lock:
                                                try:
                                                    idx = self._sim_pos_long.index(pos)
                                                except ValueError:
                                                    idx = -1
                                            if idx >= 0:
                                                self._close_sim_by_index('buy', idx, px_for_mgmt, reason=close_reason, pos_obj=pos)
                                        except Exception as e:
                                            self._safe_log(f"❌ SIM tükrözés hiba (long): {e}\n")
                                            continue
                                    else:
                                        self._safe_log(
                                            "❗ LIVE zárás sikertelen – a long pozíció nyitva marad.\n"
                                        )
                                        continue

                        except Exception as e:
                            # bármilyen más hiba a menedzsmentben – ne dőljön el a teljes worker
                            self._safe_log(f"❌ Long pozíció menedzsment hiba: {e}\n")
                            continue

                    # SELL-ek kezelése – snapshot + lock-olt módosítás, hogy elkerüljük a race condition-t
                    with self._mb_lock:
                        short_positions_snapshot = list(self._sim_pos_short)

                    for pos in short_positions_snapshot:
                        try:
                            # ha közben (GUI-ból) már törölték ezt a pozíciót, ugorjunk
                            with self._mb_lock:
                                if pos not in self._sim_pos_short:
                                    continue

                            need_close = False
                            close_reason = "mgmt_auto"

                            if pos.get('mgmt') == 'atr' and atr_val is not None:
                                need_close = _manage_atr_on_pos(pos, px_for_mgmt, atr_val)
                            elif pos.get('mgmt') == 'fixed':
                                need_close = _manage_fixed_on_pos(pos, px_for_mgmt)

                            if need_close:
                                if dry:
                                    # SIM zárás – csak akkor, ha a pozíció még benne van a listában
                                    try:
                                        with self._mb_lock:
                                            try:
                                                idx = self._sim_pos_short.index(pos)
                                            except ValueError:
                                                idx = -1
                                        if idx >= 0:
                                            self._close_sim_by_index('sell', idx, px_for_mgmt, reason=close_reason, pos_obj=pos)
                                    except Exception as e:
                                        self._safe_log(f"❌ SIM short zárás hiba: {e}\n")
                                        continue
                                else:
                                    ok = False
                                    try:
                                        ok = self._live_close_pos(
                                            'sell', pos, px_for_mgmt,
                                            symbol=symbol, mode=mode, lev=lev
                                        )
                                    except Exception as e:
                                        self._safe_log(f"❌ LIVE short zárás hiba: {e}\n")
                                        ok = False

                                    if ok:
                                        try:
                                            with self._mb_lock:
                                                try:
                                                    idx = self._sim_pos_short.index(pos)
                                                except ValueError:
                                                    idx = -1
                                            if idx >= 0:
                                                self._close_sim_by_index('sell', idx, px_for_mgmt, reason=close_reason, pos_obj=pos)
                                        except Exception as e:
                                            self._safe_log(f"❌ SIM tükrözés hiba (short): {e}\n")
                                            continue
                                    else:
                                        self._safe_log(
                                            "❗ LIVE zárás sikertelen – a short pozíció nyitva marad.\n"
                                        )
                                        continue

                        except Exception as e:
                            self._safe_log(f"❌ Short pozíció menedzsment hiba: {e}\n")
                            continue

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

                        # friss ticker: WS az első, REST csak ha nincs használható WS ár  ### WS-OPEN
                        if (not self._is_pos_num(last_px_rt)) or last_px_rt <= 0:
                            try:
                                rt = float(self.get_best_price(symbol))
                                if self._is_pos_num(rt) and rt > 0:
                                    last_px_rt = rt
                            except Exception:
                                pass

                        free_pool = max(0.0, self._pool_balance_quote - self._pool_used_quote)
                        sizep_to_use = max(0.0, min(100.0, float(sizep)))

                        size = None
                        funds = None
                        open_size = 0.0
                        commit_usdt = 0.0
                        nominal_q = 0.0

                        max_quote_for_trade = free_pool * (sizep_to_use / 100.0)

                        if max_quote_for_trade <= 0.0:
                            self._safe_log("ℹ️ Nincs szabad pool a nyitáshoz (keret limit). Kimarad.\n")
                        else:
                            if inpm == "quote":
                                _lot_step, _price_step, _, _, _ = self._mb_get_market_steps(symbol)
                                ord = self._mb_calc_order_qty(
                                    side=combined_sig,
                                    price=last_px_rt,
                                    pool_free=free_pool,
                                    size_pct=sizep_to_use,
                                    leverage=lev,
                                    mode="quote",
                                    lot_step=_lot_step,
                                    price_step=_price_step
                                )
                                open_size   = float(ord["qty_base"])
                                commit_usdt = float(ord["commit_quote"])
                                nominal_q   = float(ord["nominal_quote"])
                                size  = None
                                funds = commit_usdt
                            else:
                                size, funds = self._mb_compute_size(
                                    symbol, combined_sig, last_px_rt, sizep_to_use, inpm, mode, lev,
                                    budget_quote=max_quote_for_trade,
                                    dry=dry,
                                    auto_borrow=auto_borrow,
                                )
                                if funds is not None and funds > 0:
                                    commit_usdt = float(funds)
                                    nominal_q   = commit_usdt * max(1, lev)
                                    open_size   = nominal_q / max(last_px_rt, 1e-12)
                                elif size is not None and size > 0:
                                    open_size   = float(size)
                                    nominal_q   = open_size * last_px_rt
                                    commit_usdt = nominal_q / max(1, lev)
                                else:
                                    open_size = 0.0; commit_usdt = 0.0; nominal_q = 0.0

                            lot_step, price_step, min_base, min_funds, quote_step = self._mb_get_market_steps(symbol)
                            open_size = self._mb_floor_to_step_dec(open_size, lot_step)

                            self._safe_log(
                                f"📈 Jel: {combined_sig.upper()} | px={last_px_rt:.6f} | size%={sizep_to_use:.2f} | "
                                f"nominal={nominal_q:.2f} | commit={commit_usdt:.2f} | free_pool={free_pool:.2f} | "
                                f"lev={lev} | mode={mode} dry={dry}\n"
                            )

                            opened = False
                            if commit_usdt <= 0 or (combined_sig == 'sell' and open_size <= 0):
                                self._safe_log("ℹ️ Nulla méret / nincs keret – nincs nyitás.\n")
                            else:
                                if dry:
                                    size_to_send = None
                                    funds_to_send = None
                                    if combined_sig == 'buy':
                                        pre_funds_nominal = float(nominal_q)
                                        _sb, _fq = self._mb_sanitize_order(
                                            symbol=symbol, side='buy',
                                            price=last_px_rt,
                                            size_base=None,
                                            funds_quote=pre_funds_nominal
                                        )
                                        funds_to_send = _fq
                                        if not funds_to_send:
                                            self._safe_log("ℹ️ SIM BUY eldobva (sanitizer funds/minFunds/quote_step miatt).\n")
                                        else:
                                            size_to_send = self._mb_floor_to_step_dec(
                                                float(funds_to_send) / max(last_px_rt, 1e-12), float(lot_step or 0.0)
                                            )
                                            if min_base and size_to_send < float(min_base):
                                                self._safe_log("ℹ️ SIM BUY eldobva (méret < minBase a padlózás után).\n")
                                                size_to_send = None
                                    else:
                                        _sb, _fq = self._mb_sanitize_order(
                                            symbol=symbol, side='sell',
                                            price=last_px_rt,
                                            size_base=float(open_size),
                                            funds_quote=None
                                        )
                                        size_to_send = _sb
                                        if not size_to_send:
                                            self._safe_log("ℹ️ SIM SELL eldobva (sanitizer size/minBase/lot_step miatt).\n")

                                    if (combined_sig == 'buy' and funds_to_send) or (combined_sig == 'sell' and size_to_send):
                                        if combined_sig == 'buy':
                                            commit_sim = float(funds_to_send) / max(lev, 1)
                                            sz_sim = float(size_to_send)
                                        else:
                                            sz_sim = float(size_to_send)
                                            commit_sim = (sz_sim * float(last_px_rt)) / max(lev, 1)

                                        if use_atr and atr_val is not None:
                                            atr_pack = (mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val)
                                            _open_sim(combined_sig, last_px_rt, sz_sim, commit_sim, atr_pack=atr_pack)
                                        elif use_fixed:
                                            fixed_pack = (tpct, spct, trpct)
                                            _open_sim(combined_sig, last_px_rt, sz_sim, commit_sim, fixed_pack=fixed_pack)
                                        else:
                                            _open_sim(combined_sig, last_px_rt, sz_sim, commit_sim)
                                        opened = True
                                else:
                                    try:
                                        size_to_send = None
                                        funds_to_send = None

                                        if combined_sig == 'buy':
                                            _pre_funds = nominal_q
                                            _sb, _fq = self._mb_sanitize_order(
                                                symbol=symbol, side='buy',
                                                price=last_px_rt,
                                                size_base=None,
                                                funds_quote=_pre_funds
                                            )
                                            size_to_send, funds_to_send = _sb, _fq
                                        else:
                                            _pre_size = open_size
                                            _sb, _fq = self._mb_sanitize_order(
                                                symbol=symbol, side='sell',
                                                price=last_px_rt,
                                                size_base=_pre_size,
                                                funds_quote=None
                                            )
                                            size_to_send, funds_to_send = _sb, _fq

                                        if (combined_sig == 'buy' and not funds_to_send) or (combined_sig == 'sell' and not size_to_send):
                                            self._safe_log("ℹ️ Sanitizer eldobta a nyitást (min/step) – kihagyva.\n")
                                            opened = False
                                            continue
                                        else:
                                            _payload_dbg = {
                                                "mode": mode, "symbol": symbol, "side": combined_sig,
                                                "size_base": size_to_send, "funds_quote": funds_to_send,
                                                "leverage": lev, "auto_borrow": auto_borrow,
                                            }
                                            self._safe_log(f"🐞 SEND OPEN: {self._mb_pp(_payload_dbg)}\n")
                                            with self._ex_lock:
                                                resp = self.exchange.place_margin_market_order(
                                                    mode, symbol, combined_sig,
                                                    size_base=size_to_send,
                                                    funds_quote=funds_to_send,
                                                    leverage=lev,
                                                    auto_borrow=auto_borrow
                                                )

                                        self._safe_log(f"🐞 RECV OPEN: {self._mb_pp(resp)}\n")
                                        code = None
                                        data = None
                                        if isinstance(resp, dict):
                                            code = resp.get("code")
                                            data = resp.get("data") or {}
                                        elif hasattr(resp, "code"):
                                            code = getattr(resp, "code", None)
                                            data = getattr(resp, "data", None)

                                        oid = cid = None
                                        if isinstance(data, dict):
                                            oid = data.get("orderId") or data.get("id") or data.get("orderid")
                                            cid = data.get("clientOid") or data.get("clientOrderId")

                                        if code and str(code) != "200000":
                                            self._safe_log(f"❌ LIVE order elutasítva (code={code}) – teljes resp: {repr(resp)}\n")
                                            opened = False
                                        elif not oid and not cid:
                                            self._safe_log(f"⚠️ LIVE válasz orderId nélkül, teljes resp: {repr(resp)}\n")
                                            opened = False
                                        else:
                                            order_key = oid or cid
                                            self._safe_log(
                                                f"✅ LIVE {combined_sig.upper()} elküldve | mode={mode} lev={lev} "
                                                f"| size={size_to_send} funds={funds_to_send} commit={commit_usdt} | orderId={oid} clientOid={cid}\n"
                                            )

                                            try:
                                                lot_step_now, _price_step_now, _mb_min_base_now, _mb_min_funds_now, _quote_step_now = self._mb_get_market_steps(symbol)
                                            except Exception:
                                                lot_step_now = 0.0

                                            # --- 1) Realtime partial fill + fee (WS + REST) ---
                                            size_req = float(size_to_send) if size_to_send is not None else None
                                            funds_req = float(funds_to_send) if funds_to_send is not None else None

                                            fb, commit_real_ws, fee_open_actual = self._mb_resolve_open_fill(
                                                order_id=str(order_key),
                                                side=combined_sig,
                                                req_price=last_px_rt,
                                                req_size=size_req,
                                                req_funds=funds_req,
                                                lev=lev,
                                                lot_step=float(lot_step_now or 0.0),
                                            )

                                            size_now = None
                                            commit_used = None

                                            if fb > 0.0:
                                                # WS/REST szerinti tényleges filled méret
                                                size_now = float(fb)
                                                commit_used = float(commit_real_ws or 0.0)
                                            else:
                                                # --- 2) Fallback: régi becslés a sanitizer output alapján ---
                                                if funds_to_send is not None:
                                                    commit_used = float(funds_to_send) / max(lev, 1)
                                                    size_now = self._sdiv(float(funds_to_send), last_px_rt, 0.0)
                                                    size_now = self._mb_floor_to_step_dec(size_now, float(lot_step_now or 0.0))
                                                else:
                                                    size_now = float(size_to_send)
                                                    commit_used = self._sdiv(size_now * float(last_px_rt), lev, 0.0)

                                            if commit_used is None or commit_used <= 0:
                                                # végső fallback: marad az eredeti commit_usdt
                                                commit_used = float(commit_usdt)

                                            # --- Fee becslés / tényleges ---
                                            _fee_rate = self._mb_get_taker_fee()
                                            _fee_open_est = self._mb_est_fee_quote(last_px_rt, size_now, _fee_rate)

                                            fee_open_actual = float(fee_open_actual or 0.0)
                                            _fee_for_pnl = fee_open_actual if fee_open_actual > 0.0 else _fee_open_est

                                            # --- PnL becslés: egységes árlekérdezés ---
                                            pnl_est = None
                                            try:
                                                # Ár lekérdezése: WS → cache → REST
                                                rt_now = self.get_best_price(symbol)

                                                if self._is_pos_num(rt_now) and rt_now > 0:
                                                    gross = (rt_now - last_px_rt) * size_now * \
                                                            (1 if combined_sig == 'buy' else -1)
                                                    pnl_est = gross - float(_fee_for_pnl)
                                            except Exception:
                                                pass

                                            # History: fee = tényleges, ha elérhető, különben a becsült
                                            self._mb_hist_add_open(
                                                order_id=str(order_key),
                                                side=combined_sig, entry=last_px_rt,
                                                size=size_now,
                                                lev=lev, fee=float(_fee_for_pnl),
                                                pnl_est=pnl_est
                                            )

                                            # SIM pool/pozíció: commit_used + fee_open_actual/becslés
                                            _open_sim(
                                                combined_sig, last_px_rt,
                                                size_now, commit_used,
                                                atr_pack=(mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val) if (use_atr and atr_val is not None) else None,
                                                fixed_pack=(tpct, spct, trpct) if use_fixed else None,
                                                fee_open_actual_override=fee_open_actual if fee_open_actual > 0.0 else 0.0,
                                                fee_reserved_override=_fee_for_pnl,
                                                oid=str(order_key),
                                            )
                                            opened = True

                                    except Exception as e:
                                        self._safe_log(f"❌ LIVE order hiba: {e}\n")

                            if opened:
                                self._mb_last_cross_ts = now
                                self._mb_last_signal   = combined_sig

                    # --- Diagram frissítés ---
                    try:
                        self.root.after(0, self._mb_draw_chart)
                    except Exception:
                        pass

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

    # ============ NEW: Leállításkori / ad-hoc összegzés ============
    def _mb_summary(self):
        """Összegző statisztika (SIM trade-ek alapján)."""
        try:
            hist = getattr(self, "_sim_history", None)
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
        import pandas as pd
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
        import pandas as pd
        return series.ewm(alpha=1.0 / n, adjust=False).mean()

    # ---------- Jel-generátor: EMA KERESZTEZÉS + SLOPE SZŰRÉS ----------
    def _mb_signal_from_ema_live(
        self,
        series,
        fast: int,
        slow: int,
        last_px_rt: float | None,
        atr_eps_mult: float | None = None,
        invert: bool | None = None,
        slope_threshold: float = 0.0,  # ÚJ: Meredekség küszöb (pl. 1e-6)
    ) -> tuple[str, float, float]:
        """
        Professzionális EMA jelgenerátor:
        1. Keresztezés detektálása (Crossover).
        2. Hysteresis sáv (ATR alapú zajszűrés).
        3. Opcionális: Slope (meredekség) ellenőrzés a hamis jelek ellen oldalazáskor.
        """
        import pandas as pd
        import numpy as np

        # Biztonsági másolat és típusellenőrzés
        s = pd.Series(series, dtype="float64").copy()
        
        # Adathossz ellenőrzés: Kell elég adat a beálláshoz
        if len(s) < max(fast, slow) + 5:
            return "hold", float("nan"), float("nan")

        # Élő ár beégetése (Intrabar update)
        if last_px_rt is not None and last_px_rt > 0:
            s.iloc[-1] = float(last_px_rt)

        # Számítás
        ema_f = s.ewm(span=fast, adjust=False).mean()
        ema_s = s.ewm(span=slow, adjust=False).mean()

        # Utolsó két érték kinyerése
        ef_p, ef_l = float(ema_f.iloc[-2]), float(ema_f.iloc[-1])
        es_p, es_l = float(ema_s.iloc[-2]), float(ema_s.iloc[-1])

        diff_prev = ef_p - es_p
        diff_now  = ef_l - es_l

        # ---- 1. Hysteresis (Zajszűrő sáv) ----
        if atr_eps_mult is None:
            try:
                # GUI thread-safe olvasása (vagy default)
                ui_pct = float(getattr(self, "mb_ema_hyst_pct", 0.0).get())
                atr_eps_mult = max(0.0, ui_pct) / 100.0
            except Exception:
                atr_eps_mult = 0.0

        # ATR érték biztonságos olvasása
        atr_last = float(getattr(self, "_mb_last_atr_val", 0.0))
        
        # Sáv számítása
        band = 0.0
        if atr_last > 0 and atr_eps_mult > 0:
            band = atr_last * atr_eps_mult
        
        up_th =  band
        dn_th = -band

        # ---- 2. Keresztezés logikája ----
        # Long: Előzőleg a sáv alatt/benne volt, most a sáv felett van
        crossed_up   = (diff_prev <= dn_th) and (diff_now > up_th)
        
        # Short: Előzőleg a sáv felett/benne volt, most a sáv alatt van
        crossed_down = (diff_prev >= up_th) and (diff_now < dn_th)

        # ---- 3. Slope (Meredekség) Szűrés (Opcionális PRO funkció) ----
        # Ha a lassú mozgóátlag "lapos", akkor oldalazunk -> veszélyes a jel.
        # slope = (jelenlegi - előző) / előző
        slope_ok = True
        if slope_threshold > 0:
            slow_slope = (es_l - es_p) / es_p if es_p != 0 else 0
            if crossed_up and slow_slope < -slope_threshold:
                slope_ok = False # Ne vegyünk, ha a trend még mindig erősen esik
            elif crossed_down and slow_slope > slope_threshold:
                slope_ok = False # Ne adjunk el, ha a trend még mindig erősen emelkedik

        # Döntés
        sig = "hold"
        if crossed_up and slope_ok:
            sig = "buy"
        elif crossed_down and slope_ok:
            sig = "sell"

        # Invertálás
        if invert is None:
            try:
                invert = bool(self.mb_invert_ema.get())
            except Exception:
                invert = False
        
        if invert:
            if sig == "buy": sig = "sell"
            elif sig == "sell": sig = "buy"

        return sig, ef_l, es_l

    # ---------- ATR számítás (Javítva: Wilder's Smoothing) ----------
    def _mb_atr(self, df, n: int = 14):
        """
        Valódi ATR számítás (Wilder's Smoothing).
        Ez pontosabb és jobban egyezik a TradingView értékeivel.
        """
        import pandas as pd
        
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
        import pandas as pd
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
        HTF Filter: +1 (Bull), -1 (Bear), 0 (Semleges/Hiba).
        FONTOS: Ha ezt ciklusban hívod, a hálózati kérés (fetch_ohlcv) lassíthatja a botot!
        """
        try:
            # Adatlekérés (csak ha muszáj)
            with self._ex_lock:
                # Limit optimalizálás: nem kell 500 gyertya, elég a slow EMA beállásához kb 2-3x
                ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=max(slow * 3, 100))
            
            if not ohlcv:
                return 0
                
            import pandas as pd
            # Csak a Close árak kellenek, ne építsünk teljes DataFrame-et feleslegesen
            closes = [x[4] for x in ohlcv] 
            s = pd.Series(closes, dtype='float64')
            
            if len(s) < slow + 5:
                return 0

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
                    # Biztonságos hozzáférés
                    invert = bool(getattr(self, "mb_invert_ema", False).get())
                except Exception:
                    invert = False

            return -trend if invert else trend

        except Exception as e:
            # Opcionális: logolhatod a hibát, ha debuggolsz
            # print(f"Trend filter error: {e}")
            return 0

    # ---------- Méret-számítás (budget támogatással) ----------
    def _mb_compute_size(
        self,
        symbol: str,
        side: str,
        px: float,
        size_pct: float,
        input_mode: str,
        mode: str,
        leverage: int,
        budget_quote: float = 0.0,
        dry: bool | None = None,
        auto_borrow: bool | None = None,
    ) -> tuple[float | None, float | None]:
        """
        Méret számítás:
          - input_mode == 'quote' → funds (USDT) = (cap_quote * pct), size=None
          - input_mode == 'base'  → size (BASE)  = (avail_base * pct), funds=None

        cap_quote logika:
          - DRY-RUN: cap_quote = budget (ha >0), különben avail_quote
          - LIVE + Auto-borrow: cap_quote = budget (ha >0), különben avail_quote
          - LIVE + NINCS Auto-borrow: cap_quote = min(avail_quote, budget) ha budget>0, különben avail_quote
        """
        try:
            import tkinter as tk  # ha a fájl tetején már van, ez el is hagyható

            leverage = max(1, min(leverage, 10 if mode == 'isolated' else 5))
            base, quote = split_symbol(symbol)

            # gyors készlet-lekérés (ha van helper)
            avail_base, avail_quote = (0.0, 0.0)
            if hasattr(self, "_mt_available"):
                avail_base, avail_quote = self._mt_available(base, quote)

            pct = max(0.0, min(100.0, float(size_pct))) / 100.0
            budget_quote = float(budget_quote or 0.0)

            if input_mode == 'quote':
                # döntés a cap_quote-ról – csak akkor olvas widgetet, ha nem kaptunk paramot
                if dry is None:
                    dry = bool(self._mb_get_bool('mb_dry', True))
                if auto_borrow is None:
                    auto_borrow = bool(getattr(self, 'mb_autob', tk.BooleanVar(value=False)).get())

                if dry or auto_borrow:
                    cap_quote = budget_quote if budget_quote > 0 else avail_quote
                else:
                    if budget_quote > 0:
                        cap_quote = min(avail_quote, budget_quote)
                    else:
                        cap_quote = avail_quote

                use_quote = max(0.0, cap_quote * pct)
                if use_quote <= 0:
                    return None, None

                return None, use_quote

            else:  # 'base'
                size = max(0.0, avail_base * pct)
                return (round(size, 6), None) if size > 0 else (None, None)

        except Exception:
            return (None, None)

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
        from decimal import Decimal
        q = Decimal(str(step))
        return float((Decimal(str(x)) // q) * q)

    # --- TEMP DEBUG: biztonságos pretty print ---
    def _mb_pp(self, obj) -> str:
        """Debughoz: JSON-szerű string (kulcsok/értékek), default=str fallback-kel."""
        try:
            import json
            return json.dumps(obj, ensure_ascii=False, default=str)
        except Exception:
            try:
                return repr(obj)
            except Exception:
                return "<unprintable>"

    def _mb_calc_order_qty(self,
        side: str,
        price: float,
        pool_free: float,
        size_pct: float,
        leverage: int,
        mode: str = "quote",
        lot_step: float = 0.0,
        price_step: float = 0.0,
    ) -> dict:
        """Wrapper a régi API-hoz: belül az egységes _mb_compute_size-et használja.

        VISSZA:
            {
                "qty_base": float,       # bázismennyiség (szimbólum alapdevizájában)
                "commit_quote": float,   # ténylegesen lekötött QUOTE (pl. USDT)
                "nominal_quote": float,  # nominális pozícióméret (tőkeáttétellel)
            }
        """
        size_pct = float(max(0.0, min(100.0, size_pct)))
        budget_quote = float(pool_free) * (size_pct / 100.0)

        qty_base, commit_quote = self._mb_compute_size(
            symbol=None,                 # itt nem használjuk a sym-et
            side=side,
            price=price,
            size_pct=size_pct,
            input_mode=mode,
            mode=mode,
            leverage=leverage,
            budget_quote=budget_quote,
            dry=True,
            auto_borrow=False,
            lot_step=lot_step,
            price_step=price_step,
        )

        nominal_quote = (commit_quote or 0.0) * max(1, leverage)
        return {
            "qty_base": float(qty_base or 0.0),
            "commit_quote": float(commit_quote or 0.0),
            "nominal_quote": float(nominal_quote or 0.0),
        }

    def _mb_build_cfg(self) -> dict:
        """Margin bot beállítások snapshot – CSAK fő szálból hívd (pl. mb_start-ban)."""
        import tkinter as tk

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

            # Max nyitott, pause new
            "max_open": self._mb_get_int('mb_max_open', 0),
            "pause_new": self._mb_get_bool('mb_pause_new', False),

            # Auto-borrow + EMA invert
            "auto_borrow": bool(getattr(self, "mb_autob", tk.BooleanVar(value=False)).get()),
            "invert_ema": bool(getattr(self, "mb_invert_ema", tk.BooleanVar(value=False)).get()),

            # EMA hysteresis %
            "ema_hyst_pct": self._mb_get_float('mb_ema_hyst_pct', 1.0),
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
            now = _time.time()
            if getattr(self, "_mb_fee_cache", None) and (now - self._mb_fee_cache.get("ts", 0) < 3600):
                return float(self._mb_fee_cache["taker"])
            fee = 0.001
            ex = getattr(self, "exchange", None)
            if ex:
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
            self._mb_fee_cache = {"taker": float(fee), "ts": now}
            return float(fee)
        except Exception:
            return 0.001

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
            # KucoinMarginTrader specifikus helper
            if hasattr(ex, "get_margin_fills_by_order"):
                try:
                    fills = ex.get_margin_fills_by_order(oid) or []
                except Exception:
                    fills = []
            # Általánosabb spot/margin helper
            if (not fills) and hasattr(ex, "get_order_fills"):
                try:
                    fills = ex.get_order_fills(oid) or []
                except Exception:
                    fills = []
            # ccxt-s fetch_order_trades fallback
            if (not fills) and hasattr(ex, "fetch_order_trades"):
                try:
                    fills = ex.fetch_order_trades(oid) or []
                except Exception:
                    fills = []
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
                fills = None

                # KuCoin margin specific
                if hasattr(ex, "get_margin_fills_by_order"):
                    fills = ex.get_margin_fills_by_order(order_id)
                # KuCoin spot / alt wrapper
                elif hasattr(ex, "get_fills_by_order"):
                    fills = ex.get_fills_by_order(order_id)
                # ccxt-s stílusú wrapper
                elif hasattr(ex, "fetch_order_trades"):
                    try:
                        fills = ex.fetch_order_trades(order_id)
                    except TypeError:
                        # egyes ccxt wrapper-ek symbol-t is várnak
                        fills = ex.fetch_order_trades(order_id, None)

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

        box = ttk.Labelframe(self.tab_settings, text="Megjelenés / betűk", padding=10)
        box.pack(fill="x", padx=10, pady=10)

        # oszlop kicsit engedjen jobbra is
        box.grid_columnconfigure(1, weight=1)

        # --- Betűméret ---
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

        # --- Betűtípus ---
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