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

# -------- 3rd party --------
import requests
import pandas as pd

# Tkinter
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
from decimal import Decimal, ROUND_DOWN, ROUND_UP, getcontext

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
    import websocket  # websocket-client
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
        Aláírt KuCoin REST POST (v2). A `path` pl. '/api/v1/isolated/transfer-in'.
        """
        import time, base64, hmac, hashlib, json, requests
        base_url = "https://api.kucoin.com"
        url = base_url + path

        key        = os.getenv("KUCOIN_KEY", "")
        secret     = os.getenv("KUCOIN_SECRET", "")
        passphrase = os.getenv("KUCOIN_PASSPHRASE", "")
        if not (key and secret and passphrase):
            raise RuntimeError("Hiányzó API kulcsok (KUCOIN_KEY/SECRET/PASSPHRASE).")

        now = str(int(time.time() * 1000))
        payload_json = json.dumps(body, separators=(",", ":"))
        str_to_sign = now + "POST" + path + payload_json
        signature = base64.b64encode(
            hmac.new(secret.encode("utf-8"), str_to_sign.encode("utf-8"), hashlib.sha256).digest()
        ).decode()
        passphrase_sig = base64.b64encode(
            hmac.new(secret.encode("utf-8"), passphrase.encode("utf-8"), hashlib.sha256).digest()
        ).decode()

        headers = {
            "Content-Type": "application/json",
            "KC-API-KEY": key,
            "KC-API-SIGN": signature,
            "KC-API-TIMESTAMP": now,
            "KC-API-PASSPHRASE": passphrase_sig,
            "KC-API-KEY-VERSION": "2",
        }

        r = requests.post(url, headers=headers, data=payload_json, timeout=12)
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
        self.root.title("KuCoin Universal SDK Bot (SPOT + Margin)")
        self.root.geometry("1280x930")

        self.is_running = False
        self.exchange: Optional[KucoinSDKWrapper] = None
        self.public_mode = tk.BooleanVar(value=PUBLIC_MODE_DEFAULT)
        self.symbols: list[str] = [DEFAULT_SYMBOL]

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

        # --- Trade (SPOT) ---
        self.tab_trade = ttk.Frame(self.nb); self.nb.add(self.tab_trade, text="Trade (SPOT)")
        tf = ttk.Labelframe(self.tab_trade, text="Kézi SPOT market megbízás", padding=10); tf.pack(fill=tk.X, padx=10, pady=10)
        ttk.Label(tf, text="Pár:").grid(row=0, column=0, sticky='w')
        self.trade_symbol = ttk.Combobox(tf, values=self.symbols, width=18, state='readonly')
        self.trade_symbol.set(DEFAULT_SYMBOL); self.trade_symbol.grid(row=0, column=1, padx=6)
        ttk.Label(tf, text="Size (BASE):").grid(row=0, column=2, sticky='w')
        self.trade_size = ttk.Entry(tf, width=12); self.trade_size.grid(row=0, column=3, padx=6)
        ttk.Label(tf, text="Funds (QUOTE):").grid(row=0, column=4, sticky='w')
        self.trade_funds = ttk.Entry(tf, width=12); self.trade_funds.grid(row=0, column=5, padx=6)
        self.btn_spot_buy  = ttk.Button(tf, text="BUY (market)",  command=lambda: self.market_order('buy'));  self.btn_spot_buy.grid(row=0, column=6, padx=6)
        self.btn_spot_sell = ttk.Button(tf, text="SELL (market)", command=lambda: self.market_order('sell')); self.btn_spot_sell.grid(row=0, column=7, padx=6)

        # --- Balances (SPOT) ---
        self.tab_bal = ttk.Frame(self.nb); self.nb.add(self.tab_bal, text="Balances (SPOT)")
        bf = ttk.Labelframe(self.tab_bal, text="Egyenlegek", padding=10); bf.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        cols = ("currency","available","holds")
        self.tbl_bal = ttk.Treeview(bf, columns=cols, show='headings', height=14)
        for c in cols:
            self.tbl_bal.heading(c, text=c); self.tbl_bal.column(c, width=160, anchor='center')
        self.tbl_bal.pack(fill=tk.BOTH, expand=True)
        ttk.Button(bf, text="Frissítsd egyenlegeket", command=self.refresh_balances).pack(pady=6)

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
        ttk.Button(ticket, text="BUY (margin)",  style="Buy.TButton",
                   command=lambda: self._mt_place('buy')).grid(row=9, column=0, columnspan=2, sticky="we", padx=(0,6))
        ttk.Button(ticket, text="SELL (margin)", style="Sell.TButton",
                   command=lambda: self._mt_place('sell')).grid(row=9, column=2, columnspan=2, sticky="we", padx=(6,0))

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

        # --- Margin Bot (auto) ---
        self._build_margin_bot_tab()

        # --- Backtest fül (ÚJ) ---
        self.backtest_tab = BacktestTab(
            master=self.root,
            nb=self.nb,
            exchange_provider=lambda: self.exchange,  # a már létrehozott KucoinSDKWrapper példány
            log_fn=self.log,                           # a meglévő logoló függvényed
        )

        # Szimbólumok betöltése háttérben
        threading.Thread(target=self._load_symbols_async, daemon=True).start()

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def _init_styles(self):
        style = ttk.Style()
        style.configure("TLabel", padding=(2, 2))
        style.configure("TEntry", padding=(2, 2))
        style.configure("TButton", padding=(6, 6))
        style.configure("Card.TLabelframe", padding=12)
        style.configure("Card.TLabelframe.Label", font=("Segoe UI", 10, "bold"))
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
        """Lekérdezi, frissíti az összes számlatípus egyenlegét és kiszámolja a Bevételt/PNL-t egy külön szálon."""
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return

        def worker():
            # opcionális cache/összegző
            self.usdt_avail = 0.0

            try:
                exchange = self.exchange
                all_balances: list[dict] = []
                unique_currencies: set[str] = set()  # árfolyamokhoz

                # --- 1) Összes egyenleg lekérése ---

                # 1.1 SPOT (Main / Trade / Futures)
                r = exchange._rest_get("/api/v1/accounts", {})  # type: ignore[union-attr]
                spot_accounts = r.get("data", []) if isinstance(r, dict) else []
                for acc in spot_accounts:
                    acc_type = (acc.get("type") or "main").lower()
                    if acc_type in ("main", "trade", "futures"):
                        ccy = (acc.get("currency") or acc.get("currencyName") or "").strip().upper()
                        # KuCoin itt jellemzően 'available' + 'holds' kulcsokat ad
                        current_avail = float(acc.get("available") or 0)
                        current_holds = float(acc.get("holds") or 0)
                        if ccy and (current_avail > 0 or current_holds > 0):
                            all_balances.append({
                                "ccy": ccy,
                                "acc_type": acc_type.capitalize(),
                                "avail": current_avail,
                                "holds": current_holds,
                                "liability": 0.0,
                                "symbol": ""
                            })
                            unique_currencies.add(ccy)

                # 1.2 CROSS margin — NORMALIZÁLT olvasás
                cross_resp = exchange.fetch_cross_accounts()  # type: ignore[union-attr]
                cross_data = cross_resp.get("data", {}) if isinstance(cross_resp, dict) else {}
                cross_accounts = (
                    cross_data.get("accounts", [])
                    or cross_data.get("accountList", [])
                    or cross_data.get("debtList", [])
                )

                for acc in cross_accounts:
                    ccy = (acc.get("currency") or acc.get("currencyName") or "").strip().upper()
                    if not ccy:
                        continue

                    # ==== NORMALIZÁLÁS ====
                    # preferált kulcsok: available / availableBalance / free
                    avail = float(
                        acc.get("available",
                        acc.get("availableBalance",
                        acc.get("free", 0))) or 0.0
                    )
                    # hold/locked: holds / holdBalance
                    holds = float(
                        acc.get("holds",
                        acc.get("holdBalance", 0)) or 0.0
                    )
                    # liability/debt
                    liability = float(
                        acc.get("liability",
                        acc.get("debt", 0)) or 0.0
                    )

                    # Ha csak 'balance' van (összes), osszuk szét available + holds-ra,
                    # vagy ha holdBalance nincs, tekintsük available-nek.
                    if avail == 0 and "balance" in acc:
                        bal = float(acc.get("balance") or 0.0)
                        hb  = float(acc.get("holdBalance") or 0.0)
                        if bal > 0 and bal >= hb:
                            avail = bal - hb
                            holds = hb

                    if ccy and (avail > 0 or holds > 0 or liability > 0):
                        all_balances.append({
                            "ccy": ccy,
                            "acc_type": "Cross",
                            "avail": avail,
                            "holds": holds,
                            "liability": liability,
                            "symbol": ""
                        })
                        unique_currencies.add(ccy)

                # 1.3 ISOLATED margin
                isolated_resp = exchange.fetch_isolated_accounts()  # type: ignore[union-attr]
                # kompatibilis kinyerés
                _idata = isolated_resp.get("data", {}) if isinstance(isolated_resp, dict) else getattr(isolated_resp, "data", {}) or {}
                isolated_assets = _idata.get("assets", []) or []
                for asset in isolated_assets:
                    symbol = (asset.get("symbol") or "").upper()
                    if not symbol:
                        continue

                    base = asset.get("baseAsset") or {}
                    quote = asset.get("quoteAsset") or {}

                    base_ccy = (base.get("currency") or "").upper()
                    base_av  = float(base.get("available") or 0)
                    base_hd  = float(base.get("holds") or 0)
                    base_li  = float(base.get("liability") or 0)

                    quote_ccy = (quote.get("currency") or "").upper()
                    quote_av  = float(quote.get("available") or 0)
                    quote_hd  = float(quote.get("holds") or 0)
                    quote_li  = float(quote.get("liability") or 0)

                    if base_ccy and (base_av > 0 or base_hd > 0 or base_li > 0):
                        all_balances.append({
                            "ccy": base_ccy, "acc_type": "Isolated",
                            "avail": base_av, "holds": base_hd,
                            "liability": base_li, "symbol": symbol
                        })
                        unique_currencies.add(base_ccy)

                    if quote_ccy and (quote_av > 0 or quote_hd > 0 or quote_li > 0):
                        all_balances.append({
                            "ccy": quote_ccy, "acc_type": "Isolated",
                            "avail": quote_av, "holds": quote_hd,
                            "liability": quote_li, "symbol": symbol
                        })
                        unique_currencies.add(quote_ccy)

                # --- 2) Árfolyamok lekérése ---
                prices: dict[str, float] = {}
                for ccy in unique_currencies:
                    try:
                        # pl. ha USDT, akkor az 1.0
                        if ccy.upper() == "USDT":
                            prices[ccy] = 1.0
                        else:
                            # USD-ben kifejezve ár
                            sym = f"{ccy}-USDT"
                            prices[ccy] = float(self.exchange.fetch_last_price(sym))
                    except Exception:
                        prices[ccy] = 0.0

                # --- 3. Bevétel és PNL számítás, előbb rekordok (dict), utána rendezés és tuple-képzés ---
                records = []  # ide gyűjtjük dict formában, hogy legyen min rendezni

                for bal in all_balances:
                    ccy = bal['ccy']
                    px  = float(prices.get(ccy, 0.0))
                    avail_amount = float(bal['avail'] or 0.0)
                    holds_amount = float(bal['holds'] or 0.0)

                    # Bevétel (USD) = ELÉRHETŐ × ár
                    value_usd = avail_amount * (px if px > 0 else 0.0)
                    liability_usd = float(bal['liability'] or 0.0) * (px if px > 0 else 0.0)
                    pnl_usd = value_usd - liability_usd

                    records.append({
                        "ccy": ccy,
                        "acc_type": bal["acc_type"],
                        "avail": avail_amount,
                        "holds": holds_amount,
                        "liability": float(bal["liability"] or 0.0),
                        "value": value_usd,
                        "pnl": pnl_usd,
                        "symbol": bal["symbol"],
                    })

                # --- RENDEZÉS ---
                # 1) deviza (ccy)
                # 2) számlatípus prioritás (Main -> Trade -> Cross -> Isolated)
                # 3) pár-csoport (valódi symbol, különben szintetikus CCY-USDT) – csak finom rendezéshez
                records.sort(
                    key=lambda r: (
                        ACCOUNT_SORT_PRIORITY.get(r.get("acc_type"), 99),  # 1) számlatípus
                        _pair_group_key(r),                                 # 2) pár-csoport
                        (r.get("ccy") or "").upper()                        # 3) deviza
                    )
                )

                # --- Tuple-okká alakítás a táblához ---
                final_rows = [
                    self._get_balance_row(
                        ccy=rec["ccy"],
                        acc_type=rec["acc_type"],
                        avail=rec["avail"],
                        holds=rec["holds"],
                        liability=rec["liability"],
                        value=rec["value"],
                        pnl=rec["pnl"],
                        symbol=rec["symbol"]
                    )
                    for rec in records
                ]

                self.root.after(0, lambda: (
                    self._update_funds_balance_table(final_rows),
                    # Margin Bot „Elérhető” felirat újratöltése ugyanazzal a logikával
                    self._mb_refresh_available() if hasattr(self, "_mb_refresh_available") else None
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
        for cb in (self.e_symbol, self.trade_symbol, self.cross_symbol, self.mt_symbol, self.f_iso_sym):
            try:
                cb.configure(values=self.symbols)
                # ha a jelenlegi érték nem normalizált, próbáljuk megmenteni
                cur = normalize_symbol(cb.get() or "")
                cb.set(cur if cur in self.symbols else DEFAULT_SYMBOL)
            except Exception:
                pass

    # ---- pretty isolated view ----
    def pretty_isolated_accounts(self, payload: dict) -> str:
        data = payload.get('data', payload)
        assets = data.get('assets', []) or []
        lines = ["Isolated Margin – Részletes nézet", ""]

        symbols = [a.get('symbol', '').upper() for a in assets if a.get('symbol')]
        prices: Dict[str, float] = {}
        try:
            prices = self.exchange.fetch_last_prices_bulk(symbols) if self.exchange else {}  # type: ignore[union-attr]
        except Exception:
            prices = {}

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

            last = float(prices.get(sym, 0.0))
            if last <= 0 and self.exchange:
                try:
                    last = float(self.exchange.fetch_last_price(sym))  # type: ignore[union-attr]
                except Exception:
                    last = 0.0

            net_quote = base_tot * last + quote_tot - quote_li if last > 0 else None

            if (base_tot > 0) or (quote_tot > 0) or (quote_li > 0) or (debt_ratio > 0):
                lines.append(f"── {sym}  [{status}]")
                lines.append(f"   Risk: {self._risk_label(debt_ratio)}")
                if last > 0:
                    lines.append(f"   Last Price: {last:,.6f} {quote_ccy}")
                lines.append(f"   {base_ccy}: total {base_tot:,.6f}  |  available {base_av:,.6f}  |  liability {base_li:,.6f}")
                lines.append(f"   {quote_ccy}: total {quote_tot:,.6f}  |  available {quote_av:,.6f}  |  liability {quote_li:,.6f}")
                if net_quote is not None:
                    lines.append(f"   Net Value (≈): {net_quote:,.2f} {quote_ccy}")
                    side_txt = None; closable = None
                    if base_li > 0:
                        side_txt = "SHORT"; closable = base_li
                    elif base_tot > 0:
                        side_txt = "LONG";  closable = base_tot
                    if side_txt and closable is not None:
                        lines.append(f"   Position: {side_txt}  |  Closable size (≈): {closable:,.6f} {base_ccy}")
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
        prices = {}
        try:
            prices = self.exchange.fetch_last_prices_bulk(symbols) if self.exchange else {}  # type: ignore[union-attr]
        except Exception:
            prices = {}

        lines = [f"Cross Margin – Részletes nézet (QUOTE: {default_quote.upper()})", ""]
        for r in rows:
            sym = r["symbol"]; side = r["side"]; closable = r["closable"]
            base_ccy = sym.split("-")[0]; quote_ccy = sym.split("-")[1]
            last = float(prices.get(sym, 0.0))
            est_val = f"{closable*last:,.2f} {quote_ccy}" if last > 0 else "n/a"
            lines.append(f"── {sym}  [{side}]")
            if last > 0:
                lines.append(f"   Last Price: {last:,.6f} {quote_ccy}  |  Closable≈ {closable:,.6f} {base_ccy}  (~{est_val})")
            else:
                lines.append(f"   Closable≈ {closable:,.6f} {base_ccy}")
            lines.append(f"   {r['base']}")
            lines.append(f"   {r['quote']}")
            lines.append(f"   Risk: {r['risk']}")
            lines.append("")
        return "\n".join(lines)

    def _fill_isolated_table(self, rows: list[dict]):
        for iid in self.tbl_iso.get_children():
            self.tbl_iso.delete(iid)
        for r in rows:
            self.tbl_iso.insert("", tk.END, values=(
                r["symbol"], r["side"], f"{r['closable']:,.6f}",
                r["base"], r["quote"], r["risk"]
            ))

    # ---- price loop ----
    def _mt_start_price_loop(self):
        if self._mt_price_job:
            self.root.after_cancel(self._mt_price_job)

        def _tick():
            try:
                # Csak akkor frissítünk, ha a "Margin Trade" fül aktív
                if self.nb.tab(self.nb.select(), "text") != "Margin Trade":
                    pass
                else:
                    sym = normalize_symbol(self.mt_symbol.get())
                    px = 0.0

                    # 1) SDK/bulk próbálkozás
                    try:
                        if self.exchange:
                            px = float(self.exchange.fetch_last_price(sym))  # type: ignore[union-attr]
                    except Exception:
                        px = 0.0

                    # 2) Ha nincs ár, azonnali REST fallback ugyanebben a ciklusban
                    if px <= 0 and self.exchange:
                        try:
                            px2 = float(self.exchange.fetch_last_price(sym))  # fetch_last_price már REST fallbackel is
                            if px2 > 0:
                                px = px2
                        except Exception:
                            pass

                    # UI frissítés + becslés
                    self.mt_price_lbl.config(text=f"Ár: {px:.6f}" if px > 0 else "Ár: –")
                    self._mt_update_estimate(px)

            finally:
                self._mt_price_job = self.root.after(2000, _tick)

        self._mt_price_job = self.root.after(50, _tick)

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
            px = 0.0
            if self.exchange:
                try:
                    px = float(self.exchange.fetch_last_price(sym))  # type: ignore[union-attr]
                except Exception:
                    px = 0.0
            
            # Ez a leglassabb hívás
            avail_base, avail_quote = self._mt_available(base, quote)

            # 2. Értékek számítása
            new_size, new_funds = None, None
            input_mode = self.mt_input_mode.get()

            if action_type == 'percent':
                pct = int(value)
                if input_mode == 'base':
                    new_size = f"{(avail_base * pct / 100.0):.6f}"
                else: # 'quote'
                    new_funds = f"{(avail_quote * pct / 100.0):.2f}"
            
            elif action_type == 'max':
                side = str(value)
                if side == 'sell':
                    input_mode = 'base'  # Eladásnál mindig a BASE-t akarjuk kitölteni
                    new_size = f"{avail_base:.6f}"
                else: # 'buy'
                    input_mode = 'quote' # Vételnél mindig a QUOTE-t
                    new_funds = f"{avail_quote:.2f}"

            # 3. GUI frissítése a fő szálon (self.root.after)
            def update_ui():
                try:
                    # 'Max' gomb esetén átváltjuk a beviteli módot
                    if action_type == 'max':
                        self.mt_input_mode.set(input_mode)
                        self._mt_on_input_change() # Ez engedélyezi/letiltja a mezőket
                        self.mt_pct.set(100)       # <-- EZT A SORT ADD HOZZÁ
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
                    
                    # Becslés frissítése
                    self._mt_update_estimate(px)
                except Exception as e:
                    self.margin_log.insert(tk.END, f"❌ GUI frissítési hiba: {e}\n"); self.margin_log.see(tk.END)
                finally:
                    self.root.config(cursor="") # Kurzor visszaállítása itt

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
        ab, aq = 0.0, 0.0
        if not self.exchange or self.public_mode.get():
            return ab, aq
        try:
            if self.mt_mode.get() == 'isolated':
                sym = f"{base_ccy}-{quote_ccy}"
                resp = self.exchange.fetch_isolated_accounts()  # type: ignore[union-attr]
                payload = resp if isinstance(resp, dict) else getattr(resp, '__dict__', {}) or {'data': getattr(resp, 'data', {})}
                assets = (payload.get('data', payload) or {}).get('assets', []) or []
                for a in assets:
                    if a.get('symbol','').upper() == sym:
                        b = a.get('baseAsset', {}) or {}
                        q = a.get('quoteAsset', {}) or {}
                        ab = float(b.get('available', 0) or 0)
                        aq = float(q.get('available', 0) or 0)
                        break
            else:
                resp = self.exchange.fetch_cross_accounts()  # type: ignore[union-attr]
                data = resp.get('data', resp) if isinstance(resp, dict) else getattr(resp, 'data', {})
                accounts = (data or {}).get('accounts', []) or data.get('accountList', []) or []
                for it in accounts:
                    cur = (it.get('currency') or it.get('currencyName') or '').upper()
                    if cur == base_ccy.upper():
                        ab = float(it.get('available', it.get('availableBalance', 0)) or 0)
                    if cur == quote_ccy.upper():
                        aq = float(it.get('available', it.get('availableBalance', 0)) or 0)
        except Exception:
            pass
        return ab, aq

    def _mt_place(self, side: str):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és állítsd be az API kulcsokat.")
            return
        sym = normalize_symbol(self.mt_symbol.get())
        typ = self.mt_type.get()
        price = self.mt_price.get().strip()
        size = self.mt_size.get().strip() or None
        funds = self.mt_funds.get().strip() or None
        lev = int(self.mt_lev.get()) if self.mt_lev.get() else None
        # korlát: cross 5x, isolated 10x
        lev = min(lev or 1, 5 if self.mt_mode.get()=='cross' else 10)
        auto = bool(self.mt_autobr.get())
        try:
            if typ == 'limit' and not price:
                raise ValueError("Limit megbízáshoz ár szükséges.")
            resp = self.exchange.place_margin_market_order(  # type: ignore[union-attr]
                self.mt_mode.get(), sym, side,
                size_base=size, funds_quote=funds,
                leverage=lev, auto_borrow=auto, auto_repay=True
            )
            oid = getattr(resp, 'orderId', None) or getattr(resp, 'data', {}).get('orderId') or None
            self.margin_log.insert(tk.END, f"✅ {self.mt_mode.get()} {typ} {side} – {sym} | size={size} funds={funds} lev={lev} auto={auto} | orderId={oid}\n")
            self.margin_log.see(tk.END)
            messagebox.showinfo("Margin order", f"Sikeres {side.upper()} ({self.mt_mode.get()})\nPár: {sym}\nOrderId: {oid}")
        except Exception as e:
            self.margin_log.insert(tk.END, f"❌ Margin order hiba: {e}\n"); self.margin_log.see(tk.END)
            messagebox.showerror("Margin order hiba", str(e))

    # ---- Lifecycle ----
    def start_bot(self):

        if self.is_running:
            return
        try:
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
                        moa = self.exchange.get_margin_order_api()
                    if moa is None and hasattr(self.exchange, "_client"):
                        try:
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
        threading.Thread(target=self.loop, daemon=True).start()
    
    def stop_bot(self):
        self.is_running = False
        self.set_status("Leállítva")
        self.log("🛑 Bot leállítva a felhasználó által.")

    def on_close(self):
        self.stop_bot()
        self.root.destroy()

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
        """Azonnali manuális frissítés – most már nem blokkolja a GUI-t."""
        if getattr(self, "_tick_busy", False):
            self.log("⏳ Frissítés már folyamatban…\n")
            return

        self._tick_busy = True
        self.log("🔄 Frissítés indul…")

        def _work():
            import pandas as pd, time

            try:
                # ha még nincs exchange (tiszta indulás), inicializáljuk public módban
                if getattr(self, "exchange", None) is None:
                    try:
                        self.exchange = KucoinSDKWrapper(public_mode=True, log_fn=self.log)
                        self.log("🔧 Exchange inicializálva (public mód) – csak adatlekérésre.")
                    except Exception as ex:
                        _msg = f"❌ Exchange init hiba: {ex}"
                        self.root.after(0, lambda msg=_msg: (
                            self.log(msg),
                            setattr(self, "_tick_busy", False)
                        ))
                        return

                # Paraméterek biztonságos olvasása
                symbol = normalize_symbol(self.e_symbol.get())
                tf     = self.cb_tf.get().strip()
                short  = int(self.e_short.get())
                long   = int(self.e_long.get())
            except Exception as e:
                _msg = f"⚠️ Paraméter hiba: {e}"
                self.root.after(0, lambda msg=_msg: (
                    self.log(msg),
                    setattr(self, "_tick_busy", False)
                ))
                return

            # --- OHLCV lekérés ---
            try:
                with getattr(self, "_ex_lock", threading.RLock()):
                    ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=200)
            except Exception as e:
                _msg = f"❌ Adatlekérési hiba: {e}"
                self.root.after(0, lambda msg=_msg: (
                    self.log(msg),
                    setattr(self, "_tick_busy", False)
                ))
                return

            if not ohlcv:
                self.root.after(0, lambda: (
                    self.log("⚠️ Nincs adat a szervertől."),
                    setattr(self, "_tick_busy", False)
                ))
                return

            # --- Számítások ---
            try:
                df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
                df['short'] = df['c'].rolling(short).mean()
                df['long']  = df['c'].rolling(long).mean()
            except Exception as e:
                _msg = f"⚠️ Számítási hiba: {e}"
                self.root.after(0, lambda msg=_msg: (
                    self.log(msg),
                    setattr(self, "_tick_busy", False)
                ))
                return

            # --- GUI frissítés a főszálon ---
            def _update_ui():
                try:
                    last = df.iloc[-1]
                    self.log(
                        f"[{symbol} {tf}] close={last['c']:.6f}, short={last['short']:.6f}, long={last['long']:.6f}"
                    )
                    self.draw_chart(df, symbol, tf)
                except Exception as e:
                    self.log(f"⚠️ GUI frissítés hiba: {e}")
                finally:
                    self._tick_busy = False

            self.root.after(0, _update_ui)

        import threading
        threading.Thread(target=_work, daemon=True).start()

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
        self.btn_spot_buy.config(state=tk.DISABLED)
        self.btn_spot_sell.config(state=tk.DISABLED)
        self.root.config(cursor="watch")

        def worker():
            try:
                symbol = normalize_symbol(self.trade_symbol.get())
                size = self.trade_size.get().strip() or None
                funds = self.trade_funds.get().strip() or None
                if not (size or funds):
                    raise ValueError("Adj meg Size (BASE) vagy Funds (QUOTE) értéket.")
                resp = self.exchange.place_market_order(symbol, side, size_base=size, funds_quote=funds)  # type: ignore[arg-type]
                oid = getattr(resp, 'orderId', None) or getattr(resp, 'data', {}).get('orderId') or resp
                self.root.after(0, lambda oid=oid, s=side: [self.log(f"✅ Spot market {s.upper()} elküldve – orderId={oid}"),
                                                            messagebox.showinfo("Order", f"Sikeres {s} order. ID: {oid}")])
            except Exception as e:
                self.root.after(0, lambda e=e: [self.log(f"❌ Spot order hiba: {e}"),
                                                messagebox.showerror("Order hiba", str(e))])
            finally:
                self.root.after(0, lambda: [self.btn_spot_buy.config(state=tk.NORMAL),
                                             self.btn_spot_sell.config(state=tk.NORMAL),
                                             self.root.config(cursor="")])
        threading.Thread(target=worker, daemon=True).start()

    # ---- SPOT egyenleg (thread) ----
    def refresh_balances(self):
        if self.public_mode.get():
            messagebox.showwarning("Privát mód szükséges", "Kapcsold ki a publikus módot és add meg az API kulcsokat.")
            return
        def worker():
            try:
                balances = self.exchange.fetch_spot_balances()  # type: ignore[union-attr]
                def fill():
                    for row in self.tbl_bal.get_children():
                        self.tbl_bal.delete(row)
                    for cur, vals in sorted(balances.items()):
                        self.tbl_bal.insert("", tk.END, values=(cur, f"{vals['available']:.8f}", f"{vals['holds']:.8f}"))
                self.root.after(0, fill)
            except Exception as e:
                self.root.after(0, lambda e=e: messagebox.showerror("Egyenleg hiba", str(e)))
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

        # 3) Utolsó ár BUY funds-becsléshez (ha nem sikerül, None maradhat – a szaniter kezelni fogja)
        try:
            last_px = float(self.exchange.fetch_last_price(symbol)) or None
        except Exception:
            last_px = None

        # 4) Szaniter hívása – egységes minimumok/lépésközök
        sb = fq = None
        try:
            sb, fq = self._mb_sanitize_order(
                symbol=symbol,
                side=side,
                price=last_px,
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
        """Margin Bot fül – bal: form, jobb: napló. Opcionális EMA/RSI/HTF/ATR beállításokkal."""
        import threading
        # fül
        self.tab_mbot = ttk.Frame(self.nb)
        self.nb.add(self.tab_mbot, text="Margin Bot")
        root = self.tab_mbot
        root.grid_columnconfigure(0, weight=0)  # form (bal)
        root.grid_columnconfigure(1, weight=1)  # log (jobb)
        root.grid_rowconfigure(0, weight=1)

        # ===== bal oszlop: beállítások (form) =====
        form = ttk.Labelframe(root, text="Margin bot – beállítások", padding=10)
        form.grid(row=0, column=0, sticky="nsew", padx=(10, 6), pady=10)
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
        self.mt_symbol = ttk.Combobox(row_pair, values=self.symbols, width=12, state='readonly')
        self.mt_symbol.set(DEFAULT_SYMBOL)
        self.mt_symbol.pack(side="left")
        # Max pozíció (0 = korlátlan) – KÖZVETLENÜL a Pár mellett
        ttk.Label(row_pair, text="  Max pozíció:").pack(side="left")
        self.mb_max_open = ttk.Spinbox(row_pair, from_=0, to=999, width=6)
        self.mb_max_open.pack(side="left", padx=(4,0))
        # alapértelmezett érték
        self.mb_max_open.delete(0, "end"); self.mb_max_open.insert(0, "0")
        # párváltáskor frissítsük az elérhető egyenleget
        self.mt_symbol.bind("<<ComboboxSelected>>", lambda _e: self._mb_refresh_available())
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
        ttk.Checkbutton(live_row1, text="Élő ár figyelése (breakout/shock)", variable=self.mb_use_live)\
           .pack(side=tk.LEFT)

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

        # RSI szűrő – kapcsoló + hossz + (opcionális küszöbök)
        rsi_box = ttk.Labelframe(form, text="RSI szűrő", padding=6)
        rsi_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        rsi_row1 = ttk.Frame(rsi_box); rsi_row1.pack(anchor="w")
        self.mb_use_rsi = tk.BooleanVar(value=True)
        ttk.Checkbutton(rsi_row1, text="RSI használata", variable=self.mb_use_rsi).pack(side=tk.LEFT)
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
        ttk.Checkbutton(htf_row, text="HTF filter használata", variable=self.mb_use_htf).pack(side=tk.LEFT)
        ttk.Label(htf_row, text="  HTF TF:").pack(side=tk.LEFT, padx=(6,2))
        self.mb_htf_tf = ttk.Combobox(htf_row, state="readonly", width=6, values=["15m","30m","1h","4h","1d"])
        self.mb_htf_tf.set("15m"); self.mb_htf_tf.pack(side=tk.LEFT)
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

        # ===== jobb oszlop: (felső) LIVE Trade History + (alsó) Bot napló =====
        right = ttk.Frame(root)
        right.grid(row=0, column=1, sticky="nsew", padx=(6,10), pady=10)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(0, weight=1)   # history
        right.grid_rowconfigure(1, weight=1)   # log

        # --- LIVE Trade History ---
        hist_box = ttk.Labelframe(right, text="Trade History (LIVE)", padding=6)
        hist_box.grid(row=0, column=0, sticky="nsew", padx=0, pady=(0,6))
        hist_box.grid_columnconfigure(0, weight=1)
        hist_box.grid_rowconfigure(0, weight=1)

        cols = ("timestamp","side","entry","exit","size","lev","fee", "pnl", "orderId")
        self._mb_hist_tv = ttk.Treeview(hist_box, columns=cols, show="headings", height=8)
        for c, w, text in (
            ("timestamp", 160, "Időbélyeg"),
            ("side", 70, "Irány"),
            ("entry", 110, "Belépő ár"),
            ("exit", 110, "Kilépő ár"),
            ("size", 110, "Méret"),
            ("lev", 90, "Tőkeáttét"),
            ("fee", 90, "Díj"),
            ("pnl", 90, "PNL"),
            ("orderId", 180, "Order ID")
        ):
            self._mb_hist_tv.heading(c, text=text)
            self._mb_hist_tv.column(c, width=w, anchor="center")
        self._mb_hist_col_index = {name: i for i, name in enumerate(cols)}
        self._mb_hist_tv.column("orderId", width=180, anchor="center", stretch=True)
        vsb = ttk.Scrollbar(hist_box, orient="vertical", command=self._mb_hist_tv.yview)
        self._mb_hist_tv.configure(yscrollcommand=vsb.set)
        self._mb_hist_tv.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")

        # --- Bot napló (SIM + általános log) ---
        log_box = ttk.Labelframe(right, text="Bot napló", padding=8)
        log_box.grid(row=1, column=0, sticky="nsew", padx=0, pady=(6,0))
        log_box.grid_columnconfigure(0, weight=1)
        log_box.grid_rowconfigure(0, weight=1)
        self.mb_log = scrolledtext.ScrolledText(log_box, wrap=tk.WORD, height=12)
        self.mb_log.grid(row=0, column=0, sticky="nsew")

        # History segéd-struktúrák
        self._mb_hist_rows_by_oid = {}

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

        # a history táblázat létrehozása UTÁN:
        self._mb_hist_start_pnl_loop()

        if not hasattr(self, "_mb_stopping"): 
            self._mb_stopping = False

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
    def _mb_refresh_available(self):
        """A Margin Bot „Elérhető” feliratát a Margin Trade fül egységes logikájával tölti."""
        try:
            # a Margin Bot fül a Margin Trade combóját (mt_symbol) használja
            sym = normalize_symbol(self.mt_symbol.get())
            base, quote = split_symbol(sym)
            avail_base, avail_quote = (0.0, 0.0)
            if hasattr(self, "_mt_available"):
                avail_base, avail_quote = self._mt_available(base, quote)
            self.mb_avail_var.set(f"{avail_quote:.2f} {quote}")
        except Exception:
            try:
                self.mb_avail_var.set("–")
            except Exception:
                pass

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
        - fee: nyitási becsült fee (QUOTE-ban)
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
        """Egyszer indítandó ciklus, ami 5 mp-enként frissíti az OPEN ügyletek becsült PnL-jét."""
        if getattr(self, "_mb_hist_pnl_job", None):
            return  # már fut
        self._mb_hist_pnl_tick()

    def _mb_hist_pnl_tick(self):
        try:
            # szükséges oszlop indexek
            col = getattr(self, "_mb_hist_col_index", {})
            ENTRY_IDX = col.get("entry", 2); EXIT_IDX = col.get("exit", 3)
            SIZE_IDX  = col.get("size", 4);  SIDE_IDX = col.get("side", 1)
            FEE_IDX   = col.get("fee", 6);   PNL_IDX  = col.get("pnl", 7)

            # aktuális rt ár a jelenlegi szimbólumhoz
            try:
                symbol = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
            except Exception:
                symbol = None

            rt = None
            if symbol:
                try:
                    rt = float(self.exchange.fetch_last_price(symbol))
                except Exception:
                    rt = None

            if rt and rt > 0:
                # végigmegyünk azokon a sorokon, ahol Exit üres → OPEN státusz
                for iid in self._mb_hist_tv.get_children(""):
                    vals = list(self._mb_hist_tv.item(iid, "values"))
                    try:
                        if vals[EXIT_IDX]:  # már zárt
                            continue
                        entry = float(vals[ENTRY_IDX] or "0")
                        size  = float(vals[SIZE_IDX]  or "0")
                        side  = str(vals[SIDE_IDX]).strip().upper()
                        fee_s = vals[FEE_IDX].strip()
                        fee_est = float(fee_s) if fee_s not in ("", None) else 0.0

                        gross = (rt - entry) * size * (1 if side == "BUY" else -1)
                        pnl_est = gross - fee_est
                        vals[PNL_IDX] = f"{pnl_est:.6f}"

                        self._mb_hist_tv.item(iid, values=tuple(vals))
                    except Exception:
                        continue
        except Exception:
            pass
        finally:
            # 5 mp múlva újra
            try:
                self._mb_hist_pnl_job = self.root.after(5000, self._mb_hist_pnl_tick)
            except Exception:
                pass

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
                self.exchange = KucoinSDKWrapper(public_mode=self.public_mode.get(), log_fn=self.log)
                self.log(f"🔧 MarginBot: exchange inicializálva (dry-run: {self.mb_dry.get()}, public_mode: {self.public_mode.get()})")
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
        try: delattr(self, "_pool_balance_quote")
        except Exception: pass
        try: delattr(self, "_pool_used_quote")
        except Exception: pass

        # azonnali aktivitás – ne szűrje ki "ugyanaz a gyertya"
        self._mb_last_bar_ts = {}
        # opcionális cache-ek nullázása (ha korábban be lettek vezetve)
        self._mb_last_rt_px = {} if hasattr(self, "_mb_last_rt_px") else {}

        # belső állapotok, ha hiányoznának
        if not hasattr(self, "_sim_pnl_usdt"):     self._sim_pnl_usdt     = 0.0
        if not hasattr(self, "_sim_pos_long"):     self._sim_pos_long     = []
        if not hasattr(self, "_sim_pos_short"):    self._sim_pos_short    = []
        if not hasattr(self, "_mb_last_bar_ts"):   self._mb_last_bar_ts   = {}   # {(symbol, tf): ts}
        if not hasattr(self, "_mb_last_cross_ts"): self._mb_last_cross_ts = 0
        if not hasattr(self, "_mb_last_signal"):   self._mb_last_signal   = "hold"
        if not hasattr(self, "_mb_lock"):          self._mb_lock          = threading.Lock()

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
                self.root.after(0, lambda: (
                    self.mb_start_btn.configure(state=tk.NORMAL),
                    self.mb_stop_btn.configure(state=tk.DISABLED),
                ))

        self._mb_thread = threading.Thread(target=_loop, daemon=True)
        self._mb_thread.start()

    def mb_stop(self):
        """Margin bot leállítása + biztonságos pozíciózárás (SIM/LIVE – C opcióval)."""
        if not getattr(self, "_mb_running", False):
            self._safe_log("ℹ️ A bot nem fut.\n")
            return

        # manuális leállítás jelző
        self._mb_stopping = True
        try:
            import time as _t
            _t.sleep(0.1)
        except Exception:
            pass
        self._mb_running = False

        self._safe_log("⏹️ Bot leállítása folyamatban...\n")

        try:
            sym = normalize_symbol(self._mb_get_str("mb_symbol", self._mb_get_str("mt_symbol", DEFAULT_SYMBOL)))
            dry = self._mb_get_bool("mb_dry", True)
            lev = self._mb_get_int("mb_leverage", 10)
            mode = self._mb_get_str("mb_mode", "isolated")

            try:
                last_px = float(self.exchange.fetch_last_price(sym))
            except Exception:
                last_px = None
                self._safe_log("⚠️ Ár lekérés nem sikerült, utolsó ismert ár kerül felhasználásra.\n")

            # --- összes pozíció zárása (long + short) ---
            for side in ("buy", "sell"):
                lst = getattr(self, "_sim_pos_long", []) if side == "buy" else getattr(self, "_sim_pos_short", [])
                i = 0
                while i < len(lst):
                    pos = lst[i]
                    px = float(last_px if last_px is not None else pos.get("peak", pos.get("entry", 0.0)))
                    close_side = "sell" if side == "buy" else "buy"

                    self._safe_log(f"🔻 Pozíció zárása ({close_side.upper()}) @ {px:.6f} | dry={dry}\n")

                    if dry:
                        # --- SIMULÁLT zárás ---
                        entry = float(pos['entry'])
                        sz = float(pos['size'])
                        pnl = (px - entry) * sz * (1 if side == 'buy' else -1)

                        with self._mb_lock:
                            self._sim_pnl_usdt += pnl
                            self._pool_balance_quote += pnl
                            self._pool_used_quote = max(0.0, self._pool_used_quote - float(pos.get('commit_usdt', 0.0)))

                        try:
                            import time as _t
                            self._sim_history.append({
                                "partial": False,
                                "symbol": sym,
                                "side": side,
                                "entry": float(entry),
                                "exit": float(px),
                                "size_closed": float(sz),
                                "pnl": float(pnl),
                                "ts": _t.time()
                            })
                        except Exception:
                            pass

                        self._safe_log(
                            f"🔚 SIM CLOSE {side.upper()} | entry={entry:.6f} → exit={px:.6f} | "
                            f"sz={sz:.6f} | PnL={pnl:+.2f} USDT | Total={self._sim_pnl_usdt:+.2f}\n"
                        )
                        del lst[i]
                        continue

                    # --- ÉLES ZÁRÁS (LIVE) ---
                    try:
                        import json

                        # lépésközök lekérése
                        try:
                            lot_step, price_step, min_base, min_funds, quote_step = self._mb_get_market_steps(sym)
                        except Exception:
                            lot_step, price_step, min_base, min_funds, quote_step = (0.0001, 0.01, 0.0, 0.0, 0.01)

                        # elérhető egyenlegek (isolated vagy cross)
                        base_avail = 0.0
                        quote_avail = 0.0
                        try:
                            if mode == "isolated":
                                acc = self.exchange.fetch_isolated_accounts() or {}
                                data = acc.get("data", acc) or {}
                                assets = data.get("assets") or []
                                row = next((a for a in assets if (a.get("symbol") or "").upper()==sym.upper()), None)
                                if row:
                                    b = (row.get("baseAsset") or {})
                                    q = (row.get("quoteAsset") or {})
                                    base_avail  = float(b.get("available", b.get("availableBalance", b.get("free", 0))) or 0.0)
                                    quote_avail = float(q.get("available", q.get("availableBalance", q.get("free", 0))) or 0.0)
                            else:
                                acc = self.exchange.fetch_cross_accounts() or {}
                                data = acc.get("data", acc) or {}
                                accounts = data.get("accounts", []) or data.get("accountList", []) or []
                                base_ccy = sym.split("-")[0].upper()
                                quote_ccy = sym.split("-")[1].upper()
                                rb = next((x for x in accounts if (x.get("currency") or x.get("currencyName","")).upper()==base_ccy), None)
                                rq = next((x for x in accounts if (x.get("currency") or x.get("currencyName","")).upper()==quote_ccy), None)
                                if rb:
                                    base_avail = float(rb.get("available", rb.get("availableBalance", rb.get("free", 0))) or 0.0)
                                if rq:
                                    quote_avail = float(rq.get("available", rq.get("availableBalance", rq.get("free", 0))) or 0.0)
                        except Exception:
                            pass

                        raw_pos_size = float(pos.get("size", 0.0))
                        exit_px = float(px or 0.0)

                        # --- küldendő mezők összeállítása oldal szerint ---
                        send_size_base: float | None = None
                        send_funds_quote: float | None = None

                        if close_side == "sell":
                            # long zárás: BASE-t adunk el → size kell; ne lépjük túl az elérhető BASE-t
                            cap = base_avail if base_avail > 0 else raw_pos_size
                            sz = min(raw_pos_size, cap)
                            # lot_step-re padlózás (Decimal-al, float hibák nélkül)
                            sz = self._mb_floor_to_step_dec(float(sz), float(lot_step or 0.0))
                            # minimum ellenőrzés
                            if sz <= 0 or (min_base and float(sz) < float(min_base)):
                                self._safe_log(f"ℹ️ Záró méret a minimum alatt (size={sz:.6f}, minBase={float(min_base) if min_base else 0:g}) – kihagyva.\n")
                                i += 1
                                continue
                            send_size_base = float(sz)
                        else:
                            # short zárás: BASE-t veszünk vissza → funds (QUOTE) kell
                            if exit_px <= 0:
                                self._safe_log("⚠️ Ismeretlen ár BUY záráshoz – kihagyva.\n")
                                i += 1
                                continue
                            # maximálisan vehető BASE a rendelkezésre álló QUOTE-ból
                            buyable_base = (quote_avail / exit_px) if quote_avail > 0 else raw_pos_size
                            sz = min(raw_pos_size, buyable_base)
                            # lot_step-re padlózás
                            sz = self._mb_floor_to_step_dec(float(sz), float(lot_step or 0.0))
                            if sz <= 0 or (min_base and float(sz) < float(min_base)):
                                self._safe_log(f"ℹ️ Záró méret a minimum alatt (size={sz:.6f}, minBase={float(min_base) if min_base else 0:g}) – kihagyva.\n")
                                i += 1
                                continue
                            # funds = sz * ár, lefelé kerekítve quote_step-re; ne lépjük túl a quote_avail-t
                            funds = float(sz) * float(exit_px)
                            funds = self._mb_floor_to_step_dec(float(funds), float(quote_step or 0.0))
                            if quote_avail > 0:
                                funds = min(float(funds), float(quote_avail))
                            if funds <= 0 or (min_funds and float(funds) < float(min_funds)):
                                self._safe_log(f"ℹ️ Záró funds a minimum alatt (funds={funds:.6f}, minFunds={float(min_funds) if min_funds else 0:g}) – kihagyva.\n")
                                i += 1
                                continue
                            send_funds_quote = float(funds)

                        payload = {
                            "mode": mode, "symbol": sym, "side": close_side,
                            "size_base": (send_size_base if send_size_base is not None else None),
                            "funds_quote": (send_funds_quote if send_funds_quote is not None else None),
                            "leverage": lev, "auto_borrow": False, "auto_repay": True
                        }

                        try:
                            self._safe_log(f"🐞 SEND CLOSE: {json.dumps(payload, ensure_ascii=False)}\n")
                        except Exception:
                            self._safe_log(f"🐞 SEND CLOSE: {repr(payload)}\n")

                        resp = self.exchange.place_margin_market_order(
                            mode, sym, close_side,
                            size_base=send_size_base if send_size_base is not None else None,
                            funds_quote=send_funds_quote if send_funds_quote is not None else None,
                            leverage=lev,
                            auto_borrow=False,
                            auto_repay=True
                        )

                        try:
                            self._safe_log(
                                "🐞 RECV CLOSE: " +
                                (json.dumps(resp, ensure_ascii=False) if isinstance(resp, dict) else repr(resp)) + "\n"
                            )
                        except Exception:
                            self._safe_log(f"🐞 RECV CLOSE: {repr(resp)}\n")

                        # válasz vizsgálata
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

                        if str(code) != "200000" or (not oid and not cid):
                            self._safe_log(
                                f"❌ LIVE zárás elutasítva (code={code}) – nincs orderId/clientOid. Teljes resp: {repr(resp)}\n"
                            )
                            i += 1
                            continue

                        order_key = oid or cid
                        self._safe_log(f"✅ LIVE CLOSE {close_side.upper()} elküldve – orderId={order_key}\n")

                        try:
                            open_oid = str(pos.get('oid')) if pos.get('oid') else None
                            if open_oid:
                                self._mb_hist_update_exit(open_oid, px)
                        except Exception:
                            pass

                        # === Fee + nettó PnL ===
                        entry = float(pos.get('entry', 0.0))

                        # ténylegesen küldött mennyiség (size vagy funds/ár)
                        try:
                            if payload.get("size_base") is not None:
                                sent_sz = float(payload["size_base"])
                            elif payload.get("funds_quote") is not None:
                                sent_sz = float(payload["funds_quote"]) / max(px, 1e-12)
                            else:
                                sent_sz = float(pos.get('size', 0.0))
                        except Exception:
                            sent_sz = float(pos.get('size', 0.0))

                        gross = (px - entry) * sent_sz * (1 if side == 'buy' else -1)

                        # tényleges close fee lekérése (ha sikerül)
                        try:
                            if oid:
                                fee_close_act = self._mb_try_fetch_close_fee(str(oid))
                                if fee_close_act and fee_close_act > 0:
                                    pos['fee_close_actual'] = float(fee_close_act)
                        except Exception:
                            pass

                        fee_rate = self._mb_get_taker_fee()
                        f_open, f_close, f_total = self._mb_sum_fee_actual_or_est(pos, px, fee_rate)
                        pnl = gross - f_total

                        self._safe_log(
                            f"🔚 LIVE MIRROR {side.upper()} | entry={entry:.6f} → exit={px:.6f} | "
                            f"sz={sent_sz:.6f} | GROSS={gross:+.4f} | fee_tot={f_total:.4f} | "
                            f"PNL={pnl:+.4f} USDT\n"
                        )

                        with self._mb_lock:
                            self._sim_pnl_usdt += pnl
                            self._pool_balance_quote += pnl
                            # felszabadítjuk a commit + open fee reservet
                            self._pool_used_quote = max(
                                0.0,
                                self._pool_used_quote - (float(pos.get('commit_usdt',0.0)) + float(pos.get('fee_reserved',0.0)))
                            )

                        # History fee total (open+close) frissítése a fee oszlopban
                        try:
                            open_oid = str(pos.get('oid')) if pos.get('oid') else None
                            if open_oid:
                                self._mb_hist_update_exit(open_oid, px, fee_total=f_total)
                        except Exception:
                            pass

                        del lst[i]
                        continue

                    except Exception as e:
                        self._safe_log(f"❌ LIVE zárási hiba: {e}\n")
                        i += 1
                        continue

                    i += 1  # ha nem töröltünk

            # összegzés
            try:
                self._mb_do_summary_once("mb_stop")
            except Exception as e:
                self._safe_log(f"⚠️ Összegzés hiba (stop): {e}\n")

        except Exception as e:
            self._safe_log(f"❌ Stop során hiba: {e}\n")

        # szál lecsatlakoztatás
        try:
            if hasattr(self, "_mb_thread") and self._mb_thread.is_alive():
                self._mb_thread.join(timeout=1.0)
        except Exception:
            pass

        self._mb_stopping = False

    # === MarginBot – fő ciklus, HTF-filter + ATR menedzsment + RSI szűrő ===
    def _mb_worker(self):
        import time, math, pandas as pd

        # --- egyszeri init-ek (ha még nem léteznek) ---
        if not hasattr(self, "_sim_pos_long"):   self._sim_pos_long = []   # list[dict]
        if not hasattr(self, "_sim_pos_short"):  self._sim_pos_short = []  # list[dict]
        if not hasattr(self, "_sim_pnl_usdt"):   self._sim_pnl_usdt = 0.0
        if not hasattr(self, "_sim_history"):    self._sim_history = []
        if not hasattr(self, "_mb_last_bar_ts"): self._mb_last_bar_ts = {}
        if not hasattr(self, "_mb_last_cross_ts"): self._mb_last_cross_ts = 0
        if not hasattr(self, "_mb_last_signal"):   self._mb_last_signal   = "hold"

        # Dinamikus keret (pool) – induláskor felépítjük
        # _pool_balance_quote: a "bot kerete" (USDT), ami PnL-lel nő/csökken
        # _pool_used_quote: nyitott pozikhoz lekötött USDT (rész-zárás csökkenti)
        if not hasattr(self, "_pool_balance_quote") or not hasattr(self, "_pool_used_quote"):
            # induló keret = min(UI keret, VALÓS elérhető QUOTE); ha UI üres → elérhető QUOTE
            try:
                symbol0 = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
                base0, quote0 = split_symbol(symbol0)
            except Exception:
                base0, quote0 = "","USDT"

            ui_budget = float(self._mb_get_float('mb_budget', 0.0) or 0.0)
            dry = bool(self._mb_get_bool('mb_dry', True))
            avail_quote = 0.0
            try:
                if hasattr(self, "_mt_available"):
                    _, avail_quote = self._mt_available(base0, quote0)
            except Exception:
                pass

            # --- Pool init logika: DRY vs LIVE ---
            if dry:
                # DRY: pontosan a megadott költségvetést használjuk, nincs clamp az elérhetőre
                init_pool = max(0.0, ui_budget)
            else:
                # LIVE: továbbra is clampeljük a valós elérhetőre, és jelezzük ha vágás történt
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
            """
            side: 'buy'|'sell'
            entry_px: belépő ár
            size_base: mennyiség (BASE)
            commit_usdt: a keretből ténylegesen lefoglalt USDT (rész-zárásnál arányosan csökken)
            atr_pack: (mul_sl, mul_tp1, mul_tp2, trail_mul, atr_val) vagy None
            fixed_pack: (tpct, spct, trpct) vagy None
            """
            fee_rate = self._mb_get_taker_fee()
            fee_open_est = self._mb_est_fee_quote(entry_px, size_base, fee_rate)
            pos = {
                'side': side,
                'entry': float(entry_px),
                'size': float(size_base),
                'peak': float(entry_px),
                'pnl': 0.0,
                'commit_usdt': float(commit_usdt),
                'fee_open_est': float(fee_open_est),
                'fee_open_actual': 0.0,
                'fee_close_actual': 0.0,
                'fee_reserved': float(fee_open_est),
                'mgmt': 'none'
            }
            # opcionális mezők (pl. orderId)
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
                # lockoljuk a keretet: commit + becsült open fee
                self._pool_used_quote += float(commit_usdt) + float(fee_open_est)

            self._safe_log(
                f"🧪 SIM OPEN {side.upper()} @ {entry_px:.6f} | sz={size_base:.6f} | "
                f"commit={commit_usdt:.2f} | fee≈{fee_open_est:.4f} | "
                f"pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

        def _close_sim_by_index(side: str, idx: int, exit_px: float):
            """Teljes zárás adott indexű pozícióra; PnL visszaír a pool-ba, commit + fee lock felszabadul.
               History: Exit + Fee + PnL oszlopok frissítése (SIM becsléssel / eltárolt értékekkel).
            """
            lst = self._sim_pos_long if side == 'buy' else self._sim_pos_short
            if idx < 0 or idx >= len(lst):
                return

            pos   = lst[idx]
            entry = float(pos.get('entry', 0.0))
            sz    = float(pos.get('size', 0.0))

            # Bruttó PnL (fee nélkül)
            gross = (exit_px - entry) * sz * (1 if side == 'buy' else -1)

            # Fee-k: open (actual ha van, különben est), close (est – SIM), total
            fee_rate = self._mb_get_taker_fee()
            f_open, f_close, f_total = self._mb_sum_fee_actual_or_est(pos, exit_px, fee_rate)

            pnl = gross - f_total

            # Pool frissítés + lockok felszabadítása
            with self._mb_lock:
                self._sim_pnl_usdt   += pnl
                self._pool_balance_quote += pnl
                self._pool_used_quote -= (float(pos.get('commit_usdt', 0.0)) + float(pos.get('fee_reserved', 0.0)))
                self._pool_used_quote  = max(0.0, self._pool_used_quote)

            # SIM history (belső lista)
            try:
                symbol_safe = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
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
                    "ts": _t.time()
                })
            except Exception:
                pass

            # Log
            self._safe_log(
                f"🔚 SIM CLOSE {side.upper()} | entry={entry:.6f} → exit={exit_px:.6f} | "
                f"sz={sz:.6f} | GROSS={gross:+.6f} | fee_tot≈{f_total:.6f} | "
                f"PNL={pnl:+.6f} | Total={self._sim_pnl_usdt:+.2f} | "
                f"pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

            # Trade History UI frissítése (Exit/Fee/PnL)
            try:
                open_oid = str(pos.get('oid')) if pos.get('oid') else None
                if open_oid:
                    self._mb_hist_update_exit(open_oid, exit_px, fee_total=f_total, pnl_final=pnl)
            except Exception:
                pass

            # Pozíció törlése a listából
            del lst[idx]

        def _partial_close_50(pos: dict, side: str, px: float):
            """ATR TP1-nél 50% zár; commit_usdt fele felszabadul; PnL a poolba megy (thread-safe)."""
            if pos.get('half_closed', False):
                return

            entry = float(pos['entry']); sz = float(pos['size'])
            # --- Lépcsőzés valósághűen: lot_step-re padlózva ---
            try:
                symbol_safe = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
            except Exception:
                symbol_safe = None
            try:
                lot_step, _price_step, _min_base, _min_funds, _quote_step = self._mb_get_market_steps(symbol_safe or "BTC-USDT")
            except Exception:
                lot_step = 0.0
            raw_half = sz * 0.5
            close_sz = self._mb_floor_to_step_dec(raw_half, float(lot_step or 0.0))
            if close_sz <= 0:
                # padlózás lenullázta → ne csináljunk semmit
                return
            if sz <= 0:
                return
            pnl = (px - entry) * close_sz * (1 if side == 'buy' else -1)

            # valósághűbb: arányos felszabadítás a ténylegesen zárt méret alapján
            commit_before = float(pos.get('commit_usdt', 0.0))
            try:
                rel_ratio = close_sz / max(sz, 1e-12)
            except Exception:
                rel_ratio = 0.5
            release = commit_before * rel_ratio

            # Kritikus szakasz: PnL / pool / pos mezők
            with self._mb_lock:
                self._sim_pnl_usdt += pnl
                self._pool_balance_quote += pnl
                # pos írások egyben (maradék méret lehet nem lépcsőzött – következő zárásnál úgyis padlózzuk)
                pos.update({'size': sz - close_sz,
                            'commit_usdt': max(0.0, commit_before - release),
                            'half_closed': True})
                self._pool_used_quote = max(0.0, self._pool_used_quote - release)

            # (Opcionális) history bejegyzés a rész-zárásról
            try:
                import time as _t
                try:
                    symbol_safe = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
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
                    "ts": _t.time()
                })
            except Exception:
                pass

            # Log
            self._safe_log(
                f"🔹 PARTIAL 50% | entry={entry:.6f} → exit={px:.6f} | "
                f"zárt={close_sz:.6f} | PnL={pnl:+.2f} | pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

        def _manage_atr_on_pos(pos: dict, last_px: float, atr_val: float) -> bool:
            """
            ATR menedzsment egyetlen pozíción.
            Visszatér: True, ha teljes zárás szükséges.
            """
            side = pos['side']
            # peak frissítés
            if side == 'buy' and last_px > pos['peak']: pos['peak'] = last_px
            if side == 'sell' and last_px < pos['peak']: pos['peak'] = last_px

            # TP1 – egyszeri 50% partial
            tp1 = pos['tp1']
            if not pos.get('half_closed', False):
                if (side == 'buy' and last_px >= tp1) or (side == 'sell' and last_px <= tp1):
                    _partial_close_50(pos, side, last_px)

            # trailing
            peak = pos['peak']; trail_mul = pos.get('trail_mul', 1.0)
            if side == 'buy':
                trail_px = peak - trail_mul*atr_val
                if last_px <= trail_px: return True
            else:
                trail_px = peak + trail_mul*atr_val
                if last_px >= trail_px: return True

            # TP2 vagy hard SL
            tp2 = pos['tp2']; sl = pos['sl']
            if (side == 'buy' and (last_px >= tp2 or last_px <= sl)) or \
               (side == 'sell' and (last_px <= tp2 or last_px >= sl)):
                return True
            return False

        def _manage_fixed_on_pos(pos: dict, last_px: float) -> bool:
            """
            FIX (tp%, sl%, trail%) menedzsment egy pozíción.
            True, ha zárni kell a maradékot.
            """
            side  = pos['side']
            entry = float(pos['entry'])
            sz    = float(pos['size'])
            # peak frissítés
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

        def _live_close_pos(side: str, pos: dict, exit_px: float, *, symbol: str, mode: str, lev: int) -> bool:
            """ÉLES (LIVE) teljes zárás markettel + History EXIT/PNL/fee frissítés. True= siker, False= bukás."""
            try:
                close_side = "sell" if side == "buy" else "buy"
                sz_raw = float(pos.get("size", 0.0))
                if sz_raw <= 0:
                    self._safe_log("ℹ️ Nulla méret – nincs LIVE zárás szükség.\n")
                    return False

                size_to_send = None
                funds_to_send = None

                if close_side == "sell":
                    # long zárás: a valós poziméretből indulunk, NEM clampelünk available-re
                    # (auto_repay=True mellett a tőzsde rendezi a kölcsönt/fee-t)
                    try:
                        if mode == "isolated":
                            acc = self.exchange.fetch_isolated_accounts() or {}
                            row = next((a for a in (acc.get("data", acc) or {}).get("assets", []) if a.get("symbol")==symbol), None)
                            if row:
                                base = row.get("baseAsset", {}) or {}
                                # ha van explicit "total" vagy "positionSize", azt preferáld
                                base_tot = float(base.get("total", base.get("position", base.get("positionSize", 0))) or 0)
                                if base_tot <= 0:
                                    self._safe_log("ℹ️ Nincs zárható BASE a pozícióban (total/position=0).\n")
                                    return False
                                # csak lefelé vágjuk, ha a SIM túlbecsülte
                                sz_raw = min(sz_raw, base_tot)
                        else:
                            # cross esetén is próbálj 'total' jellegű értéket használni, ha elérhető
                            acc = self.exchange.fetch_cross_accounts() or {}
                            # ha nincs megbízható 'total', inkább ne vágd 'available'-re
                            pass
                    except Exception:
                        pass

                    # (opcionális) diag a szaniter előtt:
                    self._safe_log(
                        f"🔎 CLOSE SELL diag | pos.size={pos.get('size')} | sz_raw(before)={sz_raw} | "
                        f"lot_step/minBase={self._mb_get_market_steps(symbol)[:3]}\n"
                    )

                    # sanitizer (SELL: size_base ellenőrzés lépésköz/minimum szerint)
                    size_to_send, _ = self._mb_sanitize_order(
                        symbol=symbol, side="sell", price=exit_px,
                        size_base=sz_raw, funds_quote=None
                    )
                    if size_to_send is None:
                        self._safe_log(f"ℹ️ Zárási méret a lépésköz/minimum alatt (raw={sz_raw:.6f}). Kimarad.\n")
                        return False

                else:
                    # short zárás: BASE-t veszünk vissza → funds (QUOTE) kell; opcionálisan limitáljuk elérhető QUOTE alapján
                    quote_av = None
                    try:
                        if mode == "isolated":
                            acc = self.exchange.fetch_isolated_accounts() or {}
                            row = next((a for a in (acc.get("data", acc) or {}).get("assets", []) if a.get("symbol")==symbol), None)
                            if row:
                                quote = row.get("quoteAsset", {}) or {}
                                quote_av = float(quote.get("available", quote.get("availableBalance", quote.get("free", 0))) or 0)
                        else:
                            acc = self.exchange.fetch_cross_accounts() or {}
                            accounts = (acc.get("data", acc) or {}).get("accounts", []) or (acc.get("data", acc) or {}).get("accountList", [])
                            quote_ccy = symbol.split("-")[1]
                            r = next((x for x in accounts if (x.get("currency") or x.get("currencyName","")).upper()==quote_ccy.upper()), None)
                            if r:
                                quote_av = float(r.get("available", r.get("availableBalance", r.get("free", 0))) or 0)
                    except Exception:
                        quote_av = None

                    if exit_px <= 0:
                        self._safe_log("⚠️ Ismeretlen ár BUY záráshoz – kihagyva.\n")
                        return False

                    if quote_av is not None:
                        buyable_base = quote_av / exit_px if quote_av > 0 else 0.0
                        sz_raw = min(sz_raw, buyable_base)
                        if sz_raw <= 0:
                            self._safe_log("ℹ️ Nincs elég QUOTE a BUY záráshoz.\n")
                            return False

                    # BUY zárás: sanitizer size→funds konverziót végez
                    _sb, _fq = self._mb_sanitize_order(
                        symbol=symbol, side="buy", price=exit_px,
                        size_base=sz_raw, funds_quote=None
                    )
                    funds_to_send = _fq
                    if funds_to_send is None:
                        self._safe_log("ℹ️ BUY close eldobva (funds/minFunds/quote_step check után).\n")
                        return False

                _payload_dbg = {
                    "mode": mode, "symbol": symbol, "side": close_side,
                    "size_base": size_to_send, "funds_quote": funds_to_send, "leverage": lev,
                    "auto_borrow": False, "auto_repay": True
                }
                self._safe_log(f"🐞 SEND CLOSE: {self._mb_pp(_payload_dbg)}\n")

                resp = self.exchange.place_margin_market_order(
                    mode, symbol, close_side,
                    size_base=size_to_send,
                    funds_quote=funds_to_send,
                    leverage=lev,
                    auto_borrow=False,
                    auto_repay=True
                )
                self._safe_log(f"🐞 RECV CLOSE: {self._mb_pp(resp)}\n")

                # válasz kiértékelése
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

                if str(code) != "200000":
                    self._safe_log(f"❌ LIVE close elutasítva (code={code}) – teljes resp: {repr(resp)}\n")
                    return False
                if not oid and not cid:
                    self._safe_log(f"❌ LIVE close válasz orderId nélkül – teljes resp: {repr(resp)}\n")
                    return False

                order_key = oid or cid
                self._safe_log(f"✅ LIVE CLOSE {close_side.upper()} elküldve – orderId={order_key}\n")

                # History EXIT (ár → majd fee/PNL)
                try:
                    open_oid = str(pos.get('oid')) if pos.get('oid') else None
                    if open_oid:
                        self._mb_hist_update_exit(open_oid, exit_px)
                except Exception:
                    pass

                # Close fee tényleges lekérése
                try:
                    if oid:
                        fee_close_act = self._mb_try_fetch_close_fee(str(oid))
                        if fee_close_act and fee_close_act > 0:
                            pos['fee_close_actual'] = float(fee_close_act)
                            self._safe_log(f"💸 LIVE close fee (actual) = {fee_close_act:.6f}\n")
                except Exception:
                    pass

                # PnL véglegesítése + history frissítés
                try:
                    entry = float(pos.get("entry", 0.0))
                    if size_to_send is not None:
                        sz_now = float(size_to_send)
                    else:
                        sz_now = float(funds_to_send) / max(exit_px, 1e-12)

                    gross = (exit_px - entry) * sz_now * (1 if side == 'buy' else -1)

                    fee_rate = self._mb_get_taker_fee()
                    f_open, f_close, f_total = self._mb_sum_fee_actual_or_est(pos, exit_px, fee_rate)
                    pnl_final = gross - f_total

                    if open_oid:
                        self._mb_hist_update_exit(open_oid, exit_px, fee_total=f_total, pnl_final=pnl_final)
                except Exception:
                    pass

                return True

            except Exception as e:
                self._safe_log(f"❌ LIVE zárási hiba: {e}\n")
                return False

        try:
            while self._mb_running:
                try:
                    # --- UI beállítások kiolvasása ---
                    symbol = normalize_symbol(self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)))
                    tf     = self._mb_get_str('mb_tf', '1m')
                    fa     = self._mb_get_int('mb_ma_fast', 9)
                    slw    = self._mb_get_int('mb_ma_slow', 21)
                    sizep  = self._mb_get_float('mb_size_pct', 50.0)
                    inpm   = self._mb_get_str('mb_input_mode', 'quote')
                    mode   = self._mb_get_str('mb_mode', 'isolated')
                    lev    = max(1, self._mb_get_int('mb_leverage', 10))
                    tpct   = self._mb_get_float('mb_tp_pct', 2.0)
                    spct   = self._mb_get_float('mb_sl_pct', 1.0)
                    trpct  = self._mb_get_float('mb_trail_pct', 0.5)
                    cd_s   = self._mb_get_int('mb_cooldown_s', 30)
                    dry    = self._mb_get_bool('mb_dry', True)
                    budget_ui = self._mb_get_float('mb_budget', 0.0)  # csak logoláshoz

                    # RSI / HTF / ATR
                    use_rsi  = getattr(self, "mb_use_rsi", tk.BooleanVar(value=False)).get()
                    rsi_len  = self._mb_get_int('mb_rsi_len', 14)
                    rsi_bmin = self._mb_get_float('mb_rsi_buy_min', 45.0)
                    rsi_bmax = self._mb_get_float('mb_rsi_buy_max', 70.0)
                    rsi_smin = self._mb_get_float('mb_rsi_sell_min', 30.0)
                    rsi_smax = self._mb_get_float('mb_rsi_sell_max', 55.0)

                    use_htf = getattr(self, "mb_use_htf", tk.BooleanVar(value=False)).get()
                    htf_tf  = self._mb_get_str('mb_htf_tf', '1h')

                    use_atr = getattr(self, "mb_use_atr", tk.BooleanVar(value=False)).get()
                    atr_n   = self._mb_get_int('mb_atr_n', 14)
                    mul_sl  = self._mb_get_float('mb_atr_mul_sl', 1.2)
                    mul_tp1 = self._mb_get_float('mb_atr_mul_tp1', 1.5)
                    mul_tp2 = self._mb_get_float('mb_atr_mul_tp2', 2.5)
                    mul_tr  = self._mb_get_float('mb_atr_mul_trail', 0.9)

                    # FIX menedzsment
                    use_fixed = getattr(self, "mb_use_fixed", tk.BooleanVar(value=False)).get()

                    # BREAKOUT
                    use_brk  = getattr(self, "mb_use_brk", tk.BooleanVar(value=False)).get()
                    brk_n    = self._mb_get_int('mb_brk_n', 20)
                    brk_buf  = self._mb_get_float('mb_brk_buf', 0.05)
                    brk_with_trend = getattr(self, "mb_brk_with_trend", tk.BooleanVar(value=True)).get()

                    # kizárás: ha mindkettő ON, ATR elsőbbség
                    if use_fixed and use_atr:
                        use_fixed = False

                    # --- OHLCV ---
                    ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=200)  # type: ignore[arg-type]
                    if not ohlcv:
                        self._safe_log("⚠️ Nincs candle adat.\n")
                        time.sleep(2); continue

                    df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
                    last_ts = int(df['ts'].iloc[-1])
                    key = (symbol, tf)
                    # első ciklusban NE ugorjunk same-bar miatt
                    if getattr(self, "_mb_first_cycle", False):
                        self._mb_first_cycle = False
                    else:
                        if self._mb_last_bar_ts.get(key, 0) == last_ts:
                            time.sleep(2)
                            continue

                    self._mb_last_bar_ts[key] = last_ts

                    closes = df['c'].astype(float).tolist()
                    last_px = float(closes[-1])

                    # valós idejű (ticker) ár – default a candle close
                    last_px_rt = last_px
                    # --- ár érvényesség guard ---
                    if not self._is_pos_num(last_px) or not self._is_pos_num(last_px_rt):
                        self._safe_log("⚠️ Érvénytelen ár (0/NaN) – ciklus kihagyva.\n")
                        time.sleep(2)
                        continue
                    try:
                        rt = float(self.exchange.fetch_last_price(symbol))
                        if rt > 0:
                            last_px_rt = rt
                    except Exception:
                        pass

                    # ADD: egységes élő ár menedzsmenthez/záráshoz
                    px_for_mgmt = last_px_rt if (last_px_rt and last_px_rt > 0) else last_px

                    # (opcionális) eltérés százalék logoláshoz
                    try:
                        drift_pct = abs(last_px_rt - last_px) / max(last_px, 1e-12) * 100.0
                    except Exception:
                        drift_pct = float("nan")

                    # --- Max nyitott pozíció limit (0 = korlátlan) ---
                    try:
                        max_open = int(self.mb_max_open.get() or "0")
                    except Exception:
                        max_open = 0
                    # jelenlegi nyitottak száma (SIM listák, live-ban is tükröződnek)
                    open_now = len(self._sim_pos_long) + len(self._sim_pos_short)

                    atr_val = None
                    if use_atr:
                        atr_series = self._mb_atr(df, n=atr_n)
                        atr_val = float(atr_series.iloc[-1])
                        self._mb_last_atr_val = atr_val 

                    # --- EMA + HTF jel ---
                    closes_for_sig = df['c'].astype(float).tolist()
                    sig_raw, ef_l, es_l = self._mb_signal_from_ema_live(
                        closes_for_sig, fa, slw, last_px_rt=None,
                        atr_eps_mult=None  # UI-ból olvassa a %-ot és átszámolja
                    )
                    trend_htf = 0
                    if use_htf:
                        trend_htf = self._mb_trend_filter(symbol, htf_tf, fa, slw)

                    sig = sig_raw
                    if use_htf:
                        if (sig_raw == 'buy' and trend_htf < 0) or (sig_raw == 'sell' and trend_htf > 0):
                            sig = 'hold'

                    # --- RSI szűrő ---
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

                    # --- Breakout jel ---
                    brk_sig, hh, ll, up_lvl, dn_lvl = ("hold", float("nan"), float("nan"), float("nan"), float("nan"))
                    if use_brk:
                        brk_sig, hh, ll, up_lvl, dn_lvl = self._mb_breakout_signal(df, brk_n, brk_buf)
                        if brk_with_trend and use_htf:
                            if (brk_sig == 'buy' and trend_htf < 0) or (brk_sig == 'sell' and trend_htf > 0):
                                brk_sig = 'hold'

                    # --- Intra-bar (élő ár) breakout / kétirányú shock override ---
                    try:
                        use_live = self._mb_get_bool('mb_use_live', True)

                        if use_live:
                            # küszöbök UI-ból
                            shock_pct = float(self._mb_get_float('mb_live_shock_pct', 1.0))      # %
                            shock_atr_mul = float(self._mb_get_float('mb_live_shock_atr', 1.2))  # ATR×

                            # 1) élő ár (továbbra is az exchange->ticker az elsődleges)
                            #    ha nem megy, fallback a saját fetch_last_price-re
                            try:
                                rt_tmp = float(self.exchange.fetch_last_price(symbol))
                                if rt_tmp > 0:
                                    last_px_rt = rt_tmp
                            except Exception:
                                # marad a candle close ár, ha nem sikerült
                                pass

                            # 2) élő breakout a lezárt gyertyára számolt szinteken
                            live_break_up = (use_brk and not math.isnan(up_lvl) and last_px_rt >= up_lvl)
                            live_break_dn = (use_brk and not math.isnan(dn_lvl) and last_px_rt <= dn_lvl)

                            # 3) kétirányú shock a candle-close-hoz képest (pozitív és negatív is)
                            chg = last_px_rt - last_px
                            chg_pct = (abs(chg) / max(last_px, 1e-12)) * 100.0
                            shock_hit_pct = (chg_pct >= max(0.0, shock_pct))

                            shock_hit_atr = False
                            if atr_val is not None and shock_atr_mul > 0:
                                shock_hit_atr = (abs(chg) >= (shock_atr_mul * atr_val))

                            shock_up = (chg > 0) and (shock_hit_pct or shock_hit_atr)
                            shock_dn = (chg < 0) and (shock_hit_pct or shock_hit_atr)

                            # HTF-irány tisztelete, ha be van kapcsolva
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

                    # --- Kombinált jel (breakout elsőbbség) ---
                    combined_sig = brk_sig if brk_sig in ('buy', 'sell') else sig

                    # --- EXTRA DIAG SNAPSHOT: mindig logoljuk, hogy mi fogja meg a jelet ---
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
                        + f", live_px={'ON' if self._mb_get_bool('mb_use_live', True) else 'OFF'}"
                        + f", cd_left={cd_left}s"
                    )

                    # --- EMA/RSI kapuk: itt definiáljuk, mielőtt a 'reasons' felhasználja ---
                    ema_up = (ef_l > es_l)
                    ema_dn = (ef_l < es_l)
                    rsi_ok_buy = True
                    rsi_ok_sell = True
                    if use_rsi and rsi_val is not None:
                        rsi_ok_buy  = (rsi_bmin <= rsi_val <= rsi_bmax)
                        rsi_ok_sell = (rsi_smin <= rsi_val <= rsi_smax)

                    # Drift limit (opcionális UI: mb_drift_max_pct; ha 0/None → kikapcsolva)
                    drift_ok = True
                    drift_over_txt = None
                    try:
                        drift_max_ui = float(self._mb_get_float('mb_drift_max_pct', 0.0) or 0.0)
                        if drift_max_ui > 0 and drift_pct == drift_pct:  # not NaN
                            drift_ok = (abs(drift_pct) <= drift_max_ui)
                            if not drift_ok:
                                drift_over_txt = f"drift>{drift_max_ui:.2f}%"
                    except Exception:
                        pass

                    # Cooldown
                    cd_ok = True
                    try:
                        now_ts = int(time.time())
                        cd_ok = (now_ts - self._mb_last_cross_ts) >= cd_s
                    except Exception:
                        pass

                    # HTF blokkolás felismerése (ha a nyers EMA jel irányos volt, de HTF miatt hold lett)
                    htf_block = (use_htf and sig_raw in ('buy','sell') and (sig == 'hold'))

                    # okok gyűjtése
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

                    # --- LOG: állapot + jel + filter snapshot ---
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
                    if drift_pct == drift_pct:  # not NaN
                        log_line += f" drift={drift_pct:.2f}%"
                    log_line += f" | POOL used/bal={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}"
                    log_line += f" | OPEN={open_now}/{('∞' if max_open==0 else max_open)}"
                    # egy sorban: jel + filter snapshot
                    self._safe_log(log_line.rstrip() + f"  → {combined_sig} | {filters_line}\n")

                    # ha hold, írjuk ki a konkrét okokat is (ha vannak)
                    if combined_sig in (None, "", "hold") and reasons:
                        self._safe_log("  ↳ hold reasons: " + ",".join(reasons) + "\n")

                    # BUY-ok kezelése
                    i = 0
                    while i < len(self._sim_pos_long):
                        pos = self._sim_pos_long[i]
                        need_close = False
                        if pos.get('mgmt') == 'atr' and atr_val is not None:
                            need_close = _manage_atr_on_pos(pos, px_for_mgmt, atr_val)
                        elif pos.get('mgmt') == 'fixed':
                            need_close = _manage_fixed_on_pos(pos, px_for_mgmt)
                        # ha zárni kell
                        if need_close:
                            if dry:
                                _close_sim_by_index('buy', i, px_for_mgmt)
                            else:
                                ok = _live_close_pos('buy', pos, px_for_mgmt, symbol=symbol, mode=mode, lev=lev)
                                if ok:
                                    _close_sim_by_index('buy', i, px_for_mgmt)   # csak siker esetén tükörzárás
                                else:
                                    self._safe_log("❗ LIVE zárás sikertelen – a pozíció nyitva marad.\n")
                                    i += 1
                                    continue
                            continue  # ne növeld i-t, mert a lista rövidebb lett
                        i += 1

                    # SELL-ek kezelése
                    i = 0
                    while i < len(self._sim_pos_short):
                        pos = self._sim_pos_short[i]
                        need_close = False
                        if pos.get('mgmt') == 'atr' and atr_val is not None:
                            need_close = _manage_atr_on_pos(pos, px_for_mgmt, atr_val)
                        elif pos.get('mgmt') == 'fixed':
                            need_close = _manage_fixed_on_pos(pos, px_for_mgmt)
                        if need_close:
                            if dry:
                                _close_sim_by_index('sell', i, px_for_mgmt)
                            else:
                                ok = _live_close_pos('sell', pos, px_for_mgmt, symbol=symbol, mode=mode, lev=lev)
                                if ok:
                                    _close_sim_by_index('sell', i, px_for_mgmt)
                                else:
                                    self._safe_log("❗ LIVE zárás sikertelen – a pozíció nyitva marad.\n")
                                    i += 1
                                    continue
                            continue
                        i += 1

                    # --- ÚJ NYITÁS (cooldown + pool limit) ---
                    now = int(time.time())
                    pause_new = self._mb_get_bool("mb_pause_new", False)
                    if combined_sig in ('buy','sell') and (now - self._mb_last_cross_ts >= cd_s):
                        if pause_new:
                            self._safe_log(f"⏸️ Új nyitás szüneteltetve (Checkbox). Jel ({combined_sig}) átugorva.\n")
                            opened = False
                            time.sleep(1)
                            continue
                        # Max pozíció guard
                        if max_open > 0 and open_now >= max_open:
                            self._safe_log(
                                f"⏸ Max pozíció elérve ({open_now}/{max_open}) – új nyitás átugorva.\n"
                            )
                            opened = False
                            # kis szusszanás, aztán folytatja a ciklust – zárások/menedzsment ettől független
                            time.sleep(1)
                            continue

                        # friss ticker csak nyitás előtt / vagy LIVE módban
                        try:
                            rt = float(self.exchange.fetch_last_price(symbol))
                            if rt > 0:
                                last_px_rt = rt
                        except Exception:
                            pass

                        # szabad keret
                        free_pool = max(0.0, self._pool_balance_quote - self._pool_used_quote)

                        # UI size% normalizálása
                        sizep_to_use = max(0.0, min(100.0, float(sizep)))

                        # mindig inicializáljuk ezeket
                        size = None          # BASE mennyiség (BASE módban)
                        funds = None         # QUOTE összeg (QUOTE módban)
                        open_size = 0.0
                        commit_usdt = 0.0
                        nominal_q = 0.0

                        # max felhasználható QUOTE (USDT) erre a trade-re
                        max_quote_for_trade = free_pool * (sizep_to_use / 100.0)

                        if max_quote_for_trade <= 0.0:
                            self._safe_log("ℹ️ Nincs szabad pool a nyitáshoz (keret limit). Kimarad.\n")
                        else:
                            if inpm == "quote":
                                # valós lépésközök a piactól
                                _lot_step, _price_step, _, _, _ = self._mb_get_market_steps(symbol)
                                ord = self._mb_calc_order_qty(
                                    side=combined_sig,
                                    price=last_px_rt,
                                    pool_free=free_pool,          # mindig a SZABAD poolból
                                    size_pct=sizep_to_use,
                                    leverage=lev,
                                    mode="quote",
                                    lot_step=_lot_step,
                                    price_step=_price_step
                                )
                                open_size   = float(ord["qty_base"])
                                commit_usdt = float(ord["commit_quote"])     # ezt zároljuk a poolból (margin)
                                nominal_q   = float(ord["nominal_quote"])
                                size  = None
                                funds = commit_usdt
                            else:
                                # BASE mód – régi számoló
                                size, funds = self._mb_compute_size(
                                    symbol, combined_sig, last_px_rt, sizep_to_use, inpm, mode, lev,
                                    budget_quote=max_quote_for_trade
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

                            # --- size/funds kerekítés + minimum ellenőrzés a küldés ELŐTT ---
                            lot_step, price_step, min_base, min_funds, quote_step = self._mb_get_market_steps(symbol)
                            open_size = self._mb_floor_to_step_dec(open_size, lot_step)

                            # log
                            self._safe_log(
                                f"📈 Jel: {combined_sig.upper()} | px={last_px_rt:.6f} | size%={sizep_to_use:.2f} | "
                                f"nominal={nominal_q:.2f} | commit={commit_usdt:.2f} | free_pool={free_pool:.2f} | "
                                f"lev={lev} | mode={mode} dry={dry}\n"
                            )

                            # nyitás feltétele
                            opened = False
                            if commit_usdt <= 0 or (combined_sig == 'sell' and open_size <= 0):
                                self._safe_log("ℹ️ Nulla méret / nincs keret – nincs nyitás.\n")
                            else:
                                if dry:
                                    # === SIM: ugyanaz a szigor, mint LIVE ===
                                    size_to_send = None
                                    funds_to_send = None
                                    if combined_sig == 'buy':
                                        # LIVE-ban is a nominális (lev*commit) megy 'funds'-ként → ugyanígy SIM-ben:
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
                                            # végrehajtott méret = funds / ár, lot_step-re padlózva
                                            size_to_send = self._mb_floor_to_step_dec(
                                                float(funds_to_send) / max(last_px_rt, 1e-12), float(lot_step or 0.0)
                                            )
                                            if min_base and size_to_send < float(min_base):
                                                self._safe_log("ℹ️ SIM BUY eldobva (méret < minBase a padlózás után).\n")
                                                size_to_send = None
                                    else:  # 'sell'
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
                                        # SIM commit: BUY-nál nominális/lev, SELL-nél size*price/lev
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
                                    # --- NYITÁS: LIVE ág (BUY → funds, SELL → size) ---
                                    try:
                                        auto_b = getattr(self, "mb_autob", None)
                                        auto_borrow = bool(auto_b.get()) if auto_b else False

                                        # BUY: funds_quote, SELL: size_base (sanitizer-rel)
                                        size_to_send = None
                                        funds_to_send = None

                                        if combined_sig == 'buy':
                                            # funds = teljes nominális (lev*commit), majd sanitizer
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

                                        # --- ha a sanitizer eldobta → log + ugorjunk tovább
                                        if (combined_sig == 'buy' and not funds_to_send) or (combined_sig == 'sell' and not size_to_send):
                                            self._safe_log("ℹ️ Sanitizer eldobta a nyitást (min/step) – kihagyva.\n")
                                            opened = False
                                            continue
                                        else:
                                            _payload_dbg = {
                                                "mode": mode, "symbol": symbol, "side": combined_sig,
                                                "size_base": size_to_send, "funds_quote": funds_to_send,
                                                "leverage": lev, "auto_borrow": auto_borrow
                                            }
                                            self._safe_log(f"🐞 SEND OPEN: {self._mb_pp(_payload_dbg)}\n")
                                            resp = self.exchange.place_margin_market_order(
                                                mode, symbol, combined_sig,
                                                size_base=size_to_send,
                                                funds_quote=funds_to_send,
                                                leverage=lev,
                                                auto_borrow=auto_borrow
                                            )

                                        # --- TEMP DEBUG: pontosan mit kaptunk vissza? ---
                                        self._safe_log(f"🐞 RECV OPEN: {self._mb_pp(resp)}\n")
                                        # --- Válasz értékelése (KuCoin: success '200000') ---
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

                                            # --- KIEGÉSZÍTÉS: tényleges commit + size a sanitizer utáni értékekből ---
                                            try:
                                                lot_step_now, _price_step_now, _mb_min_base_now, _mb_min_funds_now, _quote_step_now = self._mb_get_market_steps(symbol)
                                            except Exception:
                                                lot_step_now = 0.0

                                            if funds_to_send is not None:
                                                # BUY: valós margin = funds / lev
                                                commit_real = float(funds_to_send) / max(lev, 1)
                                                size_now = self._sdiv(float(funds_to_send), last_px_rt, 0.0)
                                                # csak diag/konzisztencia kedvéért padlózzuk a size-ot is
                                                size_now = self._mb_floor_to_step_dec(size_now, float(lot_step_now or 0.0))
                                            else:
                                                # SELL: valós margin = (size * ár) / lev
                                                size_now = float(size_to_send)
                                                commit_real = self._sdiv(size_now * float(last_px_rt), lev, 0.0)
                                            # History + SIM csak siker esetén
                                            _size_now = (size_to_send if size_to_send is not None else (float(funds_to_send)/max(last_px_rt,1e-12)))
                                            _fee_rate = self._mb_get_taker_fee()
                                            _fee_open_est = self._mb_est_fee_quote(last_px_rt, size_now, _fee_rate)

                                            # --- ÚJ: nyitáskori becsült PnL (rt árhoz képest), fee-vel csökkentve
                                            pnl_est = None
                                            try:
                                                rt_now = float(self.exchange.fetch_last_price(symbol))
                                                if rt_now > 0:
                                                    gross = (rt_now - last_px_rt) * size_now * (1 if combined_sig == 'buy' else -1)
                                                    pnl_est = gross - float(_fee_open_est)
                                            except Exception:
                                                pass

                                            self._mb_hist_add_open(
                                                order_id=str(order_key),
                                                side=combined_sig, entry=last_px_rt,
                                                size=size_now,
                                                lev=lev, fee=float(_fee_open_est),
                                                pnl_est=pnl_est
                                            )
                                            # SIM/STATE – fee reserving a tényleges commit alapján
                                            _open_sim(
                                                combined_sig, last_px_rt,
                                                size_now, commit_real,
                                                atr_pack=(mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val) if (use_atr and atr_val is not None) else None,
                                                fixed_pack=(tpct, spct, trpct) if use_fixed else None,
                                                oid=str(order_key),
                                            )
                                            opened = True

                                    except Exception as e:
                                        self._safe_log(f"❌ LIVE order hiba: {e}\n")

                            if opened:
                                self._mb_last_cross_ts = now
                                self._mb_last_signal   = combined_sig

                    # --- TF-hez igazított alvás ---
                    tf_sec = {
                        "1m":60, "3m":180, "5m":300, "15m":900, "30m":1800,
                        "1h":3600, "2h":7200, "4h":14400, "6h":21600,
                        "8h":28800, "12h":43200, "1d":86400
                    }.get(tf, 30)
                    _sleep_total = max(2, min(30, tf_sec // 3))
                    for _ in range(int(_sleep_total)):
                        if not self._mb_running:
                            break
                        time.sleep(1)

                except Exception as e:
                    msg = str(e)
                    # tipikus rate limit / hálózati zaj szűrése
                    if "429" not in msg and "rate" not in msg.lower():
                        self._safe_log(f"❌ Bot hiba: {e}\n")
                    time.sleep(2)

        finally:
            self._mb_running = False
            was_manual = getattr(self, "_mb_stopping", False)

            if not was_manual:
                # csak akkor írjon, ha még nem volt összegzés
                self._mb_do_summary_once("_mb_worker")
            else:
                # manuális stopnál a summary-t már a mb_stop intézte
                # itt csak a jelzőt engedjük el
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

    # ---------- Jel-generátor: KIZÁRÓLAG EMA KERESZTEZÉS (Refaktorált) ----------
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
        Optimalizált EMA jel: Kizárólag KERESZTEZÉS alapján (edge-trigger),
        a hiszterézis sáv (zajszűrő) tiszteletben tartásával.
        Eltávolítva a "meredekség" (slope) alapú jelzés a zaj csökkentése érdekében.

        Visszaad: (sig, ema_fast_last, ema_slow_last)
        """
        import pandas as pd

        s = pd.Series(series, dtype="float64").copy()
        if len(s) < max(fast, slow) + 2:
            return "hold", float("nan"), float("nan")

        # élő (intrabar) ár beégetése (opcionális, de a jelenlegi logikában benne volt)
        if last_px_rt is not None and last_px_rt > 0:
            s.iloc[-1] = float(last_px_rt)

        ema_f = s.ewm(span=fast, adjust=False).mean()
        ema_s = s.ewm(span=slow, adjust=False).mean()

        ef_p, ef_l = float(ema_f.iloc[-2]), float(ema_f.iloc[-1])
        es_p, es_l = float(ema_s.iloc[-2]), float(ema_s.iloc[-1])

        diff_prev = ef_p - es_p                 # előző diff (EF-ES)
        diff_now  = ef_l - es_l                 # aktuális diff

        # ---- Hysteresis (Zajszűrő sáv) ----
        if atr_eps_mult is None:
            try:
                # Az "EMA filter Hyst %" értéket olvassuk a GUI-ból
                ui_pct = float(self.mb_ema_hyst_pct.get())
                atr_eps_mult = max(0.0, ui_pct) / 100.0
            except Exception:
                atr_eps_mult = 0.0 # Alapértelmezett 0, ha nincs UI

        atr_last = float(getattr(self, "_mb_last_atr_val", 0.0))
        px_last  = float(s.iloc[-1])

        # Hysteresis sáv diff-hez (ár egységben): ATR * ui%
        band = (atr_last * atr_eps_mult) if (atr_last > 0 and atr_eps_mult > 0 and px_last > 0) else 0.0
        up_th =  +band
        dn_th =  -band

        # Keresztezés detektálás (edge-trigger)
        # Szigorúbb keresztezés: az előző értéknek a sáv TÚLOLDALÁN kellett lennie.
        crossed_up   = (diff_prev <= dn_th) and (diff_now > up_th)
        crossed_down = (diff_prev >= up_th) and (diff_now < dn_th)

        # Döntés: Kizárólag keresztezés alapján
        sig = "hold"
        if crossed_up:
            sig = "buy"
        elif crossed_down:
            sig = "sell"
        # Ha nincs keresztezés, a 'sig' marad "hold"
        
        # Opcionális invertálás
        if invert is None:
            try:
                invert = bool(self.mb_invert_ema.get())
            except Exception:
                invert = False
        if invert:
            sig = "buy" if sig == "sell" else ("sell" if sig == "buy" else "hold")

        return sig, ef_l, es_l

    # ---------- HTF trend filter (HOSSZÚ fölötte = bull) ----------
    def _mb_trend_filter(self, symbol: str, tf: str = "1h", fast: int = 20, slow: int = 50) -> int:
        """+1 bull, -1 bear, 0 semleges – magasabb idősík trendje a HOSSZÚ SZERINT.
           Bull, ha slow > fast; Bear, ha slow < fast.
        """
        try:
            ohlcv = self.exchange.fetch_ohlcv(symbol, tf, limit=max(slow*2, 120))  # type: ignore[arg-type]
            if not ohlcv:
                return 0
            import pandas as pd
            df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
            s = df['c'].astype(float)
            ema_f = s.ewm(span=fast, adjust=False).mean().iloc[-1]
            ema_s = s.ewm(span=slow, adjust=False).mean().iloc[-1]
            if ema_s > ema_f: return +1   # long fölötte → bull
            if ema_s < ema_f: return -1   # long alatta → bear
            return 0
        except Exception:
            return 0

    # ---------- ATR számítás ----------
    def _mb_atr(self, df, n: int = 14):
        """Classic ATR pandas-szal: True Range -> EMA."""
        import pandas as pd
        h = df['h'].astype(float); l = df['l'].astype(float); c = df['c'].astype(float)
        prev_c = c.shift(1)
        tr = pd.concat([(h-l).abs(), (h-prev_c).abs(), (l-prev_c).abs()], axis=1).max(axis=1)
        atr = tr.ewm(span=n, adjust=False).mean()
        return atr

    # ---------- RSI Képlet ----------
    def _mb_rsi(self, series, n: int = 14):
        """RSI klasszikus képlettel (EMA-s simítással). Visszaad: pandas Series."""
        import pandas as pd
        s = pd.Series(series, dtype='float64')
        delta = s.diff()

        gain = delta.clip(lower=0.0)
        loss = -delta.clip(upper=0.0)

        # EMA-s átlagok – stabilabb, mint a sima SMA
        avg_gain = gain.ewm(alpha=1.0/n, adjust=False).mean()
        avg_loss = loss.ewm(alpha=1.0/n, adjust=False).mean()

        rs = avg_gain / avg_loss.replace(0, 1e-12)
        rsi = 100 - (100 / (1 + rs))
        return rsi

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
            leverage = max(1, min(leverage, 10 if mode == 'isolated' else 5))
            base, quote = split_symbol(symbol)

            # gyors készlet-lekérés (ha van helper)
            avail_base, avail_quote = (0.0, 0.0)
            if hasattr(self, "_mt_available"):
                avail_base, avail_quote = self._mt_available(base, quote)

            pct = max(0.0, min(100.0, float(size_pct))) / 100.0
            budget_quote = float(budget_quote or 0.0)

            if input_mode == 'quote':
                # döntés a cap_quote-ról
                dry = bool(self._mb_get_bool('mb_dry', True))
                auto_borrow = bool(getattr(self, 'mb_autob', tk.BooleanVar(value=False)).get())

                if dry or auto_borrow:
                    cap_quote = budget_quote if budget_quote > 0 else avail_quote
                else:
                    cap_quote = min(avail_quote, budget_quote) if budget_quote > 0 else avail_quote

                funds = max(0.0, cap_quote * pct)
                return (None, round(funds, 4)) if funds > 0 else (None, None)

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
        side: str,              # "buy" | "sell"
        price: float,           # aktuális ár
        pool_free: float,       # szabad QUOTE (USDT) a pooledben
        size_pct: float,        # UI % (pl. 50)
        leverage: float,        # UI tőkeáttét (pl. 10)
        mode: str = "quote",    # UI "mód" – itt főleg 'quote'
        base_free: float = 0.0, # csak ha 'base' módban használod
        lot_step: float = 0.0001,
        price_step: float = 0.01,
    ):
        """
        KuCoin-szerű számítás:
          commit_quote = pool_free * pct
          nominal_quote = commit_quote * leverage
          qty_base = nominal_quote / price
        A visszaadott 'commit_quote' vonódik le a pooledből (lock), a 'qty_base' megy az orderbe.
        """
        pct = max(0.0, min(100.0, float(size_pct))) / 100.0
        mode_ui = None
        try:
            mode_ui = self.mb_mode.get()
        except Exception:
            pass
        margin_mode = mode_ui if mode_ui in ("isolated","cross") else ("isolated" if mode!="cross" else "cross")
        lev_cap = 10.0 if margin_mode == "isolated" else 5.0
        lev = max(1.0, min(float(leverage), lev_cap))

        # --- ár-guard: ha az ár nem pozitív/NaN → üres mennyiséget adunk vissza
        try:
            p_ok = float(price) > 0 and float(price) == float(price)  # not NaN
        except Exception:
            p_ok = False
        if not p_ok:
            return {
                "side": side,
                "qty_base": 0.0,
                "commit_quote": 0.0,
                "nominal_quote": 0.0,
                "lev": lev,
                "price": 0.0
            }

        if mode == "quote":
            commit_quote = pool_free * pct                 # saját tőke (margin)
            nominal_quote = commit_quote * lev             # tényleges pozíció érték
            qty_base = nominal_quote / max(price, 1e-12)
        else:
            # BASE módnál hagyjuk meg a régi logikát – itt csak durván számolunk
            commit_quote = base_free * pct * price
            nominal_quote = commit_quote * lev
            qty_base = base_free * pct * lev

        qty_base = max(self._mb_floor_to_step_dec(qty_base, float(lot_step or 0.0)), 0.0)
        # price rounding: ha price_step == 0 vagy hibás, ne osszunk vele
        px_rounded = price
        try:
            step = float(price_step or 0.0)
            if step > 0:
                px_rounded = round(price / step) * step
        except Exception:
            pass
        return {
            "side": side,
            "qty_base": qty_base,
            "commit_quote": commit_quote,
            "nominal_quote": nominal_quote,
            "lev": lev,
            "price": px_rounded
        }

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
          1) margin bot kulturált leállítása (mb_stop),
          2) futó frissítések megvárása nem-blokkoló módon,
          3) végül ablak bezárása.
        """
        if getattr(self, "_closing", False):
            return
        self._closing = True
        try:
            self._safe_log("🧹 Bezárás kérése – bot leállítása…\n")
        except Exception:
            pass

        # 1) margin bot leállítása, ha fut
        try:
            if getattr(self, "_mb_running", False):
                self.mb_stop()
        except Exception as e:
            try: self._safe_log(f"⚠️ mb_stop hiba: {e}\n")
            except Exception: pass

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

    def _mb_try_fetch_close_fee(self, close_order_id: str) -> float:
        """
        Megpróbáljuk kinyerni a TÉNYLEGES díjat a close order-ből / fill-ekből.
        Ha nincs API támogatás, 0.0-t ad vissza (ilyenkor marad az estimate).
        """
        try:
            ex = getattr(self, "exchange", None)
            if not ex or not close_order_id:
                return 0.0
            # próbálkozások wrapper függvényekkel
            # 1) közvetlen trade-fills by order
            if hasattr(ex, "get_margin_fills_by_order"):
                fills = ex.get_margin_fills_by_order(close_order_id) or []
            elif hasattr(ex, "get_order_fills"):
                fills = ex.get_order_fills(close_order_id) or []
            elif hasattr(ex, "fetch_order_trades"):
                # egyes ccxt-s wrapper-ek
                fills = ex.fetch_order_trades(close_order_id) or []
            else:
                fills = []
            fee_sum = 0.0
            for f in (fills or []):
                # kucoin: feeCurrency, fee
                val = f.get("fee") or f.get("feeCost") or 0
                fee_sum += float(val)
            return max(0.0, float(fee_sum))
        except Exception:
            return 0.0
# ==================== BACKTEST TAB (ÚJ) ====================

import math
import threading
from dataclasses import dataclass
from typing import Optional, List, Dict, Any

@dataclass
class BacktestParams:
    symbol: str
    timeframe: str
    limit: int
    short_ma: int
    long_ma: int
    fee_bps: float         # taker fee bps (pl. 8 bps = 0.08%)
    leverage: float        # 1–10 (cross max 5, isolated max 10 – csak validáljuk)
    use_short: bool        # Engedélyezzük-e shortot
    sl_pct: float          # Stop loss % (pl. 1.5 → 1.5%)
    tp_pct: float          # Take profit % (pl. 3.0 → 3.0%)
    trail_pct: float       # Trailing stop % (0 = off)
    cooldown_bars: int     # Belépések közti minimum bar-szám
    size_mode: str         # 'quote_pct' | 'fixed_quote'
    size_value: float      # pl. 20 (%), vagy 100.0 (USDT)
    initial_equity: float  # kezdőtőke USDT-ben

class BacktestTab:
    """
    MA crossover alapú backtest fül. 
    A szimuláció long-only vagy long+short módban fut, SL/TP/Trailing és cooldown támogatással.
    """
    def __init__(self, master, nb, exchange_provider, log_fn):
        """
        master: Tk parent
        nb: ttk.Notebook
        exchange_provider: callable -> visszaadja a self.exchange objektumot (KucoinSDKWrapper vagy None)
        log_fn: callable(str) log hozzáadásához
        """
        self.master = master
        self.nb = nb
        self.get_exchange = exchange_provider
        self.log = log_fn

        # Fül + layout
        import tkinter as tk
        from tkinter import ttk, scrolledtext
        self.tab = ttk.Frame(nb)
        nb.add(self.tab, text="Backtest")

        # ---- beállítások panel
        left = ttk.Labelframe(self.tab, text="Beállítások", padding=10)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)

        # sor: symbol, timeframe, limit
        ttk.Label(left, text="Szimbólum").grid(row=0, column=0, sticky='w')
        self.e_symbol = ttk.Entry(left, width=14)
        self.e_symbol.insert(0, "SOL-USDT")
        self.e_symbol.grid(row=0, column=1, padx=6)

        ttk.Label(left, text="Idősík").grid(row=1, column=0, sticky='w')
        self.cb_tf = ttk.Combobox(left, values=["1m","3m","5m","15m","30m","1h","2h","4h","6h","8h","12h","1d"], width=10, state='readonly')
        self.cb_tf.set("5m")
        self.cb_tf.grid(row=1, column=1, padx=6)

        ttk.Label(left, text="Gyertyák száma").grid(row=2, column=0, sticky='w')
        self.sp_limit = ttk.Spinbox(left, from_=100, to=20000, width=8)
        self.sp_limit.delete(0, 'end'); self.sp_limit.insert(0, "1500")
        self.sp_limit.grid(row=2, column=1, padx=6)

        ttk.Separator(left).grid(row=3, column=0, columnspan=2, sticky='we', pady=6)

        # sor: MA-k
        ttk.Label(left, text="Rövid MA").grid(row=4, column=0, sticky='w')
        self.sp_short = ttk.Spinbox(left, from_=2, to=500, width=8)
        self.sp_short.delete(0,'end'); self.sp_short.insert(0,"20")
        self.sp_short.grid(row=4, column=1, padx=6)

        ttk.Label(left, text="Hosszú MA").grid(row=5, column=0, sticky='w')
        self.sp_long = ttk.Spinbox(left, from_=5, to=1000, width=8)
        self.sp_long.delete(0,'end'); self.sp_long.insert(0,"50")
        self.sp_long.grid(row=5, column=1, padx=6)

        ttk.Separator(left).grid(row=6, column=0, columnspan=2, sticky='we', pady=6)

        # sor: fee, lev, short
        ttk.Label(left, text="Taker fee (bps)").grid(row=7, column=0, sticky='w')
        self.sp_fee = ttk.Spinbox(left, from_=0, to=50, width=8)
        self.sp_fee.delete(0,'end'); self.sp_fee.insert(0,"8")
        self.sp_fee.grid(row=7, column=1, padx=6)

        ttk.Label(left, text="Leverage").grid(row=8, column=0, sticky='w')
        self.sp_lev = ttk.Spinbox(left, from_=1, to=10, width=8)
        self.sp_lev.delete(0,'end'); self.sp_lev.insert(0,"3")
        self.sp_lev.grid(row=8, column=1, padx=6)

        self.var_short = tk.BooleanVar(value=True)
        ttk.Checkbutton(left, text="Short engedélyezve (margin)", variable=self.var_short).grid(row=9, column=0, columnspan=2, sticky='w')

        ttk.Separator(left).grid(row=10, column=0, columnspan=2, sticky='we', pady=6)

        # sor: SL/TP/Trail
        ttk.Label(left, text="SL %").grid(row=11, column=0, sticky='w')
        self.sp_sl = ttk.Spinbox(left, from_=0.0, to=50.0, increment=0.1, width=8)
        self.sp_sl.delete(0,'end'); self.sp_sl.insert(0,"1.5")
        self.sp_sl.grid(row=11, column=1, padx=6)

        ttk.Label(left, text="TP %").grid(row=12, column=0, sticky='w')
        self.sp_tp = ttk.Spinbox(left, from_=0.0, to=50.0, increment=0.1, width=8)
        self.sp_tp.delete(0,'end'); self.sp_tp.insert(0,"3.0")
        self.sp_tp.grid(row=12, column=1, padx=6)

        ttk.Label(left, text="Trailing %").grid(row=13, column=0, sticky='w')
        self.sp_trail = ttk.Spinbox(left, from_=0.0, to=20.0, increment=0.1, width=8)
        self.sp_trail.delete(0,'end'); self.sp_trail.insert(0,"0.0")
        self.sp_trail.grid(row=13, column=1, padx=6)

        ttk.Label(left, text="Cooldown (bar)").grid(row=14, column=0, sticky='w')
        self.sp_cool = ttk.Spinbox(left, from_=0, to=200, width=8)
        self.sp_cool.delete(0,'end'); self.sp_cool.insert(0,"3")
        self.sp_cool.grid(row=14, column=1, padx=6)

        ttk.Separator(left).grid(row=15, column=0, columnspan=2, sticky='we', pady=6)

        # sor: méretezés
        ttk.Label(left, text="Méret mód").grid(row=16, column=0, sticky='w')
        self.cb_size_mode = ttk.Combobox(left, values=["quote_pct","fixed_quote"], width=12, state='readonly')
        self.cb_size_mode.set("quote_pct")
        self.cb_size_mode.grid(row=16, column=1, padx=6)

        ttk.Label(left, text="Méret érték").grid(row=17, column=0, sticky='w')
        self.e_size_val = ttk.Entry(left, width=10)
        self.e_size_val.insert(0, "20")  # 20%
        self.e_size_val.grid(row=17, column=1, padx=6)

        ttk.Label(left, text="Kezdő tőke (USDT)").grid(row=18, column=0, sticky='w')
        self.e_init_eq = ttk.Entry(left, width=10)
        self.e_init_eq.insert(0, "1000")
        self.e_init_eq.grid(row=18, column=1, padx=6)

        ttk.Button(left, text="Backtest futtatása", command=self.run_backtest_thread).grid(row=19, column=0, columnspan=2, pady=10, sticky='we')

        # ---- jobb oldal: eredmények + ábra
        right = ttk.Frame(self.tab)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,10), pady=10)

        top = ttk.Labelframe(right, text="Eredmények", padding=8)
        top.pack(fill=tk.X)
        self.lbl_summary = ttk.Label(top, text="–")
        self.lbl_summary.pack(anchor='w')

        # táblázat a trade-ekhez (rövid kivonat)
        cols = ("#","entry_time","side","entry","exit","ret_%","eq")
        self.tbl = ttk.Treeview(right, columns=cols, show='headings', height=10)
        for c, w in zip(cols, (60,160,80,100,100,80,120)):
            self.tbl.heading(c, text=c); self.tbl.column(c, width=w, anchor='center')
        self.tbl.pack(fill=tk.BOTH, expand=False, pady=(6,8))

        # Matplotlib chart – equity
        from matplotlib.figure import Figure
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
        import matplotlib.dates as mdates
        self._mdates = mdates
        self.fig = Figure(figsize=(7,3), dpi=100)
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=right)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # log panel
        lf = ttk.Labelframe(right, text="Log", padding=6)
        lf.pack(fill=tk.BOTH, expand=False, pady=(8,0))
        self.log_area = scrolledtext.ScrolledText(lf, wrap='word', height=7)
        self.log_area.pack(fill=tk.BOTH, expand=True)

    # ---------- UI helpers ----------
    def _get_params(self) -> BacktestParams:
        return BacktestParams(
            symbol = normalize_symbol(self.e_symbol.get()),
            timeframe = self.cb_tf.get().strip(),
            limit = int(self.sp_limit.get()),
            short_ma = int(self.sp_short.get()),
            long_ma = int(self.sp_long.get()),
            fee_bps = float(self.sp_fee.get()),
            leverage = float(self.sp_lev.get()),
            use_short = bool(self.var_short.get()),
            sl_pct = float(self.sp_sl.get()),
            tp_pct = float(self.sp_tp.get()),
            trail_pct = float(self.sp_trail.get()),
            cooldown_bars = int(self.sp_cool.get()),
            size_mode = self.cb_size_mode.get(),
            size_value = float(self.e_size_val.get()),
            initial_equity = float(self.e_init_eq.get()),
        )

    def _append_log(self, msg: str):
        import tkinter as tk
        self.log_area.insert(tk.END, msg + "\n"); self.log_area.see(tk.END)
        self.log(msg)

    # ---------- Futás külön szálon ----------
    def run_backtest_thread(self):
        t = threading.Thread(target=self._run_backtest, daemon=True)
        t.start()

    def _run_backtest(self):
        try:
            p = self._get_params()
            self._append_log(f"Backtest indul: {p.symbol}, {p.timeframe}, limit={p.limit}, MA({p.short_ma},{p.long_ma})")

            # Gyertyák
            exch = self.get_exchange()
            ohlcv = []
            if exch is not None:
                try:
                    ohlcv = exch.fetch_ohlcv(p.symbol, p.timeframe, p.limit)  # a te wrappered
                except Exception as e:
                    self._append_log(f"SDK hiba, REST fallback próbálkozás: {e}")
            if not ohlcv:
                # REST fallback
                import json, urllib.request
                tfmap = {
                    '1m':'1min','3m':'3min','5m':'5min','15m':'15min','30m':'30min',
                    '1h':'1hour','2h':'2hour','4h':'4hour','6h':'6hour','8h':'8hour','12h':'12hour','1d':'1day'
                }
                tfi = tfmap.get(p.timeframe, '5min')
                url = f"https://api.kucoin.com/api/v1/market/candles?symbol={p.symbol}&type={tfi}"
                with urllib.request.urlopen(url, timeout=10) as r:
                    data = json.loads(r.read().decode('utf-8'))
                rows = (data.get('data') or [])[-p.limit:]
                for row in rows:
                    # ts, open, close, high, low, volume
                    ts = int(row[0]); ts = ts*1000 if ts < 10_000_000_000 else ts
                    o = float(row[1]); c = float(row[2]); h = float(row[3]); l = float(row[4]); v = float(row[5])
                    ohlcv.append([ts,o,h,l,c,v])

            if len(ohlcv) < max(50, p.long_ma+5):
                self._append_log("Túl kevés gyertya a backtesthez.")
                return

            import pandas as pd
            df = pd.DataFrame(ohlcv, columns=['ts','open','high','low','close','volume'])
            df['ma_s'] = df['close'].rolling(p.short_ma).mean()
            df['ma_l'] = df['close'].rolling(p.long_ma).mean()

            stats, trades, curve = self._simulate(df, p)

            # UI frissítés
            self._fill_result_table(trades)
            self._plot_equity(curve)
            self._show_summary(stats, p)
            self._append_log("Backtest kész.")

        except Exception as e:
            self._append_log(f"Backtest hiba: {e}")

    # ---------- Szimuláció ----------
    def _simulate(self, df, p: BacktestParams):
        """
        Végiglépked a zárt gyertyákon. Belép jeleknél, kezeli SL/TP/Trailing-t és cooldown-t.
        Visszaad:
          stats: dict (win%, profit stb.)
          trades: list[dict] (trade kivonat)
          curve: list[(ts, equity)]
        """
        eq = p.initial_equity
        fee = p.fee_bps / 10000.0
        lev = max(1.0, min(10.0, p.leverage))
        # Cross 5×, Isolated 10× – itt csak kapuzunk, a tényleges módot nem állítjuk,
        # mert a backtest szoftveres.
        if lev > 5.0:
            self._append_log("Figyelem: 5× fölötti tőkeáttétel csak Isolated esetben értelmezhető a valós kereskedésben.")

        pos = None  # dict: {'side','entry','stop','trail','ts','sizeQuote','entry_idx'}
        last_entry_idx = -10**9
        trades = []
        curve = []

        import numpy as np
        closes = df['close'].values
        highs  = df['high'].values
        lows   = df['low'].values
        ma_s   = df['ma_s'].values
        ma_l   = df['ma_l'].values
        ts     = df['ts'].values

        def alloc_size(side: str, price: float) -> float:
            # quote mennyiség (USDT)
            if p.size_mode == 'quote_pct':
                q = (p.size_value/100.0) * eq
            else:  # fixed_quote
                q = p.size_value
            # lev felhasználás
            q *= lev
            # fee számoláshoz visszaadjuk quote-ot
            return max(0.0, q)

        cooldown = int(p.cooldown_bars)
        sl = max(0.0, p.sl_pct/100.0)
        tp = max(0.0, p.tp_pct/100.0)
        tr = max(0.0, p.trail_pct/100.0)
        use_short = bool(p.use_short)

        # segédfüggvények PnL-hez (quote-ban)
        def pnl_quote(side: str, entry: float, exit: float, q: float) -> float:
            # egyszerű “notional” P&L: q/entry = base mennyiség longnál
            if side == 'long':
                base = q / entry
                gross = base * (exit - entry)
            else:  # short
                base = q / entry
                gross = base * (entry - exit)
            # díjak (belépés+kilépés)
            fee_cost = q*fee + (base*exit)*fee
            return gross - fee_cost

        for i in range(1, len(df)):
            # csak zárt gyertyákon dolgozunk
            t = ts[i]
            cl = closes[i]
            curve.append((t, eq))

            # jelkeresés (előző bar → mostani bar)
            sig_long = (ma_s[i-1] < ma_l[i-1]) and (ma_s[i] > ma_l[i])
            sig_short = (ma_s[i-1] > ma_l[i-1]) and (ma_s[i] < ma_l[i])

            # ha van nyitott pozíció: SL/TP/Trailing vizsgálat
            if pos:
                side = pos['side']
                entry = pos['entry']
                q = pos['q']
                # trailing frissítés (nyerő irányban húzzuk)
                if tr > 0.0:
                    if side == 'long':
                        # legmagasabb ár óta trail változhat – egyszerűsítés: gyertya high alapján
                        thr = (1.0 - tr) * highs[i]
                        pos['trail'] = max(pos['trail'], thr)
                    else:
                        thr = (1.0 + tr) * lows[i]
                        pos['trail'] = min(pos['trail'], thr)

                # kilépési feltételek
                hit = None
                if sl > 0.0:
                    if side == 'long' and lows[i] <= entry*(1.0 - sl):
                        hit = ('SL', entry*(1.0 - sl))
                    if side == 'short' and highs[i] >= entry*(1.0 + sl):
                        hit = ('SL', entry*(1.0 + sl))
                if hit is None and tp > 0.0:
                    if side == 'long' and highs[i] >= entry*(1.0 + tp):
                        hit = ('TP', entry*(1.0 + tp))
                    if side == 'short' and lows[i] <= entry*(1.0 - tp):
                        hit = ('TP', entry*(1.0 - tp))
                if hit is None and tr > 0.0:
                    if side == 'long' and cl <= pos['trail']:
                        hit = ('TR', pos['trail'])
                    if side == 'short' and cl >= pos['trail']:
                        hit = ('TR', pos['trail'])

                if hit:
                    label, ex_price = hit
                    gain = pnl_quote(side, entry, ex_price, q)
                    eq += gain
                    trades.append({
                        "entry_i": pos['entry_idx'],
                        "exit_i" : i,
                        "entry_t": pos['ts'],
                        "exit_t" : t,
                        "side"   : side,
                        "entry"  : entry,
                        "exit"   : float(ex_price),
                        "ret_pct": float((gain / p.initial_equity) * 100.0),  # induló tőkéhez mérten
                        "eq"     : float(eq),
                        "reason" : label
                    })
                    pos = None
                    last_entry_idx = i
                    continue

            # ha nincs pozíció → belépés jelre, cooldown után
            if pos is None and (i - last_entry_idx) >= cooldown and (sig_long or (sig_short and use_short)):
                side = 'long' if sig_long else 'short'
                q = alloc_size(side, cl)
                if q <= 0:
                    continue
                pos = {
                    "side": side,
                    "entry": cl,
                    "q": q,
                    "ts": t,
                    "entry_idx": i,
                    "trail": cl*(1.0 - tr) if side=='long' else cl*(1.0 + tr)
                }
                # belépési fee levonását is lehetne szimulálni külön – itt a pnl_quote ezt majd kezeli kilépéskor.

        # ha maradt pozíció a végén → zárjuk a close-on
        if pos:
            side = pos['side']; entry = pos['entry']; q = pos['q']
            ex_price = closes[-1]
            gain = pnl_quote(side, entry, ex_price, q)
            eq += gain
            trades.append({
                "entry_i": pos['entry_idx'],
                "exit_i" : len(df)-1,
                "entry_t": pos['ts'],
                "exit_t" : ts[-1],
                "side"   : side,
                "entry"  : entry,
                "exit"   : float(ex_price),
                "ret_pct": float((gain / p.initial_equity) * 100.0),
                "eq"     : float(eq),
                "reason" : "EoD"
            })

        # statok
        wins = sum(1 for trd in trades if trd['eq'] > p.initial_equity)
        losses = len(trades) - wins
        ret_tot = (eq / p.initial_equity - 1.0) * 100.0
        winrate = (wins / len(trades) * 100.0) if trades else 0.0

        stats = {
            "trades": len(trades),
            "wins": wins,
            "losses": losses,
            "winrate_pct": round(winrate, 2),
            "final_equity": round(eq, 2),
            "ret_tot_pct": round(ret_tot, 2),
        }
        return stats, trades, curve

    # ---------- UI render ----------
    def _fill_result_table(self, trades: List[Dict[str, Any]]):
        # törlés
        for iid in self.tbl.get_children():
            self.tbl.delete(iid)
        # feltöltés
        import pandas as pd
        for idx, tr in enumerate(trades, start=1):
            t_entry = pd.to_datetime(tr['entry_t'], unit='ms').strftime('%Y-%m-%d %H:%M')
            t_exit  = pd.to_datetime(tr['exit_t'], unit='ms').strftime('%Y-%m-%d %H:%M')
            self.tbl.insert("", "end", values=(
                idx, t_entry, tr['side'].upper(), f"{tr['entry']:.6f}",
                f"{tr['exit']:.6f}", f"{tr['ret_pct']:.2f}", f"{tr['eq']:.2f}"
            ))

    def _plot_equity(self, curve: List[tuple]):
        import pandas as pd
        if not curve:
            self.ax.clear(); self.canvas.draw_idle(); return
        ts, eq = zip(*curve)
        dates = pd.to_datetime(list(ts), unit='ms')
        self.ax.clear()
        self.ax.plot(dates, eq, label='Equity')
        self.ax.set_title("Equity görbe")
        self.ax.legend(loc='upper left')
        self.ax.xaxis.set_major_formatter(self._mdates.DateFormatter('%m-%d %H:%M'))
        self.fig.tight_layout()
        self.canvas.draw_idle()

    def _show_summary(self, stats: Dict[str, Any], p: BacktestParams):
        txt = (
            f"Tranzakciók: {stats['trades']} | "
            f"Win: {stats['wins']} | Lose: {stats['losses']} | "
            f"WinRate: {stats['winrate_pct']}% | "
            f"Végső tőke: {stats['final_equity']:.2f} USDT | "
            f"Összesített hozam: {stats['ret_tot_pct']:.2f}%"
        )
        self.lbl_summary.config(text=txt)

# ========= main =========
if __name__ == "__main__":
    root = tk.Tk()
    app = CryptoBotApp(root)
    root.mainloop()