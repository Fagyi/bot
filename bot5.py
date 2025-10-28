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

# -------- 3rd party --------
import requests
import pandas as pd

# Tkinter
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox

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

def compute_signal_from_ohlcv(ohlcv: List[List[float]], short_period: int, long_period: int) -> Signal:
    try:
        df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
        if len(df) < max(short_period, long_period) + 2: return 'hold'
        df['short'] = df['c'].rolling(short_period).mean()
        df['long']  = df['c'].rolling(long_period).mean()
        prev, last = df.iloc[-2], df.iloc[-1]
        if pd.isna(prev['short']) or pd.isna(prev['long']) or pd.isna(last['short']) or pd.isna(last['long']): return 'hold'
        if prev['short'] < prev['long'] and last['short'] > last['long']: return 'buy'
        if prev['short'] > prev['long'] and last['short'] < last['long']: return 'sell'
        return 'hold'
    except Exception:
        return 'error'

def _pair_group_key(row: dict) -> str:
    sym = (row.get("symbol") or "").upper()
    if sym:
        return f"0-{sym}"           # valódi pár előre
    return f"1-{(row.get('ccy') or '').upper()}"  # „magányos” deviza később

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

    def get_margin_order_api(self):
        """Return margin OrderAPIImpl if available, else None."""
        return getattr(self, "_margin_order_api", None)

    def margin_order_api_available(self) -> bool:
        return self.get_margin_order_api() is not None

        def _resolve(obj, names):
            last_exc = None
            for name in names:
                try:
                    attr = getattr(obj, name, None)
                    if attr is None: continue
                    if callable(attr):
                        try:
                            res = attr()
                            return res, name+"()"
                        except Exception as e:
                            last_exc = e
                            continue
                    return attr, name
                except Exception as e:
                    last_exc = e
                    continue
            return None, last_exc

        def _dbg(label, value, name_or_exc):
            if value is None:
                txt = "N/A"
                if isinstance(name_or_exc, Exception):
                    txt += f" (last error: {type(name_or_exc).__name__}: {name_or_exc})"
                self._log(f"{label}: {txt}")
            else:
                cls = value.__class__.__name__
                suffix = f" via {name_or_exc}" if isinstance(name_or_exc, str) else ""
                self._log(f"{label}: {cls}{suffix}")

        if SDK_AVAILABLE:
            try:
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
                spot_srv, n_spot = _resolve(rs, ["get_spot_service", "spot_service"])
                margin_srv, n_margin = _resolve(rs, ["get_margin_service", "margin_service"])

                if spot_srv:
                    self._spot_market, n_mkt = _resolve(spot_srv, ["get_market_api", "market_api"])
                    self._spot_account, n_acc = _resolve(spot_srv, ["get_account_api", "account_api"])
                    self._spot_order,  n_ord = _resolve(spot_srv, ["get_order_api", "order_api"])
                else:
                    n_mkt = n_acc = n_ord = None

                if margin_srv:
                    self._isolated_api, n_iso = _resolve(margin_srv, ["get_isolated_api", "isolated_api"])
                    self._cross_api,    n_crs = _resolve(margin_srv, ["get_cross_api", "cross_api"])
                else:
                    n_iso = n_crs = None

                _dbg("SPOT market API",  self._spot_market, n_mkt)
                _dbg("SPOT account API", self._spot_account, n_acc)
                _dbg("SPOT order API",   self._spot_order,  n_ord)
                _dbg("Margin isolated API", self._isolated_api, n_iso)
                _dbg("Margin cross API",    self._cross_api,    n_crs)
            except Exception as e:
                self._log(f"SDK init hiba: {e}")
                self._spot_market = self._spot_account = self._spot_order = None
                self._isolated_api = self._cross_api = None
        else:
            self._log("SDK nem elérhető – csak REST.")

        # ár cache
        self._price_cache: Dict[str, tuple[float, float]] = {}
        self._price_ttl = 3.0

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
            body["fromAccountTag"] = symbol.upper().replace("/", "-")
        if to_type in ("ISOLATED", "ISOLATED_V2"):
            if not symbol:
                raise ValueError("Isolated transferhez meg kell adni a symbol-t (pl. 'SOL-USDT').")
            body["toAccountTag"] = symbol.upper().replace("/", "-")

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

        symbol = symbol.upper().replace("/", "-")

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
            syms = [str(it.get("symbol")).upper() for it in arr if it.get("symbol")]
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
                if (it.get('symbol') or '').upper() == symbol.upper():
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
                    if (it.get('symbol') or '').upper() == symbol.upper():
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
    def place_market_order(self, symbol: str, side: str, size_base: Optional[str] = None, funds_quote: Optional[str] = None) -> Any:
        if self.public_mode: raise RuntimeError("Publikus módban nem küldhető order.")
        body = {"clientOid": uuid.uuid4().hex, "symbol": symbol, "side": side, "type": "market"}
        if size_base: body["size"] = str(size_base)
        if funds_quote: body["funds"] = str(funds_quote)
        return self._rest_post("/api/v1/orders", body)

    # ----- Margin order (HF margin endpoint) -----
    def place_margin_market_order(self, mode: Literal['isolated','cross'], symbol: str, side: str,
                                  size_base: Optional[str] = None, funds_quote: Optional[str] = None,
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
        if size_base:  body["size"]  = str(size_base)
        if funds_quote: body["funds"] = str(funds_quote)
        if leverage is not None: body["leverage"] = leverage
        return self._rest_post("/api/v3/hf/margin/order", body)

    # ----- Pozíció zárás helpers -----
    def close_isolated_position(self, symbol: str) -> dict:
        acc = self.fetch_isolated_accounts()
        data = acc.get("data", acc)
        assets = (data or {}).get("assets", []) or []
        row = next((a for a in assets if a.get("symbol") == symbol), None)
        if not row: raise RuntimeError(f"Nincs isolated adat a(z) {symbol} párra.")
        base = row.get("baseAsset", {}) or {}
        quote = row.get("quoteAsset", {}) or {}
        base_tot = float(base.get("total", 0) or 0)
        base_li  = float(base.get("liability", 0) or 0)
        quote_li = float(quote.get("liability", 0) or 0)
        if base_li > 0: side, size = "buy",  base_li
        elif base_tot > 0: side, size = "sell", base_tot
        elif quote_li > 0 and base_tot > 0: side, size = "sell", base_tot
        else: raise RuntimeError("Nincs zárható isolated pozíció.")
        resp = self.place_margin_market_order("isolated", symbol, side, size_base=str(size), auto_borrow=True, auto_repay=True)
        return resp if isinstance(resp, dict) else {"data": resp}

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
        """
        Egy 'pár-csoport' kulcsot ad vissza a rendezéshez.
        - Ha van 'symbol' (pl. 'SOL-USDT'), azt használjuk.
        - Ha nincs, devizából szintetikus párt készítünk: 'CCY-USDT' (USDT kivétel kezelve).
        Így az adott párok (vagy ugyanahhoz a devizához tartozó sorok) egymás után maradnak.
        """
        sym = (rec.get("symbol") or "").upper()
        if sym:
            return sym
        ccy = (rec.get("ccy") or "").upper()
        if ccy and ccy != "USDT":
            return f"{ccy}-USDT"
        # tegyük a végére azokat, ahol nincs értelmes kulcs
        return f"ZZZ-{ccy or 'USDT'}"


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
                prices: dict[str, float] = self._fetch_latest_prices(unique_currencies)

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

                self.root.after(0, lambda: self._update_funds_balance_table(final_rows))


            except RuntimeError as e:
                self.root.after(0, lambda: messagebox.showwarning("Privát hívás hiba", str(e)))
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("Hiba", f"Hiba az egyenlegek frissítésekor: {e}"))

        threading.Thread(target=worker, daemon=True).start()
        
    def _fetch_latest_prices(self, currencies: set[str]) -> dict[str, float]:
        """
        Deviza -> USD ár (USDT ≈ 1.0). Többlépcsős fallback:
        1) SDK get_fiat_price (ha elérhető)
        2) REST /api/v1/fiat-price?base=USD&currencies=...
        3) REST /api/v1/market/orderbook/level1?symbol={CCY}-USDT (egyenként)
        """
        out: dict[str, float] = {}
        if not currencies:
            return out

        # USDT mindig 1.0
        cur_list = sorted({c.upper() for c in currencies})
        if "USDT" in cur_list:
            out["USDT"] = 1.0
            cur_list.remove("USDT")

        # --- 1) SDK: get_fiat_price (ha van) ---
        tried_sdk = False
        try:
            if self.exchange and getattr(self.exchange, "_spot_market", None):
                # próbálunk buildert találni
                mod = __import__('kucoin_universal_sdk.generate.spot.market', fromlist=['GetFiatPriceReqBuilder'])
                B = getattr(mod, 'GetFiatPriceReqBuilder')
                req = B().set_base("USD").set_currencies(",".join(cur_list)).build()
                resp = self.exchange._spot_market.get_fiat_price(req)  # type: ignore[attr-defined]
                data = getattr(resp, "data", None) or {}
                for k, v in (data.items() if isinstance(data, dict) else []):
                    try:
                        out[k.upper()] = float(v)
                    except Exception:
                        pass
                tried_sdk = True
        except Exception:
            pass

        # --- 2) REST: /fiat-price (ha kell) ---
        missing = [c for c in cur_list if c not in out]
        if missing:
            try:
                import json, urllib.parse, urllib.request
                qs = urllib.parse.urlencode({
                    "base": "USD",
                    "currencies": ",".join(missing)
                })
                url = f"https://api.kucoin.com/api/v1/fiat-price?{qs}"
                with urllib.request.urlopen(url, timeout=8) as r:
                    data = json.loads(r.read().decode("utf-8"))
                    d = (data or {}).get("data", {}) or {}
                    for k, v in d.items():
                        try:
                            out[k.upper()] = float(v)
                        except Exception:
                            pass
            except Exception:
                # megyünk tovább a 3. lépcsőre
                pass

        # --- 3) REST fallback: level1 {CCY}-USDT egyenként ---
        still_missing = [c for c in cur_list if c not in out]
        for ccy in still_missing:
            try:
                import json, urllib.request
                sym = f"{ccy}-USDT"
                url = f"https://api.kucoin.com/api/v1/market/orderbook/level1?symbol={sym}"
                with urllib.request.urlopen(url, timeout=6) as r:
                    data = json.loads(r.read().decode("utf-8"))
                    price = float(((data or {}).get("data") or {}).get("price") or 0.0)
                    if price > 0:
                        out[ccy] = price  # USDT ára ~1 → USD-ben kifejezve oké
            except Exception:
                # végső esetben nem tesszük bele (ne legyen 0)
                pass

        # végső simítás: semmire se tároljunk 0-t
        out = {k: v for k, v in out.items() if isinstance(v, (int, float)) and v > 0}
        if "USDT" not in out:
            out["USDT"] = 1.0
        return out

    # ---- util ----
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
                self.symbols = syms
                self.root.after(0, self._apply_symbols_to_widgets)
        except Exception as e:
            self.log(f"Symbols betöltési hiba: {e}")

    def _apply_symbols_to_widgets(self):
        for cb in (self.e_symbol, self.trade_symbol, self.cross_symbol, self.mt_symbol, self.f_iso_sym):
            try:
                cb.configure(values=self.symbols)
                if cb.get() not in self.symbols:
                    cb.set(DEFAULT_SYMBOL)
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
                    sym = self.mt_symbol.get().strip().upper().replace('/', '-')
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
        sym = self.mt_symbol.get().strip().upper().replace('/', '-')
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
            sym = self.mt_symbol.get().strip().upper().replace('/', '-')
            base, quote = sym.split('-')
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
        sym = self.mt_symbol.get().strip().upper().replace('/', '-')
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
        try:
            symbol = self.e_symbol.get().strip().upper().replace('/', '-')
            tf = self.cb_tf.get().strip()
            short_n = int(self.e_short.get()); long_n = int(self.e_long.get())
            ohlcv = self.exchange.fetch_ohlcv(symbol, tf, LIMIT)  # type: ignore[arg-type]
            if not ohlcv:
                self.log("⚠️ Nincs candle adat.")
                return
            df = pd.DataFrame(ohlcv, columns=['ts','o','h','l','c','v'])
            df['short'] = df['c'].rolling(short_n).mean()
            df['long']  = df['c'].rolling(long_n).mean()
            last = df.iloc[-1]
            sig = compute_signal_from_ohlcv(ohlcv, short_n, long_n)
            self.log(f"[{symbol} {tf}] close={last['c']:.4f} short={df['short'].iloc[-1]:.4f} long={df['long'].iloc[-1]:.4f} → {sig}")
            self.draw_chart(df, symbol, tf)
        except Exception as e:
            self.log(f"Hiba a tick-ben: {e}")

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
                symbol = self.trade_symbol.get().strip().upper().replace('/', '-')
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

        csym = (self.cross_symbol.get() or DEFAULT_SYMBOL).upper().replace("/", "-")
        dq = csym.split("-")[1] if "-" in csym else "USDT"

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
        symbol = (self.cross_symbol.get() or "").strip().upper().replace("/", "-")
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
        btn.config(state=tk.DISABLED); self.root.config(cursor="watch")

        def worker():
            try:
                if mode == "cross":
                    resp = self.exchange.close_cross_position(symbol)  # type: ignore[union-attr]
                    refreshed = self.view_cross_accounts
                    ok_title = "Close cross"
                else:
                    resp = self.exchange.close_isolated_position(symbol)  # type: ignore[union-attr]
                    refreshed = self.view_isolated_accounts
                    ok_title = "Close isolated"
                oid = (resp.get("data", {}) or {}).get("orderId")
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
        symbol = (self.cross_symbol.get() or "").strip().upper().replace("/", "-")
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
        sym = self.f_iso_sym.get().strip().upper().replace("/", "-")
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
        ttk.Radiobutton(mrow, text="Isolated", variable=self.mb_mode, value="isolated",
                        command=self._mb_sync_lev_cap).pack(side=tk.LEFT, padx=(0,12))
        ttk.Radiobutton(mrow, text="Cross",    variable=self.mb_mode, value="cross",
                        command=self._mb_sync_lev_cap).pack(side=tk.LEFT)
        r += 1

        # --- Pár (az MT fül combóját használjuk, és létrehozunk alias-t a worker kedvéért) ---
        ttk.Label(form, text="Pár").grid(row=r, column=0, sticky="w")
        self.mt_symbol = ttk.Combobox(form, values=self.symbols, width=12, state='readonly')
        self.mt_symbol.set(DEFAULT_SYMBOL); self.mt_symbol.grid(row=r, column=1, sticky="w")
        # alias, ha a worker 'mb_symbol'-t kérdezné
        self.mb_symbol = self.mt_symbol
        r += 1

        # Idősík
        ttk.Label(form, text="Idősík").grid(row=r, column=0, sticky="w", pady=(4,0))
        self.mb_tf = ttk.Combobox(form, state="readonly", width=10,
                                  values=["1m","3m","5m","15m","30m","1h","4h","1d"])
        self.mb_tf.set("3m")
        self.mb_tf.grid(row=r, column=1, sticky="w", pady=(4,0))
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
        r += 1

        # Tőkeáttét (worker: mb_leverage) + kompat alias a _mb_sync_lev_cap-hez
        ttk.Label(form, text="Tőkeáttét").grid(row=r, column=0, sticky="w", pady=(6,0))
        self.mb_leverage = ttk.Spinbox(form, from_=1, to=10, width=6)
        self.mb_leverage.delete(0, tk.END); self.mb_leverage.insert(0, "10")
        self.mb_leverage.grid(row=r, column=1, sticky="w", pady=(6,0))
        # alias a meglévő sync függvényhez (ha az mb_lev-et várja)
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
        self.mb_budget = ttk.Entry(form, width=12)  # ha üres: elérhető QUOTE-ot használ
        self.mb_budget.grid(row=r, column=1, sticky="w", pady=(2,0))
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
        self.mb_sl_pct.delete(0, tk.END); self.mb_sl_pct.insert(0, "1.0")
        self.mb_sl_pct.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(fixed_row2, text="TP %").pack(side=tk.LEFT)
        self.mb_tp_pct = ttk.Spinbox(fixed_row2, from_=0, to=50, increment=0.1, width=6)
        self.mb_tp_pct.delete(0, tk.END); self.mb_tp_pct.insert(0, "2.0")
        self.mb_tp_pct.pack(side=tk.LEFT, padx=(2,8))

        ttk.Label(fixed_row2, text="Trailing %").pack(side=tk.LEFT)
        self.mb_trail_pct = ttk.Spinbox(fixed_row2, from_=0, to=20, increment=0.1, width=6)
        self.mb_trail_pct.delete(0, tk.END); self.mb_trail_pct.insert(0, "0.9")
        self.mb_trail_pct.pack(side=tk.LEFT, padx=(2,0))
        r += 1

        # --- Breakout (kitörés) detektor – kapcsoló + paraméterek ---
        brk_box = ttk.Labelframe(form, text="Breakout (kitörés)", padding=6)
        brk_box.grid(row=r, column=0, columnspan=2, sticky="we", pady=(8,0))
        brk_row1 = ttk.Frame(brk_box); brk_row1.pack(anchor="w")

        self.mb_use_brk = tk.BooleanVar(value=True)
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

        self.mb_brk_with_trend = tk.BooleanVar(value=True)
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
        self.mb_use_htf = tk.BooleanVar(value=True)
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
        ttk.Checkbutton(ch, text="Auto-borrow/repay", variable=self.mb_autob).pack(side=tk.LEFT, padx=(0,12))
        self.mb_allow_short = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Short engedélyezése", variable=self.mb_allow_short).pack(side=tk.LEFT, padx=(0,12))
        self.mb_dry = tk.BooleanVar(value=True)
        ttk.Checkbutton(ch, text="Dry-run (nem küld ordert)", variable=self.mb_dry).pack(side=tk.LEFT)
        r += 1

        # Start / Stop
        btns = ttk.Frame(form); btns.grid(row=r, column=0, columnspan=2, sticky="we", pady=(10,0))
        self.mb_start_btn = ttk.Button(btns, text="Start bot", command=self.mb_start); self.mb_start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0,6))
        self.mb_stop_btn  = ttk.Button(btns, text="Stop bot",  command=self.mb_stop, state=tk.DISABLED); self.mb_stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        r += 1

        # ===== jobb oszlop: napló =====
        right = ttk.Labelframe(root, text="Bot napló", padding=8)
        right.grid(row=0, column=1, sticky="nsew", padx=(6,10), pady=10)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(0, weight=1)
        self.mb_log = scrolledtext.ScrolledText(right, wrap=tk.WORD, height=20)
        self.mb_log.grid(row=0, column=0, sticky="nsew")

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

        if not hasattr(self, "_mb_stopping"): 
            self._mb_stopping = False

    # --- Thread-safe logoló segéd ---
    def _safe_log(self, text: str):
        try:
            self.root.after(0, lambda: (self.mb_log.insert(tk.END, text), self.mb_log.see(tk.END)))
        except Exception:
            pass

    def mb_start(self):
        """Margin bot indítás (dry-runban is futhat)."""
        self._mb_stopping = False   # biztos ami biztos
        self._mb_summary_done = False

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
        """Margin bot leállítása + biztonságos pozíciózárás (SIM/LIVE)."""
        if not getattr(self, "_mb_running", False):
            self._safe_log("ℹ️ A bot nem fut.\n")
            return

        # manuális leállítás jelző – előbb stopping, majd kicsi puffer és futás flag le
        self._mb_stopping = True
        try:
            import time as _t
            _t.sleep(0.1)
        except Exception:
            pass
        self._mb_running = False

        self._safe_log("⏹️ Bot leállítása folyamatban...\n")

        try:
            sym = self._mb_get_str("mb_symbol", self._mb_get_str("mt_symbol", DEFAULT_SYMBOL)).replace("/", "-")
            dry = self._mb_get_bool("mb_dry", True)
            lev = self._mb_get_int("mb_leverage", 10)
            mode = self.mb_mode.get() if hasattr(self, "mb_mode") else "isolated"

            try:
                last_px = float(self.exchange.fetch_ticker(sym)["last"])
            except Exception:
                last_px = None
                self._safe_log("⚠️ Ár lekérés nem sikerült, utolsó ismert ár kerül felhasználásra.\n")

            # --- összes pozíció zárása (long + short listák) ---
            for side in ("buy", "sell"):
                lst = getattr(self, "_sim_pos_long", []) if side == "buy" else getattr(self, "_sim_pos_short", [])
                i = 0
                while i < len(lst):
                    pos = lst[i]
                    px = float(last_px if last_px is not None else pos.get("peak", pos.get("entry", 0.0)))
                    close_side = "sell" if side == "buy" else "buy"

                    self._safe_log(f"🔻 Pozíció zárása ({close_side.upper()}) @ {px:.6f} | dry={dry}\n")

                    if dry:
                        # szimulált zárás (ugyanaz mint _close_sim_by_index)
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
                            f"🔚 SIM CLOSE {side.upper()} @ {px:.6f} | sz={sz:.6f} | "
                            f"PnL={pnl:+.2f} USDT | Total={self._sim_pnl_usdt:+.2f}\n"
                        )
                        del lst[i]
                        continue  # ne növeld az i-t, mert rövidebb lett a lista

                    else:
                        # éles zárás
                        try:
                            sz = float(pos.get("size", 0.0))
                            if sz > 0:
                                resp = self.exchange.place_margin_market_order(
                                    mode, sym, close_side,
                                    size_base=sz,
                                    leverage=lev,
                                    auto_borrow=False
                                )
                                oid = (getattr(resp, 'data', None) or {}).get('orderId')
                                self._safe_log(f"✅ LIVE pozíció zárva – orderId={oid}\n")
                            else:
                                self._safe_log("ℹ️ Nulla méret – nincs zárás szükség.\n")
                        except Exception as e:
                            self._safe_log(f"❌ LIVE zárási hiba: {e}\n")

                        # sim tükör PnL frissítés
                        entry = float(pos.get('entry', 0.0))
                        sz = float(pos.get('size', 0.0))
                        pnl = (px - entry) * sz * (1 if side == 'buy' else -1)
                        with self._mb_lock:
                            self._sim_pnl_usdt += pnl
                            self._pool_balance_quote += pnl
                            self._pool_used_quote = max(0.0, self._pool_used_quote - float(pos.get('commit_usdt', 0.0)))
                        del lst[i]
                        continue

                    i += 1  # ha nem töröltünk, lépjünk tovább

            # --- összegzés csak itt (nem a workerben) ---
            try:
                self._mb_do_summary_once("mb_stop")
            except Exception as e:
                self._safe_log(f"⚠️ Összegzés hiba (stop): {e}\n")

        except Exception as e:
            self._safe_log(f"❌ Stop során hiba: {e}\n")

        # --- worker szál szelíd megvárása (maximum ~1s) ---
        try:
            if hasattr(self, "_mb_thread") and self._mb_thread.is_alive():
                self._mb_thread.join(timeout=1.0)
        except Exception:
            pass

        # jelző visszaengedése (óvatosan)
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
            # induló keret = UI "mb_budget", ha nincs megadva, akkor az elérhető QUOTE
            try:
                symbol0 = self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)).strip().upper().replace('/', '-')
                base0, quote0 = symbol0.split('-')
            except Exception:
                quote0 = "USDT"
            ui_budget = float(self._mb_get_float('mb_budget', 0.0) or 0.0)
            avail_quote = 0.0
            try:
                if hasattr(self, "_mt_available"):
                    _, avail_quote = self._mt_available(base0, quote0)  # gyors lekérés, ha van
            except Exception:
                pass
            init_pool = ui_budget if ui_budget > 0 else max(0.0, avail_quote)
            with self._mb_lock:
                self._pool_balance_quote = float(init_pool)
                self._pool_used_quote = 0.0
            # védő log
            self._safe_log(f"🏦 Pool init: balance={self._pool_balance_quote:.2f} {quote0}, used={self._pool_used_quote:.2f}\n")

        # --- belső helperek: lista oldalszerint, nyitás/zárás multi, menedzsment per-pozíció ---
        def _pos_list(side: str):
            return self._sim_pos_long if side == "buy" else self._sim_pos_short

        def _open_sim(side: str, entry_px: float, size_base: float, commit_usdt: float,
                      atr_pack=None, fixed_pack=None):
            """
            side: 'buy'|'sell'
            entry_px: belépő ár
            size_base: mennyiség (BASE)
            commit_usdt: a keretből ténylegesen lefoglalt USDT (rész-zárásnál arányosan csökken)
            atr_pack: (mul_sl, mul_tp1, mul_tp2, trail_mul, atr_val) vagy None
            fixed_pack: (tpct, spct, trpct) vagy None
            """
            pos = {
                'side': side,
                'entry': float(entry_px),
                'size': float(size_base),
                'peak': float(entry_px),
                'pnl': 0.0,
                'commit_usdt': float(commit_usdt),
                'mgmt': 'none'
            }
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
                self._pool_used_quote += float(commit_usdt)

            self._safe_log(
                f"🧪 SIM OPEN {side.upper()} @ {entry_px:.6f} | sz={size_base:.6f} | commit={commit_usdt:.2f} USDT | pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

        def _close_sim_by_index(side: str, idx: int, exit_px: float):
            """Teljes zárás adott indexű pozícióra; PnL visszaír a pool-ba, commit felszabadul."""
            lst = _pos_list(side)
            if idx < 0 or idx >= len(lst): return
            pos = lst[idx]
            entry = float(pos['entry']); sz = float(pos['size'])
            pnl = (exit_px - entry) * sz * (1 if side=='buy' else -1)

            # pool frissítés
            with self._mb_lock:
                self._sim_pnl_usdt += pnl
                self._pool_balance_quote += pnl
                self._pool_used_quote   -= float(pos['commit_usdt'])
                self._pool_used_quote = max(0.0, self._pool_used_quote)

            # history
            try:
                symbol_safe = self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)).replace('/', '-')
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

            self._safe_log(
                f"🔚 SIM CLOSE {side.upper()} @ {exit_px:.6f} | sz={sz:.6f} | PnL={pnl:+.2f} USDT | Total={self._sim_pnl_usdt:+.2f} | pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
            )

            del lst[idx]

        def _partial_close_50(pos: dict, side: str, px: float):
            """ATR TP1-nél 50% zár; commit_usdt fele felszabadul; PnL a poolba megy (thread-safe)."""
            if pos.get('half_closed', False):
                return

            entry = float(pos['entry']); sz = float(pos['size'])
            close_sz = sz * 0.5
            pnl = (px - entry) * close_sz * (1 if side == 'buy' else -1)

            # commit_usdt fele szabadul fel
            commit_before = float(pos.get('commit_usdt', 0.0))
            release = commit_before * 0.5

            # Kritikus szakasz: PnL / pool / pos mezők
            with self._mb_lock:
                self._sim_pnl_usdt += pnl
                self._pool_balance_quote += pnl
                # pos írások egyben
                pos.update({
                    'size': sz - close_sz,
                    'commit_usdt': commit_before - release,
                    'half_closed': True
                })
                self._pool_used_quote = max(0.0, self._pool_used_quote - release)

            # (Opcionális) history bejegyzés a rész-zárásról
            try:
                import time as _t
                try:
                    symbol_safe = self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)).replace('/', '-')
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
                f"🔹 PARTIAL 50% @ {px:.6f} | zárt={close_sz:.6f} | PnL={pnl:+.2f} | "
                f"pool used={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f}\n"
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

        try:
            while self._mb_running:
                try:
                    # --- UI beállítások kiolvasása ---
                    symbol = self._mb_get_str('mb_symbol', self._mb_get_str('mt_symbol', DEFAULT_SYMBOL)).strip().upper().replace('/', '-')
                    tf     = self._mb_get_str('mb_tf', '1m')
                    fa     = self._mb_get_int('mb_ma_fast', 9)
                    slw    = self._mb_get_int('mb_ma_slow', 21)
                    sizep  = self._mb_get_float('mb_size_pct', 50.0)
                    inpm   = self._mb_get_str('mb_input_mode', 'quote')
                    mode   = self._mb_get_str('mb_mode', 'isolated')
                    lev    = self._mb_get_int('mb_leverage', 10)
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
                    if self._mb_last_bar_ts.get(key, 0) == last_ts:
                        time.sleep(2); continue
                    self._mb_last_bar_ts[key] = last_ts

                    closes = df['c'].astype(float).tolist()
                    last_px = float(closes[-1])

                    # valós idejű (ticker) ár – default a candle close
                    last_px_rt = last_px
                    try:
                        tkr = self.exchange.fetch_ticker(symbol)
                        rt = float(tkr.get("last") or tkr.get("close") or 0.0)
                        if rt > 0:
                            last_px_rt = rt
                    except Exception:
                        pass

                    # (opcionális) eltérés százalék logoláshoz
                    try:
                        drift_pct = abs(last_px_rt - last_px) / max(last_px, 1e-12) * 100.0
                    except Exception:
                        drift_pct = float("nan")

                    # --- EMA + HTF jel ---
                    sig_raw, ef_l, es_l = self._mb_signal_from_ema(df['c'], fa, slw)
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

                    # --- Kombinált jel (breakout elsőbbség) ---
                    combined_sig = brk_sig if brk_sig in ('buy', 'sell') else sig

                    # --- LOG: állapot + jel ---
                    log_line = (
                        f"[{symbol} {tf}] px_candle={last_px:.6f} px_mkt={last_px_rt:.6f}  "
                        f"EMA({fa})={ef_l:.4f} / EMA({slw})={es_l:.4f}"
                    )
                    if use_htf: log_line += f" HTF={trend_htf:+d}"
                    if use_rsi and rsi_val is not None: log_line += f" RSI({rsi_len})={rsi_val:.2f}"
                    if use_brk and not (math.isnan(hh) or math.isnan(ll)):
                        log_line += f" BRK[{brk_n}] HH={hh:.4f} LL={ll:.4f} ↑{up_lvl:.4f} ↓{dn_lvl:.4f} sig={brk_sig}"
                    if drift_pct == drift_pct:  # not NaN
                        log_line += f" drift={drift_pct:.2f}%"
                    log_line += (
                        f" | POOL used/bal={self._pool_used_quote:.2f}/{self._pool_balance_quote:.2f} "
                        f"(ui={budget_ui:.2f}) → {combined_sig}\n"
                    )
                    self._safe_log(log_line)

                    # --- FUTÓ POZÍCIÓK MENEDZSMENTJE (mindkét oldalon) ---
                    atr_val = None
                    if use_atr:
                        atr_val = float(self._mb_atr(df, n=atr_n).iloc[-1])

                    # BUY-ok kezelése
                    i = 0
                    while i < len(self._sim_pos_long):
                        pos = self._sim_pos_long[i]
                        need_close = False
                        if pos.get('mgmt') == 'atr' and atr_val is not None:
                            need_close = _manage_atr_on_pos(pos, last_px, atr_val)
                        elif pos.get('mgmt') == 'fixed':
                            need_close = _manage_fixed_on_pos(pos, last_px)
                        # ha zárni kell
                        if need_close:
                            _close_sim_by_index('buy', i, last_px)
                            continue  # ne növeld i-t, mert a lista rövidebb lett
                        i += 1

                    # SELL-ek kezelése
                    i = 0
                    while i < len(self._sim_pos_short):
                        pos = self._sim_pos_short[i]
                        need_close = False
                        if pos.get('mgmt') == 'atr' and atr_val is not None:
                            need_close = _manage_atr_on_pos(pos, last_px, atr_val)
                        elif pos.get('mgmt') == 'fixed':
                            need_close = _manage_fixed_on_pos(pos, last_px)
                        if need_close:
                            _close_sim_by_index('sell', i, last_px)
                            continue
                        i += 1

                    # --- ÚJ NYITÁS (cooldown + pool limit) ---
                    now = int(time.time())
                    if combined_sig in ('buy','sell') and (now - self._mb_last_cross_ts >= cd_s):
                        # friss ticker csak nyitás előtt / vagy LIVE módban
                        try:
                            if (not dry) or True:  # ha minden nyitásnál szeretnéd
                                rt = float(self.exchange.fetch_ticker(symbol)["last"])
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
                                # KuCoin-szerű kalkuláció QUOTE módban
                                ord = self._mb_calc_order_qty(
                                    side=combined_sig,
                                    price=last_px_rt,
                                    pool_free=free_pool,          # mindig a SZABAD poolból
                                    size_pct=sizep_to_use,
                                    leverage=lev,
                                    mode="quote",
                                    lot_step=0.0001,
                                    price_step=0.01
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

                            # log
                            self._safe_log(
                                f"📈 Jel: {combined_sig.upper()} | px={last_px_rt:.6f} | size%={sizep_to_use:.2f} | "
                                f"nominal={nominal_q:.2f} | commit={commit_usdt:.2f} | free_pool={free_pool:.2f} | "
                                f"lev={lev} | mode={mode} dry={dry}\n"
                            )

                            # nyitás feltétele
                            opened = False
                            if commit_usdt > free_pool + 1e-9 or open_size <= 0:
                                self._safe_log("ℹ️ Nulla méret / nincs keret – nincs nyitás.\n")
                            else:
                                if dry:
                                    if use_atr and atr_val is not None:
                                        atr_pack = (mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val)
                                        _open_sim(combined_sig, last_px_rt, open_size, commit_usdt, atr_pack=atr_pack)
                                    elif use_fixed:
                                        fixed_pack = (tpct, spct, trpct)
                                        _open_sim(combined_sig, last_px_rt, open_size, commit_usdt, fixed_pack=fixed_pack)
                                    else:
                                        _open_sim(combined_sig, last_px_rt, open_size, commit_usdt)
                                    opened = True
                                else:
                                    try:
                                        auto_b = getattr(self, "mb_autob", None)
                                        auto_borrow = bool(auto_b.get()) if auto_b else False
                                        resp = self.exchange.place_margin_market_order(
                                            mode, symbol, combined_sig,
                                            size_base=size if size is not None else None,
                                            funds_quote=funds if funds is not None else None,
                                            leverage=lev, auto_borrow=auto_borrow
                                        )
                                        oid = (getattr(resp, 'data', None) or {}).get('orderId') if hasattr(resp, 'data') else (resp.get('data', {}) or {}).get('orderId', None)
                                        self._safe_log(f"✅ LIVE order {combined_sig.upper()} elküldve – orderId={oid}\n")
                                        _open_sim(combined_sig, last_px_rt, open_size, commit_usdt,
                                                  atr_pack=(mul_sl, mul_tp1, mul_tp2, mul_tr, atr_val) if (use_atr and atr_val is not None) else None,
                                                  fixed_pack=(tpct, spct, trpct) if use_fixed else None)
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

    # ---------- Jel-generátor: EMA keresztezés (HOSSZÚ metszés) + slope ----------
    def _mb_signal_from_ema(self, series, fast: int, slow: int) -> tuple[str, float, float]:
        """
        EMA keresztezés a HOSSZÚ (slow) oldaláról nézve + slope-megerősítés a HOSSZÚ-n.
        BUY:   ha a slow EMA alulról a fast fölé kerül (es_p < ef_p  és  es_l > ef_l) ÉS slow emelkedik
        SELL:  ha a slow EMA felülről a fast alá kerül (es_p > ef_p  és  es_l < ef_l) ÉS slow esik
        Vissza: ('buy'|'sell'|'hold', ema_fast_last, ema_slow_last)
        """
        import pandas as pd
        s = pd.Series(series, dtype='float64')
        if len(s) < max(fast, slow) + 2:
            return 'hold', float('nan'), float('nan')

        ema_f = s.ewm(span=fast, adjust=False).mean()
        ema_s = s.ewm(span=slow, adjust=False).mean()
        last, prev = len(s)-1, len(s)-2

        ef_l, es_l = float(ema_f.iloc[last]), float(ema_s.iloc[last])
        ef_p, es_p = float(ema_f.iloc[prev]), float(ema_s.iloc[prev])

        # slope a HOSSZÚ-n (slow EMA)
        slope_up_s   = es_l > es_p
        slope_down_s = es_l < es_p

        # HOSSZÚ keresztezés logika
        if es_p < ef_p and es_l > ef_l and slope_up_s:
            return 'buy', ef_l, es_l
        if es_p > ef_p and es_l < ef_l and slope_down_s:
            return 'sell', ef_l, es_l
        return 'hold', ef_l, es_l

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
            base, quote = symbol.split('-')

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

    def _mb_floor_to_step(self, x: float, step: float | None) -> float:
        from math import floor
        if not step or step <= 0:
            return x
        return floor(x / step) * step

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

        if mode == "quote":
            commit_quote = pool_free * pct                 # saját tőke (margin)
            nominal_quote = commit_quote * lev             # tényleges pozíció érték
            qty_base = nominal_quote / max(price, 1e-12)
        else:
            # BASE módnál hagyjuk meg a régi logikát – itt csak durván számolunk
            commit_quote = base_free * pct * price
            nominal_quote = commit_quote * lev
            qty_base = base_free * pct * lev

        qty_base = max(self._mb_floor_to_step(qty_base, lot_step), 0.0)
        return {
            "side": side,
            "qty_base": qty_base,
            "commit_quote": commit_quote,
            "nominal_quote": nominal_quote,
            "lev": lev,
            "price": round(price / price_step) * price_step
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
            symbol = self.e_symbol.get().strip().upper().replace('/', '-'),
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