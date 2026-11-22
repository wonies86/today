#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
국내 증시 수급 대시보드 — data.json 실시간 자동 갱신
=====================================================

· 표준 라이브러리만 사용합니다 (pip install 불필요, GitHub Actions에서 3~5초).
· 네이버 금융 공개 엔드포인트에서 실시간 시세·수급·업종·순위를 받아
  index.html이 읽는 data.json 을 갱신합니다.
· 주말·휴장일에는 아무 것도 하지 않고 종료합니다(커밋 없음).
· 이미 있는 날짜 항목은 서사(context·articles·카드 문장 등)를 보존하고
  숫자(지수·수급·시세·지표)만 새 값으로 바꿉니다.
· 새 날짜는 실시간 데이터로 요약을 새로 만듭니다.
· 어떤 엔드포인트가 실패해도 스크립트는 죽지 않습니다(이전 값 유지 + 경고).

· 조건식 × 당일 수급 교집합: 일봉 120거래일(거래량 포함)을 메모리에서 계산해
  등록된 조건식(SCANNER_DEFS)마다 통과 + 거래대금 기준 이상 종목을 골라
  data.json 최신 날짜 항목에 담는다(첫 조건식 = '세력꿈틀이').
  포착·관찰 종목의 차트 구조와 과거 유사 지점 5일 반응도 조건식마다 함께 담는다.
  새 조건식은 SCANNER_DEFS 에 항목 하나만 추가하면 대시보드에 자동으로 늘어난다.
  원본 조건식 문구(영웅문 원문)는 SCANNER_DEFS 의 rawRules·rawFormula·rawIntersection
  으로 함께 담기고, 화면의 `원본 조건식` 팝업이 그대로 보여준다.
  **저장은 암호문만**: 이 결과 전체(scanners·conditionHits·conditionScan·chartReactions)를
  `scannersEncrypted`(PBKDF2-SHA256 300k → AES-256-GCM) 한 덩어리로만 남긴다.
  키는 저장소 밖 `../.scanner_key` 또는 환경변수 SCANNER_KEY — 저장소(Public)에는 절대 적지 않는다.
  키가 없는 실행(GitHub Actions)은 스캔을 새로 저장하지 않고 기존 `scannersEncrypted`를 그대로 보존한다.
  (거래량은 data.json에 저장하지 않는다 — charts 는 [시,고,저,종] 그대로)

사용법
  python3 scripts/update_market.py            # 자동 (주말·휴장일·거래시간 판단)
  python3 scripts/update_market.py --force    # 수동 강제 갱신 (workflow_dispatch)
  python3 scripts/update_market.py --charts-only     # data.json 은 두고 일봉만 재생성
  python3 scripts/update_market.py --scan-only [--date YYYY-MM-DD]  # 조건식 스캔만 재계산
  python3 scripts/verify_scan.py [--live]     # 스캔 결과 검증(정적/독립 재계산)
"""

from __future__ import annotations

import base64
import hashlib
import json
import math
import os
import re
import secrets
import sys
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path

# ---------------------------------------------------------------- 기본 설정
KST = timezone(timedelta(hours=9))
ROOT = Path(__file__).resolve().parent.parent
DATA_PATH = ROOT / "data.json"

API = "https://m.stock.naver.com/api"
POLL_BASE = "https://polling.finance.naver.com/api/realtime/domestic"
POLL = POLL_BASE + "/index"
FCHART = "https://fchart.stock.naver.com/sise.nhn"

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36")

HEADERS = {
    "User-Agent": UA,
    "Referer": "https://m.stock.naver.com/",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "ko-KR,ko;q=0.9,en;q=0.8",
    "Cache-Control": "no-cache",
}

MAX_DATES = 20          # 보관할 최대 거래일 수 (data.json 용량 관리)
CHART_DAYS = 130        # 일봉 조회 개수 (60일선·RSI·MACD 계산용)

# 전 종목 시세 인덱스(allStocks) — 📋 바로묻기가 상위 50 밖 종목도 찾도록
ALL_STOCK_CAP = 300     # 시장별 최대 종목 수 (KOSPI 300 + KOSDAQ 300)
ALL_MV_KEEP = 150       # 시가총액 상위 150위 안이면 거래대금과 무관하게 우선 포함
ALL_STOCKS_MARK = "__ALLSTOCKS_JSON__"   # data.json 한 줄 압축 저장용 자리표시자

# 차트(일봉) — 대시보드 모달의 📈 차트 탭이 쓰는 실측 일봉
CHARTS_DAYS = 120         # 종목당 보관 일봉 수(약 6개월 — 5·20·60일선 계산·확대/축소에 충분)
CHARTS_MIN_BARS = 20      # 이보다 짧으면(신규상장·거래정지) 차트를 만들지 않는다
CHARTS_MARK = "__CHARTS_JSON__"

# 조건식 × 당일 수급 교집합 — 키움 조건식 A·B·C·D·E + 거래대금 100억 이상
SCAN_MIN_VALUE = 100      # 교집합 최소 거래대금(억 원)
SCAN_RULE = "A and (B or C) and D and E"
SCAN_FETCH = 130          # 스캔용 일봉 조회 개수(보관 120봉에 여유를 둔다)
SCAN_KEYS = ("scanners", "conditionHits", "conditionScan", "chartReactions")

# 조건식(scanners) 잠금 — data.json 에는 암호문만 남기고 평문 키는 저장하지 않는다.
# 키는 저장소 **밖** 파일(/workspace/kr-market-project/.scanner_key) 또는 환경변수만 쓴다.
# (Public 저장소이므로 index.html·이 스크립트·워크플로 어디에도 비밀번호를 적지 않는다)
SCAN_ENC_KEY = "scannersEncrypted"
SCAN_ITER = 300000                      # PBKDF2-SHA256 반복 (웹 프런트와 같아야 한다)
SCAN_KEY_PATH = ROOT.parent / ".scanner_key"

WARNINGS: list[str] = []


def log(*args) -> None:
    print(*args, flush=True)


def warn(msg: str) -> None:
    WARNINGS.append(msg)
    print(f"  ! {msg}", flush=True)


# ---------------------------------------------------------------- HTTP 유틸
def get_text(url: str, encoding: str = "utf-8", timeout: int = 12, tries: int = 3):
    """URL 본문을 문자열로. 실패하면 None (예외로 죽지 않음)."""
    last = None
    for attempt in range(tries):
        try:
            req = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(req, timeout=timeout) as res:
                return res.read().decode(encoding, "replace")
        except Exception as exc:            # noqa: BLE001 - 네트워크 오류 전부 흡수
            last = exc
            time.sleep(0.5 * (attempt + 1))
    warn(f"요청 실패 {url.split('?')[0]} ({type(last).__name__})")
    return None


def get_json(url: str, timeout: int = 12, tries: int = 3):
    text = get_text(url, "utf-8", timeout, tries)
    if text is None:
        return None
    try:
        return json.loads(text)
    except Exception:                       # noqa: BLE001
        warn(f"JSON 파싱 실패 {url.split('?')[0]}")
        return None


# ---------------------------------------------------------------- 숫자/포맷
def to_int(value):
    """'1,234' / '+2,758' / '-1,561' / 1234 → int, 실패 시 None."""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return int(value)
    s = str(value).strip().replace(",", "").replace("+", "")
    if s in ("", "-", "N/A"):
        return None
    try:
        return int(float(s))
    except ValueError:
        return None


def to_float(value):
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    s = str(value).strip().replace(",", "").replace("+", "").replace("%", "")
    if s in ("", "-", "N/A"):
        return None
    try:
        return float(s)
    except ValueError:
        return None


def comma(n) -> str:
    if n is None:
        return "—"
    return f"{int(round(n)):,}"


def eok_text(v) -> str:
    if v is None:
        return "—"
    return f"{int(v):+,}억"


def turnover_text(eok_value) -> str:
    """억 원 숫자 → '7,866억' / '4.0조'."""
    if eok_value is None:
        return "—"
    v = float(eok_value)
    if v >= 10000:
        return f"{v / 10000:.1f}조"
    if v >= 1000:
        return f"{int(round(v)):,}억"
    if v >= 10:
        return f"{int(round(v))}억"
    return f"{v:.1f}억"


def hangeul_turnover(stock: dict) -> str:
    """네이버가 주는 '7,196억원' / '1조 1,829억원' → '7,196억' / '1조 1,829억'."""
    raw = stock.get("accumulatedTradingValueKrwHangeul")
    if raw:
        return str(raw).replace("원", "").strip()
    value = to_int(stock.get("accumulatedTradingValueRaw"))
    if value:
        return turnover_text(value / 1e8)
    return "—"


def pct_text(v) -> str:
    if v is None:
        return "—"
    return f"{v:+.2f}%"


# ---------------------------------------------------------------- 업종 그룹
GROUP_RULES = [
    ("semi", ("삼성전자", "SK하이닉스", "SK스퀘어", "한미반도체", "DB하이텍", "이오테크닉스",
              "주성엔지니어링", "원익", "리노공업", "HPSP", "티씨케이", "솔브레인",
              "동진쎄미켐", "네패스", "제주반도체", "에이디테크놀로지", "가온칩스",
              "에이피알", "유진테크", "피에스케이", "케이씨텍", "월덱스", "하나머티리얼즈")),
    ("parts", ("삼성전기", "LG이노텍", "대덕전자", "비에이치", "이수페타시스", "심텍",
               "해성디에스", "코리아써키트", "인터플렉스", "엘컴텍", "티엘비")),
    ("enter", ("CJ ENM", "JYP", "에스엠", "하이브", "YG", "스튜디오드래곤", "하나투어",
               "모두투어", "롯데관광", "호텔신라", "파라다이스", "제주항공", "진에어",
               "티웨이", "강원랜드", "초록뱀", "에이스토리", "콘텐트리중앙", "쇼박스",
               "키이스트", "SM", "F&F", "삼화네트웍스", "판타지오", "iMBC", "아이엠비씨")),
    ("robot", ("로봇", "두산로보틱스", "레인보우로보틱스", "에이엘로봇", "휴림로봇",
               "유진로봇", "클로봇", "로보티즈", "로보스타")),
    ("bio", ("바이오", "제약", "셀트리온", "유한양행", "알테오젠", "HLB", "SK바이오팜",
             "삼천당제약", "한미약품", "종근당", "대웅제약", "녹십자", "휴젤", "메디톡스")),
]

GROUP_LABEL = {
    "semi": "반도체",
    "parts": "전자부품",
    "enter": "엔터·여행",
    "robot": "AI로봇",
    "bio": "바이오",
    "etc": "기타",
}

ETF_PREFIX = ("KODEX", "TIGER", "ARIRANG", "ACE ", "PLUS ", "HANARO", "KBSTAR",
              "RISE ", "SOL ", "TIME ", "BNK", "히어로즈", "마이다스", "WON ", "파워")


def _retime(text, hm):
    """'종목 시세 10:44 · 업종 등락 10:50 기준' → 현재 시각으로."""
    if not text or not hm:
        return text
    return re.sub(r"(?<!\d)\d{1,2}:\d{2}(?!\d)", hm, str(text))


def _card_key(name: str) -> str:
    """'방송·엔터' → '방송' — 업종명과 앞 두 글자로 맞춘다."""
    return re.sub(r"[^가-힣A-Za-z]", "", str(name or ""))[:2]


def _hm_minutes(hm):
    """'16:30' → 990분. 시각이 없거나 형식이 다르면 None."""
    m = re.search(r"(\d{1,2}):(\d{2})", str(hm or ""))
    if not m:
        return None
    hour, minute = int(m.group(1)), int(m.group(2))
    if hour > 23 or minute > 59:
        return None
    return hour * 60 + minute


def session_window(window):
    """'10:00~16:30' → ('10:00', '16:30'). 형식이 다르면 (None, None)."""
    m = re.search(r"(\d{1,2}:\d{2})\s*~\s*(\d{1,2}:\d{2})", str(window or ""))
    if not m:
        return None, None
    return m.group(1), m.group(2)


def closed_at(window, stamp_hm):
    """세션 마감 시각을 지난 실행이면 마감 시각('16:30'), 아직이면 None.

    마감된 세션에 실행 시각(예: 20:27)을 찍으면 실제로 없던 시각의 종가
    ('20:27 종가')를 표기하게 되므로, 표기는 세션 마감 시각으로 고정한다.
    """
    _start, end = session_window(window)
    stamp_min, end_min = _hm_minutes(stamp_hm), _hm_minutes(end)
    if stamp_min is None or end_min is None:
        return None
    return end if stamp_min > end_min else None


def _freeze_text(text, hm):
    """마감된 세션의 시간 표기를 마감 시각으로 고정 — '20:27 기준' → '16:30 마감 기준'."""
    if not text or not hm:
        return text
    out = _retime(text, hm)
    return re.sub(r"(\d{1,2}:\d{2})\s*(?:장전|장중|장후|마감\s*)?기준",
                  lambda m: f"{m.group(1)} 마감 기준", out)


def _freeze_block(value, hm):
    """세션 블록(문자열·목록·딕트) 안의 시간 표기를 마감 시각으로 고정."""
    if isinstance(value, str):
        return _freeze_text(value, hm)
    if isinstance(value, list):
        return [_freeze_block(v, hm) for v in value]
    if isinstance(value, dict):
        return {k: _freeze_block(v, hm) for k, v in value.items()}
    return value


def _is_turnover_card(card: dict) -> bool:
    """cmain이 업종 등락률이 아니라 거래대금(조·억)을 보여주는 카드인지."""
    if re.search(r"[조억]", str(card.get("cmain") or "")):
        return True
    return "자금" in str(card.get("csub") or "")


INDUSTRY_SHORT = {
    "방송과엔터테인먼트": "방송·엔터",
    "호텔,레스토랑,레저": "호텔·레저",
    "반도체와반도체장비": "반도체",
    "디스플레이장비및부품": "디스플레이",
    "전자장비와기기": "전자장비",
    "생명과학도구및서비스": "바이오",
    "건강관리장비와용품": "헬스케어",
    "무역회사와판매업체": "유통",
    "음식료품": "음식료",
    "전기제품": "전기제품",
    "운송장비·부품": "운송장비",
    "종이와목재": "종이목재",
    "기계·장비": "기계",
    "IT서비스": "IT서비스",
    "통신서비스": "통신",
    "오락·문화": "엔터",
}


def short_industry(name: str) -> str:
    """카드 헤더용 짧은 업종명 — '방송과엔터테인먼트' → '방송·엔터'."""
    n = str(name or "").strip()
    if n in INDUSTRY_SHORT:
        return INDUSTRY_SHORT[n]
    n2 = n.replace(",", "·")
    if len(n2) > 10:
        parts = [p for p in n2.split("·") if p]
        if len(parts) >= 2:
            return parts[0][:6] + "·" + parts[1][:4]
        return n2[:8]
    return n2


def group_key(name: str) -> str:
    plain = str(name).replace(" ", "").upper()
    for key, words in GROUP_RULES:
        for word in words:
            if word.replace(" ", "").upper() in plain:
                return key
    return "etc"


def is_etf(name: str) -> bool:
    upper = str(name).upper()
    if any(upper.startswith(prefix.upper()) for prefix in ETF_PREFIX):
        return True
    return any(word in name for word in ("레버리지", "인버스", "선물", "합성"))


# ---------------------------------------------------------------- 수집
def fetch_index(market: str):
    """KOSPI / KOSDAQ 실시간 지수."""
    data = get_json(f"{POLL}/{market}")
    if not data or not data.get("datas"):
        return None
    idx = data["datas"][0]
    return {
        "market": market,
        "name": idx.get("stockName") or market,
        "value": idx.get("closePrice"),
        "chg": to_float(idx.get("fluctuationsRatioRaw") or idx.get("fluctuationsRatio")),
        "diff": to_int(idx.get("compareToPreviousClosePriceRaw")),
        "open": idx.get("openPrice"),
        "high": idx.get("highPrice"),
        "low": idx.get("lowPrice"),
        "prevClose": to_int(idx.get("closePriceRaw")) - (to_int(idx.get("compareToPreviousClosePriceRaw")) or 0)
        if to_int(idx.get("closePriceRaw")) is not None else None,
        "volume": idx.get("accumulatedTradingVolume"),
        "turnover_eok": (to_int(idx.get("accumulatedTradingValueRaw")) or 0) / 1e8 or None,
        "status": idx.get("marketStatus"),
        "traded_at": idx.get("localTradedAt"),
    }


def fetch_realtime_stocks(codes):
    """여러 종목 실시간 시세 (KRX 정규장 기준 · 30개씩 묶어 요청)."""
    out = {}
    codes = [str(c) for c in codes if c]
    for i in range(0, len(codes), 30):
        chunk = codes[i:i + 30]
        data = get_json(f"{POLL_BASE}/stock/" + ",".join(chunk))
        for d in (data or {}).get("datas") or []:
            code = d.get("itemCode")
            price = to_int(d.get("closePriceRaw"))
            diff = to_int(d.get("compareToPreviousClosePriceRaw")) or 0
            exchange = (d.get("stockExchangeType") or {}).get("nameKor") or ""
            out[code] = {
                "code": code,
                "name": d.get("stockName"),
                "market": "KOSPI" if "코스피" in exchange else ("KOSDAQ" if "코스닥" in exchange else exchange),
                "price": price,
                "open": to_int(d.get("openPriceRaw")),
                "high": to_int(d.get("highPriceRaw")),
                "low": to_int(d.get("lowPriceRaw")),
                "chg": to_float(d.get("fluctuationsRatioRaw")),
                "volume": to_int(d.get("accumulatedTradingVolumeRaw")),
                "value_eok": (to_int(d.get("accumulatedTradingValueRaw")) or 0) / 1e8 or None,
                "prevClose": (price - diff) if price is not None else None,
                "traded_at": d.get("localTradedAt"),
            }
    return out


def fetch_trend(market: str):
    """투자자별 당일 누적 순매수 (억 원)."""
    data = get_json(f"{API}/index/{market}/trend")
    if not isinstance(data, dict):
        return None
    return {
        "market": market,
        "bizdate": data.get("bizdate"),
        "individual": to_int(data.get("personalValue")),
        "foreign": to_int(data.get("foreignValue")),
        "institution": to_int(data.get("institutionalValue")),
    }


def fetch_industries():
    data = get_json(f"{API}/stocks/industry")
    groups = (data or {}).get("groups") or []
    rows = []
    for g in groups:
        rate = to_float(g.get("changeRate"))
        if rate is None or float(g.get("totalCount") or 0) < 3:
            continue
        rows.append({
            "no": g.get("no"),
            "name": g.get("name"),
            "chg": rate,
            "rise": to_int(g.get("riseCount")) or 0,
            "fall": to_int(g.get("fallCount")) or 0,
            "total": to_int(g.get("totalCount")) or 0,
        })
    rows.sort(key=lambda x: x["chg"], reverse=True)
    return rows


def fetch_industry_stocks(no):
    data = get_json(f"{API}/stocks/industry/{no}?page=1&pageSize=30")
    return (data or {}).get("stocks") or []


def fetch_rank(kind: str, market: str, size: int = 40):
    data = get_json(f"{API}/stocks/{kind}/{market}?page=1&pageSize={size}")
    return (data or {}).get("stocks") or []


def fetch_market_values(market: str, pages=(1, 2, 3)):
    out = []
    for page in pages:
        data = get_json(f"{API}/stocks/marketValue/{market}?page={page}&pageSize=100")
        out.extend((data or {}).get("stocks") or [])
    return out


def fetch_sector_map():
    """종목코드 → 업종(짧은 이름). 네이버 업종 그룹 79개 목록에서 종목을 모은다."""
    data = get_json(f"{API}/stocks/industry?page=1&pageSize=100")
    groups = [g for g in (data or {}).get("groups") or [] if g.get("no") is not None]
    if not groups:
        return {}

    def one(group):
        rows = []
        total = to_int(group.get("totalCount")) or 0
        pages = 2 if total > 100 else 1
        for page in range(1, pages + 1):
            got = (get_json(f"{API}/stocks/industry/{group['no']}?page={page}&pageSize=100", tries=1) or {})
            rows.extend(got.get("stocks") or [])
        return group.get("name") or "", rows

    mapping: dict[str, str] = {}
    with ThreadPoolExecutor(max_workers=10) as pool:
        futures = [pool.submit(one, g) for g in groups]
        for fut in futures:
            name, rows = fut.result()
            short = short_industry(name) if name else ""
            for st in rows:
                code = st.get("itemCode")
                if code and short and code not in mapping:
                    mapping[code] = short
    return mapping


def build_all_stocks(mv_by_market, movers, sector_map):
    """KOSPI·KOSDAQ 전 종목 시세 인덱스 — [[코드, 이름, 시장, 현재가, 등락%, 거래대금(억), 업종]].

    소스: 시가총액 상위 500(KOSPI·KOSDAQ 각각) + 당일 상승·하락 상위(movers),
    그중 시가총액 150위 안은 무조건, 나머지는 거래대금 순으로 시장당 300종목까지.
    """
    movers_by_market = {"KOSPI": [], "KOSDAQ": []}
    for s in movers or []:
        exchange = (s.get("stockExchangeType") or {}).get("nameKor") or ""
        market = "KOSPI" if "코스피" in exchange else ("KOSDAQ" if "코스닥" in exchange else "")
        if market:
            movers_by_market[market].append(s)

    rows = []
    for market in ("KOSPI", "KOSDAQ"):
        cand: dict[str, dict] = {}
        for i, s in enumerate(mv_by_market.get(market) or []):
            code = s.get("itemCode")
            if not code or s.get("stockEndType") != "stock":
                continue
            cand[code] = {"s": s, "mv": i}
        for s in movers_by_market[market]:
            code = s.get("itemCode")
            if not code or s.get("stockEndType") != "stock":
                continue
            cand.setdefault(code, {"s": s, "mv": 10 ** 6})

        def order(v):
            big = 0 if v["mv"] < ALL_MV_KEEP else 1
            trade = -(to_int(v["s"].get("accumulatedTradingValueRaw")) or 0)
            return (big, trade)

        picked = []
        for v in sorted(cand.values(), key=order)[:ALL_STOCK_CAP]:
            s = v["s"]
            name = str(s.get("stockName") or "").strip()[:24]
            price = to_int(s.get("closePriceRaw"))
            if not name or not price or is_etf(name):
                continue
            chg = to_float(s.get("fluctuationsRatio"))
            value_eok = round((to_int(s.get("accumulatedTradingValueRaw")) or 0) / 1e8)
            picked.append([s.get("itemCode"), name, market, price,
                           round(chg, 2) if chg is not None else None,
                           value_eok, sector_map.get(s.get("itemCode"), "")])
        picked.sort(key=lambda r: -r[5])
        rows.extend(picked)
    return rows


def fetch_chart(code: str, count: int = CHART_DAYS):
    """일봉 [{'d','o','h','l','c','v'}] — 실패 시 None."""
    url = f"{FCHART}?symbol={code}&timeframe=day&count={count}&requestType=0"
    text = get_text(url, "euc-kr", timeout=15)
    if not text:
        return None
    rows = []
    for m in re.finditer(r'item data="([^"]+)"', text):
        parts = m.group(1).split("|")
        if len(parts) < 6:
            continue
        try:
            rows.append({
                "d": parts[0],
                "o": int(parts[1]),
                "h": int(parts[2]),
                "l": int(parts[3]),
                "c": int(parts[4]),
                "v": int(parts[5]),
            })
        except ValueError:
            continue
    return rows or None


# ---------------------------------------------------------------- 차트(일봉) 데이터
def charts_fresh(cached, codes, now):
    """이미 받아 둔 charts 를 그대로 써도 되는지.

    · 같은 날 마감(15:40) 뒤에 만든 최종본이면 다시 받지 않는다
      (5분마다 599종목 일봉을 다시 받으면 GitHub Actions가 감당하지 못한다)
    · 마감 전에 만든 것이면 그대로 쓰고, 마감 뒤 첫 실행에서 정식 종가로 한 번 더 만든다
    """
    if not isinstance(cached, dict) or not cached.get("stocks"):
        return False
    as_of = str(cached.get("asOf") or "")
    if not as_of:
        return False
    # 보관 일봉이 줄었으면(과거 30일본 등) 120거래일로 다시 받는다
    if int(cached.get("days") or 0) < CHARTS_DAYS:
        return False
    have = {str(k) for k in cached["stocks"].keys()}
    missing = len(set(codes) - have)
    if missing > max(3, int(len(codes) * 0.02)):
        return False                      # 새로 편입된 종목이 많으면 다시 만든다
    today = now.strftime("%Y%m%d")
    minutes = now.hour * 60 + now.minute
    try:
        gen = datetime.fromisoformat(str(cached.get("generatedAt") or ""))
        if gen.tzinfo is None:            # 예전 형식(오프셋 없음)도 KST로 읽는다
            gen = gen.replace(tzinfo=KST)
        gen_minutes = gen.hour * 60 + gen.minute
    except Exception:                     # noqa: BLE001
        gen = None
        gen_minutes = -1
    # 방금 만든 것을 다시 받지 않는다 — 일부 종목 조회가 실패해도 5분마다 599종목×120봉을
    # 다시 받는 일이 없도록 20분간은 그대로 쓴다(다음 실행에서 보완된다).
    # 개장 전에는 오늘 봉이 없어 asOf가 어제로 남으므로, 이 검사를 asOf 검사보다 먼저 둔다.
    if gen is not None and 0 <= (now - gen).total_seconds() < 20 * 60:
        return True
    if as_of < today:
        return False                      # 지난 봉이면 새로 받는다
    if gen_minutes >= 15 * 60 + 40:
        return True                       # 마감 뒤 만든 최종본
    if minutes < 15 * 60 + 40:
        return True                       # 아직 마감 전 — 장중 봉으로 그대로 사용
    return False                          # 마감 뒤 첫 실행에서 정식 종가로 재생성


def build_charts(codes, cached, now, need_series=False):
    """(data.json charts, 스캔용 일봉 series) — 종목별 최근 일봉 OHLC 경량 배열.

    · 네이버 금융 일봉(fchart) 실측값만 넣는다. 없는 봉은 보간·추정하지 않는다
    · 날짜 배열을 한 벌만 두고 종목은 [[시,고,저,종], ...] 만 저장한다(용량 절감)
    · 봉 날짜가 기준 날짜와 어긋나는 종목(거래정지·신규상장)은 넣지 않는다
    · series(거래량 포함)는 메모리에서만 쓰고 data.json에는 저장하지 않는다
      — 조건식 스캔·차트 반응 계산에만 쓰고 버린다(용량 폭증 방지)
    """
    codes = [str(c) for c in (codes or []) if c]
    if not codes:
        return (cached or None), {}
    if charts_fresh(cached, codes, now) and not need_series:
        return cached, {}

    rows_by_code = {}
    with ThreadPoolExecutor(max_workers=10) as pool:
        futures = {code: pool.submit(fetch_chart, code, CHARTS_DAYS) for code in codes}
        for code, future in futures.items():
            rows = future.result() or []
            if len(rows) >= CHARTS_MIN_BARS:
                rows_by_code[code] = rows[-CHARTS_DAYS:]
    if not rows_by_code:
        warn("일봉 차트 데이터를 받지 못했습니다 — 기존 charts 유지")
        return (cached or None), {}

    counts = {}
    for rows in rows_by_code.values():
        counts[rows[-1]["d"]] = counts.get(rows[-1]["d"], 0) + 1
    latest = max(counts, key=counts.get)
    base = next(rows for rows in rows_by_code.values() if rows[-1]["d"] == latest)
    dates = [r["d"] for r in base]

    stocks = {}
    for code, rows in rows_by_code.items():
        if [r["d"] for r in rows] != dates:
            continue                      # 봉 날짜가 어긋나면 그리지 않는다(가짜 봉 금지)
        stocks[code] = [[r["o"], r["h"], r["l"], r["c"]] for r in rows]
    if not stocks:
        return (cached or None), {}

    charts = {
        "asOf": latest,
        "basis": f"{latest[:4]}-{latest[4:6]}-{latest[6:]} 종가",
        "generatedAt": now.isoformat(timespec="seconds"),
        "days": len(dates),
        "dates": dates,
        "stocks": stocks,
    }
    series = {code: rows for code, rows in rows_by_code.items() if code in stocks}
    return charts, series


# ---------------------------------------------------------------- 조건식 × 수급 교집합
def _mean(values):
    return sum(values) / len(values) if values else None


def _mmdd(d) -> str:
    """'20261120' → '11/20'."""
    s = str(d or "")
    return f"{s[4:6]}/{s[6:]}" if len(s) == 8 else s


def condition_scan(rows):
    """키움 조건식 A~E — 일봉 실측값만 쓴다(추정·보간 없음).

    A [일] 0봉전 20이평 < 60이평 < 115이평
    B [일] 1봉전 5봉 평균거래량 >= 55,555
    C [일] 1봉전 5봉 평균거래대금 >= 50,000,000원 (금일 0봉 제외)
    D [일] 0봉전 종가 > 20이평
    E [일] 0봉전 |20이평-60이평| / min <= 2%
    조건식: A and (B or C) and D and E
    """
    if not rows or len(rows) < 116:            # 115이평 + 1봉전 5봉 평균
        return None
    closes = [r["c"] for r in rows]
    vols = [r["v"] for r in rows]
    n = len(closes)
    ma20 = _mean(closes[n - 20:])
    ma60 = _mean(closes[n - 60:])
    ma115 = _mean(closes[n - 115:])
    vol5 = _mean(vols[n - 6:n - 1])            # 1봉전까지 5봉(0봉 제외)
    value5 = _mean([c * v for c, v in zip(closes[n - 6:n - 1], vols[n - 6:n - 1])])
    gap = abs(ma20 - ma60) / min(ma20, ma60) * 100 if min(ma20, ma60) else None
    cond = {
        "A": ma20 < ma60 < ma115,
        "B": vol5 >= 55555,
        "C": value5 >= 50000000,
        "D": closes[-1] > ma20,
        "E": gap is not None and gap <= 2.0,
    }
    return {
        "ma20": round(ma20), "ma60": round(ma60), "ma115": round(ma115),
        "gap": round(gap, 2) if gap is not None else None,
        "vol5": int(round(vol5)),
        "value5_eok": round(value5 / 1e8, 2),
        "conditions": cond,
        "pass": cond["A"] and (cond["B"] or cond["C"]) and cond["D"] and cond["E"],
    }


# ---------------------------------------------------------------- 조건식 정의
#  등록된 조건식 — 여기에 항목 하나만 더하면 data.json·대시보드에 자동으로 늘어난다.
#   · evaluate(rows): 일봉 리스트 → 조건 판정 dict (계산 불가면 None)
#   · pick(scan)    : 그 dict 로 "조건 통과" 여부 판정
#   · minValue      : 당일 거래대금 교집합 기준(억 원)
#   · rules         : 화면에 그대로 보여줄 필터 기준 카드(키·짧은 라벨·설명)
SCANNER_DEFS = [
    {
        "id": "power-wiggle",
        "name": "세력꿈틀이",
        "summary": "20·60·115일선 역배열 속 20·60일선 2% 수렴, 종가가 20일선 위 — "
                   "5일 평균 거래량·거래대금 통과",
        "formula": SCAN_RULE,
        "minValue": SCAN_MIN_VALUE,
        "rules": [
            {"key": "A", "label": "20<60<115이평", "detail": "0봉전 20이평 < 60이평 < 115이평(역배열)"},
            {"key": "B", "label": "5일 평균거래량 5.5만+", "detail": "1봉전까지 5봉 평균거래량 55,555주 이상"},
            {"key": "C", "label": "5일 평균거래대금 5천만+", "detail": "1봉전까지 5봉 평균거래대금 5,000만원 이상"},
            {"key": "D", "label": "종가 > 20이평", "detail": "0봉전 종가가 20이평 위"},
            {"key": "E", "label": "20·60이평 2% 이내", "detail": "|20이평-60이평| ÷ 작은 값 ≤ 2%"},
        ],
        "intersection": f"당일 거래대금 {SCAN_MIN_VALUE}억+",
        # ── 키움증권 영웅문 [조건검색식] 원문 그대로 (별도 보관: scanners/세력꿈틀이.md) ──
        "rawSource": "키움증권 영웅문 조건검색식",
        "rawTarget": "대상변경",
        "rawRules": [
            {"key": "A", "text": "주가이평배열(3):[일]0봉전 20이평 < 60이평 < 115이평"},
            {"key": "B", "text": "[일]1봉전 5봉 평균거래량 55555이상 999999999이하"},
            {"key": "C", "text": "5일 평균거래대금(단위:백만) 50이상 999999999이하 (<금일제외>)"},
            {"key": "D", "text": "가격-이동평균 비교:[일]0봉전 (종가 20)이평 < 종가"},
            {"key": "E", "text": "이평이격도:[일]0봉전(종가 20, 종가 60) 2%이내 근접 1회이상"},
        ],
        "rawFormula": "A and (B or C) and D and E",
        "rawIntersection": "당일 거래대금 100억+ 교집합",
        "evaluate": condition_scan,
        "pick": lambda scan: bool(scan["pass"]),
    },
]


def chart_pattern(rows):
    """현재 차트 구조 — 실측 수치로 확인되는 것만 태그로. (태그들, 한 줄 문장)"""
    closes = [r["c"] for r in rows]
    highs = [r["h"] for r in rows]
    lows = [r["l"] for r in rows]
    opens = [r["o"] for r in rows]
    vols = [r["v"] for r in rows]
    n = len(closes)
    if n < 61:
        return [], "일봉이 60거래일보다 짧아 구조를 판별하지 않았습니다."
    ma20 = _mean(closes[-20:])
    ma60 = _mean(closes[-60:])
    prev_ma20 = _mean(closes[-21:-1])
    gap = abs(ma20 - ma60) / min(ma20, ma60) * 100
    close = closes[-1]
    bull = close > opens[-1]
    tags = []

    # 1) 20·60이평 수렴 — 2% 안이면 수렴, 그중 종가가 두 이평 위면 돌파
    if gap <= 2.0 and close > max(ma20, ma60):
        tags.append(f"20·60이평 {gap:.1f}% 수렴 돌파")
    elif gap <= 2.0:
        tags.append(f"20·60이평 {gap:.1f}% 수렴 구간")

    # 2) 20일선 관계 (전일 종가가 20일선 아래였다가 오늘 위로 = 돌파)
    if closes[-2] <= prev_ma20 and close > ma20:
        tags.append("20일선 상향 돌파")
    elif close > ma20:
        tags.append("20일선 위 유지")
    else:
        tags.append("20일선 아래")

    # 3) 직전 고점(당일 봉 제외) 대비
    hi20 = max(highs[-21:-1])
    hi60 = max(highs[-61:-1])
    if close >= hi60:
        tags.append(f"직전 60일 고점({comma(hi60)}원) 돌파")
    elif close >= hi20:
        tags.append(f"직전 20일 고점({comma(hi20)}원) 돌파")
    elif close >= hi20 * 0.97:
        tags.append(f"20일 고점 {100 * (hi20 - close) / hi20:.1f}% 이내")

    # 4) 거래량 — 20일 평균 대비 배수
    vol20 = _mean(vols[-21:-1])
    if vol20:
        ratio = vols[-1] / vol20
        if ratio >= 1.5:
            tags.append(f"거래량 20일 평균 {ratio:.1f}배 {'양봉' if bull else '음봉'}")

    # 5) 20일선 눌림 후 반등 — 최근 5봉 안에서 저가가 20일선 1.5% 안에 닿았고 오늘 양봉 상승
    touched = False
    for i in range(max(19, n - 6), n - 1):
        m = _mean(closes[i - 19:i + 1])
        if m and abs(lows[i] - m) / m <= 0.015:
            touched = True
            break
    if touched and bull and close > closes[-2] and close > ma20:
        tags.append("20일선 눌림 후 반등")

    return tags, " · ".join(tags)


def reaction_backtest(rows):
    """최근 120거래일(마지막 5일 제외) 같은 신호의 5거래일 내 실제 반응.

    신호: 20일선 상향 돌파(전일 종가<=20이평, 당일 종가>20이평)
          또는 20일 평균 대비 거래량 1.5배 이상 양봉
    """
    if not rows or len(rows) < 40:
        return None
    closes = [r["c"] for r in rows]
    highs = [r["h"] for r in rows]
    opens = [r["o"] for r in rows]
    vols = [r["v"] for r in rows]
    dates = [r["d"] for r in rows]
    n = len(closes)
    start = max(21, n - 120)
    signals = []
    for i in range(start, n - 5):           # 마지막 5일은 앞을 볼 수 없으므로 제외
        prev_ma20 = _mean(closes[i - 20:i])
        cur_ma20 = _mean(closes[i - 19:i + 1])
        cross = closes[i - 1] <= prev_ma20 and closes[i] > cur_ma20
        prev_vol20 = _mean(vols[i - 20:i])
        surge = bool(prev_vol20) and vols[i] >= 1.5 * prev_vol20 and closes[i] > opens[i]
        if not (cross or surge):
            continue
        gain = (max(highs[i + 1:i + 6]) / closes[i] - 1) * 100
        signals.append({
            "date": dates[i],
            "kind": "20일선 돌파" if cross else "거래량 급증 양봉",
            "both": bool(cross and surge),
            "gain": round(gain, 2),
        })
    window = f"최근 {n}거래일"
    count = len(signals)
    if not count:
        return {"n": 0, "m": 0, "rate": None, "avg": None, "best": None, "worst": None,
                "window": window, "samples": [],
                "summary": f"{window} 내 같은 신호가 없어 과거 반응을 셀 수 없습니다.",
                "recentText": ""}
    gains = [s["gain"] for s in signals]
    up = sum(1 for g in gains if g > 0)
    best = max(signals, key=lambda s: s["gain"])
    worst = min(signals, key=lambda s: s["gain"])
    avg = sum(gains) / count
    recent = signals[-3:][::-1]
    return {
        "n": count,
        "m": up,
        "rate": round(up / count * 100),
        "avg": round(avg, 2),
        "best": {"date": best["date"], "gain": best["gain"], "kind": best["kind"]},
        "worst": {"date": worst["date"], "gain": worst["gain"]},
        "window": window,
        "samples": recent,
        "summary": (f"{window} 내 20일선 돌파·수급 유입 {count}회 중 {up}회({round(up / count * 100)}%)가 "
                    f"5거래일 내 추가 상승, 평균 고점 {avg:+.1f}% "
                    f"(최대 {best['gain']:+.1f}%, 최소 {worst['gain']:+.1f}%)"),
        "recentText": "최근 신호: " + " · ".join(
            f"{_mmdd(s['date'])} {s['kind']} → 5일 고점 {s['gain']:+.1f}%" for s in recent),
    }


def scanner_meta(definition: dict) -> dict:
    """정의 → data.json 에 남길 메타(화면이 그대로 그리는 값).

    원본 조건식 문구(rawRules·rawFormula·rawIntersection)는 있으면 그대로 싣는다 —
    화면의 `원본 조건식` 팝업이 영웅문 원문을 그대로 보여주는 근거다.
    """
    meta = {
        "id": definition["id"],
        "name": definition["name"],
        "summary": definition.get("summary", ""),
        "formula": definition.get("formula", ""),
        "minValue": definition.get("minValue", SCAN_MIN_VALUE),
        "rules": definition.get("rules", []),
        "intersection": definition.get("intersection", ""),
    }
    for key in ("rawSource", "rawTarget", "rawRules", "rawFormula", "rawIntersection"):
        if definition.get(key):
            meta[key] = definition[key]
    return meta


def build_scanner_scan(definition, series, info, extra_codes, now):
    """조건식 하나 — 통과 + 거래대금 기준 이상 종목과 모달용 차트 반응.

    · series 는 메모리의 일봉(거래량 포함) — data.json에는 결과만 저장
    · 거래대금은 allStocks(당일 누적) 값을 쓰고, 없으면 마지막 봉 종가×거래량으로 계산
    """
    evaluate = definition.get("evaluate") or condition_scan
    pick = definition.get("pick") or (lambda scan: bool(scan.get("pass")))
    min_value = definition.get("minValue", SCAN_MIN_VALUE)
    scanned = 0
    hits = []
    reactions = {}
    last_dates = {}
    for code, rows in series.items():
        scan = evaluate(rows)
        if not scan:
            continue
        scanned += 1
        last_dates[rows[-1]["d"]] = last_dates.get(rows[-1]["d"], 0) + 1
        is_extra = code in extra_codes
        passed = bool(pick(scan))
        if not passed and not is_extra:
            continue
        row = info.get(code) or []
        value_eok = None
        if len(row) > 5 and row[5] is not None:
            value_eok = float(row[5])
        elif rows[-1]["v"]:
            value_eok = round(rows[-1]["c"] * rows[-1]["v"] / 1e8, 1)
        tags, text = chart_pattern(rows)
        back = reaction_backtest(rows)
        item = {
            "code": code,
            "name": (row[1] if len(row) > 1 and row[1] else code),
            "market": (row[2] if len(row) > 2 and row[2] else ""),
            "price": (row[3] if len(row) > 3 else None),
            "chg": (row[4] if len(row) > 4 else None),
            "value_eok": round(value_eok, 1) if value_eok is not None else None,
            "valueText": turnover_text(value_eok),
            "gap": scan["gap"],
            "conditions": scan["conditions"],
            "passed": passed,
            "pattern": tags,
            "patternText": text,
            "backtest": back,
        }
        if passed and (value_eok or 0) >= min_value:
            summary = tags[0] if tags else text
            if back and back.get("n"):
                summary += f" · 과거 {back['m']}/{back['n']}회 5일 내 상승"
            item["summary"] = summary
            hits.append(item)
        if is_extra and not passed:
            reactions[code] = item
        elif is_extra and (value_eok or 0) < min_value:
            reactions[code] = item        # 조건은 맞아도 거래대금 미달이면 모달용으로만
    hits.sort(key=lambda h: -(h.get("value_eok") or 0))
    bar_date = max(last_dates, key=last_dates.get) if last_dates else ""
    result = scanner_meta(definition)
    result.update({
        "asOf": bar_date,
        "basis": f"{bar_date[:4]}-{bar_date[4:6]}-{bar_date[6:]} 종가" if len(bar_date) == 8 else "",
        "updatedAt": now.isoformat(timespec="seconds"),
        "scanned": scanned,
        "passed": len(hits),
        "hits": hits,
        "reactions": reactions,
    })
    return result


def build_condition_scan(series, all_stocks, extra_codes, now):
    """등록된 조건식 전부(SCANNER_DEFS)를 계산해 스캔 결과를 만든다.

    반환값은 메모리에서만 쓰는 모양이다 — 저장은 apply_scan 이 암호화해
    `scannersEncrypted` 한 덩어리로만 남긴다(평문 키는 data.json 에 남기지 않는다).
    """
    if not series:
        return None
    info = {}
    for row in all_stocks or []:
        if row and row[0]:
            info[str(row[0])] = row
    scanners = [build_scanner_scan(defn, series, info, extra_codes, now) for defn in SCANNER_DEFS]
    primary = scanners[0] if scanners else None
    if not primary:
        return None
    meta = {
        "id": primary["id"],
        "name": primary["name"],
        "asOf": primary["asOf"],
        "basis": primary["basis"],
        "scanned": primary["scanned"],
        "passed": primary["passed"],
        "minValue": primary["minValue"],
        "rule": primary["formula"],
        "at": primary["updatedAt"],
    }
    return {"hits": primary["hits"], "meta": meta,
            "reactions": primary["reactions"], "scanners": scanners}


def scanner_key() -> str | None:
    """조건식 잠금 키 — 환경변수 SCANNER_KEY 우선, 없으면 저장소 밖 키 파일.

    키가 없으면(Actions·CI) 스캔 결과를 새로 저장하지 않고 기존 암호문을 그대로 둔다.
    """
    env = (os.environ.get("SCANNER_KEY") or "").strip()
    if env:
        return env
    try:
        text = SCAN_KEY_PATH.read_text(encoding="utf-8").strip()
    except OSError:
        return None
    return text or None


def encrypt_scan_payload(payload, password: str):
    """PBKDF2-SHA256 300k → AES-256-GCM. 브라우저 Web Crypto 와 같은 포맷:
    {v, alg, kdf, iter, salt, iv, ct} (base64)
    """
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM

    salt = secrets.token_bytes(16)
    iv = secrets.token_bytes(12)
    key = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, SCAN_ITER, 32)
    raw = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    ct = AESGCM(key).encrypt(iv, raw, None)
    return {
        "v": 1, "alg": "AES-256-GCM", "kdf": "PBKDF2-SHA256", "iter": SCAN_ITER,
        "salt": base64.b64encode(salt).decode(),
        "iv": base64.b64encode(iv).decode(),
        "ct": base64.b64encode(ct).decode(),
    }


def decrypt_scan_payload(blob, password: str):
    """scannersEncrypted 를 푼다 — 검증 스크립트·로컬 확인용(화면은 Web Crypto 로 푼다)."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM

    key = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"),
                              base64.b64decode(blob["salt"]),
                              int(blob.get("iter") or SCAN_ITER), 32)
    raw = AESGCM(key).decrypt(base64.b64decode(blob["iv"]), base64.b64decode(blob["ct"]), None)
    return json.loads(raw.decode("utf-8"))


def strip_scan_plaintext(obj):
    """조건식 평문 키를 지운다(scannersEncrypted 는 건드리지 않는다)."""
    if not isinstance(obj, dict):
        return obj
    for key in SCAN_KEYS:
        obj.pop(key, None)
    return obj


def scrub_scan_plaintext(data):
    """data.json 전체에서 조건식 평문 노출을 없앤다 — 저장 직전 안전장치."""
    for entry in data or []:
        if isinstance(entry, dict):
            strip_scan_plaintext(entry)


def legacy_scan_payload(src):
    """옛 기록(평문 scanners/conditionHits)을 암호화할 payload 모양으로 바꾼다."""
    if not isinstance(src, dict):
        return None
    if src.get("scanners") is None and src.get("conditionHits") is None:
        return None
    return {
        "scanners": src.get("scanners"),
        "conditionHits": src.get("conditionHits"),
        "conditionScan": src.get("conditionScan"),
        "chartReactions": src.get("chartReactions"),
    }


def apply_scan(entry, result, password: str | None = None):
    """스캔 결과를 **암호문으로만** 항목에 붙인다.

    · 결과가 없으면 아무 것도 하지 않는다
    · 잠금 키가 없으면(키 파일 없는 Actions) 저장하지 않고 False — 평문 저장 금지
    """
    if not result:
        return False
    password = password or scanner_key()
    if not password:
        log(f"  · 잠금 키가 없어 스캔 결과를 저장하지 않습니다(평문 저장 금지) — "
            f"기존 {SCAN_ENC_KEY} 유지")
        return False
    payload = {
        "scanners": result.get("scanners"),
        "conditionHits": result.get("hits"),
        "conditionScan": result.get("meta"),
        "chartReactions": result.get("reactions"),
    }
    try:
        entry[SCAN_ENC_KEY] = encrypt_scan_payload(payload, password)
    except Exception as exc:                # noqa: BLE001 - 암호화 실패 시 평문 금지
        warn(f"스캔 암호화 실패({type(exc).__name__}) — 평문으로 저장하지 않습니다")
        return False
    strip_scan_plaintext(entry)
    return True


def carry_scan(entry, *sources):
    """이번 실행에서 스캔을 계산하지 못했습니다 — 가장 최근 스캔을 그대로 옮긴다.

    암호문(scannersEncrypted)은 복호화하지 않고 그대로 옮긴다 — Actions 실행에서도
    절대 지우거나 덮어쓰지 않는다. 옛 평문 기록은 키가 있을 때만 그 자리에서 암호화한다.
    """
    for src in sources:
        if not isinstance(src, dict):
            continue
        enc = src.get(SCAN_ENC_KEY)
        if isinstance(enc, dict) and enc.get("ct"):
            entry[SCAN_ENC_KEY] = enc
            strip_scan_plaintext(entry)
            return True
        payload = legacy_scan_payload(src)
        if payload:
            password = scanner_key()
            if not password:
                warn(f"{src.get('date')} 스캔이 평문인데 잠금 키가 없어 옮기지 못했습니다")
                continue
            entry[SCAN_ENC_KEY] = encrypt_scan_payload(payload, password)
            strip_scan_plaintext(entry)
            return True
    strip_scan_plaintext(entry)
    return False


def serialize_data(data):
    """data.json 본문 문자열 — allStocks·charts 는 배열이라 한 줄 압축으로 둔다."""
    saved = []
    for entry in data:
        for key, mark in (("allStocks", ALL_STOCKS_MARK), ("charts", CHARTS_MARK)):
            value = entry.get(key)
            if isinstance(value, (list, dict)) and value:
                entry[key] = mark
                saved.append((entry, key, mark, value))
    text = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    for entry, key, mark, value in saved:
        entry[key] = value
        text = text.replace(f'"{mark}"',
                            json.dumps(value, ensure_ascii=False, separators=(",", ":")), 1)
    return text


# ---------------------------------------------------------------- 지표 계산
def ema(values, period):
    k = 2 / (period + 1)
    out = [values[0]]
    for v in values[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def rsi(closes, period=14):
    gains, losses = [], []
    for i in range(1, len(closes)):
        diff = closes[i] - closes[i - 1]
        gains.append(max(diff, 0))
        losses.append(max(-diff, 0))
    if len(gains) < period:
        return None
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
    if avg_loss == 0:
        return 100.0
    return 100 - 100 / (1 + avg_gain / avg_loss)


def atr(rows, period=14):
    trs = []
    for i in range(1, len(rows)):
        trs.append(max(rows[i]["h"] - rows[i]["l"],
                       abs(rows[i]["h"] - rows[i - 1]["c"]),
                       abs(rows[i]["l"] - rows[i - 1]["c"])))
    if len(trs) < period:
        return None
    value = sum(trs[:period]) / period
    for tr in trs[period:]:
        value = (value * (period - 1) + tr) / period
    return value


def indicators(rows, today_str):
    """완료된 일봉만으로 지표 계산 (오늘 부분 봉 제외)."""
    hist = [r for r in rows if r["d"] != today_str]
    if len(hist) < 30:
        hist = rows[:-1] if len(rows) > 2 else rows
    closes = [r["c"] for r in hist]
    if len(closes) < 20:
        return None

    def ma(n):
        return sum(closes[-n:]) / n if len(closes) >= n else None

    ma5, ma20, ma60 = ma(5), ma(20), ma(60)
    sd = math.sqrt(sum((c - ma20) ** 2 for c in closes[-20:]) / 20) if ma20 else None
    bb_up = ma20 + 2 * sd if sd else None
    bb_lo = ma20 - 2 * sd if sd else None

    macd_line, macd_sig = None, None
    if len(closes) >= 35:
        e12, e26 = ema(closes, 12), ema(closes, 26)
        macd_series = [a - b for a, b in zip(e12, e26)]
        macd_line = macd_series[-1]
        macd_sig = ema(macd_series, 9)[-1]

    stoch = None
    if len(hist) >= 20:
        window = hist[-14:]
        hh = max(r["h"] for r in window)
        ll = min(r["l"] for r in window)
        if hh > ll:
            stoch = 100 * (hist[-1]["c"] - ll) / (hh - ll)

    return {
        "ma5": ma5,
        "ma20": ma20,
        "ma60": ma60,
        "bbUp": bb_up,
        "bbLo": bb_lo,
        "rsi": rsi(closes),
        "macd": macd_line,
        "macdSig": macd_sig,
        "stoch": stoch,
        "atr": atr(hist),
        "pct1m": (closes[-1] / closes[-21] - 1) * 100 if len(closes) > 21 else None,
        "hi60": max(r["h"] for r in hist[-60:]) if len(hist) >= 20 else None,
        "lo60": min(r["l"] for r in hist[-60:]) if len(hist) >= 20 else None,
        "prevDate": hist[-1]["d"],
        "prevClose": hist[-1]["c"],
        "closes": closes,
    }


def signal_rows(ind, price):
    """모달의 '지표 스냅샷' 8칸."""
    if not ind:
        return []
    rows = []
    for label, key, name in (("20일선", "ma20", "20일선"), ("60일선", "ma60", "60일선")):
        ma = ind.get(key)
        if ma:
            gap = (price / ma - 1) * 100 if price else 0
            side = "위" if gap >= 0 else "아래"
            rows.append({"k": label, "v": f"{comma(ma)}원 · {abs(gap):.1f}% {side}"})
    if ind.get("rsi") is not None:
        r = ind["rsi"]
        tone = "과매수권" if r >= 70 else ("과매도권" if r <= 30 else
                                          ("중립선 위" if r >= 50 else "중립선 아래"))
        rows.append({"k": "RSI(14)", "v": f"{r:.1f} · {tone}"})
    if ind.get("macd") is not None:
        rows.append({"k": "MACD", "v": f"{ind['macd']:,.0f} · 시그널 {ind['macdSig']:,.0f}"})
    if ind.get("bbUp") and ind.get("bbLo") and price:
        pb = (price - ind["bbLo"]) / (ind["bbUp"] - ind["bbLo"]) * 100
        zone = "밴드 상단 쪽" if pb >= 70 else ("밴드 하단 쪽" if pb <= 30 else "밴드 중간")
        rows.append({"k": "볼린저 %B", "v": f"{pb:.0f} · {zone}"})
    if ind.get("stoch") is not None:
        k = ind["stoch"]
        tone = "과열권" if k >= 80 else ("과매도권" if k <= 20 else "중립")
        rows.append({"k": "스토캐스틱", "v": f"%K {k:.1f} · {tone}"})
    if ind.get("atr") and price:
        rows.append({"k": "ATR 변동성", "v": f"일 {ind['atr'] / price * 100:.2f}%"})
    if ind.get("pct1m") is not None:
        rows.append({"k": "최근 1개월", "v": f"{ind['pct1m']:+.1f}%"})
    return rows


def technical_text(name, info, ind, quote):
    """새 종목용 기술적 분석 서사(지표·시세에서 기계적으로 생성)."""
    if not ind:
        return {}
    price = to_int(quote.get("price")) if quote else None
    day = quote.get("day") or {}
    trend = (f"{comma(ind['prevClose'])}원({ind['prevDate'][4:6]}/{ind['prevDate'][6:]}) 종가 이후 "
             f"오늘은 {comma(day.get('open'))}원 출발, {comma(day.get('high'))}원~{comma(day.get('low'))}원 "
             f"범위에서 {comma(price)}원입니다. "
             f"20일선 {comma(ind.get('ma20'))}원 대비 "
             f"{(price / ind['ma20'] - 1) * 100:+.1f}%, 60일선 {comma(ind.get('ma60'))}원 대비 "
             f"{(price / ind['ma60'] - 1) * 100:+.1f}% 위치입니다." if price else "")
    support = " · ".join(x for x in [
        f"{comma(day.get('low'))}원(오늘 저가)" if day.get("low") else "",
        f"{comma(ind.get('lo60'))}원(60일 최저)" if ind.get("lo60") else "",
        f"{comma(ind.get('ma20'))}원(20일선)" if ind.get("ma20") else "",
    ] if x)
    resistance = " · ".join(x for x in [
        f"{comma(day.get('high'))}원(오늘 고가)" if day.get("high") else "",
        f"{comma(ind.get('hi60'))}원(60일 최고)" if ind.get("hi60") else "",
        f"{comma(ind.get('ma60'))}원(60일선)" if ind.get("ma60") else "",
    ] if x)
    volume = (f"거래량 {comma(quote.get('volume'))}주, 거래대금 {quote.get('turnover') or '—'}. "
              f"시가 {comma(day.get('open'))}원 → 고가 {comma(day.get('high'))}원 → "
              f"저가 {comma(day.get('low'))}원 → 현재 {comma(price)}원." if price else "")
    checkpoint = "① " + " ② ".join(x for x in [
        f"{comma(day.get('low'))}원(오늘 저가) 유지 여부" if day.get("low") else "",
        f"{comma(ind.get('ma20'))}원(20일선) 회복 여부" if ind.get("ma20") else "",
        f"거래대금 {quote.get('turnover') or '—'} 흐름이 이어지는지" if quote else "",
    ] if x)
    return {
        "trend": trend,
        "support": support,
        "resistance": resistance,
        "volumeFlow": volume,
        "checkpoint": checkpoint,
        "signals": signal_rows(ind, price),
    }


# ---------------------------------------------------------------- 지수 → 대시보드
def market_state(kospi_chg):
    if kospi_chg is None:
        return "혼조"
    if kospi_chg >= 0.3:
        return "상승장"
    if kospi_chg <= -0.3:
        return "하락장"
    return "보합장"


def time_bucket(now: datetime):
    """(stamp 접미사, asOf 표현, 기본 세션)"""
    hm = now.strftime("%H:%M")
    minutes = now.hour * 60 + now.minute
    if minutes < 9 * 60:
        return hm, "장전", "pre"
    if minutes < 15 * 60 + 30:
        return hm, "장중", "krx"
    if minutes < 20 * 60:
        return hm, "장후", "aft"
    return hm, "마감", "aft"


def flow_caption(trend):
    if not trend:
        return ""
    parts_neg, parts_pos = [], []
    for name, value in (("외국인", trend.get("foreign")),
                        ("기관", trend.get("institution")),
                        ("개인", trend.get("individual"))):
        if value is None:
            continue
        (parts_pos if value > 0 else parts_neg).append(f"{name} {value:+,}억")
    if parts_neg and parts_pos:
        return " · ".join(parts_neg) + " vs " + " · ".join(parts_pos)
    return " · ".join(parts_neg + parts_pos)


def build_flows(trends):
    flows = []
    for market in ("코스피", "코스닥"):
        t = trends.get("KOSPI" if market == "코스피" else "KOSDAQ")
        if not t:
            continue
        rows = []
        for name, key in (("기관", "institution"), ("외국인", "foreign"), ("개인", "individual")):
            value = t.get(key)
            if value is None:
                continue
            rows.append({"name": name, "eok": value})
        if not rows:
            continue
        flows.append({"market": market, "caption": flow_caption(t), "rows": rows})
    return flows


def build_indices(kospi, kosdaq, trends):
    out = []
    for raw, market in ((kospi, "코스피"), (kosdaq, "코스닥")):
        if not raw:
            continue
        t = trends.get("KOSPI" if market == "코스피" else "KOSDAQ") or {}
        sub = []
        for name, key in (("기관", "institution"), ("외국인", "foreign"), ("개인", "individual")):
            value = t.get(key)
            if value is None:
                continue
            sub.append({"k": name, "v": eok_text(value), "cls": "up" if value > 0 else "down"})
        chg = raw.get("chg")
        if chg is None:
            note = ""
        elif chg > 0:
            note = f"장중 {chg:+.2f}% · 상승 흐름"
        else:
            note = f"장중 {chg:+.2f}% · {raw.get('low') or ''}원 저점"
        out.append({
            "name": market,
            "value": raw.get("value") or "",
            "chg": chg,
            "badge": raw.get("market"),
            "note": note,
            "sub": sub,
        })
    return out


# ---------------------------------------------------------------- 세션 카드
def build_rank_up(up_stocks, turned_at):
    items = []
    for s in up_stocks:
        name = s.get("stockName")
        if not name or s.get("stockEndType") != "stock" or is_etf(name):
            continue
        chg = to_float(s.get("fluctuationsRatio"))
        if chg is None:
            continue
        note = None
        price_state = (s.get("compareToPreviousPrice") or {}).get("text")
        if price_state == "상한":
            note = "상한가"
        elif price_state == "하한":
            note = "하한가"
        items.append({
            "name": name,
            "g": group_key(name),
            "chg": round(chg, 2),
            "tv": hangeul_turnover(s),
            "note": note,
        })
        if len(items) >= 12:
            break
    return {
        "kind": "count",
        "title": "상승률 상위",
        "tag": "확산",
        "caption": "종목 수로 보는 확산",
        "sub": f"상승률 상위 {len(items)}종목 · {turned_at} 기준",
        "items": items,
    }


def build_rank_value(value_stocks, turned_at):
    items = []
    for i, s in enumerate(value_stocks, start=1):
        name = s.get("stockName")
        chg = to_float(s.get("fluctuationsRatio"))
        eok = (to_int(s.get("accumulatedTradingValueRaw")) or 0) / 1e8
        item = {
            "name": name,
            "g": group_key(name),
            "chg": round(chg, 2) if chg is not None else None,
            "tv": hangeul_turnover(s),
            "eok": int(round(eok)),
        }
        state = (s.get("compareToPreviousPrice") or {}).get("text")
        if state == "상한":
            item["note"] = "상한가"
        if s.get("newlyListed"):
            item["note"] = "신규상장"
        items.append(item)
        if len(items) >= 13:
            break
    return {
        "kind": "value",
        "title": "거래대금 상위",
        "tag": "자금",
        "caption": "거래대금 비중으로 보는 자금",
        "sub": f"거래대금 상위 {len(items)}종목 · {turned_at} 기준",
        "items": items,
    }


def sector_card(medal, accent, industry, stocks, turned_at):
    picks = sorted(stocks, key=lambda s: to_int(s.get("accumulatedTradingValueRaw")) or 0,
                   reverse=True)[:4]
    rows = []
    for s in picks:
        chg = to_float(s.get("fluctuationsRatio"))
        rows.append({
            "name": s.get("stockName"),
            "ticker": s.get("itemCode"),
            "price": s.get("closePrice") or "",
            "chg": round(chg, 2) if chg is not None else None,
            "turnover": hangeul_turnover(s),
        })
    rate = industry["chg"]
    return {
        "medal": medal,
        "accent": accent,
        "name": short_industry(industry["name"]),
        "cmain": f"{rate:+.2f}%",
        "csub": f"{industry['rise']}종목 상승",
        "issue": f"<b>{short_industry(industry['name'])} {rate:+.2f}%</b> — 상승 업종 상위, "
                 f"{industry['total']}종목 중 {industry['rise']}종목 상승",
        "stocks": rows,
        "foot": f"종목 시세 {turned_at} · 업종 등락 {turned_at} 기준",
    }


def build_sessions(now, kospi, kosdaq, trends, industries, up_stocks, value_stocks,
                   industry_stocks, turned_at):
    stamp_hm, phase, default_session = time_bucket(now)
    k_chg = (kospi or {}).get("chg")
    q_chg = (kosdaq or {}).get("chg")
    k_trend = trends.get("KOSPI") or {}
    q_trend = trends.get("KOSDAQ") or {}

    # --- 장전 ---
    pre_cards = [{
        "medal": "🥇",
        "accent": "violet",
        "name": "오늘의 출발",
        "cmain": f"코스피 {(kospi or {}).get('value') or '—'}",
        "csub": f"{pct_text(k_chg)} 현재",
        "issue": (f"코스피는 시가 {(kospi or {}).get('open') or '—'}로 출발해 "
                  f"현재 {(kospi or {}).get('value') or '—'} ({pct_text(k_chg)})입니다."),
        "stats": [
            {"k": "시가", "v": (kospi or {}).get("open") or "—"},
            {"k": "고가", "v": (kospi or {}).get("high") or "—"},
            {"k": "저가", "v": (kospi or {}).get("low") or "—"},
        ],
        "foot": f"네이버 금융 실시간 · {turned_at}",
    }, {
        "medal": "🥈",
        "accent": "indigo",
        "name": "수급 스냅샷",
        "cmain": f"외국인 {eok_text(k_trend.get('foreign'))}",
        "csub": "코스피 누적",
        "issue": (f"코스피는 외국인 {eok_text(k_trend.get('foreign'))} · "
                  f"기관 {eok_text(k_trend.get('institution'))} · "
                  f"개인 {eok_text(k_trend.get('individual'))}입니다."),
        "notes": [
            f"코스피 거래대금 {turnover_text((kospi or {}).get('turnover_eok'))} · "
            f"코스닥 {turnover_text((kosdaq or {}).get('turnover_eok'))}",
            f"코스닥 외국인 {eok_text(q_trend.get('foreign'))} · 기관 {eok_text(q_trend.get('institution'))} · "
            f"개인 {eok_text(q_trend.get('individual'))}",
            f"코스피 {pct_text(k_chg)} · 코스닥 {pct_text(q_chg)}",
        ],
        "foot": f"{turned_at} 누적 기준",
    }]
    pre = {
        "key": "pre",
        "tab": "장전 이슈",
        "code": "PRE",
        "name": "장전",
        "window": "08:00~08:50",
        "mode": "summary",
        "strip": f"{turned_at} 기준 · 코스피 {pct_text(k_chg)} · 코스닥 {pct_text(q_chg)} · NXT 프리마켓 08:00~08:50",
        "cards": pre_cards,
        "note": "프리마켓 수급은 NXT 체결분 기준이며, 정규장 수급과는 별도로 집계됩니다.",
    }

    # --- 정규장 ---
    cards = []
    accents = ("rose", "amber")
    medals = ("🥇", "🥈")
    for industry in (industries or [])[:2]:
        stocks = industry_stocks.get(industry["no"]) or []
        if stocks:
            cards.append(sector_card(medals[len(cards)], accents[len(cards)], industry, stocks, turned_at))
    if not cards:
        # 업종 데이터를 못 받았을 때: 거래대금 상위 종목으로 대체 카드
        picks = value_stocks[:4]
        if picks:
            cards.append({
                "medal": "🥇",
                "accent": "rose",
                "name": "거래대금 주도",
                "cmain": hangeul_turnover(picks[0]),
                "csub": "거래대금 1위",
                "issue": f"<b>{picks[0].get('stockName')}</b>가 거래대금 1위입니다. 업종 데이터를 받지 못해 종목 기준으로 대체했습니다.",
                "stocks": [{
                    "name": s.get("stockName"),
                    "price": s.get("closePrice") or "",
                    "chg": to_float(s.get("fluctuationsRatio")),
                    "turnover": hangeul_turnover(s),
                } for s in picks],
                "foot": f"종목 시세 {turned_at} 기준",
            })
    krx = {
        "key": "krx",
        "tab": "정규장 · 수급",
        "code": "정규장",
        "name": "정규장",
        "window": "09:00~15:30",
        "mode": "full",
        "strip": (f"{turned_at} 기준 · 코스피 {pct_text(k_chg)} · 코스닥 {pct_text(q_chg)} · "
                  f"거래대금 상위 {len(value_stocks[:13])}종목"),
        "cards": cards,
        "up": build_rank_up(up_stocks, turned_at),
        "value": build_rank_value(value_stocks, turned_at),
    }

    # --- 애프터장 ---
    aft = {
        "key": "aft",
        "tab": "애프터장 · 테마",
        "code": "AFT",
        "name": "애프터장",
        "window": "15:40~20:00",
        "mode": "summary",
        "noCta": True,
        "strip": f"{turned_at} 기준 · 정규장 15:30 마감 · NXT 애프터마켓 15:40~20:00",
        "cards": [{
            "medal": "🌙",
            "accent": "violet",
            "name": "애프터장 시간표",
            "cmain": "15:40~20:00",
            "csub": "NXT 애프터마켓",
            "issue": ("정규장은 15:30 마감하고, <b>NXT 애프터마켓은 15:40~20:00</b>에 이어집니다. "
                      "애프터장 체결분은 다음 정규장 시가에 영향을 줄 수 있습니다."),
            "stats": [
                {"k": "정규장", "v": "09:00~15:30"},
                {"k": "애프터", "v": "15:40~20:00"},
                {"k": "NXT 정규", "v": "09:00:30~15:20"},
            ],
            "foot": "한국거래소·넥스트레이드 거래시간",
        }, {
            "medal": "📊",
            "accent": "indigo",
            "name": "정규장 마감 스냅샷",
            "cmain": f"코스피 {pct_text(k_chg)}",
            "csub": f"코스닥 {pct_text(q_chg)}",
            "issue": (f"정규장 기준 코스피 {(kospi or {}).get('value') or '—'} ({pct_text(k_chg)}), "
                      f"코스닥 {(kosdaq or {}).get('value') or '—'} ({pct_text(q_chg)})입니다."),
            "notes": [
                f"코스피 고가 {(kospi or {}).get('high') or '—'} · 저가 {(kospi or {}).get('low') or '—'}",
                f"거래대금 코스피 {turnover_text((kospi or {}).get('turnover_eok'))} · "
                f"코스닥 {turnover_text((kosdaq or {}).get('turnover_eok'))}",
                f"투자자별(코스피) 외국인 {eok_text(k_trend.get('foreign'))} · "
                f"기관 {eok_text(k_trend.get('institution'))} · 개인 {eok_text(k_trend.get('individual'))}",
            ],
            "foot": f"{turned_at} 자동 갱신 기준",
        }],
        "note": "애프터장(NXT) 세부 테마별 수급은 정규장 마감 후 다음 갱신에서 채워집니다.",
    }

    return [pre, krx, aft], default_session


# ---------------------------------------------------------------- 관찰 5선
def build_watch_item(rank, info, quote, ind, why):
    return {
        "rank": rank,
        "name": info.get("name") or quote.get("name"),
        "ticker": info.get("code"),
        "market": quote.get("market") or "",
        "sector": GROUP_LABEL.get(group_key(info.get("name") or ""), "기타"),
        "price": comma(quote.get("price")),
        "turnover": info.get("turnover") or quote.get("turnover") or "—",
        "turnoverRank": quote.get("turnoverRank") or "",
        "chg": quote.get("chg"),
        "prevClose": comma(quote.get("prevClose") or info.get("prevClose")),
        "day": {
            "open": quote.get("day", {}).get("open") or info.get("open"),
            "high": quote.get("day", {}).get("high") or info.get("high"),
            "low": quote.get("day", {}).get("low") or info.get("low"),
            "close": quote.get("day", {}).get("close") or quote.get("price"),
        },
        "why": why,
        "technical": technical_text(info.get("name"), info, ind, quote),
    }


# ---------------------------------------------------------------- 수급 순환
ROT_WINDOW = 40          # 순환 후보 판정에 쓰는 거래대금 상위 범위
ROT_MAX_STOCKS = 3       # 섹터 카드에 보여줄 종목 수
ROT_RANK_MAP = 60        # 실시간 숫자 갱신용 거래대금 순위 맵 크기


def _ranked_values(value_stocks):
    """거래대금 순위를 붙인 종목 행 — rank는 전체 거래대금 순위(1부터)."""
    rows = []
    for i, s in enumerate(value_stocks, start=1):
        name = s.get("stockName")
        if not name or is_etf(name):
            continue
        rows.append({
            "rank": i,
            "name": name,
            "g": group_key(name),
            "chg": to_float(s.get("fluctuationsRatio")),
            "eok": int(round((to_int(s.get("accumulatedTradingValueRaw")) or 0) / 1e8)),
            "tv": hangeul_turnover(s),
        })
    return rows


def _avg_chg(rows):
    vals = [r["chg"] for r in rows if r["chg"] is not None]
    return sum(vals) / len(vals) if vals else 0.0


def _rot_stocks(rows):
    return [{
        "name": r["name"],
        "chg": round(r["chg"], 2) if r["chg"] is not None else None,
        "tv": r["tv"],
        "rank": r["rank"],
    } for r in rows[:ROT_MAX_STOCKS]]


def _rotation_macro(kospi, kosdaq, trends, industries):
    """'큰 판의 배경' — 지수·수급·업종 실데이터만으로 한 상자를 만든다.

    뉴욕·달러처럼 이 스크립트가 받아오지 않는 값은 넣지 않는다(확인된 값만).
    """
    facts = []
    k = kospi or {}
    q = kosdaq or {}
    if k.get("value") or q.get("value"):
        facts.append({
            "k": "지수",
            "v": (f"코스피 {k.get('value') or '—'} ({pct_text(k.get('chg'))}) · "
                  f"코스닥 {q.get('value') or '—'} ({pct_text(q.get('chg'))})"),
        })
    k_trend = (trends or {}).get("KOSPI") or {}
    q_trend = (trends or {}).get("KOSDAQ") or {}
    if k_trend:
        line = (f"코스피 외국인 {eok_text(k_trend.get('foreign'))} · "
                f"기관 {eok_text(k_trend.get('institution'))} · "
                f"개인 {eok_text(k_trend.get('individual'))}")
        if q_trend.get("foreign") is not None:
            line += f" / 코스닥 외국인 {eok_text(q_trend.get('foreign'))}"
        facts.append({"k": "수급", "v": line})
    if industries:
        best = industries[0]
        losers = [i for i in industries if i["chg"] < 0]
        worst = min(losers, key=lambda x: x["chg"]) if losers else None
        facts.append({
            "k": "업종",
            "v": (f"상승 1위 {INDUSTRY_SHORT.get(best['name'], best['name'])} {best['chg']:+.2f}%"
                  + (f" · 하위 {INDUSTRY_SHORT.get(worst['name'], worst['name'])} {worst['chg']:+.2f}%"
                     if worst else "")),
        })
    if not facts:
        return None
    title = (f"{INDUSTRY_SHORT.get(industries[0]['name'], industries[0]['name'])}로 쏠린 자금 — "
             "지수와 따로 움직이는 하루"
             if industries else "지수·수급으로 보는 오늘의 배경")
    return {"label": "큰 판의 배경", "title": title, "facts": facts}


def _rotation_risk(kospi, kosdaq, trends, sessions=None):
    """'체크 변수' — 시간표와 수급 리스크를 오늘 데이터로 채운다."""
    items = []
    k = kospi or {}
    k_trend = (trends or {}).get("KOSPI") or {}
    if k.get("low"):
        items.append(f"코스피 오늘 저가 {k.get('low')} 지지 여부 — 이탈하면 다음 지지선 확인")
    if k_trend.get("foreign") is not None:
        items.append(f"외국인 코스피 {eok_text(k_trend.get('foreign'))} 순매도가 줄어드는지")
    krx = next((s for s in sessions or [] if s.get("key") == "krx"), None)
    aft = next((s for s in sessions or [] if s.get("key") == "aft"), None)
    if krx and krx.get("window"):
        tail = f" → 애프터마켓 {aft['window']}" if aft and aft.get("window") else ""
        items.append(f"정규장 {krx['window']} 마감{tail}까지 수급이 유지되는지")
    else:
        items.append("정규장 마감 후 NXT 애프터마켓까지 수급이 이어지는지")
    return {"label": "체크 변수", "title": "시간표와 수급 리스크", "items": items}


def build_rotation(value_stocks, kospi=None, kosdaq=None, trends=None,
                   industries=None, sessions=None):
    """거래대금 상위권에서 2종목 이상이 함께 오간 섹터로 수급 순환(A→B·C)을 만든다.

    · macro     = 큰 판의 배경(지수·수급·업종 실데이터)
    · A         = 오늘 가장 많은 자금이 몰린 섹터(거래대금 합계 1위)
    · B·C       = 상위 ROT_WINDOW위 안에 2종목 이상이 있는 다른 섹터, 평균 등락 높은 순
    · riskCheck = 시간표·수급 리스크
    · 확인되지 않은 재료·수치는 쓰지 않는다(거래대금·등락률만).
    """
    rows = [r for r in _ranked_values(value_stocks) if r["rank"] <= ROT_WINDOW]
    groups: dict[str, list] = {}
    for r in rows:
        groups.setdefault(r["g"], []).append(r)
    named = {g: rs for g, rs in groups.items() if g != "etc" and len(rs) >= 2}
    if len(named) < 2:
        return None
    order = sorted(named.items(), key=lambda kv: sum(x["eok"] for x in kv[1]), reverse=True)
    a_key, a_rows = order[0]
    alts = sorted(((_avg_chg(rs), g, rs) for g, rs in order[1:]), key=lambda x: x[0], reverse=True)

    a_total = sum(x["eok"] for x in a_rows)
    a_avg = _avg_chg(a_rows)
    if a_avg >= 0:
        a_trigger = (f"섹터 평균 {a_avg:+.2f}%가 플러스로 유지되는지가 1차 기준입니다. "
                     "대표 종목이 상승분을 반납하면 수급이 다음 섹터로 옮겨갑니다.")
    else:
        a_trigger = (f"섹터 평균이 이미 {a_avg:+.2f}%로 밀렸습니다. 대표 종목이 전일 종가를 "
                     "회복하지 못하면 자금이 B·C 쪽으로 옮겨가는 흐름이 이어집니다.")
    rot = {
        "title": "수급 순환 시나리오",
        "tagline": "큰 판 → A → B·C",
        "a": {
            "label": "A",
            "sector": GROUP_LABEL.get(a_key, a_key),
            "meta": (f"상위 {ROT_WINDOW}위 안 {len(a_rows)}종목 · 합계 {a_total:,}억 · "
                     f"평균 {a_avg:+.2f}%"),
            "stocks": _rot_stocks(a_rows),
            "why": (f"거래대금 상위 {ROT_WINDOW}위 가운데 {a_total:,}억이 이 섹터에서 오갔습니다. "
                    + ", ".join(f"{x['name']} {x['tv']}" for x in a_rows[:3])
                    + " 순으로 자금이 집중됐습니다."),
            "triggerLabel": "이탈 신호",
            "trigger": a_trigger,
        },
        "candidates": [],
        "note": (f"거래대금 상위 {ROT_WINDOW}위 안에서 2종목 이상이 함께 오간 섹터만 후보로 골랐습니다."),
    }
    for label, (avg, g, rs) in zip(("B", "C"), alts[:2]):
        total = sum(x["eok"] for x in rs)
        rot["candidates"].append({
            "label": label,
            "sector": GROUP_LABEL.get(g, g),
            "meta": f"상위 {ROT_WINDOW}위 안 {len(rs)}종목 · 합계 {total:,}억 · 평균 {avg:+.2f}%",
            "stocks": _rot_stocks(rs),
            "reason": (f"{GROUP_LABEL.get(g, g)} {len(rs)}종목이 거래대금 상위 {ROT_WINDOW}위에 함께 올랐고 "
                       f"평균 {avg:+.2f}%입니다("
                       + ", ".join(f"{x['name']} {x['chg']:+.2f}%" for x in rs[:3] if x["chg"] is not None)
                       + ")."),
            "trigger": ("섹터 평균 등락이 플러스로 유지될 때 후보로 봅니다." if avg >= 0
                        else "낙폭과대 반등 후보 — 대표 종목이 전일 종가를 회복할 때 유효합니다."),
        })
    macro = _rotation_macro(kospi, kosdaq, trends, industries)
    if macro:
        rot["macro"] = macro
    risk = _rotation_risk(kospi, kosdaq, trends, sessions)
    if risk:
        rot["riskCheck"] = risk
    return rot


def _refresh_rotation(rot, ranks):
    """수급 순환 시나리오의 서사는 두고 종목 숫자(현재가 등락·거래대금·순위)만 갱신한다.

    · 통째로 복제한 뒤 stocks 의 숫자만 바꾸므로 macro·riskCheck·title·tagline·note 는
      손대지 않고 그대로 보존된다(아래에서 한 번 더 명시적으로 보장).
    """
    clone = json.loads(json.dumps(rot, ensure_ascii=False))
    for key in ("title", "tagline", "macro", "riskCheck", "note"):
        if key in rot and key not in clone:
            clone[key] = json.loads(json.dumps(rot[key], ensure_ascii=False))
    blocks = [clone.get("a") or {}] + [c for c in clone.get("candidates") or [] if isinstance(c, dict)]
    for block in blocks:
        for st in block.get("stocks") or []:
            live = ranks.get(st.get("name"))
            if not live:
                continue
            if live.get("chg") is not None:
                st["chg"] = live["chg"]
            if live.get("tv"):
                st["tv"] = live["tv"]
            if live.get("rank"):
                st["rank"] = live["rank"]
    return clone


# ---------------------------------------------------------------- 문맥(context)
def build_context(now, kospi, kosdaq, trends, industries, value_stocks, prev_entry,
                  sessions=None):
    k_chg = (kospi or {}).get("chg")
    q_chg = (kosdaq or {}).get("chg")
    k_trend = trends.get("KOSPI") or {}
    top = industries[0] if industries else None
    losers = [i for i in industries if i["chg"] < 0]
    worst = min(losers, key=lambda x: x["chg"]) if losers else None
    leaders = value_stocks[:3]

    headline = (f"코스피 <em>{pct_text(k_chg)}</em> · 코스닥 <em>{pct_text(q_chg)}</em> — "
                + (f"자금은 <em>{top['name']}</em>에 몰렸습니다." if top and top["chg"] > 0
                   else "업종 전반이 약세입니다.") if k_chg is not None else "실시간 시세를 불러오지 못했습니다.")

    reasons = []
    reasons.append({
        "title": f"지수 — 코스피 {(kospi or {}).get('value') or '—'} ({pct_text(k_chg)}), "
                 f"코스닥 {(kosdaq or {}).get('value') or '—'} ({pct_text(q_chg)})",
        "body": (f"코스피는 시가 {(kospi or {}).get('open') or '—'}로 출발, "
                 f"고가 {(kospi or {}).get('high') or '—'} · 저가 {(kospi or {}).get('low') or '—'} 범위에서 "
                 f"현재 {(kospi or {}).get('value') or '—'}입니다. "
                 f"코스피는 외국인 {eok_text(k_trend.get('foreign'))}, 기관 {eok_text(k_trend.get('institution'))}, "
                 f"개인 {eok_text(k_trend.get('individual'))} 순매수 구조입니다."),
    })
    if top:
        reasons.append({
            "title": f"{top['name']} {top['chg']:+.2f}% — 상승 업종 1위"
                     + (f", {worst['name']} {worst['chg']:+.2f}%는 하위" if worst else ""),
            "body": (f"{top['total']}종목 중 {top['rise']}종목이 올랐습니다. "
                     + (f"반대로 {worst['name']}은 {worst['chg']:+.2f}%로 "
                        f"{worst['total']}종목 중 {worst['fall']}종목이 내렸습니다. " if worst else "")
                     + "업종 등락은 지수보다 테마 자금 흐름을 먼저 보여줍니다."),
        })
    if leaders:
        names = ", ".join(f"{s.get('stockName')} {hangeul_turnover(s)}" for s in leaders)
        reasons.append({
            "title": "거래대금 집중 — " + ", ".join(s.get("stockName") or "" for s in leaders),
            "body": (f"거래대금 상위는 {names} 순입니다. "
                     f"코스피 거래대금은 {turnover_text((kospi or {}).get('turnover_eok'))}, "
                     f"코스닥은 {turnover_text((kosdaq or {}).get('turnover_eok'))}입니다."),
        })

    ctx = {
        "kicker": "오늘 달라진 이유",
        "headline": headline,
        "reasons": reasons,
    }

    if prev_entry:
        p_idx = {i.get("name"): i for i in prev_entry.get("indices") or []}
        p_k, p_q = p_idx.get("코스피"), p_idx.get("코스닥")
        paras = []
        if p_k:
            paras.append(f"코스피는 {p_k.get('value')} ({pct_text(p_k.get('chg'))})로 마감했습니다."
                         + (f" 코스닥은 {p_q.get('value')} ({pct_text(p_q.get('chg'))})." if p_q else ""))
        p_flow = (prev_entry.get("flows") or [{}])[0]
        if p_flow.get("caption"):
            paras.append(f"직전 거래일 수급은 {p_flow.get('caption')}였습니다.")
        ctx["prev"] = {
            "tag": prev_entry.get("shortLabel") or prev_entry.get("date"),
            "title": prev_entry.get("label") or "직전 거래일",
            "paras": paras or [prev_entry.get("label") or ""],
        }

    checkpoints = []
    if kospi:
        checkpoints.append(f"코스피 오늘 저가 {(kospi or {}).get('low') or '—'} 지지 여부 — 이탈 시 다음 지지선 확인")
        checkpoints.append(f"외국인 {eok_text(k_trend.get('foreign'))} · 기관 {eok_text(k_trend.get('institution'))} "
                           f"매매가 순매수로 돌아서는지")
    if top:
        checkpoints.append(f"{top['name']} {top['chg']:+.2f}% 흐름이 오후까지 이어지는지(차익실현 여부)")
    if leaders:
        checkpoints.append(f"거래대금 1위 {leaders[0].get('stockName')} "
                           f"({hangeul_turnover(leaders[0])})의 가격 흐름")
    krx_s = next((s for s in sessions or [] if s.get("key") == "krx"), None)
    aft_s = next((s for s in sessions or [] if s.get("key") == "aft"), None)
    if krx_s and aft_s and krx_s.get("window") and aft_s.get("window"):
        checkpoints.append(f"정규장 {krx_s['window']} 마감 후 NXT 애프터마켓({aft_s['window']}) 수급")
    else:
        checkpoints.append("정규장 15:30 마감 후 NXT 애프터마켓(15:40~20:00) 수급")
    ctx["next"] = {"tag": "체크포인트", "title": "오늘 남은 시간", "items": checkpoints}
    rotation = build_rotation(value_stocks, kospi, kosdaq, trends, industries, sessions)
    if rotation:
        ctx["rotation"] = rotation
    return ctx


def build_stages(now, date_str, default_session):
    hm = now.strftime("%H:%M")
    minutes = now.hour * 60 + now.minute
    stages = [{
        "time": hm,
        "name": "실시간 자동 갱신",
        "status": "done",
        "statusShort": "완료",
        "statusText": f"{date_str} {hm} 자동 갱신",
    }]
    if minutes < 15 * 60 + 30:
        stages.append({"time": "15:30", "name": "정규장 마감", "status": "waiting",
                       "statusShort": "대기", "statusText": "정규장 15:30 마감"})
    else:
        stages.append({"time": "15:30", "name": "정규장 마감", "status": "done",
                       "statusShort": "완료", "statusText": "정규장 15:30 마감"})
    stages.append({"time": "20:05", "name": "NXT 마감 요약", "status": "scheduled",
                   "statusShort": "예정", "statusText": f"{date_str} 20:05 자동 갱신"})
    return stages


# ---------------------------------------------------------------- 항목 조립
DEFAULT_DISCLAIMER = ("본 대시보드는 당일 거래대금·수급·재료 기반 객관적 관찰 정리이며, "
                      "특정 종목 매수·투자 추천이 아닙니다.")


def build_new_entry(now, kospi, kosdaq, trends, industries, industry_stocks,
                    up_stocks, value_stocks, watch_quotes, prev_entry):
    date_str = now.strftime("%Y-%m-%d")
    stamp_hm, phase, default_session = time_bucket(now)
    k_chg = (kospi or {}).get("chg")
    sessions, default_session = build_sessions(
        now, kospi, kosdaq, trends, industries, up_stocks, value_stocks,
        industry_stocks, stamp_hm)

    prev_date = None
    for q in watch_quotes.values():
        if q.get("prevDate"):
            prev_date = q["prevDate"]
            break
    if prev_date:
        indicator_basis = f"{prev_date[:4]}-{prev_date[4:6]}-{prev_date[6:]} 종가"
    else:
        indicator_basis = "직전 거래일 종가"

    weekday = "월화수목금토일"[now.weekday()]
    label = f"{date_str} ({weekday})"

    watchlist = []
    for i, q in enumerate(list(watch_quotes.values())[:5], start=1):
        chg = q.get("chg")
        why = (f"거래대금 {q.get('turnover')}으로 {q.get('turnoverRank') or '상위'}"
               f" — 오늘 가장 많은 자금이 오간 종목입니다. 현재 {q.get('price') and comma(q['price'])}원 "
               f"({pct_text(chg)}).")
        watchlist.append(build_watch_item(i, {"name": q.get("name"), "code": q.get("code")}, q,
                                          q.get("ind"), why))

    return {
        "date": date_str,
        "updatedAt": now.isoformat(timespec="seconds"),
        "defaultSession": default_session,
        "label": label,
        "shortLabel": now.strftime("%m/%d"),
        "asOf": f"{date_str} {stamp_hm} {phase} 기준",
        "stamp": f"{stamp_hm} {phase}",
        "marketState": market_state(k_chg),
        "priceBasis": f"{stamp_hm} {phase} 시세 기준",
        "indicatorBasis": indicator_basis,
        "rangeLabels": {"title": f"당일 {stamp_hm}까지 범위", "close": "현재가"},
        "axis": ["08:00", "15:30", "20:00"],
        "indices": build_indices(kospi, kosdaq, trends),
        "flows": build_flows(trends),
        "sessions": sessions,
        "context": build_context(now, kospi, kosdaq, trends, industries, value_stocks,
                                 prev_entry, sessions),
        "_value_ranks": {r["name"]: r for r in _ranked_values(value_stocks)[:ROT_RANK_MAP]},
        "articles": [],
        "stages": build_stages(now, date_str, default_session),
        "watchlist": watchlist,
        "disclaimer": DEFAULT_DISCLAIMER,
    }


def merge_entry(new, old):
    """기존 날짜 항목의 서사는 보존하고 숫자만 새 값으로."""
    out = {k: v for k, v in new.items() if not k.startswith("_")}
    if not old:
        return out
    for key in ("label", "shortLabel", "context", "articles",
                "disclaimer", "rangeLabels", "axis", "stages", "issue"):
        if key in old:
            out[key] = old[key]

    # defaultSession 은 보존하지 않는다 — 실행 시각의 세션(09:00 전 pre, 09:00~15:29 krx,
    # 15:30 이후 aft)으로 자동 전환되어야, 장이 열린 뒤에도 이전 세션 탭에 멈춰 있지 않는다.
    # (과거 날짜를 볼 때는 index.html 이 그 날짜에 저장된 defaultSession 을 그대로 연다.)
    if new.get("defaultSession"):
        out["defaultSession"] = new["defaultSession"]
    elif old.get("defaultSession"):
        out["defaultSession"] = old["defaultSession"]

    # 애프터장 마감 서사(수동·에이전트 병합, mode="full")는 스크립트가 만들 수 없으므로
    # 이미 들어 있으면 자동 갱신이 덮어쓰지 않도록 그대로 유지한다.
    old_aft = next((s for s in (old.get("sessions") or [])
                    if isinstance(s, dict) and s.get("key") == "aft"), None)
    if isinstance(old_aft, dict) and old_aft.get("mode") == "full":
        merged = []
        for s in (out.get("sessions") or []):
            merged.append(old_aft if (isinstance(s, dict) and s.get("key") == "aft") else s)
        if merged:
            out["sessions"] = merged
        for key in ("asOf", "stamp", "priceBasis"):
            if old.get(key):
                out[key] = old[key]
        # 관찰 5선의 정규장 시·고·저·종가(day)·정규장 종가(krxClose/krxChg)는
        # 애프터장 마감 뒤 자동 갱신에서 NXT 값으로 덮이므로 사람이 확인한 값을 유지한다.
        keep = {w.get("name"): w for w in (old.get("watchlist") or []) if isinstance(w, dict)}
        for w in (out.get("watchlist") or []):
            src = keep.get(w.get("name"))
            if not src:
                continue
            for f in ("day", "krxClose", "krxChg"):
                if src.get(f) is not None:
                    w[f] = src[f]

    # 수급 순환 시나리오: 기존 서사는 그대로 두고 종목 숫자만 실시간 값으로
    old_ctx = old.get("context")
    if isinstance(old_ctx, dict) and isinstance(old_ctx.get("rotation"), dict):
        ranks = new.get("_value_ranks") or {}
        if ranks:
            ctx = dict(old_ctx)
            ctx["rotation"] = _refresh_rotation(old_ctx["rotation"], ranks)
            out["context"] = ctx

    stamp_hm = (re.match(r"(\d{1,2}:\d{2})", str(new.get("stamp") or "")) or [None, None])[1]
    krx_window = next((s.get("window") for s in (old.get("sessions") or [])
                       if isinstance(s, dict) and s.get("key") == "krx"), None) \
        or next((s.get("window") for s in (new.get("sessions") or [])
                 if isinstance(s, dict) and s.get("key") == "krx"), None)
    krx_closed = closed_at(krx_window, stamp_hm)
    if isinstance(out.get("rangeLabels"), dict) and stamp_hm:
        labels = dict(out["rangeLabels"])
        if krx_closed:
            # 정규장이 끝난 뒤에는 실행 시각(20:27)이 아니라 정규장 구간을 쓴다
            labels["title"] = f"당일 정규장({krx_window}) 범위"
            labels["close"] = "종가"
        elif labels.get("title") and "~" not in str(labels["title"]):
            # '정규장(10:00~16:30)'처럼 고정된 구간은 실행 시각으로 바꾸지 않는다
            labels["title"] = _retime(labels["title"], stamp_hm)
        out["rangeLabels"] = labels

    # 지수: 이름으로 값만 갱신, 기존에만 있는 지수(수능일 시간표 등)는 유지
    new_names = {ix.get("name") for ix in new.get("indices", [])}
    merged = []
    old_by_name = {ix.get("name"): ix for ix in old.get("indices") or []}
    for ix in new.get("indices", []):
        prev = old_by_name.get(ix.get("name"))
        if not prev:
            merged.append(ix)
            continue
        m = dict(prev)
        m["value"] = ix["value"]
        m["chg"] = ix["chg"]
        if ix.get("sub"):
            m["sub"] = ix["sub"]
        if not m.get("note"):
            m["note"] = ix.get("note", "")
        merged.append(m)
    for ix in old.get("indices") or []:
        if ix.get("name") not in new_names:
            merged.append(ix)
    out["indices"] = merged

    # 세션: 카드 서사 유지, 순위표·기준시각·수급만 갱신
    old_sessions = {s.get("key"): s for s in old.get("sessions") or []}
    sessions = []
    for s in new.get("sessions", []):
        prev = old_sessions.get(s.get("key"))
        if not prev:
            sessions.append(s)
            continue
        m = dict(prev)
        # 상단 이슈 배너(session.issue)는 사람이 쓴 서사다 — 자동 갱신은 숫자만 바꾸고
        # issue 는 건드리지 않는다(dict(prev) 복사로 유지되지만 의도를 명시해 둔다).
        if prev.get("issue"):
            m["issue"] = prev["issue"]
        # 이미 마감된 세션(정규장 마감 후·애프터장 마감 후)은 실행 시각이 아니라
        # 세션 마감 시각으로 표기를 고정한다 — '20:27 종가' 같은 표기를 막는다.
        frozen = closed_at(m.get("window") or s.get("window"), stamp_hm)
        # 정규장 세션만 기준시각·순위표를 실시간으로 교체 (장전·애프터장 서사는 유지)
        if s.get("key") == "krx":
            for key in ("strip", "up", "value"):
                if s.get(key):
                    m[key] = _freeze_block(s[key], frozen) if frozen else s[key]
        elif not m.get("up") and s.get("up"):
            m["up"] = s["up"]
            m["value"] = s.get("value")
        cards = []
        for card in m.get("cards") or []:
            card = dict(card)
            metric = (new.get("_industry_metric") or {}).get(_card_key(card.get("name")))
            # 거래대금(조·억)·'자금' 카드는 업종 등락률(+2.61%)로 덮지 않는다
            if metric and not _is_turnover_card(card):
                card["cmain"] = f"{metric['chg']:+.2f}%"
                card["metric_chg"] = metric["chg"]
                if re.match(r"^\d+\s*종목", str(card.get("csub") or "")):
                    card["csub"] = f"{metric['rise']}종목 상승"
            if card.get("stocks"):
                # 애프터장은 20:00 마감 뒤 네이버가 'NXT 애프터 집계'가 아닌 다른 기준
                # (정규장 일별 합계)로 값을 돌려줘 검증된 NXT 거래대금(예: SK하이닉스 1.17조)이
                # 3.0조로 덮인다. 마감된 애프터 카드는 거래대금을 건드리지 않는다.
                keep_turnover = frozen is not None and s.get("key") == "aft"
                updated = []
                for stock in card["stocks"]:
                    live = (new.get("_prices", {}).get(str(stock.get("ticker")))
                            if stock.get("ticker") else None) \
                        or new.get("_prices", {}).get(stock.get("name"))
                    if live:
                        stock = dict(stock)
                        stock["price"] = live.get("price_text") or stock.get("price")
                        if live.get("chg") is not None:
                            stock["chg"] = live["chg"]
                        if live.get("turnover") and not keep_turnover:
                            stock["turnover"] = live["turnover"]
                    updated.append(stock)
                card["stocks"] = updated
            if card.get("metric_chg") is not None:
                if card.get("foot"):
                    card["foot"] = re.sub(r"(업종\s*)[+-]?\d+\.\d+%",
                                          lambda m: f"{m.group(1)}{card['metric_chg']:+.2f}%",
                                          card["foot"])
                card.pop("metric_chg", None)
            if stamp_hm and card.get("foot"):
                card["foot"] = (_freeze_text(card["foot"], frozen) if frozen
                                else _retime(card["foot"], stamp_hm))
            cards.append(card)
        if cards:
            m["cards"] = cards
        sessions.append(m)
    out["sessions"] = sessions

    # 관찰 5선: 가격·지표 갱신, 선정 이유·섹터 서사 유지
    live_watch = {w.get("ticker"): w for w in new.get("watchlist") or []}
    merged_watch = []
    for item in old.get("watchlist") or []:
        fresh = live_watch.get(item.get("ticker"))
        if not fresh:
            merged_watch.append(item)
            continue
        m = dict(item)
        for key in ("price", "chg", "prevClose", "day", "turnover", "rank"):
            if fresh.get(key) not in (None, "", "—"):
                m[key] = fresh[key]
        tech = dict(item.get("technical") or {})
        if fresh.get("technical"):
            tech["signals"] = fresh["technical"].get("signals") or tech.get("signals", [])
            for key in ("trend", "support", "resistance", "checkpoint"):
                if not tech.get(key):
                    tech[key] = fresh["technical"].get(key, "")
            # 거래량·캔들 흐름만은 순수 수치 요약이라 실시간 값으로 매번 교체
            if fresh["technical"].get("volumeFlow"):
                tech["volumeFlow"] = fresh["technical"]["volumeFlow"]
        m["technical"] = tech
        merged_watch.append(m)
    # 기존 목록에 없던 신규 종목은 뒤에 붙임
    used = {w.get("ticker") for w in merged_watch}
    for w in new.get("watchlist") or []:
        if w.get("ticker") not in used:
            merged_watch.append(w)
    out["watchlist"] = merged_watch[:5]
    return out


# ---------------------------------------------------------------- 메인
DYNAMIC_KEYS = ("updatedAt", "stamp", "asOf", "priceBasis", "rangeLabels")


def _without_dynamic(entry):
    """시각 표기만 다른지 비교하기 위한 사본."""
    clone = json.loads(json.dumps(entry, ensure_ascii=False))
    for key in DYNAMIC_KEYS:
        clone.pop(key, None)
    return clone


def charts_only(argv):
    """--charts-only — data.json 은 그대로 두고 일봉(charts)만 다시 만든다."""
    now = datetime.now(KST)
    if not DATA_PATH.exists():
        log("  · data.json 없음 — 먼저 전체 갱신을 실행하세요.")
        return 1
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    except Exception as exc:                # noqa: BLE001
        log(f"  · data.json 읽기 실패({type(exc).__name__})")
        return 1
    if not isinstance(data, list) or not data:
        log("  · data.json 형식이 아닙니다.")
        return 1
    entry = data[0]
    codes = [row[0] for row in (entry.get("allStocks") or []) if row]
    if not codes:
        log("  · allStocks 가 없어 차트를 만들 수 없습니다.")
        return 1
    charts, _ = build_charts(codes, entry.get("charts"), now)
    if not charts:
        log("  · 차트 생성 실패 — data.json 그대로 둡니다.")
        return 1
    entry["charts"] = charts
    text = serialize_data(data)
    if DATA_PATH.exists() and text == DATA_PATH.read_text(encoding="utf-8"):
        log("  · 변경 없음 — data.json 그대로 둡니다.")
        return 0
    DATA_PATH.write_text(text, encoding="utf-8")
    log(f"  · charts 갱신: {charts['asOf']} · {len(charts['stocks'])}종목 · "
        f"{len(text.encode()) / 1024:.1f}KB · 경고 {len(WARNINGS)}건")
    return 0


def scan_only(argv):
    """--scan-only [--date YYYY-MM-DD] — 조건식×수급 스캔과 차트 반응만 다시 만든다.

    · data.json 의 다른 필드(서사·마감 시각·closingPattern 등)는 절대 건드리지 않는다
      — 쓰기 전에 스캔 필드만 빼고 비교해 다르면 중단한다
    · 대상 항목은 --date(없으면 가장 최근 날짜)이고, 거래대금은 그 항목의 allStocks
    """
    now = datetime.now(KST)
    target = ""
    for i, arg in enumerate(argv):
        if arg.startswith("--date="):
            target = arg.split("=", 1)[1].strip()
        elif arg == "--date" and i + 1 < len(argv):
            target = argv[i + 1].strip()
    if not DATA_PATH.exists():
        log("  · data.json 없음 — 먼저 전체 갱신을 실행하세요.")
        return 1
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    except Exception as exc:                # noqa: BLE001
        log(f"  · data.json 읽기 실패({type(exc).__name__})")
        return 1
    if not isinstance(data, list) or not data:
        log("  · data.json 형식이 아닙니다.")
        return 1
    entry = next((d for d in data if str(d.get("date")) == target), None) if target else data[0]
    if entry is None:
        log(f"  · data.json 에 {target} 항목이 없습니다.")
        return 1
    rows = entry.get("allStocks") or []
    if not rows:
        log(f"  · {entry.get('date')} 항목에 allStocks 가 없어 거래대금을 확인할 수 없습니다.")
        return 1
    codes = [str(r[0]) for r in rows if r]
    extra = set()                     # 모달용 반응은 관찰 5선·카드 종목만(용량 관리)
    for w in entry.get("watchlist") or []:
        if w.get("ticker"):
            extra.add(str(w["ticker"]))
    for sess in entry.get("sessions") or []:
        for card in sess.get("cards") or []:
            for st in card.get("stocks") or []:
                if st.get("ticker"):
                    extra.add(str(st["ticker"]))
    log(f"[scan_only] {entry.get('date')} · 일봉 {len(codes)}종목 조회 중…")
    series = {}
    with ThreadPoolExecutor(max_workers=10) as pool:
        futures = {code: pool.submit(fetch_chart, code, SCAN_FETCH) for code in codes}
        for code, future in futures.items():
            bars = future.result() or []
            if len(bars) >= 116:
                series[code] = bars[-CHARTS_DAYS:]
    result = build_condition_scan(series, rows, extra, now)
    if not result or not result["meta"].get("asOf"):
        log("  · 일봉을 받지 못해 스캔을 만들지 않았습니다 — data.json 그대로 둡니다.")
        return 1

    # 다른 필드가 한 글자라도 바뀌면 쓰지 않는다(서사·마감 시각·closingPattern 보존)
    # · 스캔 저장분(scannersEncrypted)은 매번 새 salt 로 암호화되므로 비교에서 뺀다
    def without_scan(obj):
        clone = json.loads(json.dumps(obj, ensure_ascii=False))
        for key in SCAN_KEYS + (SCAN_ENC_KEY,):
            clone.pop(key, None)
        return json.dumps(clone, ensure_ascii=False, sort_keys=True)

    before = without_scan(entry)
    if not apply_scan(entry, result):
        log("  · 스캔을 암호화해 저장하지 못했습니다 — data.json 그대로 둡니다.")
        return 1
    if without_scan(entry) != before:
        log("  · 스캔 외 필드가 바뀌었습니다 — 쓰기를 중단합니다.")
        return 1
    scrub_scan_plaintext(data)
    text = serialize_data(data)
    DATA_PATH.write_text(text, encoding="utf-8")
    meta = result["meta"]
    log(f"  · 스캔 갱신: {meta['basis']} · {meta['scanned']}종목 계산 · "
        f"조건식 {len(result['scanners'])}개 · {len(text.encode()) / 1024:.1f}KB")
    for scanner in result["scanners"]:
        log(f"    [{scanner['name']}] {scanner['basis']} · {len(scanner['hits'])}종목 포착 "
            f"(거래대금 {scanner['minValue']}억+ · {scanner['formula']})")
        for hit in scanner["hits"]:
            log(f"      {hit['name']}({hit['code']}) {hit['valueText']} · 이격 {hit['gap']}% · {hit['summary']}")
        log(f"      모달용 차트 반응 {len(scanner['reactions'])}종목")
    if WARNINGS:
        log(f"    경고 {len(WARNINGS)}건")
    return 0


def main(argv):
    if "--charts-only" in argv:
        return charts_only(argv)
    if "--scan-only" in argv:
        return scan_only(argv)
    force = "--force" in argv
    now = datetime.now(KST)
    date_str = now.strftime("%Y-%m-%d")
    log(f"[update_market] {now.strftime('%Y-%m-%d %H:%M:%S')} KST · force={force}")

    if now.weekday() >= 5 and not force:
        log("  · 주말 — 갱신하지 않습니다.")
        return 0

    minutes = now.hour * 60 + now.minute
    if not force and not (8 * 60 <= minutes <= 21 * 60):
        log("  · 국내 거래시간(08:00~21:00 KST) 밖 — 갱신하지 않습니다.")
        return 0

    started = time.time()

    # 1) 지수·수급
    with ThreadPoolExecutor(max_workers=6) as pool:
        f_kospi = pool.submit(fetch_index, "KOSPI")
        f_kosdaq = pool.submit(fetch_index, "KOSDAQ")
        f_t_kospi = pool.submit(fetch_trend, "KOSPI")
        f_t_kosdaq = pool.submit(fetch_trend, "KOSDAQ")
        f_ind = pool.submit(fetch_industries)
        kospi, kosdaq = f_kospi.result(), f_kosdaq.result()
        trends = {"KOSPI": f_t_kospi.result(), "KOSDAQ": f_t_kosdaq.result()}
        industries = f_ind.result()

    if not kospi and not kosdaq:
        log("  · 지수 데이터를 받지 못했습니다. 갱신 중단(다음 실행에서 재시도).")
        return 1

    traded_at = (kospi or kosdaq or {}).get("traded_at") or ""
    if not force and not traded_at.startswith(date_str):
        log(f"  · 오늘({date_str}) 거래 데이터가 아직 없습니다(휴장일이거나 개장 전). "
            f"마지막 거래 {traded_at[:16]} — 갱신하지 않습니다.")
        return 0

    # 2) 종목 유니버스 + 순위
    with ThreadPoolExecutor(max_workers=8) as pool:
        f_mv = {m: pool.submit(fetch_market_values, m, (1, 2, 3, 4, 5)) for m in ("KOSPI", "KOSDAQ")}
        f_up = {m: pool.submit(fetch_rank, "up", m, 100) for m in ("KOSPI", "KOSDAQ")}
        f_sector = pool.submit(fetch_sector_map)
        f_down = {m: pool.submit(fetch_rank, "down", m, 30) for m in ("KOSPI", "KOSDAQ")}
        f_industry_stocks = {}
        for ind in (industries or [])[:2]:
            f_industry_stocks[ind["no"]] = pool.submit(fetch_industry_stocks, ind["no"])
        mv_by_market = {m: (f.result() or []) for m, f in f_mv.items()}
        up_all = []
        for m, f in f_up.items():
            up_all.extend(f.result() or [])
        sector_map = f_sector.result() or {}
        universe = mv_by_market["KOSPI"] + mv_by_market["KOSDAQ"]
        for m, f in f_down.items():
            universe.extend(f.result() or [])
        industry_stocks = {no: (f.result() or []) for no, f in f_industry_stocks.items()}

    quotes = {}
    for stock in universe:
        code = stock.get("itemCode")
        if not code or code in quotes:
            continue
        quotes[code] = stock
    stocks_only = [s for s in quotes.values()
                   if s.get("stockEndType") == "stock" and not is_etf(s.get("stockName") or "")]
    value_sorted = sorted(stocks_only,
                          key=lambda s: to_int(s.get("accumulatedTradingValueRaw")) or 0,
                          reverse=True)
    up_sorted = [s for s in up_all if s.get("stockEndType") == "stock" and not is_etf(s.get("stockName") or "")]

    # 3) 기존 data.json
    old_data = []
    if DATA_PATH.exists():
        try:
            loaded = json.loads(DATA_PATH.read_text(encoding="utf-8"))
            if isinstance(loaded, list):
                old_data = loaded
        except Exception as exc:            # noqa: BLE001
            warn(f"기존 data.json 파싱 실패({type(exc).__name__}) — 새로 작성합니다.")
    old_entry = next((d for d in old_data if d.get("date") == date_str), None)
    prev_entry = next((d for d in old_data if str(d.get("date")) < date_str), None)

    # 4) 관찰 5선 대상: 기존 항목의 티커 유지, 없으면 거래대금 상위
    targets = []
    if old_entry and old_entry.get("watchlist"):
        for w in old_entry["watchlist"]:
            if w.get("ticker"):
                targets.append((w["ticker"], w.get("name"), w.get("rank")))
    if len(targets) < 5:
        known = {t[0] for t in targets}
        for s in value_sorted:
            if s.get("itemCode") in known:
                continue
            targets.append((s["itemCode"], s.get("stockName"), len(targets) + 1))
            if len(targets) >= 5:
                break

    # 5) 관찰 종목 + 카드 종목 시세 (폴링 실시간 배치) + 관찰 종목 일봉
    card_codes, old_card_names = [], set()
    if old_entry:
        for sess in old_entry.get("sessions") or []:
            for card in sess.get("cards") or []:
                for st in card.get("stocks") or []:
                    if st.get("ticker"):
                        card_codes.append(str(st["ticker"]))
                    elif st.get("name"):
                        old_card_names.add(st["name"])

    code_to_name = {s.get("itemCode"): s.get("stockName")
                    for s in quotes.values() if s.get("stockName") and s.get("itemCode")}
    for name in old_card_names:
        for code, stock_name in code_to_name.items():
            if stock_name == name:
                card_codes.append(code)
                break

    target_codes = [code for code, _, _ in targets]
    all_codes = list(dict.fromkeys(target_codes + card_codes))
    realtime = fetch_realtime_stocks(all_codes) if all_codes else {}

    watch_quotes = {}
    price_map = {}
    with ThreadPoolExecutor(max_workers=8) as pool:
        f_chart = {code: pool.submit(fetch_chart, code) for code, _, _ in targets}
        for code, name, rank in targets:
            live = realtime.get(code) or {}
            stock = quotes.get(code) or {}
            rows = f_chart[code].result() or []
            price = live.get("price") or to_int(stock.get("closePriceRaw"))
            chg = live.get("chg")
            if chg is None:
                chg = to_float(stock.get("fluctuationsRatio"))
            day = {}
            if live.get("open"):
                day = {"open": live.get("open"), "high": live.get("high") or live.get("open"),
                       "low": live.get("low") or live.get("open"), "close": price}
            elif rows:
                last = rows[-1]
                day = {"open": last["o"], "high": last["h"], "low": last["l"], "close": price or last["c"]}
            ind = indicators(rows, now.strftime("%Y%m%d")) if rows else None
            rank_no = None
            for i, s in enumerate(value_sorted, start=1):
                if s.get("itemCode") == code:
                    rank_no = i
                    break
            turnover = (turnover_text(live.get("value_eok")) if live.get("value_eok")
                        else (hangeul_turnover(stock) if stock else "—"))
            watch_quotes[code] = {
                "code": code,
                "name": live.get("name") or name or stock.get("stockName"),
                "market": live.get("market") or ("KOSPI" if str(stock.get("sosok")) == "0" else "KOSDAQ"),
                "price": price,
                "price_text": comma(price),
                "chg": round(chg, 2) if chg is not None else None,
                "prevClose": live.get("prevClose") or (rows[-2]["c"] if rows and len(rows) > 1 else None),
                "day": day,
                "volume": live.get("volume") or (rows[-1]["v"] if rows else None),
                "turnover": turnover,
                "turnoverRank": f"전체 {rank_no}위" if rank_no and rank_no <= 20 else "",
                "ind": ind,
                "prevDate": ind.get("prevDate") if ind else None,
                "rank": rank,
            }

    # 카드 속 종목 시세도 같은 실시간 배치에서 (티커 우선, 없으면 이름 매칭)
    for code in card_codes:
        live = realtime.get(code)
        if not live:
            continue
        price_map[code] = {
            "price_text": comma(live.get("price")),
            "chg": round(live["chg"], 2) if live.get("chg") is not None else None,
            "turnover": turnover_text(live.get("value_eok")) if live.get("value_eok") else None,
        }
        if live.get("name"):
            price_map[live["name"]] = price_map[code]

    # 6) 새 항목 작성
    new_entry = build_new_entry(now, kospi, kosdaq, trends, industries, industry_stocks,
                                up_sorted, value_sorted, watch_quotes, prev_entry)
    industry_metric = {}
    for ind in industries or []:
        industry_metric.setdefault(_card_key(ind["name"]),
                                   {"chg": ind["chg"], "rise": ind["rise"], "fall": ind["fall"]})
    new_entry["_prices"] = price_map
    new_entry["_industry_metric"] = industry_metric
    all_stocks = build_all_stocks(mv_by_market, up_all, sector_map)
    if all_stocks:
        new_entry["allStocks"] = all_stocks
    entry = merge_entry(new_entry, old_entry)
    entry.pop("_prices", None)
    entry.pop("_industry_metric", None)
    entry.pop("_value_ranks", None)
    entry["updatedAt"] = now.isoformat(timespec="seconds")

    # 6-1) 차트(일봉) — 모달 📈 차트 탭용. 전 종목 인덱스 + 관찰·카드 종목
    chart_codes = [row[0] for row in (all_stocks or []) if row] + target_codes + card_codes
    # merge_entry 는 차트를 넘겨주지 않으므로, 같은 날짜의 이전 data.json 항목에서 캐시를 가져온다
    cached_charts = (old_entry or {}).get("charts") or entry.get("charts")
    charts, series = build_charts(chart_codes, cached_charts, now)
    if charts:
        entry["charts"] = charts
    else:
        entry.pop("charts", None)

    # 6-2) 조건식 × 당일 수급 교집합 + 과거 차트 반응 (거래량은 메모리에서만)
    if series:
        scan = build_condition_scan(series, all_stocks, set(target_codes + card_codes), now)
        if scan and apply_scan(entry, scan):
            log(f"    조건식×수급: {scan['meta']['scanned']}종목 계산 → {len(scan['hits'])}종목 포착 (암호화 저장)")
        else:
            carry_scan(entry, old_entry, prev_entry)
    else:
        # 일봉을 새로 받지 않은 실행(20분 캐시) — 직전 스캔을 그대로 이어 쓴다
        carry_scan(entry, old_entry, prev_entry)

    # 7) 병합 후 저장 (시각·스탬프만 달라졌으면 커밋하지 않음)
    if old_entry and _without_dynamic(entry) == _without_dynamic(old_entry):
        log("  · 시세가 그대로 — data.json 변경 없음.")
        return 0
    by_date = {d.get("date"): d for d in old_data if d.get("date")}
    by_date[date_str] = entry
    data = [by_date[k] for k in sorted(by_date, reverse=True)][:MAX_DATES]
    # 전 종목 시세 인덱스는 최신 날짜에만 — 지난 날짜 항목은 용량 관리를 위해 비운다
    for d in data:
        if d is not entry and d.get("date") != date_str:
            d.pop("allStocks", None)
            d.pop("charts", None)

    # allStocks는 종목 수가 많아 한 줄 압축(다른 필드는 그대로 읽기 좋게 들여쓰기 유지)
    rows = entry.get("allStocks")
    scrub_scan_plaintext(data)              # 조건식 평문은 어떤 경우에도 저장하지 않는다
    text = serialize_data(data)
    previous = DATA_PATH.read_text(encoding="utf-8") if DATA_PATH.exists() else ""
    if text == previous:
        log("  · 변경 없음 — data.json 그대로 둡니다.")
        return 0
    DATA_PATH.write_text(text, encoding="utf-8")

    elapsed = time.time() - started
    log(f"  · data.json 갱신 완료 ({len(data)}개 날짜, {len(text.encode()) / 1024:.1f}KB, {elapsed:.1f}초)")
    if rows:
        log(f"    전 종목 시세 인덱스 {len(rows)}종목 · 업종 매핑 {len(sector_map)}건")
    log(f"    코스피 {(kospi or {}).get('value')} ({pct_text((kospi or {}).get('chg'))}) · "
        f"코스닥 {(kosdaq or {}).get('value')} ({pct_text((kosdaq or {}).get('chg'))})")
    if industries:
        log("    상승 업종: " + ", ".join(f"{i['name']} {i['chg']:+.2f}%" for i in industries[:3]))
    log("    관찰 5선: " + ", ".join(f"{w['name']} {w['price']}" for w in entry.get("watchlist", [])))
    if WARNINGS:
        log(f"    경고 {len(WARNINGS)}건(위 목록) — 해당 부분은 이전 값 또는 대체 값으로 채웠습니다.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
