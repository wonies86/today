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

· 🗂 charts.json 분리(2026-11-25): 일봉(charts, 약 2.1MB)은 data.json 에서 빼
  `charts.json`({날짜: charts})에 따로 저장한다. 화면이 60초마다 다시 받는 본문이
  가벼워지고, index.html 은 차트가 필요할 때 ./charts.json 을 한 번만 받아 쓴다.
  data.json 에 charts 가 남아 있는 예전 형식도 읽어 charts.json 으로 옮긴다.

· 📈 차트 탭 고도화(2026-11-24): charts 에 거래량(vols·천주 단위)과 코스피·코스닥
  일봉 종가(index)를 함께 담아 화면이 거래량 서브차트와 RS(지수 대비 상대강도)를
  추정 없이 그린다. 주봉은 화면에서 날짜 기준으로 정확히 집계한다.

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
  (charts.stocks 는 [시,고,저,종] 4개 그대로 — 거래량은 charts.vols 에 종목코드별
   천주 단위 정수 배열로만 담는다. 조건식 스캔용 series 는 지금처럼 메모리에서만 쓴다)

사용법
  python3 scripts/update_market.py            # 자동 (주말·휴장일·거래시간 판단)
  python3 scripts/update_market.py --force    # 수동 강제 갱신 (workflow_dispatch)
  python3 scripts/update_market.py --charts-only     # data.json 은 두고 일봉만 재생성(charts.json)
  python3 scripts/update_market.py --scan-only [--date YYYY-MM-DD]  # 조건식 스캔만 재계산
  python3 scripts/verify_scan.py [--live]     # 스캔 결과 검증(정적/독립 재계산)
"""

from __future__ import annotations

import base64
import hashlib
import html as html_lib
import json
import math
import os
import re
import secrets
import subprocess
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
CHARTS_PATH = ROOT / "charts.json"       # 일봉(charts) 분리 파일 — data.json 은 60초마다 다시 받는 본문

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
CHARTS_DAYS = 120         # 종목당 보관 일봉 수(약 6개월 — 5·20·60일선 계산·주봉 24주·확대/축소에 충분)
CHARTS_MIN_BARS = 20      # 이보다 짧으면(신규상장·거래정지) 차트를 만들지 않는다
CHARTS_MARK = "__CHARTS_JSON__"
VOL_UNIT = 1000           # 거래량 저장 단위(주) — 천주 단위로 반올림해 담는다(용량 3,000KB 상한)
CHARTS_MAX_BYTES = 2_880_000   # charts 압축 본문 상한 — 넘으면 거래량(vols)을 빼고 저장한다
INDEX_SYMBOLS = (("KOSPI", "코스피"), ("KOSDAQ", "코스닥"))   # RS(상대강도) 기준 지수

# 주도 섹터 점유율(sectorDominance) — 화면 막대·카드 (모수 = 당일 등락률 +2% 이상 종목 거래대금)
RISE_MIN_PCT = 2.0       # 모수에 넣는 최소 당일 등락률(%) — 2026-11-23 사용자 확정("바꿔줘")
                         #   +1.99%는 제외, +2.00%는 포함 (이상 기준)
DOM_TOP = 3              # 기본 주도 섹터 수
DOM_TOP_MAX = 4          # 4번째 섹터 점유율이 DOM_FOURTH_SHARE 이상이면 4개까지
DOM_FOURTH_SHARE = 5.0   # 4번째 섹터를 넣는 최소 점유율(%) — 테마 통합 후 8~9% 테마가 10% 문턱에
                         #   걸려 개별이슈로 사라지던 문제로 10.0 → 5.0 (2026-11-23 사용자 지적)
DOM_STOCKS = 5           # 섹터 카드에 담는 종목 수(거래대금 순)
DOM_IND_STOCKS = 6       # 개별이슈 카드에 담는 종목 수

# ── 시총 대비 회전율(2026-11-27) — 화면의 「자금순 | 회전율순」 전환 ───────────────
# 거래대금은 큰 종목이 늘 이기므로, 같은 수급을 **시가총액 대비 거래대금**으로도 본다.
# 초소형 품절주(시총 300억에 거래대금 200억 = 회전율 66%)가 섹터 회전율을 통째로
# 왜곡하지 않도록 집계 모수에 **거래대금 TURNOVER_MIN_VALUE억 이상**을 둔다.
TURNOVER_MIN_VALUE = 300     # 회전율 집계 최소 거래대금(억) — 이 미만 종목은 분자·분모 모두 제외
                             #   100 → 300 (2026-11-27 사용자 확정 — 초소형 품절주 잡음 제거)
TURNOVER_STOCKS = 5          # 회전율순 종목 목록 크기(섹터 카드 한 칸)
TURNOVER_SECTOR_MAX = 4      # 회전율순으로 보여줄 섹터 수(막대·카드는 4개까지)
TURNOVER_SECTOR_MIN_COUNT = 2  # 회전율순 섹터 최소 종목 수 — 1종목짜리 섹터는 순위에서 뺀다

# ── NXT 프리마켓(08:00~08:50) — 장전 탭 「🌅 NXT 프리장 수급」 카드 ───────────────
# 정규장 집계(sectorDominance·allStocks)와 완전히 분리된 preMarket 블록만 갱신한다.
# 소스: 네이버 polling API 의 overMarketPriceInfo(tradingSessionType=PRE_MARKET)
PRE_MARKET_START = 8 * 60        # 08:00 KST
PRE_MARKET_END = 8 * 60 + 50     # 08:50 KST (NXT 프리마켓 종료)
# 프리장 섹터 점유율의 모수도 정규장과 같은 방식으로 상승 종목만 잡는다(+1%↑) —
#   전체 체결을 모수로 쓰면 하락 대형주(SK하이닉스 -1.33% 등)의 거래대금이 섹터 1위를 만드는 착시가 생긴다.
#   정규장은 +2%↑ 이지만 프리장은 표본이 적고 변동성이 커서 +1%↑ 로 둔다(2026-11-27 사용자 확정 "1+2 조합").
PRE_RISE_MIN_PCT = 1.0           # 프리장 모수 최소 등락률(%) — +0.99% 제외, +1.00% 포함
PRE_VALUE_TOP = 10               # 거래대금 상위 종목 수(프리장 전체 체결 기준)
PRE_RISE_TOP = 10                # 상승률 상위 종목 수
PRE_SECTOR_TOP = 5               # 점유율 막대 섹터 수
PRE_SECTOR_STOCKS = 3            # 섹터 카드에 담는 종목 수
PRE_TAIL_MIN_SHARE = 3.0         # 나머지 섹터를 묶을 최소 섹터 점유율(%) — 이보다 작으면 개별이슈
PRE_MIN_VALUE = 0.3              # 상승률 상위 후보 최소 프리장 거래대금(억) — 잡음 제거
PRE_REASON_CODES = 18            # 상승 사유(뉴스 헤드라인)를 붙일 최대 종목 수
PRE_REASON_LEN = 52              # 사유 문장 길이 상한(글자)
PRE_QUOTE_WORKERS = 10           # 프리장 시세 병렬 스레드 수

# ── 기관·외국인 연속 순매수(investorStreak) + 종목 뉴스 악재 스캔 ────────────────
# 599종목을 매번 긁으면 갱신이 느려진다 — 화면에 실제로 노출되는 종목(주도 섹터 카드·
# 관찰 5선·조건식 포착)만 병렬로 받는다. 실패한 종목은 배지만 빠지고 나머지는 그대로.
INVESTOR_TREND_URL = API + "/stock/{code}/trend"        # itemCode·bizdate·foreignerPureBuyQuant·organPureBuyQuant
INVESTOR_NEWS_URL = API + "/news/stock/{code}"          # [{items:[{title, body, mobileNewsUrl, datetime, officeName}]}]
INVESTOR_TIMEOUT = 4          # 종목당 타임아웃(초)
INVESTOR_WORKERS = 12         # 병렬 수집 스레드 수 (27종목×2요청 ≈ 2.6초)
INVESTOR_MAX_CODES = 48       # 한 실행에서 수집할 최대 종목 수(갱신 시간 상한)
INVESTOR_DAYS = 10            # trend API 가 주는 최근 거래일(최대 10)
INVESTOR_RECENT = 5           # recent5 에 담는 거래일 수
INVESTOR_MIN_STREAK = 2       # 배지를 붙이는 최소 연속 일수
INVESTOR_TTL_MIN = 30         # 연속매수 캐시 유효 시간(분) — 순매수 수량은 하루 한 번 바뀐다
NEWS_TTL_MIN = 15             # 뉴스 캐시 유효 시간(분)
NEWS_COUNT = 3                # 종목당 수집 기사 수

# 종목 뉴스에 섞여 오는 무관 기사 — 제목에 종목명이 없을 때만 이 단어로 거른다.
# (아파트 분양 홍보·견본주택 안내처럼 그 종목과 상관없는 부동산 기사)
NEWS_JUNK_WORDS = (
    "분양", "모델하우스", "견본주택", "청약", "입주자모집",
    "아파트", "오피스텔", "파크밸리", "단독주택",
)

# 악재 키워드 — 종목 뉴스 제목·요약에서 찾는다(사전에 없는 단어는 만들지 않는다)
NEWS_BAD_WORDS = (
    "유상증자", "전환사채", "CB", "BW", "신주인수권", "3자배정", "횡령", "배임",
    "투자경고", "투자주의환기", "거래정지", "감사의견", "실적쇼크",
    "관리종목", "불성실공시", "상장폐지", "파산", "회생절차",
    "압수수색", "경영권분쟁", "무상감자", "감자결정", "소송",
    "리콜", "단기과열", "공매도과열", "목표가하향",
)
# 영문 약어는 단어 경계로만 — 'CBE'·'BWTS' 같은 낱말 안에서는 잡지 않는다
NEWS_BAD_ASCII = {
    "CB": r"(?<![A-Za-z0-9])CB(?![A-Za-z0-9])",
    "BW": r"(?<![A-Za-z0-9])BW(?![A-Za-z0-9])",
}

# ── 실전 테마 매핑 ─────────────────────────────────────────────────────────────
# 네이버 업종명(`기계`·`화장품`·`소프트웨어` …)은 같은 테마를 여러 업종으로 찢어 놓는다.
# 그래서 수급이 로봇·보안·중국(소비)에 몰려도 `기계`·`소프트웨어`·`화장품`이 작은 조각으로
# 흩어져 `개별이슈`에 묻혔다. **등락률 기준(+2% 이상)과 모수는 그대로 두고 분류 이름만** 실전
# 테마로 바꾼다 — 테마에 없는 종목은 네이버 업종명을 그대로 쓴다.
#   · 로봇      : 기계 업종의 로봇주 + 다른 업종으로 빠진 로봇주 (이름에 로봇/로보틱스 포함 자동)
#   · 보안      : 사이버·정보보안주 (네이버 업종이 소프트웨어·IT서비스 등으로 흩어져 있다)
#   · 중국·소비 : 화장품 업종 전체 + 엔터·미디어 / 여행·카지노·면세
ROBOT = "로봇"
SECURITY = "보안"
CHINA_CONSUMER = "중국·소비"
THEME_NAMES = (ROBOT, SECURITY, CHINA_CONSUMER)


def _norm_name(name) -> str:
    """종목명 비교용 — 공백 제거·대문자 (GKL·JYP Ent. 같은 표기 차이 흡수)."""
    return re.sub(r"\s+", "", str(name or "")).upper()


# 로봇 — 이름에 로봇/로보틱스가 없어 자동 매칭이 안 되는 로봇주(부품·감속기·로봇비전 포함)
ROBOT_NAMES = {
    "에이엘로봇", "로보티즈", "레인보우로보틱스", "휴림로봇", "코스모로보틱스", "두산로보틱스",
    "유일로보틱스", "티로보틱스", "에스피지", "현대무벡스", "제닉스로보틱스", "고영",
    "빅웨이브로보틱스", "삼현", "클로봇", "씨메스", "케이엔알시스템", "엔젤로보틱스",
    "뉴로메카", "로보스타", "에스비비테크", "로킷헬스케어", "피앤에스로보틱스", "아이로보틱스",
}
# 보안 — 사이버·정보보안(네이버 업종: 소프트웨어·IT서비스·통신장비 등으로 분산)
SECURITY_NAMES = {
    "안랩", "지니언스", "지슨", "한싹", "라온시큐어", "샌즈랩", "파수", "파수AI", "시큐브",
    "윈스", "모니터랩", "시큐레터", "아톤", "이글루", "이글루코퍼레이션", "케이사인",
    "드림시큐리티", "한국정보인증", "카티스", "인스웨이브",
}
# 중국·소비 — 엔터·미디어 / 여행·카지노·면세 (화장품은 업종 전체를 아래에서 묶는다)
CHINA_CONSUMER_NAMES = {
    "스튜디오드래곤", "CJ ENM", "CJ CGV", "하이브", "에스엠", "JYP Ent.", "와이지엔터테인먼트",
    "디어유", "노랑풍선", "모두투어", "참좋은여행", "파라다이스", "GKL", "롯데관광개발",
    "호텔신라", "실리콘투", "마녀공장", "아모레퍼시픽",
    "아모레G", "한국화장품", "한국콜마", "코스맥스", "코스메카코리아", "에이피알", "달바글로벌",
}
ROBOT_SET = {_norm_name(n) for n in ROBOT_NAMES}
SECURITY_SET = {_norm_name(n) for n in SECURITY_NAMES}
CHINA_CONSUMER_SET = {_norm_name(n) for n in CHINA_CONSUMER_NAMES}
CHINA_CONSUMER_SECTORS = {"화장품"}   # 네이버 업종 `화장품`은 통째로 중국·소비


def theme_of(name, sector) -> str:
    """종목 하나의 표시 분류 — 실전 테마가 있으면 테마명, 없으면 네이버 업종명."""
    key = _norm_name(name)
    if key in ROBOT_SET or "로봇" in key or "로보틱스" in key:
        return ROBOT
    if key in SECURITY_SET:
        return SECURITY
    if key in CHINA_CONSUMER_SET or str(sector or "") in CHINA_CONSUMER_SECTORS:
        return CHINA_CONSUMER
    return str(sector or "")

# 조건식 × 당일 수급 교집합 — 키움 조건식 A·B·C·D·E + 거래대금 100억 이상
SCAN_MIN_VALUE = 100      # 교집합 최소 거래대금(억 원)
TREND_MIN_VALUE = 300     # 추세지속주 교집합 최소 거래대금(억 원) — 대형·중대형주만
SCAN_RULE = "A and (B or C) and D and E"
SCAN_FETCH = 130          # 스캔용 일봉 조회 개수(보관 120봉에 여유를 둔다)
SCAN_KEYS = ("scanners", "conditionHits", "conditionScan", "chartReactions")

# ── 종가베팅 핵심 지표 — 52주 신고가·앞전 매물대 소화·오후장 수급 ────────────────
#   2026-11-24 사용자 확정: "종가매매 핵심 2가지(4번 오후장 돈 유입/분봉 우상향,
#   6번 52주 신고가 근접·앞전 매물대 소화)"를 대시보드에 추가한다.
#   · 52주 신고가는 일봉 250거래일이 필요해 전 종목(120봉)으로는 계산할 수 없다
#     → 거래대금 300억 이상 + 관찰·카드 종목만 260거래일 일봉을 따로 받아 계산한다
#   · 오후장 수급은 장중 분봉 실측(네이버 fchart 분봉) — 13:00 이전에는 계산하지 않는다
SCAN_BARS = 260           # 52주 계산용 일봉 조회 수(250거래일 + 여유)
HIGH52_BARS = 250         # 52주 = 약 250거래일
SHELF_DAYS = 60           # 앞전 매물대 = 최근 60거래일 최대 거래량일
EDGE_MIN_VALUE = 300      # 종가베팅 핵심 교집합 최소 거래대금(억 원)
EDGE_REL_MIN = 2.0        # '지수 대비 강세' 기준(%p) — 종목 등락률 − 소속 지수 등락률
EDGE_NEAR_PCT = 10.0      # 52주 신고가 '근접' 기준(고점 대비 -10% 이내)
EDGE_DEEP_MAX = 160       # 250거래일 일봉을 받을 최대 종목 수(갱신 시간 상한)
PM_START_MIN = 13 * 60          # 오후장 시작 13:00
PM_JUDGE_MIN = 13 * 60 + 30     # 오후장 비중 판정 시작 13:30 (30분 이상 쌓인 뒤)
PM_END_MIN = 15 * 60 + 30       # 정규장 마감 15:30
PM_SHARE_MIN = 30.0       # '오후장 유입' 기준 — 13:00 이후 거래대금 비중(%)
PM_MAX_FETCH = 24         # 한 실행에서 분봉을 받을 최대 종목 수
SCAN_REFRESH_MIN = 25     # 오후장 판정 중 스캔을 다시 계산하는 간격(분)

# ── 주도돌파 100점 (2026-11-27) — 승률·기대수익이 높은 쪽을 100점으로 채점 ──────
#   2026-11-27 사용자 요청: "승률 기대수익이 높은쪽으루볼수있는 조건식쪽에 추가해주고
#   100점만점 으로 해서 몇점정도 될지도 표시해줘" — 같은 날 120거래일 D+1 백테스트에서
#   정배열 + 강한 상승(레인보우로보틱스 정배열 +8%↑ → D+1 62.5% · 평균 +2.30%)이
#   반도체 단순 반등(50% · -1.33%)·눌림(30%)보다 나왔던 결과를 조건식으로 옮긴다.
BREAKOUT_MIN_VALUE = 300  # 당일 거래대금 교집합(억 원)
BREAKOUT_TOP = 15         # 점수 내림차순 상위 종목 수
BREAKOUT_WIN_BARS = 120   # D+1 승률 백테스트 창(거래일)
BREAKOUT_STRONG = 5.0     # 1차 유사 강세일 — 정배열 + 당일 +5% 이상
BREAKOUT_STRONG_WIDE = 3.0  # 표본이 모자랄 때 2차 기준 — 정배열 + 당일 +3% 이상
BREAKOUT_MIN_SAMPLES = 3  # 이보다 적으면 더 넓은 기준으로 다시 센다
BREAKOUT_CAP = {"lead": 40, "trend": 25, "win": 25, "flow": 10}   # 100점 배분(2026-11-27 개편)
BREAKOUT_MIN_SCORE = 51   # 목록에 올릴 최소 점수 — 51점 초과(52점 이상)만
#   2026-11-27 사용자 요청 2차: "주도 40 · 정배열 25 · 승률 25 · 수급 10" 배점으로 바꾸고
#   목록은 51점 초과만 남긴다.
MINUTE_URL = FCHART + "?symbol={code}&timeframe=minute&count=400&requestType=0"

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
                "mv_eok": _mcap_eok(d.get("marketValueFullRaw") or d.get("marketValueRaw")),
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


def _mcap_eok(raw):
    """시가총액 원 → 억 원 정수. 값이 없거나 0이면 None(회전율을 만들지 않는다)."""
    n = to_int(raw)
    if not n or n <= 0:
        return None
    return int(round(n / 1e8))


def _turnover_pct(value_eok, mcap_eok):
    """시총 대비 회전율(%) = 거래대금 ÷ 시가총액 × 100 — 시총이 없으면 None."""
    if value_eok is None or mcap_eok is None:
        return None
    try:
        v, m = float(value_eok), float(mcap_eok)
    except (TypeError, ValueError):
        return None
    if m <= 0:
        return None
    return round(v / m * 100, 2)


def _row_mcap(row):
    return row[7] if isinstance(row, list) and len(row) > 7 else None


def _row_turn(row):
    return row[8] if isinstance(row, list) and len(row) > 8 else None


def _fill_missing_mcaps(rows):
    """시총 상위 500 밖에서 거래대금 순으로 들어온 종목의 시총을 polling 으로 채운다.

    allStocks 요소 [7]=시총(억), [8]=회전율(%). 30종목씩 한 번에 받으므로 보통 1~2회 요청이다.
    실패하면 그대로 None — 회전율을 지어내지 않는다.
    """
    missing = [r for r in (rows or []) if isinstance(r, list) and _row_mcap(r) is None]
    codes = [str(r[0]) for r in missing if r and r[0]]
    if not codes:
        return
    got = {}
    for i in range(0, len(codes), 30):
        data = get_json(f"{POLL_BASE}/stock/" + ",".join(codes[i:i + 30]), tries=1) or {}
        for d in data.get("datas") or []:
            mv = _mcap_eok(d.get("marketValueFullRaw"))
            if mv and d.get("itemCode"):
                got[str(d["itemCode"])] = mv
    for r in missing:
        while len(r) < 9:
            r.append(None)
        r[7] = got.get(str(r[0]))
        r[8] = _turnover_pct(r[5], r[7])


def build_all_stocks(mv_by_market, movers, sector_map):
    """KOSPI·KOSDAQ 전 종목 시세 인덱스
    — [[코드, 이름, 시장, 현재가, 등락%, 거래대금(억), 업종, 시총(억), 회전율(%)]].

    소스: 시가총액 상위 500(KOSPI·KOSDAQ 각각) + 당일 상승·하락 상위(movers),
    그중 시가총액 150위 안은 무조건, 나머지는 거래대금 순으로 시장당 300종목까지.
    · 8번째(인덱스 7)는 시가총액(억 원) — marketValue 를 그대로 억 단위로 옮긴 실측값
    · 9번째(인덱스 8)는 회전율(%) = 거래대금 ÷ 시총 × 100 (시총 없으면 None)
      기존 화면·코드는 앞 7개만 읽으므로 과거 날짜(7개)와도 함께 동작한다.
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
            mcap = _mcap_eok(s.get("marketValueRaw"))
            picked.append([s.get("itemCode"), name, market, price,
                           round(chg, 2) if chg is not None else None,
                           value_eok, sector_map.get(s.get("itemCode"), ""),
                           mcap, _turnover_pct(value_eok, mcap)])
        picked.sort(key=lambda r: -r[5])
        rows.extend(picked)
    _fill_missing_mcaps(rows)
    return rows


# ---------------------------------------------------------------- 주도 섹터 점유율
def _large_eok(v) -> str:
    """억 단위 금액을 읽기 좋게 — 30,954 → '3조954억', 897 → '897억'."""
    v = int(round(v or 0))
    if v >= 10000:
        jo, eok = divmod(v, 10000)
        return f"{jo:,}조{eok:,}억" if eok else f"{jo:,}조"
    return f"{v:,}억"


def _dom_stock(s):
    """섹터 카드 종목 한 개 — 시총(억)·회전율(%)까지. 없으면 None(화면은 — 표시)."""
    return {"code": s[0], "name": s[1], "market": s[2], "price": s[3],
            "chg": s[4], "valueEok": s[5],
            "marketCap": _row_mcap(s), "turnoverPct": _row_turn(s)}


def _sector_turnover(stocks):
    """섹터 회전율 — 거래대금 합 ÷ 시총 합 × 100(가중), 종목 평균도 함께.

    · 가중 회전율이 카드·막대의 기준값이다(대형주 한 종목이 섹터를 좌우하는 것을 막는다)
    · 시총을 모르는 종목이 하나라도 있으면 그 종목은 분자·분모 모두에서 뺰다
      — 반쪽 시총으로 나누어 회전율을 부풀리지 않는다
    """
    known = [s for s in stocks if _row_mcap(s) and s[5] is not None]
    mc = sum(_row_mcap(s) for s in known)
    val = sum(s[5] or 0 for s in known)
    tps = [_row_turn(s) for s in stocks if _row_turn(s) is not None]
    return {
        "marketCapEok": int(round(mc)) if known else None,
        "turnoverPct": round(val / mc * 100, 2) if mc else None,
        "avgTurnoverPct": round(sum(tps) / len(tps), 2) if tps else None,
    }


def _turnover_stocks(stocks, cap=TURNOVER_STOCKS, min_value=TURNOVER_MIN_VALUE):
    """섹터 안에서 회전율 높은 순 종목 목록 — 화면의 「회전율순」 종목 줄.

    섹터 회전율 집계와 **같은 모수**(거래대금 min_value억 이상)만 쓴는다 —
    집계에서 뺀 초소형주를 종목 목록에서만 다시 올리지 않는다.
    """
    pool = [s for s in stocks if _row_turn(s) is not None and (s[5] or 0) >= min_value]
    return [_dom_stock(s) for s in sorted(pool, key=lambda s: -(_row_turn(s) or 0))[:cap]]


def _dom_block(name, stocks, cap=DOM_STOCKS):
    """섹터 하나(또는 개별이슈 묶음)의 카드 데이터 — allStocks 실측값만."""
    values = [s[5] for s in stocks]
    chgs = [s[4] for s in stocks if s[4] is not None]
    picked = sorted(stocks, key=lambda s: -s[5])[:cap]
    block = {
        "name": name,
        "valueEok": int(sum(values)),
        "count": len(stocks),
        "rise": sum(1 for c in chgs if c > 0),
        "fall": sum(1 for c in chgs if c < 0),
        "chg": round(sum(chgs) / len(chgs), 2) if chgs else None,
        "stocks": [_dom_stock(s) for s in picked],
    }
    block.update(_sector_turnover(stocks))
    return block


def _is_rising_at(row, pct) -> bool:
    """allStocks 한 줄이 당일 등락률 pct 이상인지 — 등락률이 없으면 False.

    경계는 이상(>=) — +1.99%는 제외, +2.00%는 포함.
    """
    try:
        return float(row[4]) >= pct
    except (TypeError, ValueError, IndexError):
        return False


def _is_rising(row) -> bool:
    """allStocks 한 줄이 당일 등락률 RISE_MIN_PCT(+2.0%) 이상인지."""
    return _is_rising_at(row, RISE_MIN_PCT)


def _rise_label() -> str:
    """모수 기준 표기 — '+2%↑' (RISE_MIN_PCT 가 정수면 소수점 없이)."""
    pct = f"{RISE_MIN_PCT:g}"
    return f"+{pct}%↑"


def _pre_rise_label() -> str:
    """프리장 모수 기준 표기 — '+1%↑'."""
    return f"+{PRE_RISE_MIN_PCT:g}%↑"


def build_turnover_block(rows, rise_min, asof, rise_label="", stock_fn=None,
                         stock_cap=DOM_STOCKS, ind_cap=DOM_IND_STOCKS,
                         min_value=TURNOVER_MIN_VALUE):
    """시총 대비 회전율 기준의 섹터 순위 — 「자금순」과 **같은 모양**의 블록.

    · 모수: 업종이 있는 종목 중 ① 거래대금 min_value(TURNOVER_MIN_VALUE=300억) 이상
      ② 당일 등락률 rise_min 이상(정규장 +2%, 프리장 +1%) — 초소형 품절주 왜곡 방지
    · 섹터 회전율 = 섹터 모수 종목 거래대금 합 ÷ 시총 합 × 100 (가중)
    · 순서는 섹터 회전율 높은 순, 최대 TURNOVER_SECTOR_MAX개. 주도 3개로 자르면
      자금은 적지만 도는 섹터가 사라지므로 회전율 기준은 4개까지 둔다
    · 모수 종목이 TURNOVER_SECTOR_MIN_COUNT(2)개 미만인 섹터는 순위에서 뺀다 —
      한 종목의 하루 회전을 섹터 회전율처럼 보여 주지 않는다. 뺀 종목은 「개별이슈」로
      내려보내 점유 합계는 그대로 둔다
    · stocks(거래대금순)와 topTurnover(회전율순)를 함께 담아 화면이 정렬만 전환한다
    """
    stock_fn = stock_fn or _dom_stock
    pool = [r for r in (rows or [])
            if isinstance(r, list) and len(r) > 7 and r[6] and r[7]
            and (r[5] or 0) >= min_value and _is_rising_at(r, rise_min)]
    if not pool:
        return None
    total = sum(r[5] for r in pool)
    total_mc = sum(r[7] for r in pool)
    if total <= 0 or total_mc <= 0:
        return None

    groups: dict[str, list] = {}
    for r in pool:
        groups.setdefault(theme_of(r[1], r[6]), []).append(r)

    def tp(stocks):
        mc = sum(s[7] for s in stocks if s[7])
        return (sum(s[5] for s in stocks) / mc * 100) if mc else 0.0

    ranked = sorted(groups.items(), key=lambda kv: -tp(kv[1]))
    # 1종목짜리 섹터는 건너뛰고, 자격(2종목↑)을 갖춘 섹터로 TURNOVER_SECTOR_MAX개를 채운다
    picked = [(name, stocks) for name, stocks in ranked
              if len(stocks) >= TURNOVER_SECTOR_MIN_COUNT][:TURNOVER_SECTOR_MAX]
    sectors = []
    used = 0.0
    for name, stocks in picked:
        block = _dom_block(name, stocks, stock_cap)
        block["stocks"] = [stock_fn(s) for s in sorted(stocks, key=lambda s: -s[5])[:stock_cap]]
        turn_pool = [s for s in stocks if _row_turn(s) is not None and (s[5] or 0) >= min_value]
        block["topTurnover"] = [stock_fn(s) for s in
                                sorted(turn_pool, key=lambda s: -(_row_turn(s) or 0))[:stock_cap]]
        block["share"] = round(block["valueEok"] / total * 100, 1)
        used += block["share"]
        sectors.append(block)
    if not sectors:
        return None

    # 카드에 못 든 종목(섹터 수 초과 + 1종목 섹터)은 모두 「개별이슈」로
    used_names = {name for name, _stocks in picked}
    rest = [r for name, stocks in ranked if name not in used_names for r in stocks]
    individual = None
    if rest:
        individual = _dom_block("개별이슈", rest, ind_cap)
        ind_pool = [s for s in rest if _row_turn(s) is not None and (s[5] or 0) >= min_value]
        individual["topTurnover"] = [stock_fn(s) for s in
                                     sorted(ind_pool, key=lambda s: -(_row_turn(s) or 0))[:ind_cap]]
        individual["share"] = round(100.0 - used, 1)

    label = rise_label or f"+{rise_min:g}%↑"
    return {
        "asOf": asof,
        "basisMode": "riseTurnover",
        "minValueEok": min_value,
        "minSectorCount": TURNOVER_SECTOR_MIN_COUNT,
        "riseMinPct": rise_min,
        "universe": len(pool),
        "valueEok": int(round(total)),
        "marketCapEok": int(round(total_mc)),
        "turnoverPct": round(total / total_mc * 100, 2),
        "basis": (f"거래대금 {min_value}억↑ · {label} 상승 {len(pool):,}종목 · "
                  f"{TURNOVER_SECTOR_MIN_COUNT}종목↑ 섹터 {len(sectors)}개 · "
                  f"합계 {_large_eok(total)} · 시총 {_large_eok(total_mc)}"),
        "rule": (f"회전율 = 섹터 거래대금 ÷ 섹터 시가총액 × 100 "
                 f"(모수: 거래대금 {min_value}억↑ · {label} 상승 종목 · "
                 f"{TURNOVER_SECTOR_MIN_COUNT}종목↑ 섹터)"),
        "sectors": sectors,
        "individual": individual,
    }


def build_sector_dominance(all_stocks, now):
    """주도 섹터 점유율 — **당일 +2% 이상 상승 종목**의 거래대금 비중을 섹터별로 계산한다.

    · 모수: 전 종목 인덱스(allStocks) 중 당일 등락률이 RISE_MIN_PCT(+2.0%) 이상인 종목이면서
      업종이 붙고 거래대금이 있는 종목. 하락·보합·+2% 미만 종목의 거래대금은 넣지 않는다.
      화면에 그 모수(종목 수·금액)를 그대로 적는다 — 시장 전체 거래대금이 아니다.
    · 분류: `theme_of()`가 실전 테마(로봇·보안·중국·소비)를 먼저 붙이고, 테마에 없는
      종목만 네이버 업종명을 쓴다(네이버 업종이 테마를 여러 업종으로 찢어 놓기 때문).
    · 점유율 = 섹터 합산 거래대금 ÷ +2% 이상 종목 거래대금 × 100 (한 자리 반올림)
    · 상위 3개(4번째 섹터가 5% 이상이면 4개)를 주도 섹터로, 나머지 +2% 이상 종목을
      `개별이슈`로 묶어 합계가 정확히 100.0%가 되게 한다
    · 등락률은 섹터 종목의 단순 평균(실측 등락률만), 추정·보간 없음
    · +2% 이상 종목이 하나도 없는 날은 None — 화면은 이 패널을 숨긴다
    """
    rows = [r for r in (all_stocks or [])
            if isinstance(r, list) and len(r) >= 7 and r[6] and (r[5] or 0) > 0
            and _is_rising(r)]
    total = sum(r[5] for r in rows)
    if not rows or total <= 0:
        return None

    groups: dict[str, list] = {}
    for r in rows:
        groups.setdefault(theme_of(r[1], r[6]), []).append(r)

    ranked = sorted(groups.items(), key=lambda kv: -sum(r[5] for r in kv[1]))
    top = DOM_TOP
    if len(ranked) > DOM_TOP:
        fourth = sum(r[5] for r in ranked[DOM_TOP][1]) / total * 100
        if fourth >= DOM_FOURTH_SHARE:
            top = DOM_TOP_MAX

    sectors = []
    for name, stocks in ranked[:top]:
        block = _dom_block(name, stocks)
        block["topTurnover"] = _turnover_stocks(stocks)
        sectors.append(block)
    used = 0.0
    for item in sectors:
        item["share"] = round(item["valueEok"] / total * 100, 1)
        used += item["share"]

    rest = [r for _name, stocks in ranked[top:] for r in stocks]
    individual = _dom_block("개별이슈", rest, DOM_IND_STOCKS) if rest else None
    if individual:
        individual["share"] = round(100.0 - used, 1)
    elif sectors:
        # 남는 종목이 없으면 마지막 섹터에서 반올림 잔차를 흡수해 100.0%로 맞춘다
        sectors[-1]["share"] = round(sectors[-1]["share"] + (100.0 - used), 1)

    asof = now.strftime("%H:%M")
    return {
        "asOf": asof,
        "basis": f"{_rise_label()} {len(rows):,}종목 · 거래대금 {_large_eok(total)}",
        "basisMode": "rise",
        "totalEok": int(total),
        "universe": len(rows),
        "sectors": sectors,
        "individual": individual,
        "rule": f"점유율 = 섹터 합산 거래대금 ÷ {_rise_label()} 종목 거래대금",
        # 시총 대비 회전율 — 화면의 「자금순 | 회전율순」 두 번째 기준
        "turnover": build_turnover_block(all_stocks, RISE_MIN_PCT, asof,
                                        rise_label=_rise_label()),
    }


# ---------------------------------------------------------------- NXT 프리마켓

def _pre_market_rows(datas, industry_map):
    """polling 응답 → 프리장 체결 행
    [코드, 이름, 시장, 현재가, 등락%, 거래대금(억), 업종, 시총(억), 회전율(%)].

    overMarketPriceInfo 의 tradingSessionType 이 PRE_MARKET 인 것만 쓴다 — 정규장·애프터장
    값이 섞이지 않게 하는 첫 번째 방어선이다. 프리장 체결이 없는 종목(NXT 미상장 등)은 빠진다.
    """
    rows = []
    for d in datas or []:
        over = d.get("overMarketPriceInfo") or {}
        if str(over.get("tradingSessionType") or "") != "PRE_MARKET":
            continue
        price = to_int(over.get("overPrice"))
        chg = to_float(over.get("fluctuationsRatio"))
        value = (to_int(over.get("accumulatedTradingValueRaw")) or 0) / 1e8
        volume = to_int(over.get("accumulatedTradingVolumeRaw")) or 0
        if not price or value <= 0:
            continue
        code = str(d.get("itemCode") or "").strip()
        if not code:
            continue
        exchange = (d.get("stockExchangeType") or {}).get("nameKor") or ""
        market = "KOSPI" if "코스피" in exchange else ("KOSDAQ" if "코스닥" in exchange else exchange)
        mcap = _mcap_eok(d.get("marketValueFullRaw") or d.get("marketValueRaw"))
        rows.append([code, d.get("stockName") or code, market, price,
                     round(chg, 2) if chg is not None else None, value,
                     industry_map.get(code) or "", mcap, _turnover_pct(value, mcap)])
    return rows


def _pre_stock(row, reasons):
    """프리장 종목 한 줄 — 화면·캡처가 같이 쓰는 모양."""
    return {
        "code": row[0], "name": row[1], "market": row[2],
        "price": row[3], "priceText": comma(row[3]),
        "chg": row[4], "valueEok": int(round(row[5])),
        "valueText": turnover_text(row[5]) or _large_eok(row[5]),
        "marketCap": _row_mcap(row), "turnoverPct": _row_turn(row),
        "reason": reasons.get(row[0]) or "",
    }


def _pre_news_reason(code, name=""):
    """종목 최신 뉴스 헤드라인 한 줄 — 그 종목 기사만. 확인 안 되면 빈 문자열.

    네이버 종목 뉴스에는 시황·애프터마켓 리뷰처럼 종목과 무관한 기사도 섞여 온다.
    제목·요약에 **종목명이 있는 기사**만 사유로 쓰고(제목>요약), 없으면 비워 둔다 —
    엉뚱한 기사를 재료처럼 붙이지 않기 위한 장치다.
    """
    arts = fetch_investor_news(code, name) or []
    plain = str(name or "").replace(" ", "")
    best, best_score = "", 0
    for a in arts:
        title = (a.get("title") or "").strip()
        body = (a.get("body") or "").strip()
        if len(title) < 8:
            continue
        score = 0
        if plain:
            if plain in title.replace(" ", ""):
                score = 3
            elif plain in body.replace(" ", ""):
                score = 2
        if not score:
            continue
        if score < best_score:
            continue
        best, best_score = title, score
        if score == 3:
            break
    return best[:PRE_REASON_LEN].rstrip()


def build_pre_market(now, old_entry):
    """NXT 프리마켓(08:00~08:50) 수급 요약 — 정규장 블록과 분리 저장할 preMarket 본문.

    · 모수: 전 종목 인덱스(allStocks, 직전 실행분)의 종목코드 + 관찰 5선. 병렬 polling 으로
      프리마켓 체결분만 골라 담는다(30종목씩 10스레드 — 599종목 ≈ 2초).
    · 점유율 = 섹터 프리장 합산 거래대금 ÷ **프리장 +1%↑ 상승 종목** 거래대금
      (전체 체결을 모수로 쓰면 하락 대형주가 섹터 1위를 만드는 착시 — 2026-11-27 수정)
    · 종목 리스트(거래대금·상승률 상위)는 프리장 전체 체결 그대로 — 거래대금 상위에는
      하락 대형주도 들어갈 수 있으므로 basis/label 에 기준을 명시한다
    · 등락률은 프리장 체결 종목의 실측값 단순 평균, 상승 사유는 네이버 종목 뉴스 최신 헤드라인 1줄
    """
    industry_map = {}
    codes = []
    for r in (old_entry or {}).get("allStocks") or []:
        if isinstance(r, list) and r:
            code = str(r[0])
            codes.append(code)
            if len(r) >= 7 and r[6]:
                industry_map[code] = r[6]
    for w in (old_entry or {}).get("watchlist") or []:
        if w.get("ticker"):
            codes.append(str(w["ticker"]))
    codes = list(dict.fromkeys(c for c in codes if c))
    if not codes:
        log("  · 프리장 모수(전 종목 인덱스)가 없어 프리장 수급을 건너뜁니다")
        return None

    def chunk_call(chunk):
        data = get_json(f"{POLL_BASE}/stock/" + ",".join(chunk), tries=2)
        return (data or {}).get("datas") or []

    datas, chunks = [], [codes[i:i + 30] for i in range(0, len(codes), 30)]
    with ThreadPoolExecutor(max_workers=PRE_QUOTE_WORKERS) as pool:
        for got in pool.map(chunk_call, chunks):
            datas.extend(got or [])

    rows = [r for r in _pre_market_rows(datas, industry_map)
            if not is_etf(r[1] or "")]
    if not rows:
        log("  · NXT 프리마켓 체결 데이터가 없습니다(휴장·장전 아님)")
        return None

    total = sum(r[5] for r in rows)
    if total <= 0:
        return None
    chgs = [r[4] for r in rows if r[4] is not None]

    # 섹터 점유율 모수 — 프리장 +1%↑ 상승 종목만 (실전 테마 우선, 나머지는 네이버 업종)
    rise_dom = [r for r in rows if r[4] is not None and r[4] >= PRE_RISE_MIN_PCT]
    total_rise = sum(r[5] for r in rise_dom)
    groups: dict[str, list] = {}
    for r in rise_dom:
        groups.setdefault(theme_of(r[1], r[6]) or "기타", []).append(r)
    ranked = sorted(groups.items(), key=lambda kv: -sum(x[5] for x in kv[1]))

    value_top = sorted(rows, key=lambda r: -r[5])[:PRE_VALUE_TOP]
    rise_rows = [r for r in rows if r[5] >= PRE_MIN_VALUE and r[4] is not None]
    rise_top = sorted(rise_rows, key=lambda r: -(r[4] or 0))[:PRE_RISE_TOP]

    # 상승 사유 — 화면에 노출되는 종목만 (거래대금 상위 → 상승률 상위 순, 중복 제거)
    reason_codes = []
    reason_names = {}
    for r in value_top + rise_top:
        if r[0] not in reason_codes:
            reason_codes.append(r[0])
            reason_names[r[0]] = r[1]
    for _name, stocks in ranked[:PRE_SECTOR_TOP]:
        for r in sorted(stocks, key=lambda x: -x[5])[:PRE_SECTOR_STOCKS]:
            if r[0] not in reason_codes:
                reason_codes.append(r[0])
                reason_names[r[0]] = r[1]
    reason_codes = reason_codes[:PRE_REASON_CODES]
    reasons = {}
    if reason_codes:
        with ThreadPoolExecutor(max_workers=6) as pool:
            got = list(pool.map(_pre_news_reason, reason_codes,
                                [reason_names.get(c, "") for c in reason_codes]))
        reasons = {c: t for c, t in zip(reason_codes, got) if t}

    sectors = []
    if total_rise > 0:
        for name, stocks in ranked[:PRE_SECTOR_TOP]:
            block = _dom_block(name, stocks, PRE_SECTOR_STOCKS)
            block["share"] = round(block["valueEok"] / total_rise * 100, 1)
            block["stocks"] = [_pre_stock(r, reasons)
                               for r in sorted(stocks, key=lambda x: -x[5])[:PRE_SECTOR_STOCKS]]
            block["topTurnover"] = [_pre_stock(r, reasons) for r in
                                    sorted([r for r in stocks if _row_turn(r) is not None],
                                           key=lambda x: -(_row_turn(x) or 0))[:PRE_SECTOR_STOCKS]]
            sectors.append(block)
    used = sum(s["share"] for s in sectors)
    rest = [r for _name, stocks in ranked[PRE_SECTOR_TOP:] for r in stocks]
    individual = None
    if rest and (100.0 - used) >= PRE_TAIL_MIN_SHARE:
        individual = _dom_block("개별이슈", rest, DOM_IND_STOCKS)
        individual["share"] = round(100.0 - used, 1)
        individual["stocks"] = [_pre_stock(r, reasons)
                                for r in sorted(rest, key=lambda x: -x[5])[:DOM_IND_STOCKS]]
    elif sectors:
        sectors[-1]["share"] = round(sectors[-1]["share"] + (100.0 - used), 1)

    block = {
        "asOf": now.strftime("%H:%M"),
        "collectedAt": now.isoformat(timespec="seconds"),
        "window": "08:00~08:50",
        "label": "NXT 프리마켓",
        "universe": len(rows),
        "riseUniverse": len(rise_dom),
        "riseEok": int(round(total_rise)),
        "totalEok": int(round(total)),
        "totalText": _large_eok(total),
        "riseTotalText": _large_eok(total_rise),
        "riseCount": sum(1 for c in chgs if c > 0),
        "fallCount": sum(1 for c in chgs if c < 0),
        "avgChg": round(sum(chgs) / len(chgs), 2) if chgs else None,
        "sectors": sectors,
        "individual": individual,
        "valueTop": [_pre_stock(r, reasons) for r in value_top],
        "riseTop": [_pre_stock(r, reasons) for r in rise_top],
        "valueTopLabel": "프리장 전체 체결 거래대금 상위",
        "riseTopLabel": f"{_pre_rise_label()} · 프리장 {PRE_MIN_VALUE}억↑ 상승률 상위",
        "reasonCount": len(reasons),
        "basisMode": "rise",
        "basis": f"{_pre_rise_label()} {len(rise_dom):,}종목 · 거래대금 {_large_eok(total_rise)}",
        "rule": f"점유율 = 섹터 프리장 합산 거래대금 ÷ 프리장 {_pre_rise_label()} 종목 거래대금",
        "source": "네이버 금융 NXT 프리마켓 시세",
        # 시총 대비 회전율(프리장) — 모수는 거래대금 300억↑ · +1%↑ 종목(정규장과 같은 기준)
        "turnover": build_turnover_block(
            rows, PRE_RISE_MIN_PCT, now.strftime("%H:%M"), rise_label=_pre_rise_label(),
            stock_fn=lambda s: _pre_stock(s, reasons),
            stock_cap=PRE_SECTOR_STOCKS, ind_cap=PRE_SECTOR_STOCKS),
    }
    return block


def pre_market_update(now):
    """프리장(08:00~08:50) 전용 갱신 — 오늘 항목의 preMarket 블록만 바꾼다.

    정규장 집계(sessions·sectorDominance·allStocks·watchlist)는 손대지 않는다.
    개장(09:00) 뒤에 도는 실행은 이 경로로 들어오지 않으므로 정규장 값을 덮어쓸 수 없다.
    """
    date_str = now.strftime("%Y-%m-%d")
    old_data = []
    if DATA_PATH.exists():
        try:
            loaded = json.loads(DATA_PATH.read_text(encoding="utf-8"))
            if isinstance(loaded, list):
                old_data = loaded
        except Exception as exc:            # noqa: BLE001
            warn(f"기존 data.json 파싱 실패({type(exc).__name__}) — 새로 작성합니다.")
    old_entry = next((d for d in old_data if d.get("date") == date_str), None)

    started = time.time()
    block = build_pre_market(now, old_entry)
    if not block:
        return 0

    if old_entry is None:
        old_entry = {"date": date_str, "label": now.strftime("%Y-%m-%d"),
                     "shortLabel": now.strftime("%m/%d"), "sessions": [],
                     "defaultSession": "pre"}
        old_data.insert(0, old_entry)
    old_entry["preMarket"] = block
    old_entry["updatedAt"] = now.isoformat(timespec="seconds")

    by_date = {d.get("date"): d for d in old_data if d.get("date")}
    data = [by_date[k] for k in sorted(by_date, reverse=True)][:MAX_DATES]
    for d in data:
        if d is not old_entry:
            d.pop("allStocks", None)
            d.pop("charts", None)
    scrub_scan_plaintext(data)
    changed, _charts_changed, _text = save_data_files(data, load_charts_cache())
    segs = [f"{s['name']} {s['share']}%" for s in block["sectors"]]
    if block.get("individual"):
        segs.append(f"개별이슈 {block['individual']['share']}%")
    log(f"  · preMarket {block['asOf']} 기준 · 체결 {block['universe']}종목 · "
        f"{block['totalText']} · 모수 {block.get('basis', '')} · "
        f"사유 {block['reasonCount']}종목 ({time.time() - started:.1f}초)")
    log("    프리장 섹터 점유율: " + (" | ".join(segs) or "—"))
    log(f"    거래대금 1위 {block['valueTop'][0]['name']} "
        f"{block['valueTop'][0]['valueText']}" if block.get("valueTop") else "    거래대금 상위 없음")
    if changed:
        log("    data.json 갱신 완료(정규장 블록은 그대로)")
    else:
        log("    data.json 변경 없음")
    return 0


# ---------------------------------------------------------------- 기관·외인 연속매수
def _clean_text(value, limit: int = 0) -> str:
    """뉴스 제목·요약에서 HTML 태그·엔티티를 걷어낸 평문."""
    s = html_lib.unescape(str(value or ""))
    s = re.sub(r"<[^>]+>", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s[:limit].rstrip() if limit and len(s) > limit else s


def scan_bad_keywords(text: str) -> list[str]:
    """글에서 악재 키워드를 찾는다 — 등장한 키워드 목록(중복 없음).

    · 한글 키워드는 부분 문자열, 영문 약어(CB·BW)는 단어 경계로만 본다
    · 사전(NEWS_BAD_WORDS)에 있는 말만 돌려준다 — 문장을 새로 해석하지 않는다
    """
    s = _clean_text(text)
    if not s:
        return []
    found = []
    for word in NEWS_BAD_WORDS:
        pattern = NEWS_BAD_ASCII.get(word)
        if pattern:
            hit = bool(re.search(pattern, s))
        else:
            hit = word in s
        if hit and word not in found:
            found.append(word)
    return found


def _streak(values) -> int:
    """최신일 우선 순매수 수량 목록 → 연속 순매수 일수(순매도 연속이면 음수).

    · 첫날(최신)이 순매수가 아니면 순매도 연속을 음수로 센다
    · 0(보합)은 연속을 끊는다 — 없는 수를 이어 붙이지 않는다
    """
    if not values:
        return 0
    first = values[0]
    if not first:
        return 0
    sign = 1 if first > 0 else -1
    n = 0
    for v in values:
        if v is not None and v * sign > 0:
            n += 1
        else:
            break
    return sign * n


def build_investor_streak(rows):
    """trend API 응답 → 종목 하나의 연속매수 요약(실패·빈 값이면 None).

    반환: {asOf, days, frgnStreak, instStreak, dualStreak, recent5, instDetail}
      · frgnStreak / instStreak : 연속 순매수 일수(순매도 연속이면 음수)
      · dualStreak              : 외국인·기관이 같은 날 모두 순매수인 연속 일수(아니면 0)
      · recent5                 : 최근 5거래일 [{dt, frgn, orgn}] — **오래된 → 최신** 순
      · instDetail              : 키움 REST ka10059(투신·연기금) 세분화 자리 — 지금은 None
    """
    clean = []
    for r in rows or []:
        if not isinstance(r, dict):
            continue
        dt = str(r.get("bizdate") or "")
        if len(dt) != 8 or not dt.isdigit():
            continue
        clean.append({"dt": dt,
                      "frgn": to_int(r.get("foreignerPureBuyQuant")),
                      "orgn": to_int(r.get("organPureBuyQuant"))})
    if not clean:
        return None
    clean.sort(key=lambda x: x["dt"], reverse=True)
    clean = clean[:INVESTOR_DAYS]
    dual = 0
    for c in clean:
        if c["frgn"] is not None and c["orgn"] is not None and c["frgn"] > 0 and c["orgn"] > 0:
            dual += 1
        else:
            break
    recent = list(reversed(clean[:INVESTOR_RECENT]))      # 오래된 → 최신
    return {
        "asOf": clean[0]["dt"],
        "days": len(clean),
        "frgnStreak": _streak([c["frgn"] for c in clean]),
        "instStreak": _streak([c["orgn"] for c in clean]),
        "dualStreak": dual,
        "recent5": [{"dt": c["dt"], "frgn": c["frgn"], "orgn": c["orgn"]} for c in recent],
        "instDetail": None,
    }


def _dot_date(dt: str) -> str:
    """'20261120' → '2026.11.20'."""
    return f"{dt[:4]}.{dt[4:6]}.{dt[6:8]}" if len(dt) == 8 else dt


def fetch_investor_trend(code: str):
    """종목별 외국인·기관 순매수 수량(최근 거래일, 최신 우선). 실패 시 None."""
    data = get_json(INVESTOR_TREND_URL.format(code=code), timeout=INVESTOR_TIMEOUT, tries=1)
    return data if isinstance(data, list) and data else None


def fetch_investor_news(code: str, name: str = ""):
    """종목 뉴스 제목·요약 — 무관 기사를 걸러 최신 순 최대 NEWS_COUNT 건. 실패 시 None.

    · 네이버 종목 뉴스에는 그 종목과 무관한 아파트 분양 홍보·일반 시황 기사가 섞여 온다.
      제목에 종목명이 없으면서 부동산 분양·홍보 키워드(NEWS_JUNK_WORDS)가 있는 기사는 버린다.
      (건설사 본인 분양 기사는 제목에 종목명이 있어 남는다)
    · 남은 기사는 제목 속 종목명(1순위) > 요약 속 종목명(2순위) > 나머지(3순위) 로 정렬해
      그 종목 직접 기사가 먼저 3건에 들게 한다 — 같은 순위끼리는 최신 순.
    · 응답 전체를 훑은 뒤 3건을 고른다(처음 3건에서 끊으면 걸러낸 만큼 빈자리가 생긴다).
    """
    data = get_json(INVESTOR_NEWS_URL.format(code=code), timeout=INVESTOR_TIMEOUT, tries=1)
    if data is None:
        return None
    raw = []
    for group in data if isinstance(data, list) else []:
        if not isinstance(group, dict):
            continue
        for it in group.get("items") or []:
            if isinstance(it, dict):
                raw.append(it)
    if not raw:
        return []
    plain = str(name or "").replace(" ", "")
    seen, ranked = set(), []
    # idx = 최신 순서 — 같은 순위끼리는 최신 기사가 먼저 남게 하는 tie-break
    for idx, it in enumerate(sorted(raw, key=lambda x: str(x.get("datetime") or ""), reverse=True)):
        key = str(it.get("id") or it.get("articleId") or it.get("title") or "")
        if not key or key in seen:
            continue
        seen.add(key)
        title = _clean_text(it.get("titleFull") or it.get("title"), 140)
        body = _clean_text(it.get("body"), 90)
        in_title = bool(plain) and plain in title.replace(" ", "")
        if not in_title and any(w in title for w in NEWS_JUNK_WORDS):
            continue                        # 종목명 없는 부동산 분양·홍보 기사 — 무관
        in_body = bool(plain) and plain in body.replace(" ", "")
        ranked.append((1 if in_title else 2 if in_body else 3, idx, {
            "title": title,
            "body": body,
            "url": str(it.get("mobileNewsUrl") or ""),
            "office": _clean_text(it.get("officeName"), 20),
            "dt": str(it.get("datetime") or ""),
        }))
    ranked.sort(key=lambda x: (x[0], x[1]))
    return [art for _rank, _idx, art in ranked[:NEWS_COUNT]]


def build_news_check(articles):
    """기사 목록 → 악재 키워드 스캔 결과(종목 하나).

    · 제목과 요약을 함께 스캔하고, 걸린 키워드를 기사마다 남긴다
    · 키워드가 하나도 없으면 flagged=False — '특이 악재 뉴스 미확인'
    """
    items = []
    words = []
    for a in articles or []:
        hits = scan_bad_keywords((a.get("title") or "") + " " + (a.get("body") or ""))
        for w in hits:
            if w not in words:
                words.append(w)
        items.append({"title": a.get("title") or "", "body": a.get("body") or "",
                      "url": a.get("url") or "", "office": a.get("office") or "",
                      "dt": a.get("dt") or "", "hit": hits})
    return {"checked": len(items), "flagged": bool(words), "keywords": words, "items": items}


def investor_target_codes(dominance, watchlist, scan_hits, cached):
    """연속매수를 수집할 종목 — 화면에 노출되는 종목만(중복 제거, 최대 INVESTOR_MAX_CODES).

    주도 섹터 카드(섹터 + 개별이슈) → 관찰 5선 → 조건식 포착 → 지난 실행에 있던 종목 순.
    마지막 순서(캐시)는 잠금 키 없이 도는 실행에서도 배지가 사라지지 않게 한다.
    """
    out = []
    def add(code):
        code = str(code or "").strip()
        if code and code not in out:
            out.append(code)
    blocks = list((dominance or {}).get("sectors") or [])
    if (dominance or {}).get("individual"):
        blocks.append(dominance["individual"])
    for block in blocks:
        for st in block.get("stocks") or []:
            add(st.get("code"))
    for w in watchlist or []:
        add(w.get("ticker"))
    for h in scan_hits or []:
        add(h.get("code"))
    for code in (cached or {}).get("order") or []:
        add(code)
    return out[:INVESTOR_MAX_CODES]


def _cache_age_min(stamp, now):
    """캐시 생성 시각(iso) → 지난 분. 읽을 수 없으면 None(오래된 것으로 본다)."""
    try:
        t = datetime.fromisoformat(str(stamp or ""))
        if t.tzinfo is None:
            t = t.replace(tzinfo=KST)
        return (now - t).total_seconds() / 60
    except (TypeError, ValueError):
        return None


def build_investor_blocks(codes, cached_streak, cached_news, now, names=None):
    """(investorStreak, investorNews) — 캐시가 신선하면 그대로 쓰고 모자란 종목만 병렬 수집.

    names(코드→종목명)는 뉴스 무관 기사 필터·종목 기사 우선 정렬에 쓴다.

    · 5분마다 40종목×2요청을 다시 받지 않도록 종목별 생성 시각(`at`)으로 캐시를 판단한다
    · 수집에 실패한 종목은 이전 값을 그대로 유지한다(0이나 빈 배지를 만들지 않는다)
    · 갱신 시간은 ThreadPoolExecutor 로 묶어 2~3초 안에 끝나게 한다
    """
    codes = [str(c) for c in (codes or []) if c][:INVESTOR_MAX_CODES]
    if not codes:
        return None, None
    streak_src = ((cached_streak or {}).get("stocks") or {})
    news_src = ((cached_news or {}).get("stocks") or {})

    def fresh(src, code, ttl):
        item = src.get(code)
        if not isinstance(item, dict):
            return False
        age = _cache_age_min(item.get("at"), now)
        return age is not None and 0 <= age <= ttl

    need_streak = [c for c in codes if not fresh(streak_src, c, INVESTOR_TTL_MIN)]
    need_news = [c for c in codes if not fresh(news_src, c, NEWS_TTL_MIN)]
    streaks = {c: dict(streak_src[c]) for c in codes
               if c in streak_src and c not in need_streak}
    news = {c: dict(news_src[c]) for c in codes
            if c in news_src and c not in need_news}
    fetched = reused = 0
    started = time.time()

    if need_streak or need_news:
        with ThreadPoolExecutor(max_workers=INVESTOR_WORKERS) as pool:
            f_streak = {c: pool.submit(fetch_investor_trend, c) for c in need_streak}
            news_names = names or {}
            f_news = {c: pool.submit(fetch_investor_news, c, news_names.get(c, ""))
                      for c in need_news}
            for c, fut in f_streak.items():
                try:
                    rows = fut.result(timeout=INVESTOR_TIMEOUT + 3)
                except Exception:           # noqa: BLE001 — 한 종목 실패는 배지만 빠진다
                    rows = None
                item = build_investor_streak(rows) if rows else None
                if item:
                    item["at"] = now.isoformat(timespec="seconds")
                    streaks[c] = item
                    fetched += 1
                elif c in streak_src:
                    streaks[c] = dict(streak_src[c])     # 이번엔 실패 — 이전 값 유지
                    reused += 1
            for c, fut in f_news.items():
                try:
                    arts = fut.result(timeout=INVESTOR_TIMEOUT + 3)
                except Exception:           # noqa: BLE001
                    arts = None
                if arts:
                    item = build_news_check(arts)
                    item["at"] = now.isoformat(timespec="seconds")
                    news[c] = item
                    fetched += 1
                elif arts == [] and c not in news_src:
                    # 뉴스가 정말 없는 날 — '확인했고 없다'를 남긴다
                    news[c] = {"checked": 0, "flagged": False, "keywords": [], "items": [],
                               "at": now.isoformat(timespec="seconds")}
                    fetched += 1
                elif c in news_src:
                    news[c] = dict(news_src[c])
                    reused += 1

    order = [c for c in codes if c in streaks]
    if not order:
        return None, None
    as_dates = sorted({streaks[c].get("asOf") for c in order if streaks[c].get("asOf")})
    as_of = as_dates[-1] if as_dates else ""
    streak_block = {
        "asOf": as_of,
        "basis": (_dot_date(as_of) + " 기준 · 최근 " +
                  str(max((streaks[c].get("days") or 0) for c in order)) + "거래일 수량"),
        "rule": (f"최근 거래일부터 연속 순매수 일수(순매도 연속은 음수) · "
                 f"{INVESTOR_MIN_STREAK}일↑만 배지 · 단위 주"),
        "minStreak": INVESTOR_MIN_STREAK,
        "order": order,
        "stocks": {c: streaks[c] for c in order},
    }
    news_items = {c: news[c] for c in codes if c in news}
    news_at = max((v.get("at") or "" for v in news_items.values()), default="")
    news_block = {
        # 생성 시각은 새로 받은 종목이 있을 때만 움직인다 — 캐시만 쓴 실행은 data.json 을 바꾸지 않도록
        "asOf": (news_at[5:16].replace("T", " ") if news_at else ""),
        "rule": (f"종목 뉴스 최신 {NEWS_COUNT}건(종목명 없는 부동산 분양·홍보 기사 제외) "
                 "제목·요약 악재 키워드 스캔"),
        "keywords": list(NEWS_BAD_WORDS),
        "stocks": news_items,
    }
    log(f"    연속매수·뉴스 수집: 요청 {len(need_streak)}+{len(need_news)}건 · "
        f"새로 받음 {fetched} · 이전 값 유지 {reused} · {time.time() - started:.1f}초")
    return streak_block, news_block


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
    # 거래량·지수 시계열이 없는 예전 형식이면 한 번 다시 만든다(📈 차트 탭 거래량·RS)
    if "vols" not in cached or "index" not in cached:
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


def fetch_index_closes(symbol: str, count: int = CHARTS_DAYS):
    """지수 일봉 종가 — {날짜: 종가} (실패 시 None). 네이버 금융 일봉 그대로."""
    url = f"{FCHART}?symbol={symbol}&timeframe=day&count={count}&requestType=0"
    text = get_text(url, "euc-kr", timeout=15)
    if not text:
        return None
    out = {}
    for m in re.finditer(r'item data="([^"]+)"', text):
        parts = m.group(1).split("|")
        if len(parts) < 5:
            continue
        try:
            out[parts[0]] = round(float(parts[4]), 2)
        except ValueError:
            continue
    return out or None


def build_index_series(dates):
    """지수 종가를 종목 일봉 dates 축에 그대로 맞춘 배열 — {KOSPI: [...], KOSDAQ: [...]}

    · 없는 날짜는 null(보간·추정 금지) — 화면은 null 구간을 선으로 잇지 않는다
    · 두 지수 모두 절반 이상이 맞을 때만 담는다(어긋난 지수로 RS 를 만들지 않는다)
    """
    out = {}
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = {sym: pool.submit(fetch_index_closes, sym, CHARTS_DAYS) for sym, _ in INDEX_SYMBOLS}
        for sym, name in INDEX_SYMBOLS:
            try:
                closes = futures[sym].result() or {}
            except Exception:               # noqa: BLE001
                closes = {}
            if not closes:
                continue
            series = [closes.get(d) for d in dates]
            hit = sum(1 for v in series if v is not None)
            if hit < len(dates) * 0.5:
                warn(f"{name} 지수 일봉이 종목 날짜와 맞지 않아 RS 계산에서 뺐니다({hit}/{len(dates)})")
                continue
            out[sym] = {"name": name, "c": series}
    return out


def build_charts(codes, cached, now, need_series=False):
    """(data.json charts, 스캔용 일봉 series) — 종목별 최근 일봉 OHLC + 거래량 경량 배열.

    · 네이버 금융 일봉(fchart) 실측값만 넣는다. 없는 봉은 보간·추정하지 않는다
    · 날짜 배열을 한 벌만 두고 종목은 [[시,고,저,종], ...] 만 저장한다(용량 절감)
    · 거래량은 charts.vols 에 종목코드별 정수 배열(천주 단위 반올림)로 따로 담는다
      — 📈 차트 서브차트용. charts.stocks 는 [시,고,저,종] 4개를 그대로 유지한다
    · 코스피·코스닥 일봉 종가(charts.index)를 같은 날짜 축으로 담아 RS 를 정확히 계산한다
    · 봉 날짜가 기준 날짜와 어긋나는 종목(거래정지·신규상장)은 넣지 않는다
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
    vols = {}
    for code, rows in rows_by_code.items():
        if [r["d"] for r in rows] != dates:
            continue                      # 봉 날짜가 어긋나면 그리지 않는다(가짜 봉 금지)
        stocks[code] = [[r["o"], r["h"], r["l"], r["c"]] for r in rows]
        vols[code] = [int(round((r.get("v") or 0) / VOL_UNIT)) for r in rows]
    if not stocks:
        return (cached or None), {}

    index = build_index_series(dates)
    charts = {
        "asOf": latest,
        "basis": f"{latest[:4]}-{latest[4:6]}-{latest[6:]} 종가",
        "generatedAt": now.isoformat(timespec="seconds"),
        "days": len(dates),
        "dates": dates,
        "stocks": stocks,
        "vols": vols,
        "volUnit": VOL_UNIT,
        "index": index,
    }
    # 3,000KB 상한 — 넘으면 거래량을 빼고 일봉만 담는다(차트는 계속 뜨고 거래량·RS만 빠짐)
    if len(json.dumps(charts, ensure_ascii=False, separators=(",", ":")).encode()) > CHARTS_MAX_BYTES:
        warn(f"charts 용량 초과({len(json.dumps(charts, ensure_ascii=False)) / 1024:.0f}KB) — 거래량 시계열을 뺏니다")
        charts["vols"] = {}
    series = {code: rows for code, rows in rows_by_code.items() if code in stocks}
    return charts, series


# ---------------------------------------------------------------- 52주·매물대용 깊은 일봉
def deep_signal_series(codes, workers: int = 10):
    """52주 신고가 계산용 250거래일 일봉 — 후보(거래대금 300억↑ + 관찰·카드)만 받는다.

    · 전 종목(599)을 250봉으로 받으면 전송량이 2배가 되므로 후보만 따로 받는다
    · 120거래일 미만(신규상장·거래정지)은 넣지 않는다 — 52주라는 이름을 흘리지 않는다
    · 실패한 종목은 그냥 빠진다(그 종목만 52주 지표를 못 붙이고 나머지는 그대로)
    """
    codes = [str(c) for c in dict.fromkeys(codes or []) if c][:EDGE_DEEP_MAX]
    if not codes:
        return {}
    out = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {code: pool.submit(fetch_chart, code, SCAN_BARS) for code in codes}
        for code, future in futures.items():
            try:
                rows = future.result() or []
            except Exception:               # noqa: BLE001
                rows = []
            if len(rows) >= CHARTS_DAYS:
                out[code] = rows[-SCAN_BARS:]
    return out


def edge_candidate_codes(all_stocks, extra_codes):
    """52주 일봉을 받을 후보 — 당일 거래대금 EDGE_MIN_VALUE억 이상 + 관찰·카드 종목."""
    cand = []
    for row in all_stocks or []:
        if not row or not row[0]:
            continue
        if (row[5] or 0) >= EDGE_MIN_VALUE:
            cand.append(str(row[0]))
    cand.extend(str(c) for c in (extra_codes or ()) if c)
    return list(dict.fromkeys(cand))[:EDGE_DEEP_MAX]


def index_change_map(entry, kospi=None, kosdaq=None):
    """지수 등락률 {'KOSPI': x, 'KOSDAQ': y} — 실행 시점 값 우선, 없으면 data.json indices."""
    out = {}
    if kospi and kospi.get("chg") is not None:
        out["KOSPI"] = kospi["chg"]
    if kosdaq and kosdaq.get("chg") is not None:
        out["KOSDAQ"] = kosdaq["chg"]
    if not out:
        for item in (entry or {}).get("indices") or []:
            name = str(item.get("name") or "")
            if "코스피" in name:
                out.setdefault("KOSPI", item.get("chg"))
            elif "코스닥" in name:
                out.setdefault("KOSDAQ", item.get("chg"))
    return out


def scan_built_at(entry, key):
    """마지막 스캔 계산 시각 — 잠금 키가 있으면 복호화해 읽는다(없으면 None).

    조건식 평문은 저장하지 않으므로, 갱신 여부 판단을 위해 복호화만 해서
    `scanners[].updatedAt` 만 읽고 바로 버린다.
    """
    if not key or not isinstance(entry, dict):
        return None
    blob = entry.get(SCAN_ENC_KEY)
    if not (isinstance(blob, dict) and blob.get("ct")):
        return None
    try:
        payload = decrypt_scan_payload(blob, key)
        stamps = [s.get("updatedAt") for s in payload.get("scanners") or [] if s.get("updatedAt")]
        return datetime.fromisoformat(max(stamps)) if stamps else None
    except Exception:                       # noqa: BLE001 - 키가 다르면 갱신 판단만 건너뛴다
        return None


def scan_needs_rebuild(entry, key, now) -> bool:
    """오후장 수급은 시각이 지나면 값이 달라진다 — 장중·마감 뒤 스캔을 다시 계산할지.

    · 13:30~15:30: 마지막 스캔이 25분보다 오래되면 다시 계산(오후 비중·등락률 갱신)
    · 15:30 이후: 장중에 만든 스캔이면 한 번 다시 계산(마감 확정 분봉으로)
    · 키가 없는 실행(Actions cron)은 복호화·재암호화가 안 되므로 항상 False
    """
    if not key:
        return False
    built = scan_built_at(entry, key)
    if built is None:
        return False
    if built.tzinfo is None:
        built = built.replace(tzinfo=KST)
    if built.date() != now.date():
        return False
    hm = now.hour * 60 + now.minute
    bhm = built.hour * 60 + built.minute
    if PM_JUDGE_MIN <= hm <= PM_END_MIN:
        return (now - built).total_seconds() >= SCAN_REFRESH_MIN * 60
    if hm > PM_END_MIN and bhm < PM_END_MIN:
        return True
    return False


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


def trend_scan(rows):
    """추세지속주 — 추세가 살아 있는 대형·중대형주(연속 상승 + 정배열 + 고점 근접).

    A [일] 0봉전 종가 > 20이평 > 60이평 (정배열)
    B [일] 최근 5거래일 중 3일 이상 상승
    C [일] 5거래일 누적 수익률 > 0%
    D [일] 0봉전 종가 ≥ 직전 20일 고점 × 0.97 (고점 근접·돌파)
    조건식: A and (B or C) and D — 당일 거래대금 300억↑ 교집합(SCANNER_DEFS.minValue)
    """
    if not rows or len(rows) < 61:            # 60이평 + 직전 20일 고점
        return None
    closes = [r["c"] for r in rows]
    highs = [r["h"] for r in rows]
    n = len(closes)
    ma20 = _mean(closes[n - 20:])
    ma60 = _mean(closes[n - 60:])
    if not ma20 or not ma60:
        return None
    up5 = sum(1 for i in range(n - 5, n) if closes[i] > closes[i - 1])
    ret5 = (closes[-1] / closes[-6] - 1) * 100 if closes[-6] else None
    hi20 = max(highs[n - 21:n - 1])            # 직전 20일 고점(당일 봉 제외)
    hi_gap = (closes[-1] / hi20 - 1) * 100 if hi20 else None
    gap = (ma20 - ma60) / ma60 * 100 if ma60 else None
    cond = {
        "A": closes[-1] > ma20 > ma60,
        "B": up5 >= 3,
        "C": ret5 is not None and ret5 > 0,
        "D": hi_gap is not None and hi_gap >= -3.0,
    }
    return {
        "ma20": round(ma20), "ma60": round(ma60),
        "gap": round(gap, 2) if gap is not None else None,
        "up5": up5,
        "ret5": round(ret5, 2) if ret5 is not None else None,
        "hi_gap": round(hi_gap, 2) if hi_gap is not None else None,
        "conditions": cond,
        "pass": cond["A"] and (cond["B"] or cond["C"]) and cond["D"],
        "line2": f"20·60 정배열 {gap:+.2f}% · 5일 중 {up5}일 상승"
                 + (f" · 누적 {ret5:+.2f}%" if ret5 is not None else "")
                 + (f" · 20일 고점 {hi_gap:+.1f}%" if hi_gap is not None else ""),
    }


# ---------------------------------------------------------------- 종가베팅 핵심 지표
#  ① 52주 신고가 근접(high52)  ② 앞전 매물대 소화(shelf)  ③ 오후장 수급(pm)
#  모두 일봉·분봉 실측값만 쓴다 — 모자란 봉은 "계산 불가"로 두고 추정하지 않는다.
def high52_signal(rows, bars: int = HIGH52_BARS, price=None):
    """52주(250거래일) 신고가 대비 이격과 위치 — 당일 봉을 뺀 직전 고가와 비교.

    · 고점 기준: 당일 봉을 제외한 최근 250거래일 최고가(장중 고가)
      → 오늘 장중에 신고가를 찍고 밀린 경우도 '이격'이 정직하게 나온다
    · price: 현재가(allStocks 실시간 값) — 장중에는 일봉 마지막 종가가 늦을 수 있다
    · state: 돌파 / 신고가 근접(-5% 이내) / 10% 이내(-10% 이내) / ""(멀다)
    · todayBreak: 오늘 고가가 직전 52주 고가를 넘었는지(장중 신고가 경신)
    """
    if not rows or len(rows) < 61:
        return None
    win = rows[-(bars + 1):-1]                 # 당일 봉 제외
    if not win:
        return None
    hi_row = max(win, key=lambda r: r["h"])
    hi = hi_row["h"]
    close = price or rows[-1]["c"]
    if not hi or not close:
        return None
    gap = (close / hi - 1) * 100
    if close >= hi:
        state = "돌파"
    elif gap >= -5.0:
        state = "신고가 근접"
    elif gap >= -EDGE_NEAR_PCT:
        state = "10% 이내"
    else:
        state = ""
    return {
        "high": hi,
        "highDate": hi_row["d"],
        "price": close,
        "gap": round(gap, 2),
        "state": state,
        "near": gap >= -EDGE_NEAR_PCT,
        "todayBreak": bool(rows[-1]["h"] > hi),
        "bars": len(win),
        "partial": len(win) < bars,      # 상장 이력이 짧아 52주를 다 못 쓴 경우
    }


def volume_shelf(rows, days: int = SHELF_DAYS, price=None):
    """앞전 매물대 소화 — 최근 60거래일 최대 거래량일(직전 대량 매물대) 위 안착 여부.

    · 당일 봉은 빼고 센다(오늘 대량 거래는 '앞전' 매물대가 아니다)
    · overHigh(완전 소화): 현재가 ≥ 그날 고가 · overClose(부분): 현재가 ≥ 그날 종가
    """
    if not rows or len(rows) < days + 1:
        return None
    win = rows[-(days + 1):-1]
    shelf = max(win, key=lambda r: r["v"])
    close = price or rows[-1]["c"]
    if not shelf["v"] or not close or not shelf["h"]:
        return None
    over_close = close >= shelf["c"]
    over_high = close >= shelf["h"]
    return {
        "date": shelf["d"],
        "close": shelf["c"],
        "high": shelf["h"],
        "vol": shelf["v"],
        "value_eok": round(shelf["c"] * shelf["v"] / 1e8, 1),
        "overClose": over_close,
        "overHigh": over_high,
        "gapHigh": round((close / shelf["h"] - 1) * 100, 2),
        "state": "매물대 소화" if over_high else ("종가 위" if over_close else ""),
        "days": len(win),
    }


def fetch_minute_bars(code: str, day: str):
    """장중 분봉 [(HHMM, 가격, 누적거래량)] — 당일 봉만. 실패하면 None.

    네이버 fchart 분봉은 `YYYYMMDDHHMM|null|null|null|가격|누적거래량` 형식이고,
    거래량은 그날 누적값이다 — 분당 거래량은 앞 봉과의 차이로 구한다.
    """
    text = get_text(MINUTE_URL.format(code=code), "euc-kr", timeout=15)
    if not text:
        return None
    out = {}
    for m in re.finditer(r'item data="([^"]+)"', text):
        parts = m.group(1).split("|")
        if len(parts) < 6 or len(parts[0]) < 12:
            continue
        stamp = parts[0]
        if not stamp.startswith(day):
            continue
        try:
            hm = int(stamp[8:10]) * 60 + int(stamp[10:12])
            price = int(parts[4])
            cum = int(parts[5])
        except ValueError:
            continue
        if price <= 0:
            continue
        out[hm] = (price, cum)
    return [(hm, out[hm][0], out[hm][1]) for hm in sorted(out)] or None


class AfternoonFlow:
    """오후장(13:00 이후) 거래대금 비중·등락률 — 장중 분봉 실측.

    09:00~13:00 오전장에는 **억지로 계산하지 않는다**. `pass=None`(대기)으로 두고
    화면은 `오전장 진행 중`으로 표시한다. 13:30 이전 30분 남짓도 비중을 판정하기에
    이르므로 `오후장 초반`으로 대기 처리한다.
    """

    def __init__(self, now: datetime, limit: int = PM_MAX_FETCH):
        self.now = now
        self.limit = limit
        self.phase = self._phase()
        self.cache: dict[str, dict | None] = {}
        self.fetched = 0

    def _phase(self) -> str:
        if self.now.weekday() >= 5:
            return "휴장"
        hm = self.now.hour * 60 + self.now.minute
        if hm < PM_START_MIN:
            return "오전장 진행 중"
        if hm < PM_JUDGE_MIN:
            return "오후장 초반"
        if hm < PM_END_MIN:
            return "오후장 실측 중"
        return "오후장 마감"

    def pending(self) -> bool:
        return self.phase in ("오전장 진행 중", "오후장 초반", "휴장")

    def _measure(self, code: str):
        bars = fetch_minute_bars(code, self.now.strftime("%Y%m%d"))
        if not bars:
            return None
        px13 = None
        for hm, px, _cum in bars:
            if hm <= PM_START_MIN:
                px13 = px
        pm = [b for b in bars if PM_START_MIN <= b[0] <= PM_END_MIN]
        if not pm or px13 is None:
            return None
        value = 0.0                      # 13:00 이후 분당 (누적거래량 차이 × 가격) 합
        prev = None
        for hm, px, cum in bars:
            if hm < PM_START_MIN:
                prev = cum
                continue
            if hm > PM_END_MIN:
                break
            if prev is not None and cum > prev:
                value += (cum - prev) * px
            prev = cum
        end_hm, end_px, _c = pm[-1]
        return {"px13": px13, "px": end_px, "valueWon": value,
                "at": f"{end_hm // 60:02d}:{end_hm % 60:02d}"}

    def _measure_safe(self, code: str):
        try:
            return self._measure(code)
        except Exception as exc:            # noqa: BLE001 - 분봉 실패는 조건만 비운다
            warn(f"분봉 조회 실패 {code}({type(exc).__name__})")
            return None

    def warm(self, codes, workers: int = 8) -> None:
        """판정 시각(13:30) 이후 후보 종목 분봉을 미리 병렬로 받아 둔다.

        오전장·오후장 초반에는 아예 호출하지 않는다 — 억지 계산 금지.
        """
        if self.pending() or not codes:
            return
        todo = [str(c) for c in codes if str(c) not in self.cache][:self.limit]
        if not todo:
            return
        with ThreadPoolExecutor(max_workers=workers) as pool:
            for code, res in zip(todo, pool.map(self._measure_safe, todo)):
                self.cache[code] = res
                self.fetched += 1

    def get(self, code: str, value_eok=None):
        """종목 하나의 오후장 수급 — 판정 전이면 status만 돌려준다(API 호출 없음)."""
        if self.pending():
            return {"status": self.phase, "pass": None,
                    "basis": "13:00부터 분봉 실측(오전장은 계산하지 않음)"}
        if code not in self.cache:
            if self.fetched >= self.limit:
                return None
            self.fetched += 1
            try:
                self.cache[code] = self._measure(code)
            except Exception as exc:        # noqa: BLE001 - 분봉 실패는 조건만 비운다
                warn(f"분봉 조회 실패 {code}({type(exc).__name__})")
                self.cache[code] = None
        base = self.cache.get(code)
        if not base:
            return {"status": self.phase, "pass": None, "basis": "분봉을 받지 못해 미판정"}
        chg = (base["px"] / base["px13"] - 1) * 100 if base["px13"] else None
        share = None
        if value_eok:
            share = (base["valueWon"] / 1e8) / float(value_eok) * 100
        inflow = share is not None and share >= PM_SHARE_MIN
        up = chg is not None and chg > 0
        return {
            "status": self.phase,
            "pmShare": round(min(max(share, 0.0), 100.0), 1) if share is not None else None,
            "chgPm": round(chg, 2) if chg is not None else None,
            "px13": base["px13"],
            "px": base["px"],
            "at": base["at"],
            "inflow": bool(inflow),
            "up": bool(up),
            "pass": bool(inflow and up),
            "basis": "13:00~15:30 분봉 실측",
        }


def closing_edge_scan(rows, ctx):
    """종가베팅 핵심 — 52주 신고가 근접/매물대 소화 + 수급·강세 + 오후장 유입.

    A [일] 52주(250거래일) 신고가 대비 -10% 이내(돌파 포함)
    B [일] 직전 60일 최대 거래량일(앞전 매물대) 고가 위 = 매물대 소화
    C [수급] 외인·기관 2일 이상 연속 순매수 또는 지수 대비 +2%p 강세
    D [분봉] 13:00 이후 거래대금 비중 30% 이상 + 13:00 대비 우상향
    조건식: (A or B) and C and D — 당일 거래대금 300억↑ 교집합(SCAN_DEFS.minValue)
    13:00 이전에는 D를 판정하지 않는다(pending) — 대기 상태로 목록에 남기고 화면에 표시.
    """
    if not rows or len(rows) < 61:
        return None
    w52 = (ctx or {}).get("w52") or high52_signal(rows, price=(ctx or {}).get("price"))
    shelf = (ctx or {}).get("shelf") or volume_shelf(rows, price=(ctx or {}).get("price"))
    if not w52 and not shelf:
        return None
    chg = (ctx or {}).get("chg")
    index_chg = (ctx or {}).get("index_chg")
    rel = (chg - index_chg) if (chg is not None and index_chg is not None) else None
    inv = (ctx or {}).get("investor") or {}
    streak = max(int(inv.get("dualStreak") or 0), int(inv.get("instStreak") or 0),
                 int(inv.get("frgnStreak") or 0))
    pm = (ctx or {}).get("pm") or {}
    pending = pm.get("pass") is None
    cond = {
        "A": bool(w52 and w52["near"]),
        "B": bool(shelf and shelf["overHigh"]),
        "C": bool(streak >= INVESTOR_MIN_STREAK or (rel is not None and rel >= EDGE_REL_MIN)),
        "D": bool(pm.get("pass") is True),
    }
    passed = (cond["A"] or cond["B"]) and cond["C"] and (cond["D"] or pending)
    bits = []
    if w52 and w52["state"]:
        bits.append(f"52주 {w52['gap']:+.1f}%")
    if streak >= INVESTOR_MIN_STREAK:
        bits.append(f"외인·기관 {streak}일 연속")
    elif rel is not None:
        bits.append(f"지수 대비 {rel:+.1f}%p")
    if pending:
        bits.append("오후장 대기")
    elif pm.get("pass"):
        bits.append(f"오후 비중 {pm.get('pmShare')}% · {pm.get('chgPm'):+.1f}%")
    return {
        "gap": round(rel, 2) if rel is not None else 0.0,
        "conditions": cond,
        "pass": bool(passed),
        "pending": bool(pending),
        "line2": " · ".join(bits),
    }


# ---------------------------------------------------------------- 주도돌파 100점
def _cap(value, hi):
    """0~hi 사이로 자른다(점수 계산용 — 음수는 0)."""
    if value is None:
        return 0.0
    return max(0.0, min(float(value), float(hi)))


def d1_signal_days(rows, strong=None, window=BREAKOUT_WIN_BARS):
    """정배열 + 강한 상승일 → (신호일 index, 그날 등락률, 다음날 종가 수익률) 목록.

    · 신호일 i: 그 시점의 20·60이평이 정배열(종가 > 20이평 > 60이평)이고
      종가 등락률이 strong% 이상(strong=None 이면 등락률 조건 없이 정배열만)
    · D+1 = 바로 다음 거래일 종가 수익률((다음 종가 ÷ 신호일 종가 − 1)×100)
    · 창: 최근 window 거래일 — 마지막 봉은 다음 봉이 없어 신호에서 빠진다
    · 각 날의 이평은 그 시점 값으로 계산한다(미래 참조 없음)
    """
    closes = [r["c"] for r in rows or []]
    n = len(closes)
    if n < 62:
        return []
    start = max(60, n - window - 1)
    out = []
    for i in range(start, n - 1):
        ma20 = _mean(closes[i - 19:i + 1])
        ma60 = _mean(closes[i - 59:i + 1])
        if not ma20 or not ma60 or not (closes[i] > ma20 > ma60):
            continue
        prev = closes[i - 1]
        if not prev:
            continue
        chg = (closes[i] / prev - 1) * 100
        if strong is not None and chg < strong:
            continue
        nxt = closes[i + 1]
        if not nxt:
            continue
        out.append((i, round(chg, 2), round((nxt / closes[i] - 1) * 100, 2)))
    return out


def d1_winrate(rows, window=BREAKOUT_WIN_BARS):
    """유사 강세일 D+1 승률·평균 수익률 — 표본이 적으면 기준을 넓혀 다시 센다.

    정배열 +5%↑ → (3건 미만이면) 정배열 +3%↑ → (그래도 3건 미만이면) 정배열 상승일.
    n·m·rate·avg 는 실측값만, 어느 기준으로 셌는지(rule)를 함께 돌려준다.
    """
    tiers = ((BREAKOUT_STRONG, f"정배열 +{BREAKOUT_STRONG:.0f}%↑"),
             (BREAKOUT_STRONG_WIDE, f"정배열 +{BREAKOUT_STRONG_WIDE:.0f}%↑"),
             (None, "정배열 상승일"))
    for strong, label in tiers:
        sigs = d1_signal_days(rows, strong, window) or []
        if len(sigs) >= BREAKOUT_MIN_SAMPLES or strong is None:
            gains = [g for _i, _c, g in sigs]
            n = len(gains)
            up = sum(1 for g in gains if g > 0)
            avg = _mean(gains) if gains else None
            return {
                "n": n, "m": up,
                "rate": round(up / n * 100, 1) if n else None,
                "avg": round(avg, 2) if avg is not None else None,
                "rule": label,
            }
    return {"n": 0, "m": 0, "rate": None, "avg": None, "rule": "표본 없음"}


def breakout_score_scan(rows, ctx):
    """주도돌파 100점 — 정배열 상승 추세 + 지수 대비 강세 종목을 100점으로 채점한다.

    A [일] 0봉전 종가 > 20이평 > 60이평 (정배열 상승 추세)
    B [당일] 종목 등락률 > 소속 지수 등락률 (지수 대비 초과 강세)
    C [당일] 종목 등락률 > 0% (상승)
    조건식: A and B and C — 당일 거래대금 300억↑ 교집합(SCANNER_DEFS.minValue)

    점수(총 100) = 주도 섹터·지수 초과 40 + 정배열·이평 돌파 25
                 + 유사 강세일 D+1 승률·기대수익 25 + 거래대금·회전율 10
    점수가 BREAKOUT_MIN_SCORE(51)를 넘지 못하면 목록에서 뺀다.
    """
    ctx = ctx or {}
    closes = [r["c"] for r in rows or []]
    n = len(closes)
    if n < 61:                                # 60이평 + 당일 봉
        return None
    ma20 = _mean(closes[-20:])
    ma60 = _mean(closes[-60:])
    ma120 = _mean(closes[-120:]) if n >= 120 else None
    if not ma20 or not ma60:
        return None
    close = closes[-1]
    chg = ctx.get("chg")
    index_chg = ctx.get("index_chg")
    rel = (chg - index_chg) if (chg is not None and index_chg is not None) else None
    cond = {
        "A": bool(close > ma20 > ma60),
        "B": bool(rel is not None and rel > 0),
        "C": bool(chg is not None and chg > 0),
    }
    passed = cond["A"] and cond["B"] and cond["C"]

    # ── 1) 정배열·이평 돌파 (25) ─────────────────────────────────────────────
    trend = 0
    if close > ma20:
        trend += 5
    if ma20 > ma60:
        trend += 7
    if ma120 and ma60 > ma120:
        trend += 7
    if ma120 and close >= ma120:
        trend += 3
    fresh = False                              # 최근 5봉 안 20·60이평 상향 돌파
    for i in range(max(60, n - 5), n):
        if i < 61:
            continue
        prev20 = _mean(closes[i - 21:i])
        cur20 = _mean(closes[i - 20:i + 1])
        prev60 = _mean(closes[i - 61:i])
        cur60 = _mean(closes[i - 60:i + 1])
        if not (prev20 and cur20 and prev60 and cur60):
            continue
        if (closes[i - 1] <= prev20 and closes[i] > cur20) or \
           (closes[i - 1] <= prev60 and closes[i] > cur60):
            fresh = True
            break
    if fresh:
        trend += 3
    trend = int(_cap(trend, BREAKOUT_CAP["trend"]))

    # ── 2) 주도 섹터·지수 초과 강도 (40) ─────────────────────────────────────
    lead = 0.0
    if rel is not None:
        lead += 16 * _cap(rel / 8.0, 1)                     # 지수 대비 +8%p = 만점
    rank = ctx.get("sector_rank")
    if rank and rank <= (ctx.get("dominance_top") or 0):
        lead += 11                                          # 주도 섹터(상위 3~4) 소속
    share = ctx.get("sector_share")
    if share:
        lead += 8 * _cap(share / 20.0, 1)                   # 섹터 점유율 20% = 만점
    if chg is not None:
        lead += 5 * _cap(chg / 5.0, 1)                      # 당일 상승 강도(+5% = 만점)
    lead = int(round(_cap(lead, BREAKOUT_CAP["lead"])))

    # ── 3) 유사 강세일 D+1 실측 승률·기대수익 (25) ───────────────────────────
    wr = d1_winrate(rows)
    nn, mm = int(wr.get("n") or 0), int(wr.get("m") or 0)
    conf = nn / (nn + 4.0)                                  # 표본 신뢰도(1건 0.2 · 7건 0.64)
    adjusted = (mm + 2.0) / (nn + 4.0) if nn else 0.5       # 표본 적으면 50%로 수축
    win = 15 * _cap((adjusted - 0.40) / 0.40, 1)            # 승률 40%→0 · 80%→15
    if wr.get("avg") is not None:
        win += 10 * _cap((wr["avg"] + 1.0) / 5.0, 1) * conf  # 평균 +4%→만점 · -1%→0
    win = int(round(_cap(win, BREAKOUT_CAP["win"])))

    # ── 4) 거래대금·시총 대비 회전율 (10) ────────────────────────────────────
    value_eok = float(ctx.get("value_eok") or 0)
    flow = 0.0
    if value_eok > BREAKOUT_MIN_VALUE:
        flow += 6 * _cap(math.log(value_eok / BREAKOUT_MIN_VALUE)
                         / math.log(2000 / BREAKOUT_MIN_VALUE), 1)
    turn = ctx.get("turn")
    if turn:
        flow += 4 * _cap(float(turn) / 5.0, 1)              # 회전율 5% = 만점
    flow = int(round(_cap(flow, BREAKOUT_CAP["flow"])))

    parts = {"lead": lead, "trend": trend, "win": win, "flow": flow}
    score = min(100, sum(parts.values()))
    # 51점 초과만 목록에 올린다(52점 이상) — 조건을 맞아도 점수가 낮으면 제외
    passed = bool(passed and score > BREAKOUT_MIN_SCORE)
    rate_text = (f"{wr['rate']:.1f}% ({mm}/{nn})" if wr.get("rate") is not None
                 else "표본 없음")
    avg_text = (f"{wr['avg']:+.2f}%" if wr.get("avg") is not None else "—")
    detail = (f"주도 {lead} · 정배열 {trend} · 승률 {win} · 수급 {flow}")
    bits = []
    if rel is not None:
        bits.append(f"지수 대비 {rel:+.1f}%p")
    bits.append(f"D+1 승률 {rate_text}")
    bits.append(f"평균 {avg_text}")
    return {
        "gap": round(rel, 2) if rel is not None else 0.0,
        "conditions": cond,
        "pass": bool(passed),
        "line2": " · ".join(bits),
        "score": score,
        "scoreParts": parts,
        "scoreDetail": detail,
        "winRate": rate_text,
        "avgD1": avg_text,
        "winN": nn,
        "winM": mm,
        "winRule": wr.get("rule") or "",
        "relPct": round(rel, 2) if rel is not None else None,
    }


# ---------------------------------------------------------------- 조건식 정의
#  등록된 조건식 — 여기에 항목 하나만 더하면 data.json·대시보드에 자동으로 늘어난다.
#   · evaluate(rows): 일봉 리스트 → 조건 판정 dict (계산 불가면 None)
#   · evaluate(rows, ctx): ctx 가 필요한 조건식(52주·오후장 같은 외부 실측값)
#   · pick(scan)    : 그 dict 로 "조건 통과" 여부 판정
#   · minValue      : 당일 거래대금 교집합 기준(억 원)
#   · rules         : 화면에 그대로 보여줄 필터 기준 카드(키·짧은 라벨·설명)
#   · deep          : 250거래일 일봉이 필요한 조건식(거래대금 300억↑ 종목만 따로 받아 계산)
#   · ctx / pm      : 수급·지수·분봉 같은 실행 시점 값을 쓰는 조건식(오후장 수급 포함)
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
    {
        "id": "trend-follow",
        "name": "추세지속주",
        "summary": "종가 > 20이평 > 60이평 정배열 + 최근 5일 중 3일 이상 상승(또는 5일 누적 +) "
                   "+ 직전 20일 고점 3% 이내 — 당일 거래대금 300억↑ 대형·추세 지속주",
        "formula": "A and (B or C) and D",
        "minValue": TREND_MIN_VALUE,
        "rules": [
            {"key": "A", "label": "종가 > 20 > 60이평", "detail": "0봉전 종가 > 20이평 > 60이평(정배열)"},
            {"key": "B", "label": "5일 중 3일↑ 상승", "detail": "최근 5거래일 중 3일 이상 종가 상승"},
            {"key": "C", "label": "5일 누적 +", "detail": "5거래일 누적 수익률 > 0%"},
            {"key": "D", "label": "20일 고점 3% 이내", "detail": "0봉전 종가가 직전 20일 고점의 97% 이상"},
        ],
        "intersection": f"당일 거래대금 {TREND_MIN_VALUE}억+",
        # ── 시루 자체 조건식(영웅문 원문 아님) — 화면 `원본 조건식` 팝업에 그대로 보여줄 문구 ──
        "rawSource": "시루 자체 조건식 (일봉 실측)",
        "rawTarget": "120거래일 일봉 보유 종목 전체(감시 599종목)",
        "rawRules": [
            {"key": "A", "text": "가격-이동평균 비교:[일]0봉전 종가 > 20이평 > 60이평 (정배열)"},
            {"key": "B", "text": "최근 5거래일 중 3일 이상 상승(종가 기준)"},
            {"key": "C", "text": "[일]5봉 누적 수익률 0% 초과"},
            {"key": "D", "text": "[일]0봉전 종가 ≥ 직전 20일 고점 × 0.97 (고점 근접·돌파)"},
        ],
        "rawFormula": "A and (B or C) and D",
        "rawIntersection": f"당일 거래대금 {TREND_MIN_VALUE}억+ 교집합",
        "rawNote": "A·D를 모두 만족하고 B·C 중 하나 이상을 통과한 종목 중 당일 거래대금 "
                   f"{TREND_MIN_VALUE}억 이상만 포착으로 남깁니다.",
        "evaluate": trend_scan,
        "pick": lambda scan: bool(scan["pass"]),
    },
    {
        "id": "closing-edge",
        "name": "종가베팅 핵심",
        "summary": "52주 신고가 -10% 이내(돌파·근접) 또는 앞전 매물대(60일 최대 거래량일) 소화 "
                   "+ 외인·기관 2일↑ 연속 순매수 또는 지수 대비 +2%p 강세 "
                   "+ 오후장(13:00 이후) 거래대금 비중 30%↑·13:00 대비 우상향 — 당일 거래대금 300억↑",
        "formula": "(A or B) and C and D",
        "minValue": EDGE_MIN_VALUE,
        "deep": True,
        "ctx": True,
        "pm": True,
        "rules": [
            {"key": "A", "label": "52주 신고가 -10% 이내",
             "detail": "당일 봉을 뺀 250거래일 최고가 대비 현재가 -10% 이내(돌파 포함)"},
            {"key": "B", "label": "앞전 매물대 소화",
             "detail": "최근 60거래일 최대 거래량일 고가 위에 현재가 안착"},
            {"key": "C", "label": "수급 또는 지수 대비 강세",
             "detail": f"외인·기관 {INVESTOR_MIN_STREAK}일 이상 연속 순매수 또는 종목 등락률이 "
                       f"소속 지수보다 +{EDGE_REL_MIN:.0f}%p 이상"},
            {"key": "D", "label": "오후장 유입·우상향",
             "detail": f"13:00 이후 거래대금 비중 {PM_SHARE_MIN:.0f}% 이상 + 13:00 대비 플러스 "
                       "(13:00 이전은 '오전장 진행 중'으로 대기)"},
        ],
        "intersection": f"당일 거래대금 {EDGE_MIN_VALUE}억+",
        "rawSource": "시루 자체 조건식 (일봉 250거래일 + 장중 분봉 실측)",
        "rawTarget": f"당일 거래대금 {EDGE_MIN_VALUE}억 이상 종목(250거래일 일봉 보유분)",
        "rawRules": [
            {"key": "A", "text": f"[일]0봉전 종가 ≥ (직전 250거래일 최고가 × 0.9) — 52주 신고가 -10% 이내"},
            {"key": "B", "text": "[일]0봉전 종가 ≥ 최근 60거래일 최대 거래량일 고가 (앞전 매물대 소화)"},
            {"key": "C", "text": "외인·기관 2일 이상 연속 순매수 또는 (종목 등락률 − 소속 지수 등락률) ≥ +2%p"},
            {"key": "D", "text": "[분봉] 13:00 이후 거래대금 비중 ≥ 30% 이고 13:00 대비 등락률 > 0%"},
        ],
        "rawFormula": "(A or B) and C and D",
        "rawIntersection": f"당일 거래대금 {EDGE_MIN_VALUE}억+ 교집합",
        "rawNote": "D(오후장 수급)는 13:00부터 분봉으로 실측합니다. 그 전에는 판정하지 않고 "
                   "'오전장 진행 중'으로 표시하며, A·B·C를 통과한 종목을 대기 상태로 보여줍니다.",
        "evaluate": closing_edge_scan,
        "pick": lambda scan: bool(scan["pass"]),
    },
    {
        "id": "breakout-100",
        "name": "주도돌파 100점",
        "summary": "종가 > 20이평 > 60이평 정배열 상승 추세 + 소속 지수 대비 초과 상승(당일 +)"
                   " — 주도 40·정배열 25·승률 25·수급 10 배점으로 100점 만점 채점, "
                   "51점 초과 종목만(점수 내림차순 상위 15종목)",
        "formula": "A and B and C",
        "minValue": BREAKOUT_MIN_VALUE,
        "deep": True,
        "ctx": True,
        "sortBy": "score",
        "limit": BREAKOUT_TOP,
        "rules": [
            {"key": "A", "label": "종가 > 20 > 60이평",
             "detail": "0봉전 종가 > 20이평 > 60이평(정배열 상승 추세)"},
            {"key": "B", "label": "지수 대비 초과 상승",
             "detail": "당일 등락률 − 소속 지수(코스피·코스닥) 등락률 > 0%p"},
            {"key": "C", "label": "당일 상승", "detail": "당일 등락률 > 0%"},
        ],
        "intersection": f"당일 거래대금 {BREAKOUT_MIN_VALUE}억+ · {BREAKOUT_MIN_SCORE}점 초과"
                        f" · 점수 상위 {BREAKOUT_TOP}종목",
        "rawSource": "시루 자체 조건식 (일봉 250거래일 실측 · 100점 채점)",
        "rawTarget": f"당일 거래대금 {BREAKOUT_MIN_VALUE}억 이상 종목(250거래일 일봉 보유분)",
        "rawRules": [
            {"key": "A", "text": "[일]0봉전 종가 > 20이평 > 60이평 (정배열 상승 추세)"},
            {"key": "B", "text": "[당일] 등락률 − 소속 지수 등락률 > 0%p (지수 대비 초과 강세)"},
            {"key": "C", "text": "[당일] 등락률 > 0% (상승 마감)"},
            {"key": "점수1", "text": "주도 섹터·지수 초과 40점 — 지수 대비 초과 최대 16(+8%p 만점) · "
                                  "주도 섹터(상위권) 11 · 섹터 점유율 최대 8(20% 만점) · "
                                  "당일 상승 강도 최대 5(+5% 만점)"},
            {"key": "점수2", "text": "정배열·이평 돌파 25점 — 종가>20이평 5 · 20>60이평 7 · "
                                  "60>120이평 7 · 종가≥120이평 3 · 최근 5봉 내 20·60이평 돌파 3"},
            {"key": "점수3", "text": "D+1 승률·기대수익 25점 — 최근 120거래일 '정배열 +5%↑' 다음날 "
                                  "승률 15 + 평균 수익률 10 (표본 3건 미만이면 +3%↑ → 정배열 전체로 확대, "
                                  "표본이 적을수록 50%로 수축하고 평균 수익률 점수는 표본 수에 비례해 줄입니다)"},
            {"key": "점수4", "text": "거래대금·회전율 10점 — 당일 거래대금 300억~2,000억 6 · "
                                  "시총 대비 회전율 5% 이상 4"},
            {"key": "필터", "text": f"점수 {BREAKOUT_MIN_SCORE}점 초과(52점 이상)만 목록에 올림"},
        ],
        "rawFormula": f"A and B and C and score > {BREAKOUT_MIN_SCORE}",
        "rawIntersection": f"당일 거래대금 {BREAKOUT_MIN_VALUE}억+ 교집합 · "
                            f"점수 {BREAKOUT_MIN_SCORE}점 초과 · 점수 내림차순 상위 {BREAKOUT_TOP}종목",
        "rawNote": "점수는 일봉 실측값만으로 계산합니다(추정·보정 없음). D+1 승률은 그 종목의 "
                   "과거 정배열 강세일 다음날 종가가 오른 비율이고, 표본이 적으면 넓은 기준으로 "
                   "다시 세어 표본 수를 함께 표시합니다.",
        "evaluate": breakout_score_scan,
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
    for key in ("rawSource", "rawTarget", "rawRules", "rawFormula", "rawIntersection", "rawNote"):
        if definition.get(key):
            meta[key] = definition[key]
    return meta


def build_scanner_scan(definition, series, info, extra_codes, now, *, deep_series=None,
                       deep_map=None, ctx_base=None):
    """조건식 하나 — 통과 + 거래대금 기준 이상 종목과 모달용 차트 반응.

    · series 는 메모리의 일봉(거래량 포함) — data.json에는 결과만 저장
    · 거래대금은 allStocks(당일 누적) 값을 쓰고, 없으면 마지막 봉 종가×거래량으로 계산
    · deep 조건식은 250거래일 일봉(deep_series)으로 계산하고, 52주·매물대 같은
      실측값(deep_map)은 모든 조건식의 종목 항목에 같이 붙인다(행 배지·모달용)
    """
    evaluate = definition.get("evaluate") or condition_scan
    pick = definition.get("pick") or (lambda scan: bool(scan.get("pass")))
    min_value = definition.get("minValue", SCAN_MIN_VALUE)
    use_ctx = bool(definition.get("ctx"))
    base = ctx_base or {}
    flow = base.get("pm_flow")
    pm_codes = set(base.get("pm_codes") or ())
    index_chg = base.get("index_chg") or {}
    investor = base.get("investor") or {}
    sector_rank = base.get("sector_rank") or {}
    sector_share = base.get("sector_share") or {}
    dominance_top = base.get("dominance_top") or 0
    src = deep_series if (definition.get("deep") and deep_series) else series
    scanned = 0
    hits = []
    reactions = {}
    last_dates = {}
    for code, rows in src.items():
        row = info.get(code) or []
        market = row[2] if len(row) > 2 else ""
        value_eok = None
        if len(row) > 5 and row[5] is not None:
            value_eok = float(row[5])
        elif rows and rows[-1].get("v"):
            value_eok = round(rows[-1]["c"] * rows[-1]["v"] / 1e8, 1)
        dmap = (deep_map or {}).get(code) or {}
        pm = None
        if flow and (definition.get("pm") or code in pm_codes):
            pm = flow.get(code, value_eok)
        ctx = None
        if use_ctx:
            sector = row[6] if len(row) > 6 else ""
            theme = theme_of(row[1] if len(row) > 1 else "", sector)
            ctx = {
                "code": code,
                "market": market,
                "name": row[1] if len(row) > 1 else "",
                "chg": row[4] if len(row) > 4 else None,
                "value_eok": value_eok,
                "index_chg": index_chg.get(market),
                "investor": investor.get(code),
                "price": row[3] if len(row) > 3 else None,
                "w52": dmap.get("w52"),
                "shelf": dmap.get("shelf"),
                "pm": pm,
                "sector": sector,
                "theme": theme,
                "mcap": row[7] if len(row) > 7 else None,
                "turn": row[8] if len(row) > 8 else None,
                "sector_rank": sector_rank.get(theme),
                "sector_share": sector_share.get(theme),
                "dominance_top": dominance_top,
            }
        scan = evaluate(rows, ctx) if use_ctx else evaluate(rows)
        if not scan:
            continue
        scanned += 1
        last_dates[rows[-1]["d"]] = last_dates.get(rows[-1]["d"], 0) + 1
        is_extra = code in extra_codes
        passed = bool(pick(scan))
        if not passed and not is_extra:
            continue
        pat_rows = rows[-CHARTS_DAYS:]          # 차트 구조·과거 반응은 늘 최근 120거래일 기준
        tags, text = chart_pattern(pat_rows)
        back = reaction_backtest(pat_rows)
        item = {
            "code": code,
            "name": (row[1] if len(row) > 1 and row[1] else code),
            "market": market,
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
        if scan.get("pending"):
            item["pending"] = True
        if dmap.get("w52"):
            item["w52"] = dmap["w52"]
        if dmap.get("shelf"):
            item["shelf"] = dmap["shelf"]
        if pm:
            item["pm"] = pm
        if passed and (value_eok or 0) >= min_value:
            summary = tags[0] if tags else text
            if back and back.get("n"):
                summary += f" · 과거 {back['m']}/{back['n']}회 5일 내 상승"
            item["summary"] = summary
            hits.append(item)
        if scan.get("line2"):
            item["line2"] = scan["line2"]
        for key in ("score", "scoreParts", "scoreDetail", "winRate", "avgD1",
                    "winN", "winM", "winRule", "relPct"):
            if scan.get(key) is not None:
                item[key] = scan[key]
        if is_extra and not passed:
            reactions[code] = item
        elif is_extra and (value_eok or 0) < min_value:
            reactions[code] = item        # 조건은 맞아도 거래대금 미달이면 모달용으로만
    if definition.get("sortBy") == "score":
        # 점수 조건식은 점수 내림차순 — 같으면 거래대금 큰 쪽 먼저
        hits.sort(key=lambda h: (-(h.get("score") or 0), -(h.get("value_eok") or 0)))
    else:
        hits.sort(key=lambda h: -(h.get("value_eok") or 0))
    limit = definition.get("limit")
    passed_total = len(hits)
    if limit:
        hits = hits[:int(limit)]
    bar_date = max(last_dates, key=last_dates.get) if last_dates else ""
    result = scanner_meta(definition)
    result.update({
        "asOf": bar_date,
        "basis": f"{bar_date[:4]}-{bar_date[4:6]}-{bar_date[6:]} 종가" if len(bar_date) == 8 else "",
        "updatedAt": now.isoformat(timespec="seconds"),
        "scanned": scanned,
        "passed": len(hits),
        "passedTotal": passed_total,
        "hits": hits,
        "reactions": reactions,
    })
    if definition.get("sortBy"):
        result["sortBy"] = definition["sortBy"]
    if limit:
        result["limit"] = int(limit)
    if definition.get("pm") and flow:
        # 오후장 수급 판정 상태 — 화면이 '오전장 진행 중'·'오후장 실측 중'을 그대로 보여준다
        result["phase"] = flow.phase
        result["pmBasis"] = (f"13:00 이후 거래대금 비중 {PM_SHARE_MIN:.0f}%↑ · 13:00 대비 우상향")
        result["pmMeasured"] = flow.fetched
    return result


def build_condition_scan(series, all_stocks, extra_codes, now, *, deep_series=None,
                         index_chg=None, investor=None, dominance=None):
    """등록된 조건식 전부(SCANNER_DEFS)를 계산해 스캔 결과를 만든다.

    반환값은 메모리에서만 쓰는 모양이다 — 저장은 apply_scan 이 암호화해
    `scannersEncrypted` 한 덩어리로만 남긴다(평문 키는 data.json 에 남기지 않는다).
    · deep_series: 거래대금 300억↑ 종목의 250거래일 일봉(52주 신고가 계산용)
    · index_chg  : {'KOSPI': 3.7, 'KOSDAQ': 2.75} — 지수 대비 강세 판정
    · investor   : 직전 실행의 investorStreak.stocks — 외인·기관 연속 순매수 판정
    · dominance  : 당일 주도 섹터 점유율(sectorDominance) — 주도돌파 100점의 '주도 섹터' 점수
    """
    if not series:
        return None
    info = {}
    for row in all_stocks or []:
        if row and row[0]:
            info[str(row[0])] = row
    deep_map = {}
    for code, rows in (deep_series or {}).items():
        row = info.get(code) or []
        price = row[3] if len(row) > 3 else None
        sig = {"w52": high52_signal(rows, price=price),
               "shelf": volume_shelf(rows, price=price)}
        if sig["w52"] or sig["shelf"]:
            deep_map[code] = sig
    # 오후장 수급은 거래대금 큰 종목부터 — 13:00 이후에만 분봉을 받는다(오전장엔 호출 없음)
    flow = AfternoonFlow(now)
    ordered = sorted(((deep_series or {}).keys()),
                     key=lambda c: -((info.get(c) or [None] * 6)[5] or 0))
    pm_codes = set(str(c) for c in (extra_codes or ())) | set(ordered[:PM_MAX_FETCH])
    flow.warm(ordered[:PM_MAX_FETCH])
    # 주도 섹터 — 이름→순위·점유율 (theme_of 로 묶은 이름 그대로)
    sector_rank, sector_share = {}, {}
    sectors = (dominance or {}).get("sectors") or []
    for idx, sec in enumerate(sectors):
        sec_name = str(sec.get("name") or "")
        if not sec_name or sec_name == "개별이슈":
            continue
        sector_rank[sec_name] = idx + 1
        if sec.get("share") is not None:
            sector_share[sec_name] = sec["share"]
    ctx_base = {"pm_flow": flow, "pm_codes": pm_codes,
                "index_chg": index_chg or {}, "investor": investor or {},
                "sector_rank": sector_rank, "sector_share": sector_share,
                "dominance_top": len(sectors)}
    scanners = [build_scanner_scan(defn, series, info, extra_codes, now,
                                  deep_series=deep_series, deep_map=deep_map,
                                  ctx_base=ctx_base)
                for defn in SCANNER_DEFS]
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
    """data.json 본문 문자열 — allStocks 는 배열이라 한 줄 압축으로 둔다.

    charts(일봉)는 여기서 쓰지 않는다 — collect_charts 로 charts.json 에 따로 저장한다.
    """
    saved = []
    for entry in data:
        for key, mark in (("allStocks", ALL_STOCKS_MARK),):
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


def load_charts_cache():
    """charts.json — {날짜: charts}. 없거나 깨졌으면 빈 dict(다시 받는다)."""
    if not CHARTS_PATH.exists():
        return {}
    try:
        raw = json.loads(CHARTS_PATH.read_text(encoding="utf-8"))
    except Exception:                       # noqa: BLE001
        warn("charts.json 파싱 실패 — 차트를 새로 받습니다")
        return {}
    if not isinstance(raw, dict):
        return {}
    return {str(date): charts for date, charts in raw.items()
            if isinstance(charts, dict) and charts.get("stocks")}


def collect_charts(data, base=None):
    """data.json 항목의 charts 를 걷어 charts.json 본문({날짜: charts})으로 모은다.

    · data.json 은 60초마다 다시 받는 본문이라 2.4MB 차트를 빼 두고,
      화면(index.html)은 ./charts.json 을 한 번만 받아 쓴다
    · 지난 날짜 항목에는 차트를 두지 않는다(용량 관리) — data.json 에 남은 날짜만 유지
    """
    by_date = {}
    for date, charts in (base or {}).items():
        if isinstance(charts, dict) and charts.get("stocks"):
            by_date[str(date)] = charts
    for entry in data:
        charts = entry.pop("charts", None)
        if isinstance(charts, dict) and charts.get("stocks"):
            by_date[str(entry.get("date"))] = charts
    keep = {str(entry.get("date")) for entry in data}
    return {date: charts for date, charts in by_date.items() if date in keep}


def serialize_charts(by_date):
    """charts.json 본문 — 날짜별로 한 줄에 압축한다(파일 전체가 2.4MB라 전송·diff 최소화)."""
    rows = ["  " + json.dumps(date) + ": " +
            json.dumps(by_date[date], ensure_ascii=False, separators=(",", ":"))
            for date in sorted(by_date, reverse=True)]
    return "{\n" + ",\n".join(rows) + "\n}\n" if rows else "{}\n"


def stage_charts_in_ci():
    """GitHub Actions 에서 charts.json 을 스테이징한다.

    · 워크플로의 `git add data.json` 만으로는 새로 만들어진 charts.json 이 커밋되지 않아,
      배포본이 지난 날짜 차트에 멈춘다. GitHub App 에 workflows 권한이 없어
      워크플로 파일을 고칠 수 없는 동안의 보완책이다.
    · 권한이 생겨 워크플로가 charts.json 을 직접 add 하게 되면 이 함수는 지워도 된다(중복 add 는 무해).
    """
    if os.environ.get("GITHUB_ACTIONS") != "true":
        return
    try:
        done = subprocess.run(["git", "add", "charts.json"], cwd=str(ROOT),
                              capture_output=True, text=True, timeout=30)
        if done.returncode == 0:
            log("    charts.json 스테이징 완료(워크플로 git add 보완)")
        else:
            log("    charts.json 스테이징 실패 — 다음 실행에서 다시 시도")
    except Exception:                            # noqa: BLE001
        log("    charts.json 스테이징 실패 — 다음 실행에서 다시 시도")


def save_data_files(data, charts_base=None):
    """data.json + charts.json 을 함께 쓴다(내용이 바뀐 파일만).

    반환: (data_changed, charts_changed, data_text)
    """
    charts_by_date = collect_charts(data, charts_base)
    text = serialize_data(data)
    previous = DATA_PATH.read_text(encoding="utf-8") if DATA_PATH.exists() else ""
    data_changed = text != previous
    charts_text = serialize_charts(charts_by_date)
    previous_charts = CHARTS_PATH.read_text(encoding="utf-8") if CHARTS_PATH.exists() else ""
    charts_changed = charts_text != previous_charts
    if data_changed:
        DATA_PATH.write_text(text, encoding="utf-8")
    if charts_changed:
        CHARTS_PATH.write_text(charts_text, encoding="utf-8")
        stage_charts_in_ci()
    return data_changed, charts_changed, text


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
        "marketCap": quote.get("marketCap"),
        "turnoverPct": quote.get("turnoverPct"),
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
                "disclaimer", "rangeLabels", "axis", "stages", "issue", "threads",
                "preMarket"):
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
                # 스크립트가 만든 업종 카드 문구('N종목 상승')만 갱신한다 —
                # 마감 리포트가 쓴 '17종목 5,709억 · 점유율 28.8%' 같은 서사는 건드리지 않는다.
                if re.match(r"^\d+\s*종목\s*상승$", str(card.get("csub") or "")):
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
        for key in ("price", "chg", "prevClose", "day", "turnover", "rank",
                    "marketCap", "turnoverPct"):
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
    charts_base = load_charts_cache()
    cached = entry.get("charts") or charts_base.get(str(entry.get("date")))
    charts, _ = build_charts(codes, cached, now)
    if not charts:
        log("  · 차트 생성 실패 — data.json 그대로 둡니다.")
        return 1
    charts_base[str(entry.get("date"))] = charts
    data_changed, charts_changed, text = save_data_files(data, charts_base)
    if not data_changed and not charts_changed:
        log("  · 변경 없음 — data.json 그대로 둡니다.")
        return 0
    log(f"  · charts 갱신: {charts['asOf']} · {len(charts['stocks'])}종목 · "
        f"data.json {len(text.encode()) / 1024:.1f}KB · "
        f"charts.json {CHARTS_PATH.stat().st_size / 1024:.1f}KB · 경고 {len(WARNINGS)}건")
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
    deep_series = deep_signal_series(edge_candidate_codes(rows, extra))
    log(f"  · 52주·매물대용 250거래일 일봉 {len(deep_series)}종목")
    result = build_condition_scan(series, rows, extra, now, deep_series=deep_series,
                                 index_chg=index_change_map(entry),
                                 investor=(entry.get("investorStreak") or {}).get("stocks"),
                                 dominance=entry.get("sectorDominance"))
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
    data_changed, charts_changed, text = save_data_files(data, load_charts_cache())
    if not data_changed and not charts_changed:
        log("  · 변경 없음 — data.json 그대로 둡니다.")
        return 0
    meta = result["meta"]
    log(f"  · 스캔 갱신: {meta['basis']} · {meta['scanned']}종목 계산 · "
        f"조건식 {len(result['scanners'])}개 · {len(text.encode()) / 1024:.1f}KB")
    for scanner in result["scanners"]:
        log(f"    [{scanner['name']}] {scanner['basis']} · {len(scanner['hits'])}종목 포착 "
            f"(거래대금 {scanner['minValue']}억+ · {scanner['formula']})")
        for hit in scanner["hits"]:
            if hit.get("score") is not None:
                log(f"      {hit['name']}({hit['code']}) {hit['score']}점/100 · {hit['valueText']} · "
                    f"D+1 {hit.get('winRate')} · 평균 {hit.get('avgD1')} · {hit.get('scoreDetail')}")
            else:
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

    # NXT 프리마켓(08:00~08:50) — 정규장 집계와 분리된 preMarket 블록만 갱신한다.
    # 이 시간대에는 정규장 데이터가 아직 없어 아래 정규장 경로는 어차피 중단되므로, 먼저 돌린다.
    if PRE_MARKET_START <= minutes < PRE_MARKET_END and "--regular" not in argv:
        pre_rc = pre_market_update(now)
        if not force or "--premarket-only" in argv:
            return pre_rc

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
            # 시총·회전율 — 관찰 5선 카드의 「시총 1.2조 · 회전율 8.4%」 배지
            mv_eok = live.get("mv_eok") or _mcap_eok((stock or {}).get("marketValueRaw"))
            val_eok = live.get("value_eok") or (((to_int((stock or {}).get("accumulatedTradingValueRaw")) or 0) / 1e8) or None)
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
                "marketCap": mv_eok,
                "turnoverPct": _turnover_pct(val_eok, mv_eok),
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
    dominance = build_sector_dominance(all_stocks, now)
    if dominance:
        new_entry["sectorDominance"] = dominance
    entry = merge_entry(new_entry, old_entry)
    entry.pop("_prices", None)
    entry.pop("_industry_metric", None)
    entry.pop("_value_ranks", None)
    entry["updatedAt"] = now.isoformat(timespec="seconds")

    # 6-1) 차트(일봉) — 모달 📈 차트 탭용. 전 종목 인덱스 + 관찰·카드 종목
    chart_codes = [row[0] for row in (all_stocks or []) if row] + target_codes + card_codes
    # merge_entry 는 차트를 넘겨주지 않으므로, 같은 날짜의 이전 data.json 항목이나
    # charts.json(분리 저장분)에서 캐시를 가져온다 — 없으면 599종목 일봉을 새로 받는다
    charts_base = load_charts_cache()
    cached_charts = ((old_entry or {}).get("charts") or charts_base.get(date_str)
                     or entry.get("charts"))
    # 오후장 수급(13:00 이후)은 시각이 지나면 값이 달라진다 — 장중·마감 뒤에는 스캔을 다시 계산
    need_series = scan_needs_rebuild(old_entry, scanner_key(), now)
    if need_series:
        log("  · 오후장 수급 갱신 — 일봉·분봉으로 스캔을 다시 계산합니다")
    charts, series = build_charts(chart_codes, cached_charts, now, need_series=need_series)
    if charts:
        entry["charts"] = charts
    else:
        entry.pop("charts", None)

    # 6-2) 조건식 × 당일 수급 교집합 + 과거 차트 반응 (거래량은 메모리에서만)
    scan = None
    if series:
        extra_all = set(target_codes + card_codes)
        deep_series = deep_signal_series(edge_candidate_codes(all_stocks, extra_all))
        if deep_series:
            log(f"    52주·매물대용 250거래일 일봉 {len(deep_series)}종목")
        scan = build_condition_scan(series, all_stocks, extra_all, now,
                                    deep_series=deep_series,
                                    index_chg=index_change_map(old_entry, kospi, kosdaq),
                                    investor=((old_entry or {}).get("investorStreak") or {}).get("stocks"),
                                    dominance=entry.get("sectorDominance"))
        if scan and apply_scan(entry, scan):
            log(f"    조건식×수급: {scan['meta']['scanned']}종목 계산 → {len(scan['hits'])}종목 포착 (암호화 저장)")
            for sc in scan["scanners"]:
                log(f"      [{sc['name']}] {len(sc['hits'])}종목" +
                    (f" · 오후장 수급 {sc.get('phase')}" if sc.get("phase") else ""))
        else:
            carry_scan(entry, old_entry, prev_entry)
    else:
        # 일봉을 새로 받지 않은 실행(20분 캐시) — 직전 스캔을 그대로 이어 쓴다
        carry_scan(entry, old_entry, prev_entry)

    # 6-3) 기관·외국인 연속 순매수 배지 + 종목 뉴스 3건 악재 스캔
    #      화면에 노출되는 종목(주도 섹터 카드·관찰 5선·조건식 포착)만 병렬 수집한다.
    #      잠금 키 없이 도는 실행(5분 cron)은 이전 값을 이어 쓰고 모자란 종목만 새로 받는다.
    invest_started = time.time()
    invest_codes = investor_target_codes(entry.get("sectorDominance"), entry.get("watchlist"),
                                        (scan or {}).get("hits"), (old_entry or {}).get("investorStreak"))
    name_of = {str(r[0]): r[1] for r in (all_stocks or []) if r and len(r) > 1 and r[1]}
    for w in entry.get("watchlist") or []:
        if w.get("ticker") and w.get("name"):
            name_of.setdefault(str(w["ticker"]), w["name"])
    streak_block, news_block = build_investor_blocks(
        invest_codes,
        (old_entry or {}).get("investorStreak"),
        (old_entry or {}).get("investorNews"),
        now,
        names=name_of)
    if streak_block:
        for code, item in streak_block["stocks"].items():
            if name_of.get(code) and not item.get("name"):
                item["name"] = name_of[code]        # 종목명으로도 배지를 찾을 수 있게
        entry["investorStreak"] = streak_block
    if news_block:
        entry["investorNews"] = news_block
    invest_secs = time.time() - invest_started

    # 7) 병합 후 저장 (시각·스탬프만 달라졌으면 커밋하지 않음)
    #    charts 는 charts.json 으로 분리 — 비교도 분리해 data.json 이 늘 달라 보이지 않게 한다
    entry_charts = entry.pop("charts", None)
    if isinstance(entry_charts, dict) and entry_charts.get("stocks"):
        charts_base[date_str] = entry_charts
    if old_entry and _without_dynamic(entry) == _without_dynamic(old_entry):
        # data.json 은 그대로 — 차트만 다시 만들어졌으면 charts.json 만 쓴다
        charts_changed = save_data_files(old_data, charts_base)[1]
        log("  · 시세가 그대로 — data.json 변경 없음" +
            (" · charts.json 만 갱신." if charts_changed else "."))
        return 0
    by_date = {d.get("date"): d for d in old_data if d.get("date")}
    by_date[date_str] = entry
    data = [by_date[k] for k in sorted(by_date, reverse=True)][:MAX_DATES]
    # 전 종목 시세 인덱스는 최신 날짜에만 — 지난 날짜 항목은 용량 관리를 위해 비운다
    for d in data:
        if d is not entry and d.get("date") != date_str:
            d.pop("allStocks", None)
            d.pop("charts", None)
            d.pop("investorStreak", None)
            d.pop("investorNews", None)

    # allStocks는 종목 수가 많아 한 줄 압축(다른 필드는 그대로 읽기 좋게 들여쓰기 유지)
    rows = entry.get("allStocks")
    scrub_scan_plaintext(data)              # 조건식 평문은 어떤 경우에도 저장하지 않는다
    data_changed, charts_changed, text = save_data_files(data, charts_base)
    if not data_changed and not charts_changed:
        log("  · 변경 없음 — data.json 그대로 둡니다.")
        return 0

    elapsed = time.time() - started
    log(f"  · data.json 갱신 완료 ({len(data)}개 날짜, {len(text.encode()) / 1024:.1f}KB, {elapsed:.1f}초)")
    if charts_changed:
        log(f"    charts.json {CHARTS_PATH.stat().st_size / 1024:.1f}KB (일봉 분리 저장)")
    if rows:
        log(f"    전 종목 시세 인덱스 {len(rows)}종목 · 업종 매핑 {len(sector_map)}건")
    dom = entry.get("sectorDominance") or {}
    if dom.get("sectors"):
        segs = [f"{s['name']} {s['share']}%" for s in dom["sectors"]]
        if dom.get("individual"):
            segs.append(f"개별이슈 {dom['individual']['share']}%")
        log(f"    주도 섹터 점유율({dom.get('asOf')}): " + " | ".join(segs))
    log(f"    코스피 {(kospi or {}).get('value')} ({pct_text((kospi or {}).get('chg'))}) · "
        f"코스닥 {(kosdaq or {}).get('value')} ({pct_text((kosdaq or {}).get('chg'))})")
    if industries:
        log("    상승 업종: " + ", ".join(f"{i['name']} {i['chg']:+.2f}%" for i in industries[:3]))
    log("    관찰 5선: " + ", ".join(f"{w['name']} {w['price']}" for w in entry.get("watchlist", [])))
    if entry.get("investorStreak"):
        isb = entry["investorStreak"]
        def _badge_on(item):
            item = item or {}
            return ((item.get("dualStreak") or 0) >= INVESTOR_MIN_STREAK
                    or (item.get("instStreak") or 0) >= INVESTOR_MIN_STREAK
                    or (item.get("frgnStreak") or 0) >= INVESTOR_MIN_STREAK)
        on = sum(1 for c in isb.get("order") or [] if _badge_on(isb["stocks"].get(c)))
        flagged = sum(1 for v in ((entry.get("investorNews") or {}).get("stocks") or {}).values()
                      if v.get("flagged"))
        log(f"    연속매수 {len(isb.get('order') or [])}종목 수집({isb.get('asOf')} 기준, "
            f"배지 {on}종목, {invest_secs:.1f}초 추가) · 악재 키워드 감지 {flagged}종목")
    if WARNINGS:
        log(f"    경고 {len(WARNINGS)}건(위 목록) — 해당 부분은 이전 값 또는 대체 값으로 채웠습니다.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
