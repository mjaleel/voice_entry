
# -*- coding: utf-8 -*-
"""
نظام التفعيل الموحّد — ملف واحد لكل برامجك (الرواتب القديم والجديد، والإدخال الصوتي). لا يحتاج إلا streamlit.
التشغيل:  streamlit run activation.py --server.address 127.0.0.1
المفاتيح تُحفظ في مجلد keys بجانب هذا الملف (هو نفسه الذي يستخدمه build.bat).
"""
import csv
import datetime
import datetime as dt
import hashlib
import hmac
import io
import json
import os
import sqlite3

import base64
import re
import struct
import sys

import streamlit as st

HERE = os.path.dirname(os.path.abspath(__file__))
KEYS = os.path.join(HERE, "keys")          # نفس مجلد keys الذي يستخدمه build.bat
DB = os.path.join(KEYS, "licenses.db")
OLD_SECRET_FILE = os.path.join(KEYS, "old_secret.txt")
PRIV = os.path.join(KEYS, "private.key")
PUB = os.path.join(KEYS, "public.key")


# ═════════════════ التوقيع Ed25519 (بايثون خالص) ═════════════════
_p = 2 ** 255 - 19
_L = 2 ** 252 + 27742317777372353535851937790883648493


def _inv(x):
    return pow(x, _p - 2, _p)


_d = -121665 * _inv(121666) % _p
_I = pow(2, (_p - 1) // 4, _p)


def _H(m):
    return hashlib.sha512(m).digest()


def _add(P, Q):
    A = (P[1] - P[0]) * (Q[1] - Q[0]) % _p
    B = (P[1] + P[0]) * (Q[1] + Q[0]) % _p
    C = 2 * P[3] * Q[3] * _d % _p
    D = 2 * P[2] * Q[2] % _p
    E, F, G, H = B - A, D - C, D + C, B + A
    return (E * F % _p, G * H % _p, F * G % _p, E * H % _p)


def _mul(s, P):
    Q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            Q = _add(Q, P)
        P = _add(P, P)
        s >>= 1
    return Q


def _equal(P, Q):
    return ((P[0] * Q[2] - Q[0] * P[2]) % _p == 0 and
            (P[1] * Q[2] - Q[1] * P[2]) % _p == 0)


def _recover_x(y, sign):
    if y >= _p:
        return None
    x2 = (y * y - 1) * _inv(_d * y * y + 1)
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (_p + 3) // 8, _p)
    if (x * x - x2) % _p != 0:
        x = x * _I % _p
    if (x * x - x2) % _p != 0:
        return None
    if (x & 1) != sign:
        x = _p - x
    return x


_gy = 4 * _inv(5) % _p
_gx = _recover_x(_gy, 0)
_G = (_gx, _gy, 1, _gx * _gy % _p)


def _compress(P):
    zi = _inv(P[2])
    x, y = P[0] * zi % _p, P[1] * zi % _p
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")


def _decompress(s):
    if len(s) != 32:
        return None
    y = int.from_bytes(s, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _recover_x(y, sign)
    if x is None:
        return None
    return (x, y, 1, x * y % _p)


def _expand(secret):
    if len(secret) != 32:
        raise ValueError("secret must be 32 bytes")
    h = _H(secret)
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def _modq(s):
    return int.from_bytes(_H(s), "little") % _L


def ed_public_key(secret: bytes) -> bytes:
    a, _ = _expand(secret)
    return _compress(_mul(a, _G))


def ed_sign(secret: bytes, msg: bytes) -> bytes:
    a, prefix = _expand(secret)
    A = _compress(_mul(a, _G))
    r = _modq(prefix + msg)
    Rs = _compress(_mul(r, _G))
    h = _modq(Rs + A + msg)
    s = (r + h * a) % _L
    return Rs + int.to_bytes(s, 32, "little")


def ed_verify(public: bytes, msg: bytes, signature: bytes) -> bool:
    try:
        if len(public) != 32 or len(signature) != 64:
            return False
        A = _decompress(public)
        R = _decompress(signature[:32])
        if A is None or R is None:
            return False
        s = int.from_bytes(signature[32:], "little")
        if s >= _L:
            return False
        h = _modq(signature[:32] + public + msg)
        return _equal(_mul(s, _G), _add(R, _mul(h, A)))
    except Exception:
        return False


# ═════════════════ صيغة مفتاح التفعيل (مطابقة لـ license_format.py في البرنامج) ═════════════════
# البرامج التي تصدر لها هذه الصفحة مفاتيح. اسم المنتج داخل التوقيع: مفتاح برنامج لا يعمل على آخر.
PRODUCTS = {
    "payroll2": {"label": "أداة الرواتب — الإصدار الجديد", "id": b"MJ-PAYROLL-v2", "features": True},
    "voice": {"label": "برنامج الإدخال الصوتي المستقل", "id": b"MJ-VOICE-ENTRY-v1", "features": False},
    "payroll1": {"label": "أداة الرواتب — الإصدار القديم", "id": None, "features": False},
}
FEATURES = {"voice": (1, "الإدخال الصوتي")}
PRODUCT = PRODUCTS["voice"]["id"]
EPOCH = datetime.date(2024, 1, 1)
NEVER = 0xFFFF
VERSION = 1
PLANS = {0: "تجريبي", 1: "شهري", 2: "سنوي", 3: "دائم", 4: "مخصص"}


def day_num(d: datetime.date) -> int:
    return (d - EPOCH).days


def day_date(n: int) -> datetime.date:
    return EPOCH + datetime.timedelta(days=n)


def _b32(b: bytes) -> str:
    return base64.b32encode(b).decode().rstrip("=")


def _unb32(s: str) -> bytes:
    s = re.sub(r"[^A-Z2-7]", "", s.upper().replace("0", "O").replace("1", "I").replace("8", "B"))
    return base64.b32decode(s + "=" * (-len(s) % 8))


def group(s: str, n: int) -> str:
    return "-".join(s[i:i + n] for i in range(0, len(s), n))


def request_code(machine: bytes) -> str:
    assert len(machine) == 10
    return group(_b32(machine), 4)


def parse_request_code(code: str) -> bytes:
    raw = _unb32(code)
    if len(raw) != 10:
        raise ValueError("رمز الطلب غير صحيح (يجب أن يكون 16 حرفًا)")
    return raw


def make_license(secret: bytes, machine: bytes, issued: datetime.date,
                 expiry: "datetime.date | None", plan: int = 4, product: bytes = PRODUCT) -> str:
    exp = NEVER if expiry is None else day_num(expiry)
    payload = struct.pack(">B10sHHB", VERSION, machine, day_num(issued), exp, plan)
    sig = ed_sign(secret, product + payload)
    return group(_b32(payload + sig), 8)


def ar_date(d: datetime.date) -> str:
    """تاريخ للعرض داخل نص عربي: الشرطة المائلة تبقي الأرقام متماسكة في اتجاه الكتابة."""
    return f"{d.year}/{d.month:02d}/{d.day:02d}"


# ═════════════════ الإصدار القديم (HMAC) — نفس خوارزمية البرنامج القديم حرفيًا ═════════════════

def old_make_key(secret: str, machine_id: str, days: int = 0) -> str:
    mid = re.sub(r"[^A-F0-9]", "", (machine_id or "").upper())[:16]
    if len(mid) < 8:
        raise ValueError("معرف الجهاز غير صالح (16 حرفًا من 0-9 و A-F)")
    exp = (dt.datetime.now() + dt.timedelta(days=int(days))).strftime("%Y%m%d") if days and int(days) > 0 else "0"
    sig = hmac.new(secret.encode("utf-8"), f"{mid}:{exp}".encode("utf-8"), hashlib.sha256).hexdigest()[:16].upper()
    return f"{mid}-{exp}-{sig}"


def old_secret():
    return _cloud_secret("old_secret") or (open(OLD_SECRET_FILE, encoding="utf-8").read().strip()
                                           if os.path.exists(OLD_SECRET_FILE) else None)


class License:
    def __init__(self, machine, issued, expiry, plan):
        self.machine, self.issued, self.expiry, self.plan = machine, issued, expiry, plan

    @property
    def perpetual(self):
        return self.expiry is None

    def describe(self):
        if self.perpetual:
            return "ترخيص دائم"
        return f"صالح حتى {ar_date(self.expiry)}"


def read_license(public: bytes, key: str, product: bytes = PRODUCT) -> License:
    """Raises ValueError with an Arabic message if the key is not genuine."""
    try:
        raw = _unb32(key)
    except Exception:
        raise ValueError("مفتاح التفعيل غير مقروء")
    if len(raw) != 80:
        raise ValueError("مفتاح التفعيل ناقص أو زائد — انسخه كاملًا")
    payload, sig = raw[:16], raw[16:]
    if not ed_verify(public, product + payload, sig):
        raise ValueError("مفتاح التفعيل غير صالح")
    ver, machine, issued, exp, plan = struct.unpack(">B10sHHB", payload)
    if ver != VERSION:
        raise ValueError("إصدار مفتاح غير مدعوم")
    return License(machine, day_date(issued), None if exp == NEVER else day_date(exp), plan)


st.set_page_config(page_title="نظام التفعيل", page_icon="🔏", layout="centered")
st.markdown("""
<style>
html, body, [data-testid="stAppViewContainer"], [data-testid="stSidebar"] {direction: rtl;}
[data-testid="stMarkdownContainer"], label, .stTextInput, .stSelectbox, .stDateInput, .stRadio {text-align: right;}
h1, h2, h3 {font-family: "Simplified Arabic","Noto Naskh Arabic",serif !important; font-weight: 700; letter-spacing: 0;}
code, pre, .stCode, input[type=text] {direction: ltr; text-align: left;}
.stamp {display:inline-block; color:#6B3E98; border:2.5px double #6B3E98; border-radius:4px; padding:2px 12px;
        transform:rotate(-4deg); font: 700 1.05rem "Simplified Arabic","Noto Naskh Arabic",serif;}
.muted {color:#6F7F79; font-size:.9rem}
[data-testid="stDataFrame"] {direction: ltr;}
</style>
""", unsafe_allow_html=True)


# ───────────────────────── المفاتيح وكلمة السر ─────────────────────────

def _cloud_secret(name):
    """قيمة من Secrets في Streamlit Cloud (أو .streamlit/secrets.toml محليًا)."""
    try:
        v = st.secrets.get(name)
        return str(v).strip() if v else None
    except Exception:
        return None


def ensure_keys():
    """المفتاح من Secrets إن وُجد (للنشر على الإنترنت)، وإلا من مجلد keys بجانب الملف."""
    if _cloud_secret("private_key"):
        return False
    if os.path.exists(PRIV):
        return False
    # لا ننشئ مفاتيح بصمت: مفتاح جديد يعني أن البرامج المبنية سابقًا لن تقبل مفاتيحه
    st.title("نظام التفعيل")
    st.error("لا يوجد مفتاح توقيع.")
    st.markdown(
        "**على Streamlit Cloud:** افتح على جهازك الملف `keys/private.key` (الذي بُني به البرنامج)، "
        "وانسخ محتواه. ثم في Streamlit Cloud: **Settings ← Secrets** والصق:")
    st.code('private_key = "المحتوى هنا"\nadmin_password = "كلمة سر للصفحة"', language="toml")
    st.markdown("**على جهازك لأول مرة فقط:** شغّل `build.bat` قبل هذه الصفحة، فهو ينشئ المفتاح.")
    st.stop()


def secret():
    s = _cloud_secret("private_key") or open(PRIV).read().strip()
    return bytes.fromhex(s)


def public_hex():
    return ed_public_key(secret()).hex()


def require_password():
    """كلمة السر مطلوبة إذا ضُبط admin_password في Secrets (إلزامي عند النشر على الإنترنت)."""
    pw = _cloud_secret("admin_password")
    online = bool(_cloud_secret("private_key"))
    if online and not pw:
        st.error("الصفحة منشورة دون كلمة سر. أضف admin_password في Secrets.")
        st.stop()
    if not pw or st.session_state.get("auth"):
        return
    st.title("نظام التفعيل")
    typed = st.text_input("كلمة السر", type="password")
    if st.button("دخول", type="primary"):
        if hmac.compare_digest(typed.encode(), pw.encode()):
            st.session_state.auth = True
            st.rerun()
        st.error("كلمة السر غير صحيحة.")
    st.stop()


# ───────────────────────── قاعدة البيانات ─────────────────────────

def db():
    path = DB
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
    except OSError:
        import tempfile
        path = os.path.join(tempfile.gettempdir(), "licenses.db")
    c = sqlite3.connect(path)
    c.execute("""CREATE TABLE IF NOT EXISTS licenses(
        id INTEGER PRIMARY KEY AUTOINCREMENT, created TEXT, customer TEXT, contact TEXT,
        request_code TEXT, plan TEXT, issued TEXT, expiry TEXT, license_key TEXT, notes TEXT)""")
    cols = [r[1] for r in c.execute("PRAGMA table_info(licenses)")]
    if "product" not in cols:
        c.execute("ALTER TABLE licenses ADD COLUMN product TEXT DEFAULT 'voice'")
    if "features" not in cols:
        c.execute("ALTER TABLE licenses ADD COLUMN features TEXT DEFAULT ''")
    return c


def save(row, product="voice", features=""):
    with db() as c:
        c.execute("INSERT INTO licenses(created,customer,contact,request_code,plan,issued,expiry,license_key,notes,"
                  "product,features) VALUES(?,?,?,?,?,?,?,?,?,?,?)", tuple(row) + (product, features))


def rows():
    with db() as c:
        return c.execute("SELECT id,created,customer,contact,request_code,plan,issued,expiry,license_key,notes,"
                         "product,features FROM licenses ORDER BY id DESC").fetchall()


# ───────────────────────── الصفحات ─────────────────────────

PLANS = {
    "تجربة 7 أيام": (0, 7), "شهر": (1, 30), "3 أشهر": (1, 91), "6 أشهر": (1, 182),
    "سنة": (2, 365), "دائم": (3, None), "حتى تاريخ محدد": (4, "custom"),
}


def page_issue():
    st.subheader("إصدار مفتاح")
    prefill = st.session_state.pop("prefill", {})
    keys = list(PRODUCTS)
    prod = st.radio("البرنامج", keys, format_func=lambda k: PRODUCTS[k]["label"], horizontal=True,
                    index=keys.index(prefill.get("product", "payroll2")), key="prod")
    P_ = PRODUCTS[prod]
    old = P_["id"] is None
    if old and not old_secret():
        st.warning("لإصدار مفاتيح الإصدار القديم أضف سره: في Secrets سطر old_secret = \"...\" "
                   "أو ملف keys/old_secret.txt. السر هو قيمة LICENSE_SECRET في البرنامج القديم.")
        return
    with st.form("issue", clear_on_submit=False):
        code = st.text_input("معرف الجهاز (Hard ID — 16 حرفًا)" if old else "رمز الطلب من جهاز العميل",
                             value=prefill.get("code", ""),
                             placeholder="XXXXXXXXXXXXXXXX" if old else "XXXX-XXXX-XXXX-XXXX")
        c1, c2 = st.columns(2)
        customer = c1.text_input("اسم العميل", value=prefill.get("customer", ""))
        contact = c2.text_input("هاتف أو جهة", value=prefill.get("contact", ""))
        feats = []
        if P_["features"]:
            st.markdown("**الصلاحيات**")
            for fk, (bit, lbl) in FEATURES.items():
                if st.checkbox(lbl, value=fk in prefill.get("features", ""), key=f"f_{fk}"):
                    feats.append(fk)
        plan = st.radio("المدة", list(PLANS), horizontal=True, index=4)
        c3, c4 = st.columns(2)
        start = c3.date_input("يبدأ من", value=dt.date.today(), disabled=old)
        until = c4.date_input("ينتهي في (للمدة المحددة فقط)", value=dt.date.today() + dt.timedelta(days=365))
        notes = st.text_input("ملاحظات")
        go = st.form_submit_button("أصدر المفتاح", type="primary")
    if not go:
        return
    pid, days = PLANS[plan]
    today = dt.date.today()
    if old:
        if days == "custom":
            days = max(1, (until - today).days)
        try:
            key = old_make_key(old_secret(), code, 0 if days is None else days)
        except ValueError as e:
            st.error(str(e)); return
        exp = key.split("-")[1]
        desc = "دائم" if exp == "0" else f"حتى {exp[:4]}/{exp[4:6]}/{exp[6:]}"
        save((dt.datetime.now().isoformat(timespec="seconds"), customer, contact, key.split("-")[0],
              plan, today.isoformat(), "" if exp == "0" else f"{exp[:4]}-{exp[4:6]}-{exp[6:]}", key, notes), prod)
    else:
        try:
            machine = parse_request_code(code)
        except Exception as e:
            st.error(str(e) or "رمز الطلب غير صحيح."); return
        expiry = None if days is None else (until if days == "custom" else start + dt.timedelta(days=days))
        if expiry is not None and expiry < start:
            st.error("تاريخ الانتهاء قبل تاريخ البدء."); return
        flags = sum(FEATURES[f][0] for f in feats) if P_["features"] else pid
        key = make_license(secret(), machine, start, expiry, flags, P_["id"])
        lic = read_license(bytes.fromhex(public_hex()), key, P_["id"])          # تحقق ذاتي قبل الحفظ
        desc = lic.describe()
        if P_["features"]:
            desc = ("دائم" if lic.perpetual else f"حتى {ar_date(lic.expiry)}") + \
                   (" — " + "، ".join(FEATURES[f][1] for f in feats) if feats else " — أساسي (دون صوت)")
        save((dt.datetime.now().isoformat(timespec="seconds"), customer, contact, request_code(machine),
              plan, start.isoformat(), expiry.isoformat() if expiry else "", key, notes), prod, ",".join(feats))
    st.markdown(f'<span class="stamp">صدر</span> &nbsp; <span class="muted">{P_["label"]} · {desc}</span>',
                unsafe_allow_html=True)
    st.code(key, language=None)
    st.caption("انسخ المفتاح بالزر في زاوية المربع وأرسله للعميل. يُلصق في نافذة «تفعيل البرنامج».")


def status(expiry):
    if not expiry:
        return "دائم"
    left = (dt.date.fromisoformat(expiry) - dt.date.today()).days
    return "منتهٍ" if left < 0 else f"باقٍ {left} يومًا"


def page_log():
    st.subheader("السجل")
    data = rows()
    if not data:
        st.info("لم يصدر أي مفتاح بعد."); return
    q = st.text_input("بحث باسم العميل أو رمز الطلب").strip().lower()
    view = [r for r in data if not q or q in (r[2] or "").lower() or q in (r[4] or "").lower() or q in (r[3] or "").lower()]
    st.dataframe(
        [{"#": r[0], "البرنامج": PRODUCTS.get(r[10] or "voice", {}).get("label", r[10]),
          "العميل": r[2], "الجهة": r[3], "رمز الطلب": r[4], "الصلاحيات": (r[11] or "").replace("voice", "صوت") or "—",
          "المدة": r[5], "من": r[6], "إلى": r[7] or "—", "الحالة": status(r[7])} for r in view],
        hide_index=True, width="stretch")
    ids = [r[0] for r in view]
    pick = st.selectbox("عرض مفتاح أو تجديده", ids, format_func=lambda i: next(f"#{r[0]}  {r[2] or ''}  {r[4]}" for r in view if r[0] == i))
    r = next(r for r in view if r[0] == pick)
    st.code(r[8], language=None)
    if st.button("تجديد لنفس الجهاز"):
        st.session_state.prefill = {"code": r[4], "customer": r[2], "contact": r[3],
                                    "product": r[10] or "voice", "features": r[11] or ""}
        st.session_state.goto = "إصدار مفتاح"
        st.rerun()
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["id", "created", "customer", "contact", "request_code", "plan", "issued", "expiry", "license_key", "notes",
                "product", "features"])
    w.writerows(data)
    st.download_button("تنزيل السجل CSV", buf.getvalue().encode("utf-8-sig"), "licenses.csv", "text/csv")


def page_keys(new):
    st.subheader("المفاتيح")
    if _cloud_secret("private_key"):
        st.info("على Streamlit Cloud يُمسح السجل عند إعادة تشغيل التطبيق. انسخ كل مفتاح تصدره، أو نزّل السجل CSV دوريًا.")
    st.write("المفتاح الخاص في مجلد keys هو ما يُصدر مفاتيح التفعيل. خذ نسخة من مجلد keys في فلاشة.")
    st.code(public_hex(), language=None)
    st.caption("هذا المفتاح العام يطلبه build_exe.bat عند بناء أداة الرواتب الجديدة. الصقه هناك.")


def main():
    new = ensure_keys()
    require_password()
    st.title("نظام التفعيل")
    st.markdown(f'<span class="muted">رقم النسخة: <b dir="ltr">{public_hex()[:8].upper()}</b> — يجب أن يطابق الرقم '
                f'في نافذة تفعيل البرنامج الجديد. إن اختلف: أعد البناء بالمفتاح العام من قسم «المفاتيح».</span>',
                unsafe_allow_html=True)
    tabs = ["إصدار مفتاح", "السجل", "المفاتيح"]
    if "goto" in st.session_state:
        st.session_state.tab = st.session_state.pop("goto")
    st.session_state.setdefault("tab", tabs[0])
    tab = st.radio("القسم", tabs, horizontal=True, label_visibility="collapsed", key="tab")
    if tab == tabs[0]:
        page_issue()
    elif tab == tabs[1]:
        page_log()
    else:
        page_keys(new)


main()
