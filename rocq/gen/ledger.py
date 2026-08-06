"""Numerics for the Zone I ledger cover.

Everything the generator emits into Rocq is computed here first, with
mpmath at ``mp.dps = 40``, and rounded OUTWARD before it is printed.  No
constant is ever guessed.  The interval arithmetic below deliberately
mirrors, term by term, what CoqInterval's ``interval`` tactic does on the
corresponding goal -- in particular it DECOUPLES repeated occurrences of a
variable, exactly as the tactic does -- so that a bound accepted here is
accepted by the prover too.  (A bound that is too tight makes the Rocq
build fail loudly; it can never make it unsound.)
"""

from mpmath import mp, mpf, log, findroot, power, floor, ceil

mp.dps = 40

# ---- the constants of the ansatz, matching LedgerA.v exactly ----------
KHI = mpf('3317423792563106') / mpf('10000000000000000')
LAM = mpf(30)
MU = mpf(30)
EPS = mpf(1) / 100
QS = mpf('15153832361072514') / mpf('10000000000000000')
LN2 = log(2)


# ---------------------------------------------------------------- rho_c
def gval(q, r):
    return power(r, -q) + power(1 + r, -q) - 1


_rcache = {}


def rhoc(q):
    key = str(q)
    if key in _rcache:
        return _rcache[key]
    v = findroot(lambda r: gval(q, r),
                 (mpf(1) + mpf('1e-35'), power(2, 1 / q)),
                 solver='anderson', tol=mpf('1e-70'))
    _rcache[key] = v
    return v


def fval(q):
    return q * log(rhoc(q)) / LN2


def fprime(q, h=mpf('1e-12')):
    return (fval(q + h) - fval(q - h)) / (2 * h)


# ------------------------------------------------- outward rounding ----
def dn(x, d):
    """largest n/10^d that is <= x (with one ulp of slack)"""
    return (floor(mpf(x) * mpf(10) ** d) - 1) / mpf(10) ** d


def up(x, d):
    return (ceil(mpf(x) * mpf(10) ** d) + 1) / mpf(10) ** d


def rat(x, d):
    """Rocq source text for the exact rational x, which must be n/10^d"""
    n = mp.nint(mpf(x) * mpf(10) ** d)
    assert abs(mpf(x) * mpf(10) ** d - n) < mpf('1e-10'), (x, d)
    return "%s/%s" % (int(n), 10 ** d)


class I:
    """interval, with the tactic's decoupling semantics"""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        self.lo = mpf(lo)
        self.hi = mpf(lo if hi is None else hi)

    def __add__(s, o):
        o = iv(o)
        return I(s.lo + o.lo, s.hi + o.hi)

    __radd__ = __add__

    def __sub__(s, o):
        o = iv(o)
        return I(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return iv(o) - s

    def __mul__(s, o):
        o = iv(o)
        c = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(min(c), max(c))

    __rmul__ = __mul__

    def w(s):
        return s.hi - s.lo

    def __repr__(s):
        return "[%s, %s]" % (mp.nstr(s.lo, 12), mp.nstr(s.hi, 12))


def iv(x):
    return x if isinstance(x, I) else I(x)


# ------------------------------------------------- the primitives ------
sp = lambda z: log(1 + power(2, z)) / LN2
sigm = lambda z: 1 / (1 + power(2, -z))
Sz = lambda z: 1 - (QS / LAM) * sp(z)


def G_decoupled(zlo, zhi):
    """(QS/LAM)*(sp z - z*sigm z) as `interval` sees it: sp increasing,
    and the product z*sigm z evaluated from the two ranges separately."""
    P = I(zlo, zhi) * I(sigm(zlo), sigm(zhi))
    return (QS / LAM) * I(sp(zlo) - P.hi, sp(zhi) - P.lo)


def G_true(zlo, zhi):
    """the real range: d/dz (sp z - z sigm z) = -z sigm'(z), so the
    expression increases for z<0, decreases for z>0."""
    Gv = lambda z: (QS / LAM) * (sp(z) - z * sigm(z))
    if zhi <= 0:
        return I(Gv(zlo), Gv(zhi))
    if zlo >= 0:
        return I(Gv(zhi), Gv(zlo))
    return I(min(Gv(zlo), Gv(zhi)), Gv(mpf(0)))


def rho_box(qlo, qhi, d=12):
    """[a,b] with a <= rho_c(q) <= b for every q in [qlo,qhi]; rho_c is
    decreasing in q, so the extremes sit at the endpoints."""
    return dn(rhoc(qhi), d), up(rhoc(qlo), d)


def f_box(qlo, qhi, d=12, dv=9):
    """f over [qlo,qhi] as `f_in` gets it: the rho box times the q box,
    with fq = q ln r / ln 2 increasing in both arguments."""
    a, b = rho_box(qlo, qhi, d)
    lo = dn(qlo * log(a) / LN2, dv)
    hi = up(qhi * log(b) / LN2, dv)
    return (a, b, lo, hi)


# --------------------------------------------------------- a window ----
def window(qa, qb, blo, bhi, dv=9):
    """Every constant the Rocq lemmas for the window [qa,qb] need, given
    a slope bracket [blo,bhi].  Returns a dict of exact rationals."""
    zlo = dn(LAM * (KHI - bhi), dv)
    zhi = up(LAM * (KHI - blo), dv)

    q2 = I(dn(QS * sigm(zlo), dv), up(QS * sigm(zhi), dv))
    Gd = G_decoupled(zlo, zhi)
    G = I(dn(Gd.lo, dv), up(Gd.hi, dv))
    S = I(dn(Sz(zhi), dv), up(Sz(zlo), dv))

    r1a, r1b, f1lo, f1hi = f_box(qa, qb)
    f1 = I(f1lo, f1hi)

    E = I(qa, qb) * I(blo, bhi) + f1
    w1raw = I(1 / (1 + power(2, -MU * (S.lo - E.hi))),
              1 / (1 + power(2, -MU * (S.hi - E.lo))))
    w1 = I(dn(w1raw.lo, dv), up(w1raw.hi, dv))

    qtraw = w1 * I(qa, qb) + (1 - w1) * q2
    qt = I(dn(qtraw.lo, dv), up(qtraw.hi, dv))

    r2a, r2b, f2lo, f2hi = f_box(q2.lo, q2.hi)
    rta, rtb, ftlo, fthi = f_box(qt.lo, qt.hi)
    f2, ft = I(f2lo, f2hi), I(ftlo, fthi)

    led = (w1 * I(qa, qb) * EPS + (1 - w1) * (q2 * EPS + G)
           - (w1 * f1 + (1 - w1) * f2 - ft))
    val = dn(led.lo, 6)

    return dict(qa=qa, qb=qb, blo=blo, bhi=bhi, zlo=zlo, zhi=zhi,
                q2=q2, G=G, S=S, f1=f1, w1=w1, qt=qt, f2=f2, ft=ft,
                r1=(r1a, r1b), r2=(r2a, r2b), rt=(rta, rtb),
                led=led, val=val, Gtrue=G_true(zlo, zhi))
