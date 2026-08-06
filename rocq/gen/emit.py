"""Emit the Rocq text of a cover of Zone I's slope range.

Every constant printed here was computed in ``ledger.py`` with mpmath at
``mp.dps = 40`` and rounded OUTWARD.  Nothing is guessed: a constant that
is too tight makes ``rocq c`` fail on the corresponding ``interval`` call.
"""

import sys
from mpmath import mp, mpf, log
import ledger as L
from ledger import dn, up, rat, mpf as _m

DQ = 7      # decimals used for grid points
DV = 9      # decimals used for the window's derived constants
DR = 12     # decimals used for rho boxes and point values of f


# --------------------------------------------------------------- nodes
def node_data(q, h):
    """the three point enclosures of f, and the slope bracket they give"""
    out = {'q': q, 'h': h}
    for tag, qq in (('A', q), ('M', q - h), ('P', q + h)):
        r = L.rhoc(qq)
        a, b = dn(r, DR), up(r, DR)
        out[tag] = dict(q=qq, a=a, b=b,
                        lo=dn(qq * log(a) / L.LN2, DR),
                        hi=up(qq * log(b) / L.LN2, DR))
    flo = out['A']['lo']
    out['bhi'] = up((out['M']['hi'] - flo) / h, DV)
    out['blo'] = dn((flo - out['P']['hi']) / h, DV)
    return out


def emit_point_lower(name, d, prec):
    return """
Lemma %s (r : R) : 0 < r -> g (%s) r = 0 -> %s <= fq (%s) r.
Proof.
  apply (f_lower_at (%s) (%s) (%s)); try lra; unfold g, fq;
    try (intros y Hy); interval with (i_prec %d).
Qed.
""" % (name, rat(d['q'], DQ), rat(d['lo'], DR), rat(d['q'], DQ),
       rat(d['q'], DQ), rat(d['a'], DR), rat(d['b'], DR), prec)


def emit_point_upper(name, d, prec, dq):
    return """
Lemma %s (r : R) : 0 < r -> g (%s) r = 0 -> fq (%s) r <= %s.
Proof.
  apply (f_upper_at (%s) (%s) (%s)); try lra; unfold g, fq;
    try (intros y Hy); interval with (i_prec %d).
Qed.
""" % (name, rat(d['q'], dq), rat(d['q'], dq), rat(d['hi'], DR),
       rat(d['q'], dq), rat(d['a'], DR), rat(d['b'], DR), prec)


def emit_node(i, nd, prec=200, pfx=""):
    """Node lemma names carry the part's prefix: a part repeats the node it
    shares with the next part, and duplicate short names across Required
    modules would shadow each other."""
    q, h = nd['q'], nd['h']
    dqh = DQ                               # q +/- h stays on the DQ grid
    i = "%s%d" % (pfx, i)
    s = "(** node %s: q = %s *)\n" % (i, mp.nstr(q, 10))
    s += emit_point_lower("nA_%s" % i, nd['A'], prec)
    s += emit_point_upper("nM_%s" % i, nd['M'], prec, dqh)
    s += emit_point_upper("nP_%s" % i, nd['P'], prec, dqh)
    s += """
Lemma bhi_%s (b r : R) : 0 < r -> g (%s) r = 0 -> EminRel b (%s) (fq (%s) r) ->
  b <= %s.
Proof.
  intros Hr Hg Hm.
  refine (slope_upper (%s) (%s) (%s) (%s) (%s) (%s) b r
            _ _ _ _ Hr Hg Hm _ nM_%s _);
    [lra|lra|lra|lra| exact (nA_%s r Hr Hg) | lra].
Qed.

Lemma blo_%s (b r : R) : 0 < r -> g (%s) r = 0 -> EminRel b (%s) (fq (%s) r) ->
  %s <= b.
Proof.
  intros Hr Hg Hm.
  refine (slope_lower (%s) (%s) (%s) (%s) (%s) (%s) b r
            _ _ _ _ Hr Hg Hm _ nP_%s _);
    [lra|lra|lra|lra| exact (nA_%s r Hr Hg) | lra].
Qed.
""" % (i, rat(q, DQ), rat(q, DQ), rat(q, DQ), rat(nd['bhi'], DV),
       rat(q, DQ), rat(h, DQ), rat(nd['M']['q'], dqh), rat(nd['A']['lo'], DR),
       rat(nd['M']['hi'], DR), rat(nd['bhi'], DV), i, i,
       i, rat(q, DQ), rat(q, DQ), rat(q, DQ), rat(nd['blo'], DV),
       rat(q, DQ), rat(h, DQ), rat(nd['P']['q'], dqh), rat(nd['A']['lo'], DR),
       rat(nd['P']['hi'], DR), rat(nd['blo'], DV), i, i)
    return s


# ------------------------------------------------------------- windows
def emit_window(i, w, prec=120, pfx=""):
    R = lambda x: rat(x, DV)
    qa, qb = rat(w['qa'], DQ), rat(w['qb'], DQ)
    r1a, r1b = rat(w['r1'][0], DR), rat(w['r1'][1], DR)
    r2a, r2b = rat(w['r2'][0], DR), rat(w['r2'][1], DR)
    rta, rtb = rat(w['rt'][0], DR), rat(w['rt'][1], DR)
    d = dict(i=i, qa=qa, qb=qb, blo=R(w['blo']), bhi=R(w['bhi']),
             zlo=R(w['zlo']), zhi=R(w['zhi']),
             q2lo=R(w['q2'].lo), q2hi=R(w['q2'].hi),
             Glo=R(w['G'].lo), Ghi=R(w['G'].hi),
             Slo=R(w['S'].lo), Shi=R(w['S'].hi),
             f1lo=R(w['f1'].lo), f1hi=R(w['f1'].hi),
             f2lo=R(w['f2'].lo), f2hi=R(w['f2'].hi),
             ftlo=R(w['ft'].lo), fthi=R(w['ft'].hi),
             w1lo=R(w['w1'].lo), w1hi=R(w['w1'].hi),
             qtlo=R(w['qt'].lo), qthi=R(w['qt'].hi),
             val=rat(w['val'], 6),
             r1a=r1a, r1b=r1b, r2a=r2a, r2b=r2b, rta=rta, rtb=rtb,
             p=prec, lo="%s%d" % (pfx, i), hi="%s%d" % (pfx, i + 1))
    return """
(** window %(i)d: q1 in [%(qa)s, %(qb)s] *)

Lemma hz_%(i)d (b : R) : %(blo)s <= b <= %(bhi)s ->
  %(zlo)s <= zof b <= %(zhi)s.
Proof. intros H. unfold zof, LAM in *. lra. Qed.

Lemma hq2_%(i)d (z : R) : %(zlo)s <= z <= %(zhi)s ->
  %(q2lo)s <= QS * sigm z <= %(q2hi)s.
Proof. intros H. unfold sigm, QS. split; interval with (i_prec %(p)d). Qed.

Lemma hG_%(i)d (z : R) : %(zlo)s <= z <= %(zhi)s ->
  %(Glo)s <= (QS / LAM) * (sp z - z * sigm z) <= %(Ghi)s.
Proof. intros H. unfold sigm, sp, QS, LAM. split; interval with (i_prec %(p)d). Qed.

Lemma hS_%(i)d (z : R) : %(zlo)s <= z <= %(zhi)s ->
  %(Slo)s <= 1 - (QS / LAM) * sp z <= %(Shi)s.
Proof. intros H. unfold sp, QS, LAM. split; interval with (i_prec %(p)d). Qed.

Lemma hf1_%(i)d (q r : R) : %(qa)s <= q <= %(qb)s -> 0 < r -> g q r = 0 ->
  %(f1lo)s <= fq q r <= %(f1hi)s.
Proof.
  apply (f_in (%(qa)s) (%(qb)s) (%(r1a)s) (%(r1b)s)); try lra; unfold g, fq.
  - interval with (i_prec %(p)d).
  - interval with (i_prec %(p)d).
  - intros x y Hx Hy. split; interval with (i_prec %(p)d).
Qed.

Lemma hf2_%(i)d (q r : R) : %(q2lo)s <= q <= %(q2hi)s -> 0 < r -> g q r = 0 ->
  %(f2lo)s <= fq q r <= %(f2hi)s.
Proof.
  apply (f_in (%(q2lo)s) (%(q2hi)s) (%(r2a)s) (%(r2b)s)); try lra; unfold g, fq.
  - interval with (i_prec %(p)d).
  - interval with (i_prec %(p)d).
  - intros x y Hx Hy. split; interval with (i_prec %(p)d).
Qed.

Lemma hft_%(i)d (q r : R) : %(qtlo)s <= q <= %(qthi)s -> 0 < r -> g q r = 0 ->
  %(ftlo)s <= fq q r <= %(fthi)s.
Proof.
  apply (f_in (%(qtlo)s) (%(qthi)s) (%(rta)s) (%(rtb)s)); try lra; unfold g, fq.
  - interval with (i_prec %(p)d).
  - interval with (i_prec %(p)d).
  - intros x y Hx Hy. split; interval with (i_prec %(p)d).
Qed.

Lemma hw1_%(i)d (q1 b f1 Sb : R) :
  %(qa)s <= q1 <= %(qb)s -> %(blo)s <= b <= %(bhi)s ->
  %(f1lo)s <= f1 <= %(f1hi)s -> %(Slo)s <= Sb <= %(Shi)s ->
  %(w1lo)s <= w1of Sb (q1 * b + f1) <= %(w1hi)s.
Proof.
  intros Hq Hb Hf HS. unfold w1of, MU in *.
  split; interval with (i_prec %(p)d).
Qed.

Lemma hqt_%(i)d (q1 q2 w1 : R) :
  %(qa)s <= q1 <= %(qb)s -> %(q2lo)s <= q2 <= %(q2hi)s ->
  %(w1lo)s <= w1 <= %(w1hi)s ->
  %(qtlo)s <= w1 * q1 + (1 - w1) * q2 <= %(qthi)s.
Proof. intros H1 H2 H3. split; interval with (i_prec %(p)d). Qed.

Lemma hled_%(i)d (q1 q2 G w1 f1 f2 ft : R) :
  %(qa)s <= q1 <= %(qb)s -> %(q2lo)s <= q2 <= %(q2hi)s ->
  %(Glo)s <= G <= %(Ghi)s -> %(w1lo)s <= w1 <= %(w1hi)s ->
  %(f1lo)s <= f1 <= %(f1hi)s -> %(f2lo)s <= f2 <= %(f2hi)s ->
  %(ftlo)s <= ft <= %(fthi)s ->
  %(val)s <= ledger q1 q2 G w1 f1 f2 ft.
Proof. intros. unfold ledger, EPS. interval with (i_prec %(p)d). Qed.

Theorem window_%(i)d
  (q1 b1 r1 r2 rt ra rb ba bb f1 f2 ft q2 G w1 qt : R) :
  %(qa)s <= q1 <= %(qb)s ->
  0 < r1 -> 0 < r2 -> 0 < rt -> 0 < ra -> 0 < rb ->
  g q1 r1 = 0 -> g (%(qa)s) ra = 0 -> g (%(qb)s) rb = 0 ->
  EminRel b1 q1 (fq q1 r1) ->
  EminRel ba (%(qa)s) (fq (%(qa)s) ra) ->
  EminRel bb (%(qb)s) (fq (%(qb)s) rb) ->
  q2 = q2of b1 -> G = Gof b1 -> f1 = fq q1 r1 ->
  w1 = w1of (Sof b1) (q1 * b1 + f1) -> qt = w1 * q1 + (1 - w1) * q2 ->
  f2 = fq q2 r2 -> ft = fq qt rt ->
  g q2 r2 = 0 -> g qt rt = 0 ->
  %(val)s <= ledger q1 q2 G w1 f1 f2 ft.
Proof.
  intros Hq1 Hr1 Hr2 Hrt Hra Hrb Hg1 Hga Hgb Hm1 Hma Hmb
         Hq2 HG Hf1 Hw1 Hqt Hf2 Hft Hg2 Hgt.
  assert (Hb : %(blo)s <= b1 <= %(bhi)s).
  { refine (slope_closed (%(qa)s) (%(qb)s) q1 (%(blo)s) (%(bhi)s) b1 r1 ra rb ba bb
              _ _ _ Hr1 Hra Hrb Hg1 Hga Hgb Hm1 Hma Hmb bhi_%(lo)s blo_%(hi)s);
      lra. }
  exact (ledger_window _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           hz_%(i)d hq2_%(i)d hG_%(i)d hS_%(i)d hf1_%(i)d hf2_%(i)d hft_%(i)d
           hw1_%(i)d hqt_%(i)d hled_%(i)d
           q1 b1 r1 r2 rt f1 f2 ft q2 G w1 qt
           Hq1 Hb Hq2 HG Hf1 Hw1 Hqt Hf2 Hft Hr1 Hr2 Hrt Hg1 Hg2 Hgt).
Qed.
""" % d
