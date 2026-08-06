(** * The slope over a window, without differentiating  (Rocq + CoqInterval)

    m43 measured that a Zone I proof needs beta pinned to about 3e-4 over
    a q-window, and that bracketing beta by difference quotients across
    the window gives width ~ 0.26 sqrt(W) — too slow.  The conclusion
    drawn there was that the implicit function theorem is needed.

    IT IS NOT.  The 1/h amplification in that measurement comes from
    evaluating f over the WHOLE window and then dividing by h.  Bracket
    instead at the two ENDPOINTS — single points, where f is known to
    interval precision — and transport to the interior by monotonicity.

    The monotonicity is free.  If q1 minimises q |-> q b1 + f(q) and q2
    minimises q |-> q b2 + f(q), then adding the two minimality
    statements against each other gives

        (q1 - q2) (b1 - b2) <= 0,

    so the optimal slope is ANTITONE in the minimiser.  This is Topkis's
    monotone comparative statics: two applications of the hypothesis and
    one [nra].  No derivative, no convexity, no smoothness.

    Consequently, for q1 strictly inside (qa, qb),

        b(qb) <= b(q1) <= b(qa),

    and each endpoint is bracketed AT A POINT, where the difference
    quotient costs only |f''| h and h is free.  The window enclosure is
    then |b(qa) - b(qb)| ~ |f''| W — LINEAR in the window width, which
    is exactly what the derivative would have given.

    Measured on the window (2.4, 2.6): this route gives 0.0239, against
    0.116 for the derivative-free bracket taken across the window.

    ON THE RANGE WHERE THIS APPLIES.  Antitonicity holds between genuine
    minimisers only.  Where f is concave (q <~ 0.5) a q is not a
    minimiser at all, and the point bracket there comes out EMPTY — its
    lower end exceeds its upper end — which is a machine-checkable
    certificate of that fact rather than a gap.  The slopes that
    actually occur in Zone I are q in [1.42, 3.25] (measured: beta =
    0.12 gives argmin 3.180, beta = 0.36 gives 1.423), matching the
    appendix's [1.45, 3.25]; and past beta = kappa* + eps the E-branch
    is at the ceiling anyway, where [EnvelopeE.E_ge_one] takes over. *)

From Stdlib Require Import Reals Lra.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar RhoEnclose LedgerParam EnvelopeE.
Local Open Scope R_scope.

(** ** Topkis: the optimal slope is antitone in the minimiser *)

Theorem topkis (b1 b2 q1 q2 r1 r2 : R) :
  0 < q1 -> 0 < q2 -> 0 < r1 -> 0 < r2 ->
  g q1 r1 = 0 -> g q2 r2 = 0 ->
  EminRel b1 q1 (fq q1 r1) -> EminRel b2 q2 (fq q2 r2) ->
  (q1 - q2) * (b1 - b2) <= 0.
Proof.
  intros Hq1 Hq2 Hr1 Hr2 Hg1 Hg2 H1 H2.
  (* q1 is at least as good as q2 for b1, and vice versa for b2 *)
  assert (A := H1 q2 r2 Hq2 Hr2 Hg2).
  assert (B := H2 q1 r1 Hq1 Hr1 Hg1).
  nra.
Qed.

(** ** The window

    Strictness on the [q] side is what turns the product bound into a
    bound on [b]; a cover therefore uses windows whose endpoints are
    the previous window's interior, which costs nothing. *)

Theorem slope_window (qa qb q1 ba bb b1 ra rb r1 : R) :
  0 < qa -> qa < q1 -> q1 < qb ->
  0 < ra -> 0 < rb -> 0 < r1 ->
  g qa ra = 0 -> g qb rb = 0 -> g q1 r1 = 0 ->
  EminRel ba qa (fq qa ra) -> EminRel bb qb (fq qb rb) ->
  EminRel b1 q1 (fq q1 r1) ->
  bb <= b1 <= ba.
Proof.
  intros Hqa Hab Hbq Hra Hrb Hr1 Hga Hgb Hg1 Ha Hb H1.
  assert (Hq1 : 0 < q1) by lra.
  assert (Hqb : 0 < qb) by lra.
  split.
  - (* q1 < qb, so (q1 - qb) < 0 and the product bound flips *)
    assert (T := topkis b1 bb q1 qb r1 rb Hq1 Hqb Hr1 Hrb Hg1 Hgb H1 Hb).
    nra.
  - (* qa < q1, so (q1 - qa) > 0 *)
    assert (T := topkis b1 ba q1 qa r1 ra Hq1 Hqa Hr1 Hra Hg1 Hga H1 Ha).
    nra.
Qed.

(** ** The same two facts under eps-minimality

    [LedgerParam.EminEps] replaces exact minimality by minimality to
    within eps -- the version that [EminExists.emin_eps_exists] actually
    produces.  Adding the two eps-statements against each other leaves an
    eps on each side, so Topkis's inequality loses exactly [2 eps]. *)

Theorem topkis_eps (eps b1 b2 q1 q2 r1 r2 : R) :
  0 < q1 -> 0 < q2 -> 0 < r1 -> 0 < r2 ->
  g q1 r1 = 0 -> g q2 r2 = 0 ->
  EminEps eps b1 q1 (fq q1 r1) -> EminEps eps b2 q2 (fq q2 r2) ->
  (q1 - q2) * (b1 - b2) <= 2 * eps.
Proof.
  intros Hq1 Hq2 Hr1 Hr2 Hg1 Hg2 H1 H2.
  assert (A := H1 q2 r2 Hq2 Hr2 Hg2).
  assert (B := H2 q1 r1 Hq1 Hr1 Hg1).
  nra.
Qed.

(** **THE WINDOW, eps-VERSION -- AND ITS HONEST DEFECT.**

    Dividing the product bound by the gap is the only thing Topkis
    permits, so the loss is [2 eps / (q1 - qa)] on the upper side and
    [2 eps / (qb - q1)] on the lower: it BLOWS UP as [q1] approaches
    either node.  The statement below says exactly that, and no more.

    A cover cannot use this form -- its windows are as narrow as
    4e-7, and the endpoints are grid points shared with the neighbouring
    window.  What the cover uses instead is
    [CoverGlue.slope_hi_eps]/[slope_lo_eps], which anchors the transport
    on the node's own difference-quotient step [h] rather than on the
    gap, and loses [2 eps / h] UNIFORMLY over the closed window,
    endpoints included. *)

Theorem slope_window_eps (eps qa qb q1 ba bb b1 ra rb r1 : R) :
  0 < qa -> qa < q1 -> q1 < qb ->
  0 < ra -> 0 < rb -> 0 < r1 ->
  g qa ra = 0 -> g qb rb = 0 -> g q1 r1 = 0 ->
  EminEps eps ba qa (fq qa ra) -> EminEps eps bb qb (fq qb rb) ->
  EminEps eps b1 q1 (fq q1 r1) ->
  bb - 2 * eps / (qb - q1) <= b1 <= ba + 2 * eps / (q1 - qa).
Proof.
  intros Hqa Hab Hbq Hra Hrb Hr1 Hga Hgb Hg1 Ha Hb H1.
  assert (Hq1 : 0 < q1) by lra.
  assert (Hqb : 0 < qb) by lra.
  split.
  - assert (T := topkis_eps eps b1 bb q1 qb r1 rb Hq1 Hqb Hr1 Hrb Hg1 Hgb H1 Hb).
    (* (q1 - qb)(b1 - bb) <= 2 eps  with  q1 - qb < 0 *)
    apply Rplus_le_reg_r with (r := - bb).
    replace (bb - 2 * eps / (qb - q1) + - bb) with (- (2 * eps / (qb - q1)))
      by ring.
    apply Ropp_le_cancel. rewrite Ropp_involutive.
    apply Rmult_le_reg_r with (r := qb - q1); [lra|].
    replace (2 * eps / (qb - q1) * (qb - q1)) with (2 * eps) by (field; lra).
    nra.
  - assert (T := topkis_eps eps b1 ba q1 qa r1 ra Hq1 Hqa Hr1 Hra Hg1 Hga H1 Ha).
    apply Rplus_le_reg_r with (r := - ba).
    apply Rmult_le_reg_r with (r := q1 - qa); [lra|].
    replace (ba + 2 * eps / (q1 - qa) + - ba) with (2 * eps / (q1 - qa))
      by ring.
    replace (2 * eps / (q1 - qa) * (q1 - qa)) with (2 * eps) by (field; lra).
    nra.
Qed.

(** ** A worked window: (2.4, 2.6)

    The two endpoint brackets use [h = 1/1000] and enclose rho to
    1e-12, so the point brackets are tight to about 1e-9 and the
    window's width is the genuine slope variation. *)

(** f(2.399) <= 0.272615057 *)
Lemma f_hi_2399 (r : R) : 0 < r -> g (2399/1000) r = 0 ->
  fq (2399/1000) r <= 272615057/1000000000.
Proof.
  apply (f_upper_at (2399/1000)
           (1081952344384/1000000000000) (1081952344385/1000000000000));
    try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 200).
Qed.

(** f(2.4) >= 0.272427623 *)
Lemma f_lo_24 (r : R) : 0 < r -> g (24/10) r = 0 ->
  272427623/1000000000 <= fq (24/10) r.
Proof.
  apply (f_lower_at (24/10)
           (1081858270114/1000000000000) (1081858270115/1000000000000));
    try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 200).
Qed.

(** f(2.6) >= 0.237378612 *)
Lemma f_lo_26 (r : R) : 0 < r -> g (26/10) r = 0 ->
  237378612/1000000000 <= fq (26/10) r.
Proof.
  apply (f_lower_at (26/10)
           (1065329315291/1000000000000) (1065329315292/1000000000000));
    try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 200).
Qed.

(** f(2.601) <= 0.237215044 *)
Lemma f_hi_2601 (r : R) : 0 < r -> g (2601/1000) r = 0 ->
  fq (2601/1000) r <= 237215044/1000000000.
Proof.
  apply (f_upper_at (2601/1000)
           (1065256959955/1000000000000) (1065256959956/1000000000000));
    try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 200).
Qed.

(** The slope at the left endpoint, from above. *)
Lemma ba_le (ba ra : R) :
  0 < ra -> g (24/10) ra = 0 -> EminRel ba (24/10) (fq (24/10) ra) ->
  ba <= 187434/1000000.
Proof.
  intros Hra Hga Ha.
  assert (Hf1 := f_lo_24 ra Hra Hga).
  (* the [fp] side only feeds the lower bound, which is discarded here *)
  assert (Hp : forall r, 0 < r -> g (24/10 + 1/1000) r = 0 ->
               fq (24/10 + 1/1000) r <= 1).
  { intros r Hr Hg. apply (f_le_one (24/10 + 1/1000) r); [lra | exact Hr | exact Hg]. }
  assert (Hm : forall r, 0 < r -> g (24/10 - 1/1000) r = 0 ->
               fq (24/10 - 1/1000) r <= 272615057/1000000000).
  { replace (24/10 - 1/1000) with (2399/1000) by field. exact f_hi_2399. }
  destruct (beta_bracket ba (24/10) (fq (24/10) ra) (1/1000)
              1 (272615057/1000000000)
              ltac:(lra) ltac:(lra) ltac:(lra) Ha Hp Hm) as [_ Hhi].
  apply Rle_trans with (r2 := (272615057/1000000000 - fq (24/10) ra) / (1/1000));
    [exact Hhi |].
  apply Rmult_le_reg_r with (r := 1/1000); [lra|].
  replace ((272615057/1000000000 - fq (24/10) ra) / (1/1000) * (1/1000))
    with (272615057/1000000000 - fq (24/10) ra) by (field; lra).
  lra.
Qed.

(** The slope at the right endpoint, from below. *)
Lemma bb_ge (bb rb : R) :
  0 < rb -> g (26/10) rb = 0 -> EminRel bb (26/10) (fq (26/10) rb) ->
  163568/1000000 <= bb.
Proof.
  intros Hrb Hgb Hb.
  assert (Hf1 := f_lo_26 rb Hrb Hgb).
  assert (Hp : forall r, 0 < r -> g (26/10 + 1/1000) r = 0 ->
               fq (26/10 + 1/1000) r <= 237215044/1000000000).
  { replace (26/10 + 1/1000) with (2601/1000) by field. exact f_hi_2601. }
  (* the [fm] side only feeds the upper bound, which is discarded here *)
  assert (Hm : forall r, 0 < r -> g (26/10 - 1/1000) r = 0 ->
               fq (26/10 - 1/1000) r <= 1).
  { intros r Hr Hg. apply (f_le_one (26/10 - 1/1000) r); [lra | exact Hr | exact Hg]. }
  destruct (beta_bracket bb (26/10) (fq (26/10) rb) (1/1000)
              (237215044/1000000000) 1
              ltac:(lra) ltac:(lra) ltac:(lra) Hb Hp Hm) as [Hlo _].
  apply Rle_trans with (r2 := (fq (26/10) rb - 237215044/1000000000) / (1/1000));
    [| exact Hlo].
  apply Rmult_le_reg_r with (r := 1/1000); [lra|].
  replace ((fq (26/10) rb - 237215044/1000000000) / (1/1000) * (1/1000))
    with (fq (26/10) rb - 237215044/1000000000) by (field; lra).
  lra.
Qed.

(** **THE WINDOW.**  Every minimiser strictly inside (2.4, 2.6) has its
    slope in an interval of width 0.0239 — against 0.116 for the
    across-the-window bracket, and matching what the derivative gives. *)
Theorem slope_in_24_26 (q1 b1 r1 ra rb ba bb : R) :
  24/10 < q1 -> q1 < 26/10 ->
  0 < r1 -> 0 < ra -> 0 < rb ->
  g q1 r1 = 0 -> g (24/10) ra = 0 -> g (26/10) rb = 0 ->
  EminRel b1 q1 (fq q1 r1) ->
  EminRel ba (24/10) (fq (24/10) ra) ->
  EminRel bb (26/10) (fq (26/10) rb) ->
  163568/1000000 <= b1 <= 187434/1000000.
Proof.
  intros H1 H2 Hr1 Hra Hrb Hg1 Hga Hgb E1 Ea Eb.
  assert (Hw := slope_window (24/10) (26/10) q1 ba bb b1 ra rb r1
                  ltac:(lra) H1 H2 Hra Hrb Hr1 Hga Hgb Hg1 Ea Eb E1).
  assert (Hba := ba_le ba ra Hra Hga Ea).
  assert (Hbb := bb_ge bb rb Hrb Hgb Eb).
  lra.
Qed.
