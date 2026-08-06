(** * The E-branch of the profile  (Rocq + CoqInterval)

    Both zones of the one-step appendix are built on

      E(beta) = min_{q>0} ( q beta + f(q) ),    f(q) = q log2 rho_c(q),

    the Legendre transform of -f.  This file bounds it.

    The point of the file is that the two global bounds it needs are
    already theorems:

      f(q) >= 1 - q kappa*     is exactly KappaStar.kappa_upper, rewritten
                               (V q r <= KHI  is  1 - q KHI <= f),
      f(q) <= 1                is LedgerParam.g_at_top, rewritten
                               (every root is below 2^(1/q)).

    So  1 - q KHI <= f(q) <= 1  for every slope, with no new numerics.
    From that:

      beta >= kappa*   =>   q beta + f(q) >= 1 + q (beta - kappa_star) >= 1,

    and the value 1 is approached (take q small), so the E-branch sits
    *exactly* at the ceiling for beta >= kappa* — which is why the
    profile is min(E, 1) there.  That is the cap the appendix's
    S_lambda mollifies.

    E is never constructed as a function: bounds on it are stated as
    quantified inequalities over roots, as everywhere else here. *)

From Stdlib Require Import Reals Lra Ranalysis_reg Ranalysis5.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar RhoEnclose LedgerParam.
Local Open Scope R_scope.

(** ** f, bounded globally *)

(** [1 - q KHI <= f q], i.e. [kappa_upper] with the quotient cleared. *)
Theorem f_ge_global (q r : R) :
  0 < q -> 0 < r -> g q r = 0 -> 1 - q * KHI <= fq q r.
Proof.
  intros Hq Hr Hroot.
  assert (HV := kappa_upper q r Hq Hr Hroot).
  unfold V in HV. unfold fq.
  assert (Hl2 := ln2_pos).
  (* /q - ln r/ln 2 <= KHI  ==>  q (ln r/ln 2) >= 1 - q*KHI *)
  apply Rmult_le_reg_r with (r := / q); [apply Rinv_0_lt_compat; assumption|].
  replace ((1 - q * KHI) * / q) with (/ q - KHI) by (field; lra).
  replace (q * (ln r / ln 2) * / q) with (ln r / ln 2) by (field; lra).
  lra.
Qed.

(** [f q <= 1]: every root is at most [2^(1/q)], because [g] is already
    negative there ([g_at_top]). *)
Theorem f_le_one (q r : R) :
  0 < q -> 0 < r -> g q r = 0 -> fq q r <= 1.
Proof.
  intros Hq Hr Hroot.
  assert (Hle : r <= Rpower 2 (/ q)).
  { apply (root_le q r (Rpower 2 (/ q)) Hq Hr (Rpower_pos _ _) Hroot).
    left; apply g_at_top; assumption. }
  assert (Hl2 := ln2_pos).
  assert (Hlnr : ln r <= / q * ln 2).
  { rewrite <- (ln_Rpower 2 (/ q)).
    apply (ln_le_iff r (Rpower 2 (/ q))); [lra | apply Rpower_pos | exact Hle]. }
  unfold fq.
  apply Rmult_le_reg_r with (r := / q); [apply Rinv_0_lt_compat; assumption|].
  replace (q * (ln r / ln 2) * / q) with (ln r / ln 2) by (field; lra).
  replace (1 * / q) with (/ q) by ring.
  apply Rmult_le_reg_r with (r := ln 2); [lra|].
  replace (ln r / ln 2 * ln 2) with (ln r) by (field; lra).
  lra.
Qed.

(** ** The E-branch

    A lower bound on a minimum is a statement about every slope; an
    upper bound only needs one.  Both are stated over roots. *)

Definition Elb (beta L : R) : Prop :=
  forall q r, 0 < q -> 0 < r -> g q r = 0 -> L <= q * beta + fq q r.

(** **THE CEILING.**  Past kappa*, the E-branch is at least 1. *)
Theorem E_ge_one (beta : R) : KHI <= beta -> Elb beta 1.
Proof.
  intros Hb q r Hq Hr Hroot.
  assert (Hf := f_ge_global q r Hq Hr Hroot).
  (* q beta + f >= q beta + 1 - q KHI = 1 + q (beta - KHI) >= 1 *)
  nra.
Qed.

(** …and 1 is approached from above, so the bound is sharp: for any
    slack [d] there is a slope whose line is within [d] of 1. *)
Theorem E_le_one_plus (beta d : R) :
  0 < beta -> 0 < d ->
  exists q, 0 < q /\
    forall r, 0 < r -> g q r = 0 -> q * beta + fq q r <= 1 + d.
Proof.
  intros Hb Hd.
  exists (d / beta). split; [apply Rdiv_lt_0_compat; assumption|].
  intros r Hr Hroot.
  assert (Hf := f_le_one (d / beta) r (Rdiv_lt_0_compat _ _ Hd Hb) Hr Hroot).
  replace (d / beta * beta) with d by (field; lra).
  lra.
Qed.

(** Below kappa_star the ceiling bound degrades, but the same two global
    bounds still give a clean closed form with NO interval arithmetic.
    Split the family at q = 3:

      q <= 3 : q beta + f >= 1 + q(beta - KHI) >= 3 beta + (1 - 3 KHI)
      q >= 3 : q beta + f  > q beta            >= 3 beta

    and 1 - 3 KHI = 0.00477... > 0, so both branches clear 3 beta.  At
    beta = kappa_star this gives 0.9952 against the true 1 -- half a
    percent, for a bound that costs nothing. *)

Lemma f_pos (q r : R) : 0 < q -> 0 < r -> g q r = 0 -> 0 < fq q r.
Proof.
  intros Hq Hr Hroot.
  assert (H1 : 1 < r) by (apply (root_gt_1 q r); assumption).
  unfold fq.
  assert (0 < ln r) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (Hl2 := ln2_pos).
  apply Rmult_lt_0_compat; [lra | apply Rdiv_lt_0_compat; lra].
Qed.

Theorem E_lower_ratio (beta : R) :
  0 < beta -> beta <= KHI -> Elb beta (3 * beta).
Proof.
  intros Hb Hbk q r Hq Hr Hroot.
  assert (H3K : 3 * KHI <= 1) by lra.
  destruct (Rle_or_lt q 3) as [Hs|Hs].
  - assert (Hf := f_ge_global q r Hq Hr Hroot). nra.
  - assert (Hf := f_pos q r Hq Hr Hroot). nra.
Qed.

(** A worked value: at beta = 1/4 the E-branch is at least 3/4. *)
Corollary E_at_quarter : Elb (1/4) (3/4).
Proof.
  intros q r Hq Hr Hroot.
  assert (H := E_lower_ratio (1/4) ltac:(lra) ltac:(lra) q r Hq Hr Hroot).
  lra.
Qed.
