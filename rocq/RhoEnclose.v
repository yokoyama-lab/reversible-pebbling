(** * Enclosing rho_c over an interval of q  (Rocq + CoqInterval)

    KappaStar.v needed rho_c only through a sign test, so it never had to
    say what rho_c(q) *is*.  Zone I of the one-step appendix does need
    values: its ledger is built from f(q) = q log2 rho_c(q) at three
    slopes.  This file supplies the missing piece —

      q in [qlo,qhi]  and  g q r = 0   =>   a <= r <= b,

    certified by two sign tests that the interval tactic discharges.

    The mechanism is that g is antitone in BOTH arguments.  In rho that
    is KappaStar.g_decr; in q it holds as soon as r > 1 (both bases of
    the powers exceed 1), and every root does exceed 1
    (KappaStar.root_gt_1).  So

      q <= qhi  ->  g qhi a <= g q a,    and  0 <= g qhi a  gives a <= r,
      qlo <= q  ->  g q b  <= g qlo b,   and  g qlo b <= 0  gives r <= b.

    No interval Newton, no Krawczyk: monotonicity in q replaces them, and
    the only numeric facts needed are the signs of g at the four corners.

    NOTE ON SCOPE.  This is the value layer.  The ledger of Lemma A also
    uses f'(q), whose closed form comes from the implicit function
    theorem; formalising that derivative is separate work and is NOT
    done here. *)

From Stdlib Require Import Reals Lra Ranalysis_reg Ranalysis5.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar.
Local Open Scope R_scope.

(** ** g is antitone in q, above 1 *)

Lemma exp_le_mono (x y : R) : x <= y -> exp x <= exp y.
Proof.
  intro H. destruct (Rle_lt_or_eq_dec _ _ H) as [Hlt|Heq].
  - left; apply exp_increasing; assumption.
  - right; f_equal; assumption.
Qed.

Lemma Rpower_antitone_q (r q1 q2 : R) :
  1 < r -> q1 <= q2 -> Rpower r (-q2) <= Rpower r (-q1).
Proof.
  intros Hr Hq. unfold Rpower. apply exp_le_mono.
  assert (0 < ln r) by (rewrite <- ln_1; apply ln_increasing; lra).
  nra.
Qed.

Lemma g_antitone_q (r q1 q2 : R) :
  1 < r -> q1 <= q2 -> g q2 r <= g q1 r.
Proof.
  intros Hr Hq. unfold g.
  assert (Rpower r (-q2) <= Rpower r (-q1)) by (apply Rpower_antitone_q; lra).
  assert (Rpower (1 + r) (-q2) <= Rpower (1 + r) (-q1))
    by (apply Rpower_antitone_q; lra).
  lra.
Qed.

(** ** THE ENCLOSURE

    Two sign tests at the corners pin every root on the whole q-window. *)

Theorem rho_in (qlo qhi a b : R) :
  0 < qlo -> qlo <= qhi -> 1 < a -> a <= b ->
  0 <= g qhi a -> g qlo b <= 0 ->
  forall q r, qlo <= q <= qhi -> 0 < r -> g q r = 0 -> a <= r <= b.
Proof.
  intros Hqlo Hq Ha Hab Hsa Hsb q r [Hq1 Hq2] Hr Hroot.
  assert (Hqpos : 0 < q) by lra.
  split.
  - (* a <= r *)
    apply (root_ge q r a Hqpos Hr ltac:(lra) Hroot).
    apply Rle_trans with (r2 := g qhi a); [exact Hsa|].
    apply g_antitone_q; lra.
  - (* r <= b *)
    apply (root_le q r b Hqpos Hr ltac:(lra) Hroot).
    apply Rle_trans with (r2 := g qlo b); [| exact Hsb].
    apply g_antitone_q; lra.
Qed.

(** ** Worked instances

    Each is two `interval` calls on concrete numbers. *)

(** The window that contains q* = 1.51538…  *)
Corollary rho_window_qstar (q r : R) :
  15/10 <= q <= 153/100 -> 0 < r -> g q r = 0 ->
  1249/1000 <= r <= 1262/1000.
Proof.
  apply rho_in; try lra; unfold g.
  - interval with (i_prec 60).
  - interval with (i_prec 60).
Qed.

(** The whole slope range Zone I sweeps. *)
Corollary rho_window_zoneI (q r : R) :
  35/100 <= q <= 32/10 -> 0 < r -> g q r = 0 ->
  1034/1000 <= r <= 677/100.
Proof.
  apply rho_in; try lra; unfold g.
  - interval with (i_prec 90).
  - interval with (i_prec 90).
Qed.

(** ** f(q) = q log2 rho_c(q), enclosed *)

Definition fq (q r : R) : R := q * (ln r / ln 2).

Theorem f_in (qlo qhi a b lo hi : R) :
  0 < qlo -> qlo <= qhi -> 1 < a -> a <= b ->
  0 <= g qhi a -> g qlo b <= 0 ->
  (forall x y, qlo <= x <= qhi -> a <= y <= b -> lo <= fq x y <= hi) ->
  forall q r, qlo <= q <= qhi -> 0 < r -> g q r = 0 -> lo <= fq q r <= hi.
Proof.
  intros Hqlo Hq Ha Hab Hsa Hsb Hnum q r Hqr Hr Hroot.
  apply Hnum; [exact Hqr|].
  exact (rho_in qlo qhi a b Hqlo Hq Ha Hab Hsa Hsb q r Hqr Hr Hroot).
Qed.

(** On the q* window, `f` is pinned to three decimals — enough to see the
    layer works; a Zone I proof would slice the range far more finely. *)
Corollary f_window_qstar (q r : R) :
  15/10 <= q <= 153/100 -> 0 < r -> g q r = 0 ->
  481/1000 <= fq q r <= 515/1000.
Proof.
  apply (f_in (15/10) (153/100) (1249/1000) (1262/1000)); try lra; unfold g, fq.
  - interval with (i_prec 60).
  - interval with (i_prec 60).
  - intros x y Hx Hy. split; interval with (i_prec 60).
Qed.

(** ** A closed-form anchor: rho_c(1) is the golden ratio

    g 1 r = 1/r + 1/(1+r) - 1, which vanishes exactly at r^2 = r + 1.
    Useful as a check that `g` is the intended equation. *)

Lemma Rpower_neg_one (x y : R) : 0 < x -> y = 1 -> Rpower x (- y) = / x.
Proof.
  intros Hx ->. unfold Rpower.
  replace (- (1) * ln x) with (- ln x) by ring.
  rewrite exp_Ropp, exp_ln by lra. reflexivity.
Qed.

Theorem rho_c_at_1 (r : R) : 0 < r -> g 1 r = 0 -> r * r = r + 1.
Proof.
  intros Hr Hroot. unfold g in Hroot.
  rewrite (Rpower_neg_one r 1 Hr eq_refl) in Hroot.
  rewrite (Rpower_neg_one (1 + r) 1 ltac:(lra) eq_refl) in Hroot.
  assert (Hr0 : r <> 0) by lra.
  assert (Hr1 : 1 + r <> 0) by lra.
  assert (H : / r + / (1 + r) = 1) by lra.
  field_simplify_eq in H; [nra | lra].
Qed.
