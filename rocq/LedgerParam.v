(** * beta without a derivative  (Rocq + CoqInterval)

    Lemma A's ledger is built at a point where the E-branch slope is q1,
    and beta is tied to q1 by the tangency  f'(q1) = eps - beta.  That
    equation is the ONLY place a derivative enters the appendix, and
    formalising it would need the implicit function theorem for rho_c.

    It is avoidable.  The tangency is a *consequence* of a
    derivative-free fact: E is the lower envelope of the lines
    q |-> q b + f(q), so q1 minimises that family at b = beta - eps.
    Minimality alone brackets b by DIFFERENCE QUOTIENTS of f:

      q = q1 + h :  q1 b + f(q1) <= (q1+h) b + f(q1+h)
                    =>  b >= (f(q1) - f(q1+h)) / h
      q = q1 - h :  q1 b + f(q1) <= (q1-h) b + f(q1-h)
                    =>  b <= (f(q1-h) - f(q1)) / h

    and both endpoints are *values* of f, which RhoEnclose already
    encloses.  The bracket narrows like |f''| h, so h is a knob traded
    against the ledger's margin — no differentiability needed anywhere.

    This file proves that bracket, plus the general root existence the
    statement needs (KappaStar only produced a root at one slope). *)

From Stdlib Require Import Reals Lra Ranalysis_reg Ranalysis5.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar RhoEnclose.
Local Open Scope R_scope.

(** ** Root existence at every slope

    g q 1 = 2^(-q) > 0  and  g q (2^(1/q)) < 0, so IVT applies on
    [1, 2^(1/q)]. *)

Lemma g_at_1 (q : R) : g q 1 = Rpower 2 (-q).
Proof.
  unfold g. rewrite Rpower_base_1. replace (1 + 1) with 2 by ring. ring.
Qed.

Lemma g_at_top (q : R) : 0 < q -> g q (Rpower 2 (/ q)) < 0.
Proof.
  intros Hq.
  set (T := Rpower 2 (/ q)).
  assert (HT : 0 < T) by apply Rpower_pos.
  assert (E1 : Rpower T (-q) = / 2).
  { unfold T. rewrite Rpower_Rpower.
    replace (/ q * - q) with (-(1)) by (field; lra).
    unfold Rpower. replace (- (1) * ln 2) with (- ln 2) by ring.
    rewrite exp_Ropp, exp_ln by lra. reflexivity. }
  assert (E2 : Rpower (1 + T) (-q) < Rpower T (-q))
    by (apply Rpower_neg_decr; lra).
  unfold g. rewrite E1 in *. lra.
Qed.

Lemma one_lt_top (q : R) : 0 < q -> 1 < Rpower 2 (/ q).
Proof.
  intros Hq.
  assert (Hinv : 0 < / q) by (apply Rinv_0_lt_compat; assumption).
  assert (H : Rpower 2 0 < Rpower 2 (/ q)).
  { unfold Rpower. apply exp_increasing.
    assert (0 < ln 2) by apply ln2_pos. nra. }
  rewrite Rpower_O in H by lra. exact H.
Qed.

(** **THE ROOT EXISTS AT EVERY SLOPE.** *)
Theorem root_exists (q : R) : 0 < q -> exists r, 1 < r /\ g q r = 0.
Proof.
  intros Hq.
  destruct (IVT_interv (fun r => - g q r) 1 (Rpower 2 (/ q))) as [r [Hr Hval]].
  - intros a Ha. apply continuity_pt_opp. apply g_continuous.
    assert (1 < Rpower 2 (/ q)) by (apply one_lt_top; assumption). lra.
  - apply one_lt_top; assumption.
  - assert (H := g_at_1 q). assert (0 < Rpower 2 (-q)) by apply Rpower_pos. lra.
  - assert (H := g_at_top q Hq). lra.
  - assert (Hroot : g q r = 0) by lra.
    (* the root is > 1 because g q 1 > 0 *)
    exists r. split; [| exact Hroot].
    apply (root_gt_1 q r Hq); [| exact Hroot].
    assert (1 < Rpower 2 (/ q)) by (apply one_lt_top; assumption). lra.
Qed.

(** ** Minimality of the E-branch slope, as a relation

    Stated over roots rather than over a constructed [rho_c]: [f1] is the
    value of [f] at [q1], and the hypothesis says the line through it is
    the lowest of the family at [b]. *)

Definition EminRel (b q1 f1 : R) : Prop :=
  forall q r, 0 < q -> 0 < r -> g q r = 0 -> q1 * b + f1 <= q * b + fq q r.

(** **THE BRACKET.**  Minimality alone, no derivative. *)
Theorem beta_bracket (b q1 f1 h fp fm : R) :
  0 < q1 -> 0 < h -> h < q1 -> EminRel b q1 f1 ->
  (forall r, 0 < r -> g (q1 + h) r = 0 -> fq (q1 + h) r <= fp) ->
  (forall r, 0 < r -> g (q1 - h) r = 0 -> fq (q1 - h) r <= fm) ->
  (f1 - fp) / h <= b <= (fm - f1) / h.
Proof.
  intros Hq1 Hh Hhq Hmin Hp Hm.
  destruct (root_exists (q1 + h) ltac:(lra)) as [rp [Hrp1 Hrp]].
  destruct (root_exists (q1 - h) ltac:(lra)) as [rm [Hrm1 Hrm]].
  assert (Hfp : fq (q1 + h) rp <= fp) by (apply Hp; [lra | exact Hrp]).
  assert (Hfm : fq (q1 - h) rm <= fm) by (apply Hm; [lra | exact Hrm]).
  assert (Hup := Hmin (q1 + h) rp ltac:(lra) ltac:(lra) Hrp).
  assert (Hdn := Hmin (q1 - h) rm ltac:(lra) ltac:(lra) Hrm).
  split.
  - (* h b >= f1 - f(q1+h) >= f1 - fp *)
    apply Rmult_le_reg_r with (r := h); [lra|].
    replace ((f1 - fp) / h * h) with (f1 - fp) by (field; lra).
    lra.
  - (* h b <= f(q1-h) - f1 <= fm - f1 *)
    apply Rmult_le_reg_r with (r := h); [lra|].
    replace ((fm - f1) / h * h) with (fm - f1) by (field; lra).
    lra.
Qed.

(** ** eps-MINIMALITY: the same hypothesis, weakened until it is free

    [EminRel] asks q1 to minimise the family EXACTLY.  Nothing in this
    development produces such a q1, and producing one is not cheap: an
    exact minimiser needs compactness of the range plus continuity of
    rho_c, so every theorem carrying [EminRel] was conditional on a
    hypothesis nobody had shown to be satisfiable at all.

    An eps-MINIMISER, by contrast, exists for ANY family bounded below,
    straight from the definition of an infimum -- no compactness, no
    continuity, no derivative.  [EminExists.emin_eps_exists] proves it.

    Everything downstream degrades only LINEARLY in eps:
      - the bracket below loosens by eps/h on each side;
      - [SlopeWindow.topkis_eps] becomes (q1-q2)(b1-b2) <= 2 eps;
      - the node-to-window transport ([CoverGlue.slope_hi_eps]) loosens
        by 2 eps/h, UNIFORMLY -- no division by the window width. *)

Definition EminEps (eps b q1 f1 : R) : Prop :=
  forall q r, 0 < q -> 0 < r -> g q r = 0 -> q1 * b + f1 <= q * b + fq q r + eps.

(** Exact minimality is the eps = 0 case, in both directions. *)

Lemma EminRel_eps (eps b q1 f1 : R) :
  0 <= eps -> EminRel b q1 f1 -> EminEps eps b q1 f1.
Proof. intros He H q r Hq Hr Hg. specialize (H q r Hq Hr Hg). lra. Qed.

Lemma EminEps_exact (b q1 f1 : R) : EminEps 0 b q1 f1 -> EminRel b q1 f1.
Proof. intros H q r Hq Hr Hg. specialize (H q r Hq Hr Hg). lra. Qed.

Lemma EminEps_mono (e1 e2 b q1 f1 : R) :
  e1 <= e2 -> EminEps e1 b q1 f1 -> EminEps e2 b q1 f1.
Proof. intros He H q r Hq Hr Hg. specialize (H q r Hq Hr Hg). lra. Qed.

(** **THE BRACKET, eps-VERSION.**  Each side loses exactly [eps/h]. *)
Theorem beta_bracket_eps (eps b q1 f1 h fp fm : R) :
  0 < q1 -> 0 < h -> h < q1 -> 0 <= eps -> EminEps eps b q1 f1 ->
  (forall r, 0 < r -> g (q1 + h) r = 0 -> fq (q1 + h) r <= fp) ->
  (forall r, 0 < r -> g (q1 - h) r = 0 -> fq (q1 - h) r <= fm) ->
  (f1 - fp - eps) / h <= b <= (fm - f1 + eps) / h.
Proof.
  intros Hq1 Hh Hhq Heps Hmin Hp Hm.
  destruct (root_exists (q1 + h) ltac:(lra)) as [rp [Hrp1 Hrp]].
  destruct (root_exists (q1 - h) ltac:(lra)) as [rm [Hrm1 Hrm]].
  assert (Hfp : fq (q1 + h) rp <= fp) by (apply Hp; [lra | exact Hrp]).
  assert (Hfm : fq (q1 - h) rm <= fm) by (apply Hm; [lra | exact Hrm]).
  assert (Hup := Hmin (q1 + h) rp ltac:(lra) ltac:(lra) Hrp).
  assert (Hdn := Hmin (q1 - h) rm ltac:(lra) ltac:(lra) Hrm).
  split.
  - apply Rmult_le_reg_r with (r := h); [lra|].
    replace ((f1 - fp - eps) / h * h) with (f1 - fp - eps) by (field; lra).
    lra.
  - apply Rmult_le_reg_r with (r := h); [lra|].
    replace ((fm - f1 + eps) / h * h) with (fm - f1 + eps) by (field; lra).
    lra.
Qed.

(** ** A worked bracket

    At q1 = 3/2 with h = 1/100 the three values of f involved are pinned
    by the RhoEnclose layer, and the bracket follows.  The true value is
    beta - eps = -f'(3/2) = 0.33476895…, and the bracket below is
    [0.33361, 0.33601] — obtained without ever differentiating. *)

Lemma f_upper_at (q a b hi : R) :
  0 < q -> 1 < a -> a <= b -> 0 <= g q a -> g q b <= 0 ->
  (forall y, a <= y <= b -> fq q y <= hi) ->
  forall r, 0 < r -> g q r = 0 -> fq q r <= hi.
Proof.
  intros Hq Ha Hab Hsa Hsb Hnum r Hr Hroot.
  apply Hnum.
  exact (rho_in q q a b Hq (Rle_refl q) Ha Hab Hsa Hsb q r
           (conj (Rle_refl q) (Rle_refl q)) Hr Hroot).
Qed.

Lemma f_lower_at (q a b lo : R) :
  0 < q -> 1 < a -> a <= b -> 0 <= g q a -> g q b <= 0 ->
  (forall y, a <= y <= b -> lo <= fq q y) ->
  forall r, 0 < r -> g q r = 0 -> lo <= fq q r.
Proof.
  intros Hq Ha Hab Hsa Hsb Hnum r Hr Hroot.
  apply Hnum.
  exact (rho_in q q a b Hq (Rle_refl q) Ha Hab Hsa Hsb q r
           (conj (Rle_refl q) (Rle_refl q)) Hr Hroot).
Qed.

Corollary bracket_at_1_5 (b r1 : R) :
  0 < r1 -> g (3/2) r1 = 0 -> EminRel b (3/2) (fq (3/2) r1) ->
  33361/100000 <= b <= 33601/100000.
Proof.
  intros Hr1 Hroot1 Hmin.
  (* f(3/2) >= 0.5024083 *)
  assert (Hf1 : 5024083/10000000 <= fq (3/2) r1).
  { apply (f_lower_at (3/2) (1261324/1000000) (1261325/1000000));
      try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 90). }
  (* f(1.51) <= 0.4990722 *)
  assert (Hp : forall r, 0 < r -> g (3/2 + 1/100) r = 0 ->
               fq (3/2 + 1/100) r <= 4990722/10000000).
  { apply (f_upper_at (3/2 + 1/100) (1257458/1000000) (1257459/1000000));
      try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 90). }
  (* f(1.49) <= 0.5057684 *)
  assert (Hm : forall r, 0 < r -> g (3/2 - 1/100) r = 0 ->
               fq (3/2 - 1/100) r <= 5057684/10000000).
  { apply (f_upper_at (3/2 - 1/100) (1265266/1000000) (1265267/1000000));
      try lra; unfold g, fq; try (intros y Hy); interval with (i_prec 90). }
  destruct (beta_bracket b (3/2) (fq (3/2) r1) (1/100)
              (4990722/10000000) (5057684/10000000)
              ltac:(lra) ltac:(lra) ltac:(lra) Hmin Hp Hm) as [Hlo Hhi].
  split.
  - apply Rle_trans with (r2 := (fq (3/2) r1 - 4990722/10000000) / (1/100));
      [lra | exact Hlo].
  - apply Rle_trans with (r2 := (5057684/10000000 - fq (3/2) r1) / (1/100));
      [exact Hhi | lra].
Qed.
