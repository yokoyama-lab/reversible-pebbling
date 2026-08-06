(** * kappa_star, enclosed inside the prover (Rocq + CoqInterval)

    kappa_star = sup over q > 0 of  V q = 1/q - log2 (rho_c q),
    where rho_c q is the unique root of

      g q rho = rho^(-q) + (1+rho)^(-q) - 1 = 0.

    The published growth-rate value  c = 2^(1 + kappa_star)
    = 2.5170648368938161...  rests on an Arb computation (602 Krawczyk
    boxes) run outside any prover.  This file replaces that by a
    machine-checked enclosure.

    rho_c is never constructed as a function: every statement quantifies
    over an arbitrary root, and the existence needed for the lower bound
    comes from the intermediate value theorem.

    KEY REDUCTION.  g q . is strictly decreasing, so

      V q r <= K   iff   r >= 2^(1/q - K)   iff   0 <= g q (2^(1/q - K)),

    and g at that test point has the closed form

      2^(q K - 1) * (1 + (1 + 2^(K - 1/q))^(-q)) - 1,

    an explicit one-variable expression.  On 2/5 <= q <= 302/100 the
    interval tactic settles it; the two tails are elementary. *)

From Stdlib Require Import Reals Lra Ranalysis_reg Ranalysis5.
From Interval Require Import Tactic.
Local Open Scope R_scope.

Definition g (q r : R) : R := Rpower r (-q) + Rpower (1 + r) (-q) - 1.

Definition V (q r : R) : R := / q - ln r / ln 2.

(** kappa_star is pinned between these; Q0 is the witness slope. *)
Notation KLO := (3317423792563105 / 10000000000000000).
Notation KHI := (3317423792563106 / 10000000000000000).
Notation Q0  := (15153832361072514 / 10000000000000000).

(** ** Elementary facts about Rpower *)

Lemma Rpower_pos (x y : R) : 0 < Rpower x y.
Proof. unfold Rpower; apply exp_pos. Qed.

Lemma ln_Rpower (x y : R) : ln (Rpower x y) = y * ln x.
Proof. unfold Rpower; apply ln_exp. Qed.

Lemma Rpower_inv (x y : R) : / Rpower x y = Rpower x (- y).
Proof.
  unfold Rpower. rewrite <- exp_Ropp. f_equal. ring.
Qed.

Lemma Rpower_mult_distr (x y z : R) :
  0 < x -> 0 < y -> Rpower (x * y) z = Rpower x z * Rpower y z.
Proof.
  intros Hx Hy. unfold Rpower.
  rewrite ln_mult by assumption.
  rewrite Rmult_plus_distr_l, exp_plus. reflexivity.
Qed.

Lemma Rpower_Rpower (x y z : R) : Rpower (Rpower x y) z = Rpower x (y * z).
Proof.
  unfold Rpower. rewrite ln_exp. f_equal. ring.
Qed.

Lemma Rpower_base_1 (y : R) : Rpower 1 y = 1.
Proof. unfold Rpower. rewrite ln_1, Rmult_0_r. apply exp_0. Qed.

Lemma ln_le_iff (x y : R) : 0 < x -> 0 < y -> (ln x <= ln y <-> x <= y).
Proof.
  intros Hx Hy. split; intro H.
  - destruct (Rle_or_lt x y) as [|Hlt]; [assumption|].
    assert (ln y < ln x) by (apply ln_increasing; lra). lra.
  - destruct (Rle_lt_or_eq_dec _ _ H) as [Hlt|Heq].
    + left; apply ln_increasing; assumption.
    + right; f_equal; assumption.
Qed.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

(** 1 + x <= exp x, both signs. *)
Lemma exp_lb (x : R) : 1 + x <= exp x.
Proof.
  destruct (Req_dec x 0) as [->|Hne].
  - rewrite exp_0; lra.
  - left; apply exp_ineq1; assumption.
Qed.

(** ** Monotonicity of g in its second argument *)

Lemma Rpower_neg_decr (q x y : R) :
  0 < q -> 0 < x -> x < y -> Rpower y (-q) < Rpower x (-q).
Proof.
  intros Hq Hx Hxy. unfold Rpower. apply exp_increasing.
  assert (ln x < ln y) by (apply ln_increasing; lra). nra.
Qed.

Lemma g_decr (q x y : R) : 0 < q -> 0 < x -> x < y -> g q y < g q x.
Proof.
  intros Hq Hx Hxy. unfold g.
  assert (Rpower y (-q) < Rpower x (-q)) by (apply Rpower_neg_decr; lra).
  assert (Rpower (1 + y) (-q) < Rpower (1 + x) (-q))
    by (apply Rpower_neg_decr; lra).
  lra.
Qed.

(** ** The reduction *)

Lemma root_ge (q r T : R) :
  0 < q -> 0 < r -> 0 < T -> g q r = 0 -> 0 <= g q T -> T <= r.
Proof.
  intros Hq Hr HT Hroot Hsign.
  destruct (Rle_or_lt T r) as [|Hlt]; [assumption|].
  assert (g q T < g q r) by (apply g_decr; lra). lra.
Qed.

Lemma root_le (q r T : R) :
  0 < q -> 0 < r -> 0 < T -> g q r = 0 -> g q T <= 0 -> r <= T.
Proof.
  intros Hq Hr HT Hroot Hsign.
  destruct (Rle_or_lt r T) as [|Hlt]; [assumption|].
  assert (g q r < g q T) by (apply g_decr; lra). lra.
Qed.

Lemma V_le_iff (q r K : R) :
  0 < q -> 0 < r -> (V q r <= K <-> Rpower 2 (/ q - K) <= r).
Proof.
  intros Hq Hr. unfold V.
  assert (Hl2 := ln2_pos).
  assert (Hstep : (/ q - ln r / ln 2 <= K) <-> ((/ q - K) * ln 2 <= ln r)).
  { split; intro H.
    - apply Rmult_le_reg_r with (r := / ln 2).
      + apply Rinv_0_lt_compat; assumption.
      + replace ((/ q - K) * ln 2 * / ln 2) with (/ q - K) by (field; lra).
        replace (ln r * / ln 2) with (ln r / ln 2) by (field; lra). lra.
    - assert (H' : / q - K <= ln r / ln 2).
      { apply Rmult_le_reg_r with (r := ln 2); [lra|].
        replace (ln r / ln 2 * ln 2) with (ln r) by (field; lra). lra. }
      lra. }
  rewrite Hstep.
  rewrite <- (ln_Rpower 2 (/ q - K)).
  apply ln_le_iff; [apply Rpower_pos | assumption].
Qed.

(** ** Closed form of g at the test point *)

Lemma g_test (q K : R) :
  0 < q ->
  g q (Rpower 2 (/ q - K))
  = Rpower 2 (q * K - 1) * (1 + Rpower (1 + Rpower 2 (K - / q)) (-q)) - 1.
Proof.
  intros Hq.
  assert (Hq0 : q <> 0) by lra.
  set (T := Rpower 2 (/ q - K)).
  assert (HT : 0 < T) by apply Rpower_pos.
  assert (E1 : Rpower T (-q) = Rpower 2 (q * K - 1)).
  { unfold T. rewrite Rpower_Rpower. f_equal. field; assumption. }
  assert (Hinv : / T = Rpower 2 (K - / q)).
  { unfold T. rewrite Rpower_inv. f_equal. ring. }
  assert (Hepos : 0 < Rpower 2 (K - / q)) by apply Rpower_pos.
  assert (E2 : 1 + T = T * (1 + Rpower 2 (K - / q))).
  { rewrite <- Hinv. field. lra. }
  unfold g. fold T. rewrite E2, Rpower_mult_distr by lra.
  rewrite E1. ring.
Qed.

(** ** The middle range: interval arithmetic *)

Lemma core_mid (q : R) :
  2/5 <= q <= 302/100 ->
  1 <= Rpower 2 (q * KHI - 1) * (1 + Rpower (1 + Rpower 2 (KHI - / q)) (-q)).
Proof.
  intros H.
  interval with (i_bisect q, i_taylor q, i_prec 200, i_depth 80).
Qed.

(** ** The small-q tail: elementary

    With e = 2^(K - 1/q) <= 2^(K - 5/2), the two inequalities
    (1+e)^(-q) >= 1 - q e  and  2^(qK) >= 1 + q K ln 2  suffice. *)

(** The arithmetic core of the tail, with every constant abstracted so
    that [nra] sees only small coefficients. *)
Lemma tail_arith (q e K L : R) :
  0 < q -> q <= 2/5 -> 0 < e -> e <= 223/1000 ->
  33/100 <= K -> K <= 34/100 -> 69/100 <= L -> L <= 70/100 ->
  2 <= (1 + q * K * L) * (2 - q * e).
Proof.
  intros Hq0 Hq1 He0 He1 HK0 HK1 HL0 HL1.
  assert (HKp : 0 < K) by lra.
  assert (HLp : 0 < L) by lra.
  assert (Ha : q * K <= 68/500) by nra.
  assert (Hap : 0 <= q * K) by nra.
  assert (Hb : q * K * L <= 1/10) by nra.
  assert (Hbp : 0 <= q * K * L) by nra.
  assert (H1 : e * (1 + q * K * L) <= 223/1000 * (11/10)) by nra.
  assert (HKL : 33/100 * (69/100) <= K * L) by nra.
  assert (H2 : 223/1000 * (11/10) <= 2 * (K * L)) by lra.
  assert (H3 : e * (1 + q * K * L) <= 2 * (K * L)) by lra.
  assert (H4 : q * (e * (1 + q * K * L)) <= q * (2 * (K * L))) by nra.
  assert (Hexp : (1 + q * K * L) * (2 - q * e)
                 = 2 * (1 + q * K * L) - q * (e * (1 + q * K * L))) by ring.
  nra.
Qed.

Lemma tail_low (q : R) :
  0 < q <= 2/5 ->
  1 <= Rpower 2 (q * KHI - 1) * (1 + Rpower (1 + Rpower 2 (KHI - / q)) (-q)).
Proof.
  intros [Hq0 Hq1].
  set (e := Rpower 2 (KHI - / q)).
  assert (Hepos : 0 < e) by apply Rpower_pos.
  (* e is small: 1/q >= 5/2 *)
  assert (Hinvq : 5/2 <= / q).
  { apply Rmult_le_reg_r with (r := q); [lra|].
    rewrite Rinv_l by lra. lra. }
  assert (He : e <= Rpower 2 (KHI - 5/2)).
  { unfold e. unfold Rpower. destruct (Req_dec (/ q) (5/2)) as [->|Hne].
    - right; reflexivity.
    - left; apply exp_increasing.
      assert (0 < ln 2) by apply ln2_pos. nra. }
  assert (He' : e <= 223/1000).
  { eapply Rle_trans; [exact He|]. interval with (i_prec 60). }
  (* (1+e)^(-q) >= 1 - q e *)
  assert (Hln : ln (1 + e) <= e).
  { assert (Hp1 : 0 < 1 + e) by lra.
    assert (Hp2 : 0 < exp e) by apply exp_pos.
    assert (H1 : 1 + e <= exp e) by apply exp_lb.
    assert (H2 : ln (1 + e) <= ln (exp e))
      by (apply (ln_le_iff _ _ Hp1 Hp2); exact H1).
    rewrite ln_exp in H2. exact H2. }
  assert (Hpow : 1 - q * e <= Rpower (1 + e) (-q)).
  { unfold Rpower.
    eapply Rle_trans; [| apply exp_lb].
    assert (- q * ln (1 + e) >= - q * e) by nra. lra. }
  (* 2^(qK) >= 1 + q K ln 2 *)
  assert (Hexp : 1 + q * KHI * ln 2 <= Rpower 2 (q * KHI)).
  { unfold Rpower. eapply Rle_trans; [| apply exp_lb]. lra. }
  (* assemble *)
  assert (Hsplit : Rpower 2 (q * KHI - 1) = Rpower 2 (q * KHI) * / 2).
  { replace (q * KHI - 1) with (q * KHI + (-1)) by ring.
    rewrite Rpower_plus. f_equal.
    unfold Rpower. replace (-1 * ln 2) with (- ln 2) by ring.
    rewrite exp_Ropp, exp_ln by lra. reflexivity. }
  rewrite Hsplit.
  assert (Hkey : 2 <= Rpower 2 (q * KHI) * (1 + Rpower (1 + e) (-q))).
  { assert (Hpos2 : 0 < Rpower 2 (q * KHI)) by apply Rpower_pos.
    assert (H1 : Rpower 2 (q * KHI) * (1 + (1 - q * e))
                 <= Rpower 2 (q * KHI) * (1 + Rpower (1 + e) (-q)))
      by (apply Rmult_le_compat_l; lra).
    eapply Rle_trans; [| exact H1].
    assert (H2 : (1 + q * KHI * ln 2) * (2 - q * e)
                 <= Rpower 2 (q * KHI) * (2 - q * e)).
    { apply Rmult_le_compat_r; [nra | exact Hexp]. }
    replace (1 + (1 - q * e)) with (2 - q * e) by ring.
    eapply Rle_trans; [| exact H2].
    apply tail_arith; try lra; try (split; interval).
    - interval.
    - interval. }
  lra.
Qed.

(** ** The large-q tail: every root exceeds 1 *)

Lemma root_gt_1 (q r : R) : 0 < q -> 0 < r -> g q r = 0 -> 1 < r.
Proof.
  intros Hq Hr Hroot.
  assert (Hg1 : g q 1 = Rpower 2 (-q)).
  { unfold g. rewrite Rpower_base_1. replace (1 + 1) with 2 by ring. ring. }
  assert (0 < Rpower 2 (-q)) by apply Rpower_pos.
  destruct (Rle_or_lt r 1) as [Hle|]; [|assumption].
  destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt|Heq].
  - assert (g q 1 < g q r) by (apply g_decr; lra). lra.
  - rewrite Heq in Hroot. lra.
Qed.

(** ** THE UPPER BOUND *)

Theorem kappa_upper (q r : R) :
  0 < q -> 0 < r -> g q r = 0 -> V q r <= KHI.
Proof.
  intros Hq Hr Hroot.
  destruct (Rle_or_lt q (302/100)) as [Hsmall|Hbig].
  - (* the test point is admissible *)
    assert (Hcore : 1 <= Rpower 2 (q * KHI - 1)
                         * (1 + Rpower (1 + Rpower 2 (KHI - / q)) (-q))).
    { destruct (Rle_or_lt q (2/5)) as [|Hmid].
      - apply tail_low; lra.
      - apply core_mid; lra. }
    assert (Hg : 0 <= g q (Rpower 2 (/ q - KHI)))
      by (rewrite g_test by lra; lra).
    apply (V_le_iff q r KHI Hq Hr).
    apply (root_ge q r _ Hq Hr (Rpower_pos _ _) Hroot Hg).
  - (* V q r < 1/q <= 100/302 < KHI *)
    assert (H1 : 1 < r) by (apply (root_gt_1 q r); assumption).
    assert (Hlr : 0 < ln r) by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hl2 := ln2_pos).
    assert (Hdiv : 0 < ln r / ln 2)
      by (apply Rdiv_lt_0_compat; assumption).
    assert (Hinv : / q < 100/302).
    { apply Rmult_lt_reg_r with (r := q); [lra|].
      rewrite Rinv_l by lra. lra. }
    unfold V. lra.
Qed.

(** ** THE LOWER BOUND

    A root at the witness slope Q0 exists by the intermediate value
    theorem, and the sign test at 2^(1/Q0 - KLO) places it low enough. *)

Lemma ln_cont (x : R) : 0 < x -> continuity_pt ln x.
Proof.
  intros Hx. apply derivable_continuous_pt. exists (/ x).
  apply derivable_pt_lim_ln; assumption.
Qed.

Lemma g_continuous (q : R) :
  forall r, 0 < r -> continuity_pt (g q) r.
Proof.
  intros r Hr. unfold g, Rpower.
  reg; try (apply Rgt_not_eq; lra); try lra; apply ln_cont; lra.
Qed.

Theorem kappa_lower :
  exists r : R, 0 < r /\ g Q0 r = 0 /\ KLO <= V Q0 r.
Proof.
  assert (Hq : 0 < Q0) by lra.
  (* g Q0 1 > 0 and g Q0 4 < 0 *)
  assert (Hlo : 0 < g Q0 1).
  { unfold g. rewrite Rpower_base_1. replace (1 + 1) with 2 by ring.
    assert (Rpower 2 (- Q0) > 0) by apply Rpower_pos. lra. }
  assert (Hhi : g Q0 4 < 0).
  { unfold g. replace (1 + 4) with 5 by ring.
    interval with (i_prec 60). }
  (* IVT on [1,4] *)
  destruct (IVT_interv (fun r => - g Q0 r) 1 4) as [r [Hr Hval]].
  - intros a Ha. apply continuity_pt_opp. apply g_continuous. lra.
  - lra.
  - lra.
  - lra.
  - assert (Hroot : g Q0 r = 0) by lra.
    exists r. split; [lra|]. split; [exact Hroot|].
    (* the sign test at the low end *)
    assert (Hsign : g Q0 (Rpower 2 (/ Q0 - KLO)) <= 0).
    { rewrite g_test by lra.
      interval with (i_prec 200). }
    assert (Hle : r <= Rpower 2 (/ Q0 - KLO))
      by (apply (root_le Q0 r _ Hq ltac:(lra) (Rpower_pos _ _) Hroot Hsign)).
    (* r <= 2^(1/Q0 - KLO)  gives  V Q0 r >= KLO *)
    assert (Hl2 := ln2_pos).
    assert (Hlnr : ln r <= (/ Q0 - KLO) * ln 2).
    { rewrite <- (ln_Rpower 2 (/ Q0 - KLO)).
      apply ln_le_iff; [lra | apply Rpower_pos | exact Hle]. }
    unfold V.
    apply Rmult_le_reg_r with (r := ln 2); [lra|].
    replace ((/ Q0 - ln r / ln 2) * ln 2) with (/ Q0 * ln 2 - ln r)
      by (field; lra).
    lra.
Qed.

(** ** THE ENCLOSURE, AND THE GROWTH RATE

    Every root gives V <= KHI, and the witness gives V >= KLO, so

      kappa_star  in  [0.3317423792563105, 0.3317423792563106],
      c = 2^(1+kappa_star)  in  [2.5170648368938160, 2.5170648368938163].

    (The Arb certificate says 2.51706483689381612057...) *)

Theorem c_bracket_of_kappa (k : R) :
  KLO <= k <= KHI ->
  2517064836893816/1000000000000000 <= Rpower 2 (1 + k)
  <= 2517064836893817/1000000000000000.
Proof.
  intros [H1 H2]. split.
  - assert (Rpower 2 (1 + KLO) <= Rpower 2 (1 + k)).
    { unfold Rpower. destruct (Req_dec k KLO) as [->|Hne].
      - right; reflexivity.
      - left; apply exp_increasing.
        assert (0 < ln 2) by apply ln2_pos. nra. }
    eapply Rle_trans; [| eassumption]. interval with (i_prec 200).
  - assert (Rpower 2 (1 + k) <= Rpower 2 (1 + KHI)).
    { unfold Rpower. destruct (Req_dec k KHI) as [->|Hne].
      - right; reflexivity.
      - left; apply exp_increasing.
        assert (0 < ln 2) by apply ln2_pos. nra. }
    eapply Rle_trans; [eassumption |]. interval with (i_prec 200).
Qed.
