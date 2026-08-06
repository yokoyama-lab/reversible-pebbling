(** * rho_c as a function, and the partial derivatives of g

    Everything so far quantified over roots and never built rho_c.  The
    tangency  f'(q) = eps - beta  of Lemma A does need a derivative, and
    a derivative needs a function, so this file constructs one.

    WHY THE DERIVATIVE IS NEEDED AFTER ALL.  LedgerParam brackets beta
    without differentiating, and pointwise that costs 0.07%.  But a
    machine-checked Zone I proof covers WINDOWS of q, and over a window
    of width W the difference-quotient bracket has width ~ 0.26 sqrt(W)
    while the tangency gives |f''| W.  Reaching the 3e-4 that the
    softmin weight demands needs W ~ 1e-7 (30 million windows) without
    the derivative and W ~ 2e-3 (about 1400) with it.  Measured in
    scripts/probe_brw/m43_zone1_windows.py of the paper repository.

    This file builds the function and the partials; the implicit
    function theorem itself is the next step. *)

From Stdlib Require Import Reals Lra Ranalysis_reg Ranalysis5 MVT.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar RhoEnclose LedgerParam.
Local Open Scope R_scope.

(** ** The function *)

(** The informative form of [root_exists]: [IVT_interv] already returns
    a [sig], so nothing is lost. *)
Lemma root_sig (q : R) (Hq : 0 < q) : {r : R | 1 < r /\ g q r = 0}.
Proof.
  destruct (IVT_interv (fun r => - g q r) 1 (Rpower 2 (/ q))) as [r [Hr Hval]].
  - intros a Ha. apply continuity_pt_opp. apply g_continuous.
    assert (1 < Rpower 2 (/ q)) by (apply one_lt_top; assumption). lra.
  - apply one_lt_top; assumption.
  - assert (H := g_at_1 q). assert (0 < Rpower 2 (-q)) by apply Rpower_pos. lra.
  - assert (H := g_at_top q Hq). lra.
  - exists r. assert (Hroot : g q r = 0) by lra.
    split; [| exact Hroot].
    apply (root_gt_1 q r Hq); [| exact Hroot].
    assert (1 < Rpower 2 (/ q)) by (apply one_lt_top; assumption). lra.
Defined.

(** [rhoc q] is the root for [q > 0], and [1] elsewhere (never used). *)
Definition rhoc (q : R) : R :=
  match Rlt_dec 0 q with
  | left H => proj1_sig (root_sig q H)
  | right _ => 1
  end.

Theorem rhoc_spec (q : R) : 0 < q -> 1 < rhoc q /\ g q (rhoc q) = 0.
Proof.
  intros Hq. unfold rhoc.
  destruct (Rlt_dec 0 q) as [H|H]; [| lra].
  exact (proj2_sig (root_sig q H)).
Qed.

Corollary rhoc_pos (q : R) : 0 < q -> 0 < rhoc q.
Proof. intros Hq. destruct (rhoc_spec q Hq). lra. Qed.

Corollary rhoc_root (q : R) : 0 < q -> g q (rhoc q) = 0.
Proof. intros Hq. destruct (rhoc_spec q Hq). assumption. Qed.

(** **UNIQUENESS.**  Strict monotonicity of [g] in [rho] leaves no room. *)
Theorem rhoc_unique (q r : R) : 0 < q -> 0 < r -> g q r = 0 -> r = rhoc q.
Proof.
  intros Hq Hr Hroot.
  destruct (rhoc_spec q Hq) as [H1 H2].
  destruct (Rtotal_order r (rhoc q)) as [Hlt | [Heq | Hgt]].
  - assert (g q (rhoc q) < g q r) by (apply g_decr; lra). lra.
  - exact Heq.
  - assert (g q r < g q (rhoc q)) by (apply g_decr; lra). lra.
Qed.

(** Every statement proved over roots now applies to [rhoc]. *)
Corollary rhoc_in (qlo qhi a b q : R) :
  0 < qlo -> qlo <= qhi -> 1 < a -> a <= b ->
  0 <= g qhi a -> g qlo b <= 0 -> qlo <= q <= qhi ->
  a <= rhoc q <= b.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7.
  assert (Hq : 0 < q) by lra.
  exact (rho_in qlo qhi a b H1 H2 H3 H4 H5 H6 q (rhoc q) H7
           (rhoc_pos q Hq) (rhoc_root q Hq)).
Qed.

(** ** Continuity

    Squeeze the root between two levels where [g] has a strict sign, and
    move [q] little enough that the two signs survive.  Continuity of
    [g] in [q] at a fixed [rho] is all that is used. *)

Lemma g_cont_in_q (r : R) : 0 < r -> forall q, continuity_pt (fun x => g x r) q.
Proof.
  intros Hr q. unfold g, Rpower.
  reg; try (apply Rgt_not_eq; lra); try lra.
Qed.

(** A strict sign of [g] at a fixed level survives a small move in [q]. *)
Lemma sign_persists_pos (r c : R) :
  0 < g c r -> continuity_pt (fun x => g x r) c ->
  exists dlt, 0 < dlt /\ forall x, Rabs (x - c) < dlt -> 0 < g x r.
Proof.
  intros Hpos Hcont.
  destruct (Hcont (g c r) Hpos) as [alp [Halp Hd]].
  exists alp. split; [assumption|].
  intros x Hx.
  destruct (Req_dec x c) as [->|Hne]; [assumption|].
  assert (HD : D_x no_cond c x /\ R_dist x c < alp).
  { split; [split; [exact I | apply not_eq_sym; exact Hne] | exact Hx]. }
  specialize (Hd x HD). unfold R_dist in Hd.
  apply Rabs_def2 in Hd. lra.
Qed.

Lemma sign_persists_neg (r c : R) :
  g c r < 0 -> continuity_pt (fun x => g x r) c ->
  exists dlt, 0 < dlt /\ forall x, Rabs (x - c) < dlt -> g x r < 0.
Proof.
  intros Hneg Hcont.
  destruct (Hcont (- g c r) ltac:(lra)) as [alp [Halp Hd]].
  exists alp. split; [assumption|].
  intros x Hx.
  destruct (Req_dec x c) as [->|Hne]; [assumption|].
  assert (HD : D_x no_cond c x /\ R_dist x c < alp).
  { split; [split; [exact I | apply not_eq_sym; exact Hne] | exact Hx]. }
  specialize (Hd x HD). unfold R_dist in Hd.
  apply Rabs_def2 in Hd. lra.
Qed.

Theorem rhoc_continuous (q : R) : 0 < q -> continuity_pt rhoc q.
Proof.
  intros Hq eps Heps.
  destruct (rhoc_spec q Hq) as [Hr1 Hroot].
  remember (Rmin (eps / 2) ((rhoc q - 1) / 2)) as d eqn:Hdef.
  assert (Hd : 0 < d) by (rewrite Hdef; apply Rmin_glb_lt; lra).
  assert (Hd1 : d <= eps / 2) by (rewrite Hdef; apply Rmin_l).
  assert (Hd2 : d <= (rhoc q - 1) / 2) by (rewrite Hdef; apply Rmin_r).
  assert (Hlo : 0 < g q (rhoc q - d)).
  { assert (g q (rhoc q) < g q (rhoc q - d)) by (apply g_decr; lra). lra. }
  assert (Hhi : g q (rhoc q + d) < 0).
  { assert (g q (rhoc q + d) < g q (rhoc q)) by (apply g_decr; lra). lra. }
  destruct (sign_persists_pos (rhoc q - d) q Hlo
              (g_cont_in_q (rhoc q - d) ltac:(lra) q)) as [a1 [Ha1 H1]].
  destruct (sign_persists_neg (rhoc q + d) q Hhi
              (g_cont_in_q (rhoc q + d) ltac:(lra) q)) as [a2 [Ha2 H2]].
  exists (Rmin (Rmin a1 a2) q). split.
  - repeat apply Rmin_glb_lt; assumption.
  - intros x [_ Hx]. unfold R_dist in Hx.
    assert (Hxq : Rabs (x - q) < q)
      by (eapply Rlt_le_trans; [exact Hx | apply Rmin_r]).
    assert (Hx12 : Rabs (x - q) < Rmin a1 a2)
      by (eapply Rlt_le_trans; [exact Hx | apply Rmin_l]).
    assert (Hxpos : 0 < x) by (apply Rabs_def2 in Hxq; lra).
    assert (Hs1 : 0 < g x (rhoc q - d)).
    { apply H1. eapply Rlt_le_trans; [exact Hx12 | apply Rmin_l]. }
    assert (Hs2 : g x (rhoc q + d) < 0).
    { apply H2. eapply Rlt_le_trans; [exact Hx12 | apply Rmin_r]. }
    destruct (rhoc_spec x Hxpos) as [Hx1 Hxroot].
    assert (Hbox : rhoc q - d <= rhoc x <= rhoc q + d).
    { split.
      - apply (root_ge x (rhoc x) (rhoc q - d) Hxpos ltac:(lra) ltac:(lra)
                 Hxroot ltac:(lra)).
      - apply (root_le x (rhoc x) (rhoc q + d) Hxpos ltac:(lra) ltac:(lra)
                 Hxroot ltac:(lra)). }
    unfold R_dist. apply Rabs_def1; lra.
Qed.

(** ** Partial derivatives of g

    [Rpower] has no derivative lemma in the standard library, so both
    partials are built from [exp] and [ln] by the chain rule. *)

Lemma derive_Rpower_q (r : R) : 0 < r ->
  forall q, derivable_pt_lim (fun x => Rpower r (-x)) q
              (- ln r * Rpower r (-q)).
Proof.
  intros Hr q.
  assert (H : derivable_pt_lim (fun x => - x * ln r) q (- ln r)).
  { assert (H0 : derivable_pt_lim (fun x : R => - x) q (-1)).
    { apply (derivable_pt_lim_opp (fun x : R => x) q 1). apply derivable_pt_lim_id. }
    assert (H1 : derivable_pt_lim (fun _ : R => ln r) q 0)
      by apply derivable_pt_lim_const.
    assert (H2 := derivable_pt_lim_mult _ _ q _ _ H0 H1).
    replace (- ln r) with (-1 * ln r + - q * 0) by ring.
    exact H2. }
  assert (Hc := derivable_pt_lim_exp (- q * ln r)).
  assert (HC := derivable_pt_lim_comp (fun x => - x * ln r) exp q (- ln r)
                  (exp (- q * ln r)) H Hc).
  unfold comp in HC. unfold Rpower.
  replace (- ln r * exp (- q * ln r)) with (exp (- q * ln r) * - ln r) by ring.
  exact HC.
Qed.

(** [d/dq g q r = - ln r * r^(-q) - ln(1+r) * (1+r)^(-q)] *)
Theorem derive_g_q (r : R) : 0 < r ->
  forall q, derivable_pt_lim (fun x => g x r) q
              (- ln r * Rpower r (-q) - ln (1 + r) * Rpower (1 + r) (-q)).
Proof.
  intros Hr q. unfold g.
  assert (H1 := derive_Rpower_q r Hr q).
  assert (H2 := derive_Rpower_q (1 + r) ltac:(lra) q).
  assert (H3 := derivable_pt_lim_plus _ _ q _ _ H1 H2).
  assert (H4 : derivable_pt_lim (fun _ : R => 1) q 0)
    by apply derivable_pt_lim_const.
  assert (H5 := derivable_pt_lim_minus _ _ q _ _ H3 H4).
  replace (- ln r * Rpower r (-q) - ln (1 + r) * Rpower (1 + r) (-q))
    with (- ln r * Rpower r (-q) + - ln (1 + r) * Rpower (1 + r) (-q) - 0)
    by ring.
  exact H5.
Qed.

(** The other partial: [d/dr (r^a) = a r^a / r]. *)
Lemma derive_Rpower_r (a r : R) : 0 < r ->
  derivable_pt_lim (fun x => Rpower x a) r (a * Rpower r a / r).
Proof.
  intros Hr.
  assert (Hln : derivable_pt_lim ln r (/ r))
    by (apply derivable_pt_lim_ln; assumption).
  assert (Hc : derivable_pt_lim (fun x => a * ln x) r (a * / r)).
  { assert (Hk : derivable_pt_lim (fun _ : R => a) r 0)
      by apply derivable_pt_lim_const.
    assert (H := derivable_pt_lim_mult _ _ r _ _ Hk Hln).
    replace (a * / r) with (0 * ln r + a * / r) by ring.
    exact H. }
  assert (He := derivable_pt_lim_exp (a * ln r)).
  assert (HC := derivable_pt_lim_comp (fun x => a * ln x) exp r (a * / r)
                  (exp (a * ln r)) Hc He).
  unfold comp in HC. unfold Rpower.
  replace (a * exp (a * ln r) / r) with (exp (a * ln r) * (a * / r))
    by (field; lra).
  exact HC.
Qed.

(** [d/dr g q r = -q r^(-q)/r - q (1+r)^(-q)/(1+r)], strictly negative
    for [q > 0] — the nondegeneracy the implicit function theorem needs. *)
Theorem derive_g_r (q : R) : forall r, 0 < r ->
  derivable_pt_lim (fun x => g q x) r
    (- q * Rpower r (-q) / r + - q * Rpower (1 + r) (-q) / (1 + r)).
Proof.
  intros r Hr. unfold g.
  assert (H1 := derive_Rpower_r (-q) r Hr).
  (* the shifted power, through (fun x => 1 + x) *)
  assert (Hsh : derivable_pt_lim (fun x : R => 1 + x) r 1).
  { assert (Hk : derivable_pt_lim (fun _ : R => 1) r 0)
      by apply derivable_pt_lim_const.
    assert (H := derivable_pt_lim_plus _ _ r _ _ Hk (derivable_pt_lim_id r)).
    replace (0 + 1) with 1 in H by ring. exact H. }
  assert (H2 := derive_Rpower_r (-q) (1 + r) ltac:(lra)).
  assert (H2' := derivable_pt_lim_comp (fun x : R => 1 + x)
                   (fun x => Rpower x (-q)) r 1
                   (- q * Rpower (1 + r) (-q) / (1 + r)) Hsh H2).
  unfold comp in H2'.
  assert (H3 := derivable_pt_lim_plus _ _ r _ _ H1 H2').
  assert (H4 : derivable_pt_lim (fun _ : R => 1) r 0)
    by apply derivable_pt_lim_const.
  assert (H5 := derivable_pt_lim_minus _ _ r _ _ H3 H4).
  replace (- q * Rpower r (-q) / r + - q * Rpower (1 + r) (-q) / (1 + r))
    with (- q * Rpower r (-q) / r
          + - q * Rpower (1 + r) (-q) / (1 + r) * 1 - 0) by ring.
  exact H5.
Qed.

(** **NONDEGENERACY.**  [d/dr g q r < 0] whenever [q > 0] and [r > 0]. *)
Theorem derive_g_r_neg (q r : R) : 0 < q -> 0 < r ->
  - q * Rpower r (-q) / r + - q * Rpower (1 + r) (-q) / (1 + r) < 0.
Proof.
  intros Hq Hr.
  assert (H1 : 0 < Rpower r (-q)) by apply Rpower_pos.
  assert (H2 : 0 < Rpower (1 + r) (-q)) by apply Rpower_pos.
  assert (A : - q * Rpower r (-q) / r < 0).
  { apply Rdiv_neg_pos; [nra | lra]. }
  assert (B : - q * Rpower (1 + r) (-q) / (1 + r) < 0).
  { apply Rdiv_neg_pos; [nra | lra]. }
  lra.
Qed.
