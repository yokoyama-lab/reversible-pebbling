(** * The eps-minimiser EXISTS, at every slope  (Rocq)

    Every theorem of the Zone I chain used to carry

      EminRel b q1 f1  :=  forall q r, 0 < q -> 0 < r -> g q r = 0 ->
                             q1 b + f1 <= q b + fq q r,

    "q1 minimises q |-> q b + f(q) EXACTLY".  That hypothesis was never
    discharged, and discharging it is not cheap: an exact minimiser of a
    family over an unbounded index set needs compactness of an effective
    range plus continuity of rho_c, i.e. the implicit function machinery
    of [RhoDeriv] and then some.  Until it is discharged, nothing rules
    out that the hypothesis is UNSATISFIABLE and every theorem carrying
    it vacuous.

    [LedgerParam.EminEps] weakens it to eps-minimality, and THAT is free.
    The family

      Phi = { q b + fq q r : 0 < q, 0 < r, g q r = 0 }

    is non-empty (a root exists at q = 1, by [root_exists]) and bounded
    below by 0 (both terms are positive: q b > 0, and fq q r > 0 by
    [EnvelopeE.f_pos], since every root exceeds 1).  Its infimum
    therefore exists by the completeness of R, and for every eps > 0 some
    member of Phi is within eps of it -- which is exactly [EminEps].

    No compactness, no continuity, no derivative, and in particular no
    [rhoc]: the statement quantifies over ROOTS of g, and the witness
    comes out of the infimum as a root, so this file does not need
    [RhoDeriv] at all.

    THE ONE CLASSICAL STEP.  "the infimum is approached" needs, from
    [is_lub m], a member above m - eps.  Constructively one only gets
    "m - eps is not an upper bound"; turning that into a witness is
    [Classical_Prop.classic], which is already in this development's
    trust base (Rocq's classical reals). *)

From Stdlib Require Import Reals Lra Classical_Prop.
From RevPebblingRocq Require Import KappaStar RhoEnclose LedgerParam EnvelopeE.
Local Open Scope R_scope.

Section EpsMinimiser.

Variable b : R.
Hypothesis Hb : 0 < b.

(** The family, negated so that Rocq's [completeness] (a LEAST UPPER
    bound principle) applies directly: [Phineg y] iff [-y] is a value of
    the line family. *)
Definition Phineg (y : R) : Prop :=
  exists q r, 0 < q /\ 0 < r /\ g q r = 0 /\ - y = q * b + fq q r.

Lemma Phineg_inhabited : exists y, Phineg y.
Proof.
  destruct (root_exists 1 Rlt_0_1) as [r [Hr1 Hgr]].
  exists (- (1 * b + fq 1 r)), 1, r.
  repeat split; [lra | lra | exact Hgr | ring].
Qed.

(** Bounded above by 0, because every value of the family is positive. *)
Lemma Phineg_bounded : bound Phineg.
Proof.
  exists 0. intros y [q [r [Hq [Hr [Hgr Hval]]]]].
  assert (Hf := f_pos q r Hq Hr Hgr).
  assert (0 < q * b) by (apply Rmult_lt_0_compat; lra).
  lra.
Qed.

(** **THE eps-MINIMISER EXISTS.**  For every eps > 0 there is a slope q1
    and a root r1 there at which the line family is minimised to within
    eps.  Unconditional. *)
Theorem emin_eps_exists (eps : R) : 0 < eps ->
  exists q1 r1, 0 < q1 /\ 0 < r1 /\ g q1 r1 = 0 /\
                EminEps eps b q1 (fq q1 r1).
Proof.
  intros Heps.
  destruct (completeness Phineg Phineg_bounded Phineg_inhabited) as [m Hm].
  destruct Hm as [Hub Hleast].
  (* the infimum is approached: some member of Phineg exceeds m - eps *)
  destruct (classic (exists y, Phineg y /\ m - eps < y)) as [Hex | Hno].
  - destruct Hex as [y [Hy Hgt]].
    destruct Hy as [q1 [r1 [Hq1 [Hr1 [Hg1 Hval]]]]].
    exists q1, r1. repeat split; try assumption.
    intros q r Hq Hr Hg.
    (* -m is a lower bound for the family *)
    assert (Hlb : - m <= q * b + fq q r).
    { assert (Hmem : Phineg (- (q * b + fq q r)))
        by (exists q, r; repeat split; [lra | lra | exact Hg | ring]).
      assert (H := Hub _ Hmem). lra. }
    lra.
  - exfalso.
    assert (Hub' : is_upper_bound Phineg (m - eps)).
    { intros y Hy. destruct (Rle_or_lt y (m - eps)) as [H | H]; [exact H |].
      exfalso. apply Hno. exists y. split; assumption. }
    assert (H := Hleast _ Hub'). lra.
Qed.

End EpsMinimiser.

(** The statement with the slope quantified, for citation. *)
Theorem emin_eps_exists_all (eps b : R) : 0 < eps -> 0 < b ->
  exists q1 r1, 0 < q1 /\ 0 < r1 /\ g q1 r1 = 0 /\
                EminEps eps b q1 (fq q1 r1).
Proof. intros He Hb. exact (emin_eps_exists b Hb eps He). Qed.

(** **THE HYPOTHESIS IS SATISFIABLE.**  Restated as the negation of the
    vacuity worry: at every positive slope, and for every eps > 0, the
    class of eps-minimisers is inhabited. *)
Corollary EminEps_inhabited (eps b : R) : 0 < eps -> 0 < b ->
  ~ (forall q1 r1, 0 < q1 -> 0 < r1 -> g q1 r1 = 0 ->
       ~ EminEps eps b q1 (fq q1 r1)).
Proof.
  intros He Hb Hall.
  destruct (emin_eps_exists_all eps b He Hb) as [q1 [r1 [Hq [Hr [Hg Hm]]]]].
  exact (Hall q1 r1 Hq Hr Hg Hm).
Qed.

(** A first unconditional consequence: the difference-quotient bracket of
    [LedgerParam.beta_bracket_eps] applies to a slope that is now KNOWN
    to exist.  (The two enclosures of [f] are still supplied by the
    caller, at whatever q1 the infimum produced.) *)
Corollary bracket_of_some_minimiser (eps b : R) : 0 < eps -> 0 < b ->
  exists q1 r1, 0 < q1 /\ 0 < r1 /\ g q1 r1 = 0 /\
    forall step fp fm, 0 < step -> step < q1 ->
      (forall r, 0 < r -> g (q1 + step) r = 0 -> fq (q1 + step) r <= fp) ->
      (forall r, 0 < r -> g (q1 - step) r = 0 -> fq (q1 - step) r <= fm) ->
      (fq q1 r1 - fp - eps) / step <= b <= (fm - fq q1 r1 + eps) / step.
Proof.
  intros He Hb.
  destruct (emin_eps_exists_all eps b He Hb) as [q1 [r1 [Hq [Hr [Hg Hm]]]]].
  exists q1, r1.
  split; [exact Hq | split; [exact Hr | split; [exact Hg |]]].
  intros step fp fm Hh Hhq Hp Hmm.
  exact (beta_bracket_eps eps b q1 (fq q1 r1) step fp fm Hq Hh Hhq
           (Rlt_le _ _ He) Hm Hp Hmm).
Qed.
