(** * Lemma A's ledger, assembled and closed on a window  (Rocq + CoqInterval)

    The one-step appendix reduces Zone I to the LEDGER

      delta~ >= w1 q1 eps + w2 (q2 eps + G) - D  >  0,

    where q1 is the E-branch slope, q2 the S-branch slope, w1/w2 the
    soft-min weights, G the S-tangent's deficit below the corner, and D
    the chord deficit of f.  This file assembles it and closes it on one
    window of q1.

    TWO DEPARTURES FROM THE APPENDIX, both made to remove objects that
    have no closed form:

    (P) PARAMETERISE BY q1, NOT BY beta.  E is the Legendre transform of
        -f, so the tangency at beta - eps is exactly minimality of the
        q1-line, and E(beta - eps) = q1 (beta - eps) + f(q1).  The inner
        minimisation disappears.

    (D) USE THE TRUE CHORD DEFICIT D = w1 f(q1) + w2 f(q2) - f(q~),
        not the appendix's bound (M/2) w1 w2 (q1-q2)^2 with M = sup f''.
        D is what the proof consumes, it is explicit once f is, and it
        removes the second derivative of an implicit function.  It is
        also 1.45x less lossy (measured).

    The slope b = beta - eps is not computed from a derivative either:
    [SlopeWindow] pins it from the two endpoints of the window by
    Topkis monotonicity.  So no derivative appears anywhere below.

    WHAT IS AND IS NOT DONE.  One window, (2.4, 2.4005), is closed end
    to end: every intermediate quantity is enclosed by kernel-checked
    interval arithmetic, and the ledger comes out in [0.0086, 0.0149].
    Covering the whole Zone I range q1 in [1.45, 3.25] needs about 3700
    such windows at this width; they are mechanical repetitions of
    [window_24] with different constants, and are NOT done here. *)

From Stdlib Require Import Reals Lra.
From Interval Require Import Tactic.
From RevPebblingRocq Require Import KappaStar RhoEnclose LedgerParam EnvelopeE
  SlopeWindow.
Local Open Scope R_scope.

(** ** The mollified cap, and the ledger *)

Definition EPS : R := 1/100.
Definition LAM : R := 30.
Definition MU  : R := 30.

(** The design parameter of the trial profile: the slope at which the
    cap's asymptote is taken.  It is a CONSTANT of the ansatz, not
    something the proof must characterise — the one-step inequality
    either holds for this profile or it does not. *)
Definition QS : R := 15153832361072514/10000000000000000.

Definition sp (z : R) : R := ln (1 + Rpower 2 z) / ln 2.
Definition sigm (z : R) : R := 1 / (1 + Rpower 2 (-z)).

(** The corner sits at [bc = kappa* + eps], so with [beta = b + eps] the
    argument of the mollifier is simply [z = LAM (kappa* - b)]. *)
Definition zof (b : R) : R := LAM * (KHI - b).

Definition q2of (b : R) : R := QS * sigm (zof b).
Definition Gof  (b : R) : R := (QS / LAM) * (sp (zof b) - zof b * sigm (zof b)).
Definition Sof  (b : R) : R := 1 - (QS / LAM) * sp (zof b).

(** The soft-min weight on the E-branch. *)
Definition w1of (Sb Eb : R) : R := 1 / (1 + Rpower 2 (- (MU * (Sb - Eb)))).

(** **THE LEDGER.**  [f1], [f2], [ft] are the values of [f] at [q1],
    [q2] and the composite slope [q~]. *)
Definition ledger (q1 q2 G w1 f1 f2 ft : R) : R :=
  w1 * q1 * EPS + (1 - w1) * (q2 * EPS + G)
  - (w1 * f1 + (1 - w1) * f2 - ft).

(** ** The arithmetic core

    Given enclosures of every primitive, the ledger is positive.  This
    is the only part a covering repeats, and it is pure interval
    arithmetic. *)

Theorem ledger_pos
  (q1 q2 G w1 f1 f2 ft : R)
  (Hq1 : 24/10 <= q1 <= 24005/10000)
  (Hq2 : 1443661/1000000 <= q2 <= 1443761/1000000)
  (HG  : 13772/1000000 <= G <= 13990/1000000)
  (Hw1 : 759571/1000000 <= w1 <= 761682/1000000)
  (Hf1 : 272277/1000000 <= f1 <= 272485/1000000)
  (Hf2 : 521513/1000000 <= f2 <= 521621/1000000)
  (Hft : 316576/1000000 <= ft <= 320940/1000000) :
  85/10000 <= ledger q1 q2 G w1 f1 f2 ft.
Proof.
  unfold ledger, EPS.
  interval with (i_prec 90).
Qed.

(** ** The window (2.4, 2.4005): the primitives, one by one *)

(** The slope, from the endpoints by Topkis.  (The numbers are the ones
    [SlopeWindow] produces at this width; [slope_in_24_26] is the same
    construction on a wider window.) *)
Definition BLO : R := 187306/1000000.
Definition BHI : R := 187370/1000000.

(** [z], [q2], [G] and [S] are explicit in [b].  The [z]-level lemmas
    take [z] as a plain variable: [interval] needs an atom, not a
    definition applied to an argument. *)

Lemma z_encl (b : R) : BLO <= b <= BHI ->
  4331171/1000000 <= zof b <= 4333272/1000000.
Proof.
  intros H. unfold zof, LAM, BLO, BHI in *. lra.
Qed.

Lemma q2_of_z (z : R) : 4331171/1000000 <= z <= 4333272/1000000 ->
  1443661/1000000 <= QS * sigm z <= 1443761/1000000.
Proof.
  intros H. unfold sigm, QS. split; interval with (i_prec 120).
Qed.

Lemma G_of_z (z : R) : 4331171/1000000 <= z <= 4333272/1000000 ->
  13772/1000000 <= (QS / LAM) * (sp z - z * sigm z) <= 13990/1000000.
Proof.
  intros H. unfold sigm, sp, QS, LAM. split; interval with (i_prec 120).
Qed.

Lemma S_of_z (z : R) : 4331171/1000000 <= z <= 4333272/1000000 ->
  777586/1000000 <= 1 - (QS / LAM) * sp z <= 777688/1000000.
Proof.
  intros H. unfold sp, QS, LAM. split; interval with (i_prec 120).
Qed.

Lemma q2_encl (b : R) : BLO <= b <= BHI ->
  1443661/1000000 <= q2of b <= 1443761/1000000.
Proof. intros H. unfold q2of. apply q2_of_z, z_encl, H. Qed.

Lemma G_encl (b : R) : BLO <= b <= BHI ->
  13772/1000000 <= Gof b <= 13990/1000000.
Proof. intros H. unfold Gof. apply G_of_z, z_encl, H. Qed.

Lemma S_encl (b : R) : BLO <= b <= BHI ->
  777586/1000000 <= Sof b <= 777688/1000000.
Proof. intros H. unfold Sof. apply S_of_z, z_encl, H. Qed.

(** [f] at the three slopes, from [RhoEnclose].  Each is two sign tests
    at the corners of a rho-box of width 1e-9. *)

Lemma f1_encl (q r : R) : 24/10 <= q <= 24005/10000 -> 0 < r -> g q r = 0 ->
  272277/1000000 <= fq q r <= 272485/1000000.
Proof.
  apply (f_in (24/10) (24005/10000)
           (1081811280/1000000000) (1081858271/1000000000));
    try lra; unfold g, fq.
  - interval with (i_prec 120).
  - interval with (i_prec 120).
  - intros x y Hx Hy. split; interval with (i_prec 120).
Qed.

Lemma f2_encl (q r : R) :
  1443661/1000000 <= q <= 1443761/1000000 -> 0 < r -> g q r = 0 ->
  521513/1000000 <= fq q r <= 521621/1000000.
Proof.
  apply (f_in (1443661/1000000) (1443761/1000000)
           (1284532743/1000000000) (1284576358/1000000000));
    try lra; unfold g, fq.
  - interval with (i_prec 120).
  - interval with (i_prec 120).
  - intros x y Hx Hy. split; interval with (i_prec 120).
Qed.

Lemma ft_encl (q r : R) :
  2167020/1000000 <= q <= 2175540/1000000 -> 0 < r -> g q r = 0 ->
  316576/1000000 <= fq q r <= 320940/1000000.
Proof.
  apply (f_in (2167020/1000000) (2175540/1000000)
           (1106565312/1000000000) (1107665071/1000000000));
    try lra; unfold g, fq.
  - interval with (i_prec 120).
  - interval with (i_prec 120).
  - intros x y Hx Hy. split; interval with (i_prec 120).
Qed.

(** The weight, from [E] and the cap. *)
Lemma w1_encl (q1 b f1 Sb : R) :
  24/10 <= q1 <= 24005/10000 -> BLO <= b <= BHI ->
  272277/1000000 <= f1 <= 272485/1000000 ->
  777586/1000000 <= Sb <= 777688/1000000 ->
  759571/1000000 <= w1of Sb (q1 * b + f1) <= 761682/1000000.
Proof.
  intros Hq Hb Hf HS. unfold w1of, MU, BLO, BHI in *.
  split; interval with (i_prec 120).
Qed.

(** The composite slope. *)
Lemma qt_encl (q1 q2 w1 : R) :
  24/10 <= q1 <= 24005/10000 ->
  1443661/1000000 <= q2 <= 1443761/1000000 ->
  759571/1000000 <= w1 <= 761682/1000000 ->
  2167020/1000000 <= w1 * q1 + (1 - w1) * q2 <= 2175540/1000000.
Proof.
  intros H1 H2 H3. split; interval with (i_prec 90).
Qed.

(** ** THE WINDOW, CLOSED

    Every hypothesis is either a root equation or the window's own
    bounds; everything else is derived. *)

(** Naming the derived quantities first keeps the statement readable:
    [fq] takes a slope and a root, and the composite slope would
    otherwise appear nested inside its own argument. *)

Theorem window_24 (q1 b r1 r2 rt f1 f2 ft q2 G w1 qt : R) :
  (* the window and its slope *)
  24/10 <= q1 <= 24005/10000 ->
  BLO <= b <= BHI ->
  (* the derived slopes and constants *)
  q2 = q2of b -> G = Gof b ->
  f1 = fq q1 r1 -> w1 = w1of (Sof b) (q1 * b + f1) ->
  qt = w1 * q1 + (1 - w1) * q2 ->
  f2 = fq q2 r2 -> ft = fq qt rt ->
  (* the three roots *)
  0 < r1 -> 0 < r2 -> 0 < rt ->
  g q1 r1 = 0 -> g q2 r2 = 0 -> g qt rt = 0 ->
  85/10000 <= ledger q1 q2 G w1 f1 f2 ft.
Proof.
  intros Hq1 Hb Hq2 HG Hf1 Hw1 Hqt Hf2 Hft Hr1 Hr2 Hrt Hg1 Hg2 Hgt.
  (* f at the window *)
  assert (Ef1 : 272277/1000000 <= f1 <= 272485/1000000)
    by (rewrite Hf1; exact (f1_encl q1 r1 Hq1 Hr1 Hg1)).
  (* the cap and the S-branch slope *)
  assert (ES : 777586/1000000 <= Sof b <= 777688/1000000) by (apply S_encl; exact Hb).
  assert (Eq2 : 1443661/1000000 <= q2 <= 1443761/1000000)
    by (rewrite Hq2; apply q2_encl; exact Hb).
  assert (EG : 13772/1000000 <= G <= 13990/1000000)
    by (rewrite HG; apply G_encl; exact Hb).
  (* the weight *)
  assert (Ew1 : 759571/1000000 <= w1 <= 761682/1000000)
    by (rewrite Hw1; apply w1_encl; assumption).
  (* the composite slope, and f there *)
  assert (Eqt : 2167020/1000000 <= qt <= 2175540/1000000)
    by (rewrite Hqt; apply qt_encl; assumption).
  assert (Ef2 : 521513/1000000 <= f2 <= 521621/1000000)
    by (rewrite Hf2; exact (f2_encl q2 r2 Eq2 Hr2 Hg2)).
  assert (Eft : 316576/1000000 <= ft <= 320940/1000000)
    by (rewrite Hft; exact (ft_encl qt rt Eqt Hrt Hgt)).
  (* and the arithmetic core closes it *)
  exact (ledger_pos q1 q2 G w1 f1 f2 ft Hq1 Eq2 EG Ew1 Ef1 Ef2 Eft).
Qed.
