import RevPebbling.RateTransfer
import RevPebbling.DispersionRealGrowth
import RevPebbling.Final
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

/-!
# The left endpoint of a minimal-space interval, and the rate transfer

`RateTransfer` supplies the sandwich (`gameT_mono_len`) and the right
endpoint `T(2^S − 1, S) = 2 Σ_{i≤S} f_i`.  What was missing there is the
**lower** bound at the left endpoint `n = 2^{S−1}`, where the split of
the min-plus recurrence (H) is *not* pinned to a single point.  This file
supplies it and closes the transfer

  `T(n, S_min(n)) = n^{log₂ c + o(1)}`.

## The route

1.  **Capacity pigeonhole** (`fpre_le_of_halfReachIn`).  Unrolling (H)
    writes a half-reach of `n` cells with `S` pebbles as a sequence of
    clean checkpoints of lengths `m_S, …, m_1` with `m_i ≤ 2^{i−1}` and
    cost `Σ_i F(m_i, i)`.  If every `m_i` were `≤ K` the chain could
    only be `cap S K = Σ_i min(2^{i−1}, K)` long, so some `m_i > K`, and
    that one checkpoint already costs `F(K+1, i) ≥ F(K+1, S)`.  At
    `K = 2^{r}`, `S = r+3`, `n = 2^{r+2}` the capacity is `2^{r+2} − 1`,
    one short of `n`, so the pigeonhole fires:

      `F(2^r + 1, r+3) ≤ H(2^{r+2}, r+3)`.

2.  **Counting** (`fpre_ge_of_countLe`).  `F(k+1, S) = 1 + 2 Σ_{i<k} δ_i`
    and at most `C_S(v)` of the `δ_i` are `≤ v`, so
    `F(k+1,S) ≥ 2 (k − C_S(v))(v+1)`.

3.  **Dispersion** (`DispersionReal.dispersion_real`) bounds `C_S(v)`,
    and the two combine into a geometric lower bound with the *same*
    base `2·(2/λ)^{1/q}` that `DispersionRealGrowth.c_ge_real` gives for
    `f_S` itself.  Taking the supremum over the admissible parameters —
    which is `c`, by `Final.c_eq_two_rpow_kappaStar` — gives the left
    endpoint the growth rate `c`.

4.  The sandwich of `RateTransfer` then transports the rate to every `n`
    in the interval.

## What is *not* used

The merge machinery of `HalfReachMerge` — the marginal list
`halfMarginals` and the threshold identity `halfMarginals_countLe`,
i.e. `D_S(x) = S + Σ_{i≤S} C_i(⌊x/2⌋)` — is **not** needed here, and the
row family is never connected to it.  That route asks for a dispersion
bound on the *sum* `Σ_{i≤S} C_i`, which the lower rows alone push close
to the whole prefix length `2^{S−1}`.  The capacity pigeonhole avoids the
sum entirely: it throws away every checkpoint but the longest one, at a
cost of a constant factor (empirically the bound of step 1 is about
`0.20·H(2^{S−1},S)`, stable in `S`), which the exponential rate does not
see.  So the left endpoint closes with the top row only.

Nor is the right endpoint `RateTransfer.gameT_full` needed for the lower
half; it enters only through the upper half, via `sumF_le_two_mul`.

## STATUS

Everything in this file is unconditional: no `sorry`, and every theorem
depends on `propext`, `Classical.choice`, `Quot.sound` only.  The
dispersion input is `DispersionReal.dispersion_real`, which is itself
unconditional, and the identification of the supremum of its bases with
`c` is `Final.c_eq_two_rpow_kappaStar`.
-/

namespace RevPebbling.RateTransferLow

open Filter Topology
open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty
open RevPebbling.RowMax RevPebbling.RowExact RevPebbling.GameCost
open RevPebbling.HalfReachRecurrence RevPebbling.HalfReachBridge
open RevPebbling.ReachLimit RevPebbling.CompleteReach RevPebbling.GameCompleteCost
open RevPebbling.RateTransfer

-- ==================================================================
-- 1.  The capacity pigeonhole
-- ==================================================================

/-- `cap S K = Σ_{i=1}^{S} min (2^{i−1}) K` — the greatest chain length a
half-reach with `S` pebbles can cover if every checkpoint of the
unrolled recurrence (H) is at most `K` long. -/
def cap : Nat → Nat → Nat
  | 0, _ => 0
  | S + 1, K => cap S K + min (2 ^ S) K

theorem cap_sat : ∀ (S K : Nat), 2 ^ S ≤ K → cap (S + 1) K = 2 ^ (S + 1) - 1 := by
  intro S
  induction S with
  | zero =>
      intro K h
      have h1 : (2:Nat) ^ 0 = 1 := rfl
      have hK : 1 ≤ K := by omega
      show cap 0 K + min (2 ^ 0) K = 2 ^ 1 - 1
      have hm : min (2 ^ 0) K = 1 := by omega
      have hc : cap 0 K = 0 := rfl
      have h21 : (2:Nat) ^ 1 - 1 = 1 := rfl
      omega
  | succ S ih =>
      intro K h
      have hstep : (2:Nat) ^ S ≤ 2 ^ (S + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hprev := ih K (le_trans hstep h)
      show cap (S + 1) K + min (2 ^ (S + 1)) K = 2 ^ (S + 2) - 1
      rw [hprev, Nat.min_eq_left h]
      have e : (2:Nat) ^ (S + 2) = 2 ^ (S + 1) * 2 := Nat.pow_succ 2 (S + 1)
      have hone : (1:Nat) ≤ 2 ^ (S + 1) := Nat.one_le_two_pow
      omega

theorem cap_full (r : Nat) : cap (r + 3) (2 ^ r) = 2 ^ (r + 2) - 1 := by
  have h1 : cap (r + 1) (2 ^ r) = 2 ^ (r + 1) - 1 := cap_sat r (2 ^ r) (Nat.le_refl _)
  have e2 : cap (r + 2) (2 ^ r) = cap (r + 1) (2 ^ r) + min (2 ^ (r + 1)) (2 ^ r) := rfl
  have e3 : cap (r + 3) (2 ^ r) = cap (r + 2) (2 ^ r) + min (2 ^ (r + 2)) (2 ^ r) := rfl
  have hm1 : min (2 ^ (r + 1)) (2 ^ r) = 2 ^ r :=
    Nat.min_eq_right (Nat.pow_le_pow_right (by omega) (by omega))
  have hm2 : min (2 ^ (r + 2)) (2 ^ r) = 2 ^ r :=
    Nat.min_eq_right (Nat.pow_le_pow_right (by omega) (by omega))
  have hp1 : (2:Nat) ^ (r + 1) = 2 ^ r * 2 := Nat.pow_succ 2 r
  have hp2 : (2:Nat) ^ (r + 2) = 2 ^ (r + 1) * 2 := Nat.pow_succ 2 (r + 1)
  have hone : (1:Nat) ≤ 2 ^ r := Nat.one_le_two_pow
  omega

/-- Prefix sums are nondecreasing in the prefix length. -/
theorem sum_take_mono : ∀ (l : List Nat) {a b : Nat}, a ≤ b →
    (l.take a).sum ≤ (l.take b).sum := by
  intro l
  induction l with
  | nil => intro a b _; simp
  | cons x t ih =>
      intro a b hab
      match a, b with
      | 0, _ => simp
      | _ + 1, 0 => omega
      | a + 1, b + 1 =>
          have := ih (a := a) (b := b) (by omega)
          simp only [List.take_succ_cons, List.sum_cons]
          omega

/-- `Fpre` is nondecreasing in the chain length. -/
theorem Fpre_mono (l : List Nat) {a b : Nat} (h : a ≤ b) : Fpre l a ≤ Fpre l b := by
  have := sum_take_mono l (a := a - 1) (b := b - 1) (by omega)
  show 1 + 2 * _ ≤ 1 + 2 * _
  omega

/-- `Fpre` is nonincreasing in the space index, along a whole chain of
levels (`KnillObs.Fpre_antitone_space` iterated). -/
theorem Fpre_antitone_chain {a b n : Nat} (hab : a ≤ b) (hn : n ≤ 2 ^ (a + 1)) :
    Fpre (rowIter b) n ≤ Fpre (rowIter a) n := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  clear hab
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      have hstep : Fpre (rowIter (a + d + 1)) n ≤ Fpre (rowIter (a + d)) n := by
        refine RevPebbling.KnillObs.Fpre_antitone_space (a + d) n ?_
        exact le_trans hn (Nat.pow_le_pow_right (by omega) (by omega))
      exact le_trans hstep ih

/-- **THE PIGEONHOLE.**  A half-reach longer than the capacity `cap S K`
must contain one clean checkpoint of length more than `K`, and that
checkpoint alone costs at least `F(K+1, ·)`, hence at least its value at
the top level `s + 2` (`Fpre_antitone_chain`).

Unrolling (H) writes the half-reach as checkpoints `m_S, …, m_1` with
`m_i ≤ 2^{i−1}`; the induction below is that unrolling, carried out one
level at a time, with the two cases "this checkpoint is already long
enough" and "recurse with a shorter chain". -/
theorem fpre_le_of_halfReachIn (s K : Nat) :
    ∀ (S : Nat), S ≤ s + 2 → ∀ {n t : Nat}, HalfReachIn n S t → cap S K < n →
      Fpre (rowIter s) (K + 1) ≤ t := by
  intro S
  induction S with
  | zero =>
      intro _ n t h hcap
      have hz := eq_zero_of_halfReachIn_zero h
      have : cap 0 K = 0 := rfl
      omega
  | succ S ih =>
      intro hSle n t h hcap
      have hcap0 : 0 ≤ cap (S + 1) K := Nat.zero_le _
      have hn1 : 1 ≤ n := by omega
      have hnle := le_two_pow_sub_one_of_halfReachIn (S + 1) h
      have hKlt : K < 2 ^ S := by
        rcases Nat.lt_or_ge K (2 ^ S) with h' | h'
        · exact h'
        · rw [cap_sat S K h'] at hcap
          omega
      obtain ⟨m, tf, th, hm, hmn, hf, hh, htime⟩ :=
        halfReach_decompose hn1 (Nat.succ_le_succ (Nat.zero_le S)) h
      by_cases hmK : K + 1 ≤ m
      · have hmle : m ≤ 2 ^ S := by simpa using le_two_pow_of_reachIn hm hf
        have hgf : gameF m (S + 1) ≤ tf := gameF_le hf
        rcases Nat.eq_zero_or_pos S with rfl | hSpos
        · -- one pebble: the checkpoint is a single cell and costs one move
          have h20 : (2:Nat) ^ 0 = 1 := rfl
          have hm1 : m = 1 := by omega
          have hK0 : K = 0 := by omega
          rw [hm1, RevPebbling.GameDecomposition.gameF_one 1 (Nat.le_refl _)] at hgf
          rw [hK0, RevPebbling.GameKnill.Fpre_one]
          omega
        · obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
          have hSs : S' ≤ s := by omega
          have heq : gameF m (S' + 2) = Fpre (rowIter S') m :=
            gameF_eq_row S' m hm hmle
          have h1 : Fpre (rowIter s) (K + 1) ≤ Fpre (rowIter S') (K + 1) :=
            Fpre_antitone_chain hSs (by omega)
          have h2 : Fpre (rowIter S') (K + 1) ≤ Fpre (rowIter S') m := Fpre_mono _ hmK
          rw [show S' + 1 + 1 = S' + 2 from rfl, heq] at hgf
          omega
      · have hmK' : m ≤ K := by omega
        have hminK : min (2 ^ S) K = K := Nat.min_eq_right (le_of_lt hKlt)
        have hcapS : cap (S + 1) K = cap S K + K := by
          show cap S K + min (2 ^ S) K = cap S K + K
          rw [hminK]
        have hlt : cap S K < n - m := by omega
        have hres := ih (by omega) hh hlt
        omega

/-- **THE LEFT ENDPOINT, combinatorial half.**
`F(2^r + 1, r+3) ≤ H(2^{r+2}, r+3)`.  The capacity at `K = 2^r` and
`S = r+3` is exactly `2^{r+2} − 1`, one short of the chain, so the
pigeonhole fires with nothing to spare. -/
theorem fpre_le_gameH_left (r : Nat) :
    Fpre (rowIter (r + 1)) (2 ^ r + 1) ≤ gameH (2 ^ (r + 2)) (r + 3) := by
  have hone : (1:Nat) ≤ 2 ^ (r + 2) := Nat.one_le_two_pow
  have hex : ∃ t, HalfReachIn (2 ^ (r + 2)) (r + 3) t := by
    obtain ⟨t, ht⟩ :=
      (reachIn_iff (2 ^ (r + 2)) (r + 1) hone).mpr (Nat.le_refl _)
    exact ⟨t, halfReach_of_reach hone ht⟩
  have hmem : HalfReachIn (2 ^ (r + 2)) (r + 3) (gameH (2 ^ (r + 2)) (r + 3)) :=
    halfReachIn_gameH hex
  refine fpre_le_of_halfReachIn (r + 1) (2 ^ r) (r + 3) (by omega) hmem ?_
  rw [cap_full r]
  omega

-- ==================================================================
-- 2.  Counting: a prefix sum from a threshold count
-- ==================================================================

/-- At most `countLe l v` entries of `l` are `≤ v`, so the remaining
`l.length − countLe l v` entries are each at least `v+1`. -/
theorem sum_ge_of_countLe (l : List Nat) (v : Nat) :
    (l.length - countLe l v) * (v + 1) ≤ l.sum := by
  induction l with
  | nil => simp [countLe]
  | cons x t ih =>
      have hc := countLe_le_length t v
      rw [countLe_cons, List.length_cons, List.sum_cons]
      by_cases hx : x ≤ v
      · simp only [hx, if_true]
        have hrw : t.length + 1 - (countLe t v + 1) = t.length - countLe t v := by omega
        rw [hrw]
        omega
      · simp only [hx, if_false, Nat.add_zero]
        have hxv : v + 1 ≤ x := by omega
        have hrw : t.length + 1 - countLe t v = (t.length - countLe t v) + 1 := by omega
        rw [hrw, Nat.succ_mul]
        omega

theorem countLe_take_le : ∀ (l : List Nat) (k v : Nat),
    countLe (l.take k) v ≤ countLe l v := by
  intro l
  induction l with
  | nil => intro k v; simp [countLe]
  | cons x t ih =>
      intro k v
      match k with
      | 0 => simp [countLe]
      | k + 1 =>
          rw [List.take_succ_cons, countLe_cons, countLe_cons]
          have := ih k v
          omega

theorem sum_take_ge_of_countLe (l : List Nat) (k v : Nat) (hk : k ≤ l.length) :
    (k - countLe l v) * (v + 1) ≤ (l.take k).sum := by
  have hlen : (l.take k).length = k := by
    rw [List.length_take]; omega
  have h1 := sum_ge_of_countLe (l.take k) v
  rw [hlen] at h1
  have h2 := countLe_take_le l k v
  have h4 : (k - countLe l v) * (v + 1) ≤ (k - countLe (l.take k) v) * (v + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **THE COUNT-TO-COST STEP.**  `F(k+1,S) = 1 + 2 Σ_{i<k} δ(i,S)` and at
most `C_S(v)` of those `δ` are `≤ v`, so the prefix sum is at least
`(k − C_S(v))(v+1)`. -/
theorem fpre_ge_of_countLe (s k v : Nat) (hk : k ≤ 2 ^ (s + 1) - 1) :
    2 * ((k - countLe (rowIter s) v) * (v + 1)) ≤ Fpre (rowIter s) (k + 1) := by
  have hlen : k ≤ (rowIter s).length := by rw [rowIter_length]; exact hk
  have h := sum_take_ge_of_countLe (rowIter s) k v hlen
  show _ ≤ 1 + 2 * (((rowIter s).take (k + 1 - 1)).sum)
  simp only [Nat.add_sub_cancel]
  omega

-- ==================================================================
-- 3.  `f` at least doubles, so `Σ_{i≤S} f_i ≤ 2 f_S`
-- ==================================================================

theorem smerge_sum (a b : List Nat) : (smerge a b).sum = a.sum + b.sum := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [ih]; omega
  | case4 x xs y ys h ih => simp [ih]; omega

theorem sum_zipWith_ge : ∀ (a b : List Nat), b.length ≤ a.length →
    b.sum ≤ (List.zipWith (· + ·) a b).sum
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], _ => by simp
  | x :: xs, y :: ys, h => by
      have hrec := sum_zipWith_ge xs ys (by simpa using h)
      simp only [List.zipWith_cons_cons, List.sum_cons]
      omega

/-- **THE ROW SUM AT LEAST DOUBLES.**  `rowIter (s+1)` contains a copy of
`rowIter s` (the A-stream) and, in the B-stream, a pointwise larger copy,
plus the base entry `1`. -/
theorem rowIter_sum_double (s : Nat) :
    2 * (rowIter s).sum + 1 ≤ (rowIter (s + 1)).sum := by
  have hz : (rowIter s).sum
      ≤ (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)).sum :=
    sum_zipWith_ge _ _ (rowIter_succ_length_ge s)
  conv_rhs => rw [rowIter_succ_rep s]
  rw [List.sum_cons, smerge_sum]
  omega

/-- `2 f_S + 1 ≤ f_{S+1}` for `S ≥ 2`. -/
theorem fRow_double : ∀ p, 2 ≤ p → 2 * fRow p + 1 ≤ fRow (p + 1) := by
  intro p hp
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 2 := ⟨p - 2, by omega⟩
  have h := rowIter_sum_double s
  show 2 * (1 + 2 * (rowIter s).sum) + 1 ≤ 1 + 2 * (rowIter (s + 1)).sum
  omega

/-- **`Σ_{i=1}^{S} f_i ≤ 2 f_S`.**  The geometric doubling makes the
partial sums of `f` comparable to their last term, so the right endpoint
`2 Σ_{i≤S} f_i` has the same growth rate as `f_S` itself. -/
theorem sumF_le_two_mul : ∀ (S : Nat), 1 ≤ S → sumF S ≤ 2 * fRow S := by
  intro S
  induction S with
  | zero => intro h; omega
  | succ S ih =>
      intro _
      rcases Nat.lt_or_ge S 2 with hS | hS
      · interval_cases S
        · decide
        · decide
      · have hprev := ih (by omega)
        have hd := fRow_double S hS
        rw [sumF_succ]
        omega

-- ==================================================================
-- 4.  The geometric lower bound at the left endpoint
-- ==================================================================

/-- `T = 2H` at the left endpoint. -/
theorem gameT_left_eq (r : Nat) :
    gameT (2 ^ (r + 2)) (r + 3) = 2 * gameH (2 ^ (r + 2)) (r + 3) := by
  have hone : (1:Nat) ≤ 2 ^ (r + 2) := Nat.one_le_two_pow
  have hpow : (2:Nat) ^ (r + 3) = 2 ^ (r + 2) * 2 := Nat.pow_succ 2 (r + 2)
  have hle : 2 ^ (r + 2) ≤ 2 ^ (r + 3) - 1 := by omega
  have hcomp : CompleteIn (2 ^ (r + 2)) (r + 3) :=
    completeIn_of_le (r + 3) (2 ^ (r + 2)) (by omega) hone hle
  have hex : ∃ t, CompleteInAt (2 ^ (r + 2)) (r + 3) t :=
    ⟨_, completeInAt_gameT hcomp⟩
  rw [RevPebbling.HalfReach.gameT_eq_two_mul_gameH hex, ← gameH_bridge_eq hone]

/-- **THE LEFT ENDPOINT, analytic half.**  Every admissible parameter
quadruple of `DispersionReal.dispersion_real` gives the left endpoint the
geometric lower bound with base `2·(2/λ)^{1/q}` — the same base
`DispersionRealGrowth.c_ge_real` gives to `f_S`. -/
theorem gameH_left_ge (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 < q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) (r : ℕ) (hr : 1 ≤ r) :
    (2 * M * lam) ^ (-q⁻¹) * (2 * (2 / lam) ^ q⁻¹) ^ r
      ≤ (gameH (2 ^ (r + 2)) (r + 3) : ℝ) := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  show (2 * M * lam) ^ (-q⁻¹) * (2 * (2 / lam) ^ q⁻¹) ^ (p + 1)
      ≤ (gameH (2 ^ (p + 3)) (p + 4) : ℝ)
  have hMpos : (0:ℝ) < M := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hden : (0:ℝ) < 2 * M * lam := by positivity
  have hbase : (0:ℝ) < 2 / lam := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 / lam) ^ (p + 1) / (2 * M * lam) := ⟨_, rfl⟩
  have hA0 : (0:ℝ) < A := by rw [hA]; positivity
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = A ^ q⁻¹ := ⟨_, rfl⟩
  have hV0 : (0:ℝ) < V := by rw [hVdef]; exact Real.rpow_pos_of_pos hA0 _
  -- `V^q = A`, and `M·A·λ^{p+2} = 2^p`: the threshold is chosen so that the
  -- dispersion bound cuts the count down to half the prefix length.
  have hVq : V ^ q = A := by
    rw [hVdef, ← Real.rpow_mul (le_of_lt hA0), inv_mul_cancel₀ (ne_of_gt hq),
      Real.rpow_one]
  have hval : M * A * lam ^ (p + 2) = 2 ^ p := by
    rw [hA, div_pow]
    field_simp
    ring
  have hdisp := RevPebbling.DispersionReal.dispersion_real M q lam th hM (le_of_lt hq)
    hlam hth0 hth1 hstep (p + 2) ⌊V⌋₊
  have hfl : ((⌊V⌋₊ : ℕ) : ℝ) ≤ V := Nat.floor_le (le_of_lt hV0)
  have hmono : ((⌊V⌋₊ : ℕ) : ℝ) ^ q ≤ V ^ q :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfl (le_of_lt hq)
  have hlamp : (0:ℝ) < lam ^ (p + 2) := by positivity
  have hchain : (countLe (rowIter (p + 2)) ⌊V⌋₊ : ℝ) ≤ (2:ℝ) ^ p := by
    have hphi : RevPebbling.DispersionReal.Phi M q ⌊V⌋₊
        = M * ((⌊V⌋₊ : ℕ) : ℝ) ^ q := rfl
    have h1 : M * ((⌊V⌋₊ : ℕ) : ℝ) ^ q ≤ M * V ^ q :=
      mul_le_mul_of_nonneg_left hmono (le_of_lt hMpos)
    have h2 : M * ((⌊V⌋₊ : ℕ) : ℝ) ^ q * lam ^ (p + 2) ≤ M * V ^ q * lam ^ (p + 2) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hlamp)
    rw [hphi] at hdisp
    rw [hVq] at h2
    rw [← hval]
    linarith
  have hcountNat : countLe (rowIter (p + 2)) ⌊V⌋₊ ≤ 2 ^ p := by
    have hc : ((countLe (rowIter (p + 2)) ⌊V⌋₊ : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by
      push_cast
      exact hchain
    exact_mod_cast hc
  -- half the prefix is above the threshold, so the prefix cost is at least
  -- `2^{p+1}·(⌊V⌋+1)`
  have hk : 2 ^ (p + 1) ≤ 2 ^ (p + 2 + 1) - 1 := by
    have h1 : (2:Nat) ^ (p + 2 + 1) = 2 ^ (p + 1) * 4 := by ring
    have h2 : (1:Nat) ≤ 2 ^ (p + 1) := Nat.one_le_two_pow
    omega
  have hpre := fpre_ge_of_countLe (p + 2) (2 ^ (p + 1)) ⌊V⌋₊ hk
  have hsub : 2 ^ p ≤ 2 ^ (p + 1) - countLe (rowIter (p + 2)) ⌊V⌋₊ := by
    have h1 : (2:Nat) ^ (p + 1) = 2 ^ p * 2 := Nat.pow_succ 2 p
    omega
  have hmul : 2 ^ p * (⌊V⌋₊ + 1)
      ≤ (2 ^ (p + 1) - countLe (rowIter (p + 2)) ⌊V⌋₊) * (⌊V⌋₊ + 1) :=
    Nat.mul_le_mul_right _ hsub
  have hleft := fpre_le_gameH_left (p + 1)
  simp only [show p + 1 + 1 = p + 2 by omega, show p + 1 + 2 = p + 3 by omega,
    show p + 1 + 3 = p + 4 by omega] at hleft
  have hNat : 2 * (2 ^ p * (⌊V⌋₊ + 1)) ≤ gameH (2 ^ (p + 3)) (p + 4) := by omega
  -- cast to the reals
  have hcast : (2:ℝ) * ((2:ℝ) ^ p * (((⌊V⌋₊ : ℕ) : ℝ) + 1))
      ≤ (gameH (2 ^ (p + 3)) (p + 4) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hNat
    push_cast at this
    linarith
  have hfloor : V < ((⌊V⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one V
  have h2p : (0:ℝ) < (2:ℝ) ^ (p + 1) := by positivity
  have hstepV : (2:ℝ) ^ (p + 1) * V ≤ (gameH (2 ^ (p + 3)) (p + 4) : ℝ) := by
    have h1 : (2:ℝ) ^ (p + 1) * V
        ≤ (2:ℝ) ^ (p + 1) * (((⌊V⌋₊ : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hfloor) (le_of_lt h2p)
    have h2 : (2:ℝ) ^ (p + 1) * (((⌊V⌋₊ : ℕ) : ℝ) + 1)
        = 2 * ((2:ℝ) ^ p * (((⌊V⌋₊ : ℕ) : ℝ) + 1)) := by ring
    linarith [h1, hcast, h2.le, h2.ge]
  -- and identify the constant
  have hVsplit : V = ((2 / lam) ^ q⁻¹) ^ (p + 1) * (2 * M * lam) ^ (-q⁻¹) := by
    rw [hVdef, hA]
    exact RevPebbling.DispersionRealGrowth.rpow_pow_div (le_of_lt hbase) hden (p + 1) q⁻¹
  have hgoal : (2 * M * lam) ^ (-q⁻¹) * (2 * (2 / lam) ^ q⁻¹) ^ (p + 1)
      = (2:ℝ) ^ (p + 1) * V := by
    rw [hVsplit, mul_pow]
    ring
  rw [hgoal]
  exact hstepV

/-- Every number below `c` is below the base of some admissible
quadruple: the supremum of the bases **is** `c`
(`Final.c_eq_two_rpow_kappaStar`). -/
theorem exists_admissible_gt {y : ℝ} (hy : y < RevPebbling.BlockSim.c) :
    ∃ M q lam th : ℝ, 1 ≤ M ∧ 0 < q ∧ 1 ≤ lam ∧ 0 ≤ th ∧ th < 1 ∧
      (1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) ∧
      y < 2 * (2 / lam) ^ q⁻¹ := by
  -- (i) a root value `x ∈ Vset` with `y < 2^{1+x}`
  obtain ⟨x, hxmem, hxy⟩ : ∃ x ∈ RevPebbling.Final.Vset, y < (2:ℝ) ^ (1 + x) := by
    rcases lt_or_ge 0 y with hy0 | hy0
    swap
    · obtain ⟨x, hx⟩ := RevPebbling.Final.Vset_nonempty
      exact ⟨x, hx, lt_of_le_of_lt hy0 (Real.rpow_pos_of_pos (by norm_num) _)⟩
    · have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hyval : (2:ℝ) ^ (Real.log y / Real.log 2) = y :=
        RevPebbling.MarginAnchors.two_rpow_log_div_log hy0
      have hcval : (2:ℝ) ^ (Real.log RevPebbling.BlockSim.c / Real.log 2)
          = RevPebbling.BlockSim.c :=
        RevPebbling.MarginAnchors.two_rpow_log_div_log RevPebbling.Final.c_pos
      have hexp : Real.log y / Real.log 2
          < Real.log RevPebbling.BlockSim.c / Real.log 2 := by
        rcases lt_or_ge (Real.log y / Real.log 2)
            (Real.log RevPebbling.BlockSim.c / Real.log 2) with h | h
        · exact h
        · exfalso
          have hle := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h
          rw [hyval, hcval] at hle
          linarith
      have hlogc : Real.log RevPebbling.BlockSim.c
          = (1 + RevPebbling.Final.kappaStar) * Real.log 2 := by
        rw [RevPebbling.Final.c_eq_two_rpow_kappaStar, Real.log_rpow (by norm_num)]
      have hsimp : ((1 + RevPebbling.Final.kappaStar) * Real.log 2) / Real.log 2
          = 1 + RevPebbling.Final.kappaStar := by
        field_simp
      rw [hlogc, hsimp] at hexp
      have hks : Real.log y / Real.log 2 - 1 < RevPebbling.Final.kappaStar := by linarith
      obtain ⟨x, hxmem, hxgt⟩ :=
        exists_lt_of_lt_csSup RevPebbling.Final.Vset_nonempty hks
      refine ⟨x, hxmem, ?_⟩
      calc y = (2:ℝ) ^ (Real.log y / Real.log 2) := hyval.symm
        _ < (2:ℝ) ^ (1 + x) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  -- (ii) unpack the root
  obtain ⟨q, ρ, hq, hρ, hg, rfl⟩ := hxmem
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hL : (1:ℝ) ≤ ρ ^ q := RevPebbling.CriticalRoot.one_le_rpow hq hρ
  have hLpos : (0:ℝ) < ρ ^ q := by linarith
  have hbound : (2:ℝ) ^ (1 + (1 / q - Real.log ρ / Real.log 2))
      = 2 * (2 / ρ ^ q) ^ q⁻¹ :=
    (RevPebbling.Final.two_rpow_one_add_V hρ0).trans
      (RevPebbling.CriticalRoot.bound_eq hq hρ0).symm
  rw [hbound] at hxy
  -- (iii) push `λ` slightly above the critical value, keeping `y` below the bound
  have hcontb : ContinuousAt (fun z : ℝ => (2:ℝ) / z) (ρ ^ q) :=
    continuousAt_const.div continuousAt_id (ne_of_gt hLpos)
  have hcont : ContinuousAt (fun z : ℝ => (2:ℝ) * ((2:ℝ) / z) ^ q⁻¹) (ρ ^ q) :=
    ContinuousAt.mul continuousAt_const
      (hcontb.rpow_const (Or.inr (le_of_lt (inv_pos.mpr hq))))
  have hseq : Tendsto (fun n : ℕ => ρ ^ q + 1 / ((n : ℝ) + 1)) atTop (𝓝 (ρ ^ q)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => ρ ^ q) atTop (𝓝 (ρ ^ q)) := tendsto_const_nhds
    simpa using hc.add h0
  have hlim := hcont.tendsto.comp hseq
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds hxy)).exists
  -- (iv) the admissible quadruple at that `λ`
  have hgap : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hlamgt : ρ ^ q < ρ ^ q + 1 / ((n : ℝ) + 1) := by linarith
  have hMpos : (0:ℝ) < 1 + ρ ^ q / (1 / ((n : ℝ) + 1)) := by positivity
  have hMbig : 1 / (1 + ρ ^ q / ((ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q))
      ≤ ((ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q) / ρ ^ q := by
    have hsimp : (ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q = 1 / ((n : ℝ) + 1) := by ring
    rw [hsimp, div_le_div_iff₀ hMpos hLpos]
    have hexp : 1 / ((n : ℝ) + 1) * (1 + ρ ^ q / (1 / ((n : ℝ) + 1)))
        = 1 / ((n : ℝ) + 1) + ρ ^ q := by
      field_simp
    rw [hexp]
    linarith
  have hMone : (1:ℝ) ≤ 1 + ρ ^ q / ((ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q) := by
    have hsimp : (ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q = 1 / ((n : ℝ) + 1) := by ring
    rw [hsimp]
    have : (0:ℝ) ≤ ρ ^ q / (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  refine ⟨1 + ρ ^ q / ((ρ ^ q + 1 / ((n : ℝ) + 1)) - ρ ^ q), q,
    ρ ^ q + 1 / ((n : ℝ) + 1), 1 / (1 + ρ), hMone, hq, by linarith, by positivity, ?_, ?_, hn⟩
  · rw [div_lt_one (by linarith)]; linarith
  · exact RevPebbling.CriticalRoot.hstep_of_root hq hρ hg hlamgt hMbig

/-- **THE LEFT ENDPOINT.**  Below `c`, every geometric sequence is
eventually dominated by `T(2^{S−1}, S)`. -/
theorem eventually_pow_le_gameT_left {y : ℝ} (hy0 : 0 < y)
    (hy : y < RevPebbling.BlockSim.c) :
    ∀ᶠ r : ℕ in atTop, y ^ r ≤ (gameT (2 ^ (r + 2)) (r + 3) : ℝ) := by
  obtain ⟨M, q, lam, th, hM, hq, hlam, hth0, hth1, hstep, hylt⟩ := exists_admissible_gt hy
  have hlam0 : (0:ℝ) < lam := by linarith
  have hMpos : (0:ℝ) < M := by linarith
  have hB0 : (0:ℝ) < 2 * (2 / lam) ^ q⁻¹ := by positivity
  have hK0 : (0:ℝ) < (2 * M * lam) ^ (-q⁻¹) := Real.rpow_pos_of_pos (by positivity) _
  have hratio : y / (2 * (2 / lam) ^ q⁻¹) < 1 := by
    rw [div_lt_one hB0]; exact hylt
  have hrat0 : (0:ℝ) ≤ y / (2 * (2 / lam) ^ q⁻¹) := by positivity
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hrat0 hratio
  have hev : ∀ᶠ r : ℕ in atTop, (y / (2 * (2 / lam) ^ q⁻¹)) ^ r
      ≤ (2 * M * lam) ^ (-q⁻¹) :=
    (htend.eventually (eventually_lt_nhds hK0)).mono fun r h => le_of_lt h
  filter_upwards [hev, eventually_ge_atTop 1] with r hr1 hr2
  have hBr : (0:ℝ) < (2 * (2 / lam) ^ q⁻¹) ^ r := by positivity
  have hstep1 : y ^ r
      = (y / (2 * (2 / lam) ^ q⁻¹)) ^ r * (2 * (2 / lam) ^ q⁻¹) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hstep2 : (y / (2 * (2 / lam) ^ q⁻¹)) ^ r * (2 * (2 / lam) ^ q⁻¹) ^ r
      ≤ (2 * M * lam) ^ (-q⁻¹) * (2 * (2 / lam) ^ q⁻¹) ^ r :=
    mul_le_mul_of_nonneg_right hr1 (le_of_lt hBr)
  have hstep3 := gameH_left_ge M q lam th hM hq hlam hth0 hth1 hstep r hr2
  have hT := gameT_left_eq r
  have hHnn : (0:ℝ) ≤ (gameH (2 ^ (r + 2)) (r + 3) : ℝ) := Nat.cast_nonneg _
  have hTcast : (gameH (2 ^ (r + 2)) (r + 3) : ℝ) ≤ (gameT (2 ^ (r + 2)) (r + 3) : ℝ) := by
    rw [hT]
    push_cast
    linarith
  linarith

-- ==================================================================
-- 5.  The minimal-space interval
-- ==================================================================

theorem one_le_Smin {n : Nat} (hn : 1 ≤ n) : 1 ≤ Smin n := by
  rcases Nat.eq_zero_or_pos (Smin n) with h | h
  · exfalso
    have hb := (Smin_spec hn).1
    rw [h] at hb
    have : (2:Nat) ^ 0 - 1 = 0 := rfl
    omega
  · exact h

theorem two_pow_Smin_sub_one_le {n : Nat} (hn : 1 ≤ n) : 2 ^ (Smin n - 1) ≤ n := by
  have h1 := one_le_Smin hn
  rcases Nat.lt_or_ge (Smin n) 2 with h | h
  · have hS : Smin n = 1 := by omega
    rw [hS]
    simpa using hn
  · rcases Nat.lt_or_ge n (2 ^ (Smin n - 1)) with hcon | hok
    · exfalso
      have hle : n ≤ 2 ^ (Smin n - 1) - 1 := by omega
      have := (Smin_spec hn).2 (Smin n - 1) (by omega) hle
      omega
    · exact hok

theorem tendsto_Smin : Tendsto Smin atTop atTop := by
  refine tendsto_atTop_atTop.2 ?_
  intro N
  refine ⟨2 ^ N, fun n hn => ?_⟩
  have h2N : (1:Nat) ≤ 2 ^ N := Nat.one_le_two_pow
  have hn1 : 1 ≤ n := by omega
  have hle := (Smin_spec hn1).1
  have hpos : (1:Nat) ≤ 2 ^ Smin n := Nat.one_le_two_pow
  rcases Nat.lt_or_ge (Smin n) N with hcon | hok
  · exfalso
    have : (2:Nat) ^ Smin n ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · exact hok

theorem three_le_Smin {n : Nat} (hn : 4 ≤ n) : 3 ≤ Smin n := by
  have hn1 : 1 ≤ n := by omega
  have hb := (Smin_spec hn1).1
  rcases Nat.lt_or_ge (Smin n) 3 with h | h
  · exfalso
    have h4 : (2:Nat) ^ Smin n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : (2:Nat) ^ 2 = 4 := rfl
    omega
  · exact h

/-- The left endpoint of the interval is below every point of it. -/
theorem gameT_left_le {n : Nat} (hn : 4 ≤ n) :
    gameT (2 ^ (Smin n - 1)) (Smin n) ≤ gameT n (Smin n) := by
  have hn1 : 1 ≤ n := by omega
  have hb := (Smin_spec hn1).1
  have hlow := two_pow_Smin_sub_one_le hn1
  have hc : CompleteIn n (Smin n) :=
    completeIn_of_le (Smin n) n (one_le_Smin hn1) hn1 hb
  exact gameT_mono_len Nat.one_le_two_pow hlow hc

/-- The right endpoint bounds the whole interval from above, and
`Σ_{i≤S} f_i ≤ 2 f_S`. -/
theorem gameT_Smin_le {n : Nat} (hn : 1 ≤ n) : gameT n (Smin n) ≤ 4 * fRow (Smin n) := by
  have h1 := one_le_Smin hn
  have hb := (Smin_spec hn).1
  have hone : (1:Nat) ≤ 2 ^ Smin n := Nat.one_le_two_pow
  have hc : CompleteIn (2 ^ Smin n - 1) (Smin n) :=
    completeIn_of_le (Smin n) (2 ^ Smin n - 1) h1 (by omega) (Nat.le_refl _)
  have hmono : gameT n (Smin n) ≤ gameT (2 ^ Smin n - 1) (Smin n) :=
    gameT_mono_len hn hb hc
  rw [gameT_full h1] at hmono
  have hsum := sumF_le_two_mul (Smin n) h1
  omega

theorem two_le_gameT_Smin {n : Nat} (hn : 4 ≤ n) : 2 ≤ gameT n (Smin n) := by
  have h3 := three_le_Smin hn
  obtain ⟨r, hr⟩ : ∃ r, Smin n = r + 3 := ⟨Smin n - 3, by omega⟩
  have hle := gameT_left_le hn
  rw [show Smin n - 1 = r + 2 by omega, hr] at hle
  rw [hr]
  rw [gameT_left_eq r] at hle
  have hfp := fpre_le_gameH_left r
  have hFpos : 1 ≤ Fpre (rowIter (r + 1)) (2 ^ r + 1) := by
    show 1 ≤ 1 + 2 * _
    omega
  omega

/-- `(S−1)·log 2 ≤ log n < S·log 2` on the minimal-space interval. -/
theorem log_n_bounds {n : Nat} (hn : 4 ≤ n) :
    ((Smin n : ℝ) - 1) * Real.log 2 ≤ Real.log n ∧
      Real.log n < (Smin n : ℝ) * Real.log 2 := by
  have hn1 : 1 ≤ n := by omega
  have h3 := three_le_Smin hn
  have hlow := two_pow_Smin_sub_one_le hn1
  have hb := (Smin_spec hn1).1
  have hone : (1:Nat) ≤ 2 ^ Smin n := Nat.one_le_two_pow
  have hcastsub : ((Smin n - 1 : ℕ) : ℝ) = (Smin n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ Smin n)]
    ring
  constructor
  · have hR : ((2 ^ (Smin n - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlow
    have h0 : (0:ℝ) < ((2 ^ (Smin n - 1) : ℕ) : ℝ) := by
      have : (1:Nat) ≤ 2 ^ (Smin n - 1) := Nat.one_le_two_pow
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hlg := Real.log_le_log h0 hR
    rw [Nat.cast_pow, Real.log_pow, hcastsub] at hlg
    simpa using hlg
  · have hlt : n < 2 ^ Smin n := by omega
    have hR : (n : ℝ) < ((2 ^ Smin n : ℕ) : ℝ) := by exact_mod_cast hlt
    have h0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlg := Real.log_lt_log h0 hR
    rw [Nat.cast_pow, Real.log_pow] at hlg
    simpa using hlg

/-- **THE RATE TRANSFER.**  `T(n, S_min(n)) = n^{log₂ c + o(1)}`: the
exponent of the complete-computation cost at the minimal budget
converges to `log₂ c`, uniformly over each minimal-space interval. -/
theorem tendsto_log_gameT_Smin :
    Tendsto (fun n : ℕ => Real.log (gameT n (Smin n)) / Real.log n) atTop
      (𝓝 (Real.log RevPebbling.BlockSim.c / Real.log 2)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc1 : (1:ℝ) < RevPebbling.BlockSim.c := by
    have h := RevPebbling.BlockSim.c_ge_2_51706472
    norm_num at h
    linarith
  have hLpos : 0 < Real.log RevPebbling.BlockSim.c / Real.log 2 :=
    div_pos (Real.log_pos hc1) hlog2
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- ## the lower half
    intro a ha
    obtain ⟨a', ha1, ha2⟩ : ∃ a' : ℝ, max a 0 < a' ∧
        a' < Real.log RevPebbling.BlockSim.c / Real.log 2 := by
      have hmx : max a 0 < Real.log RevPebbling.BlockSim.c / Real.log 2 :=
        max_lt ha hLpos
      exact ⟨(max a 0 + Real.log RevPebbling.BlockSim.c / Real.log 2) / 2,
        by linarith, by linarith⟩
    have ha0 : 0 < a' := lt_of_le_of_lt (le_max_right a 0) ha1
    have haa : a < a' := lt_of_le_of_lt (le_max_left a 0) ha1
    have hy0 : (0:ℝ) < (2:ℝ) ^ a' := Real.rpow_pos_of_pos (by norm_num) _
    have hyc : (2:ℝ) ^ a' < RevPebbling.BlockSim.c := by
      have hcval : (2:ℝ) ^ (Real.log RevPebbling.BlockSim.c / Real.log 2)
          = RevPebbling.BlockSim.c :=
        RevPebbling.MarginAnchors.two_rpow_log_div_log (by linarith)
      calc (2:ℝ) ^ a'
          < (2:ℝ) ^ (Real.log RevPebbling.BlockSim.c / Real.log 2) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ha2
        _ = RevPebbling.BlockSim.c := hcval
    have hev := eventually_pow_le_gameT_left hy0 hyc
    have hsm : Tendsto (fun n : ℕ => Smin n - 3) atTop atTop :=
      (Filter.tendsto_sub_atTop_nat 3).comp tendsto_Smin
    have hev2 := hsm.eventually hev
    -- `S·(a′ − a) > 3a′` eventually
    have hbig : ∀ᶠ n : ℕ in atTop, 3 * a' < (Smin n : ℝ) * (a' - a) := by
      have hd : (0:ℝ) < a' - a := by linarith
      have hmul : Tendsto (fun S : ℕ => (S : ℝ) * (a' - a)) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hd tendsto_natCast_atTop_atTop
      exact tendsto_Smin.eventually (hmul.eventually (eventually_gt_atTop (3 * a')))
    filter_upwards [hev2, hbig, eventually_ge_atTop 4] with n hpow hSbig hn4
    have h3 := three_le_Smin hn4
    have hn1 : 1 ≤ n := by omega
    obtain ⟨r, hr⟩ : ∃ r, Smin n = r + 3 := ⟨Smin n - 3, by omega⟩
    have hrn : Smin n - 3 = r := by omega
    rw [hrn] at hpow
    -- the left endpoint dominates
    have hle := gameT_left_le hn4
    rw [show Smin n - 1 = r + 2 by omega, hr] at hle
    have hlecast : ((gameT (2 ^ (r + 2)) (r + 3) : ℕ) : ℝ)
        ≤ ((gameT n (Smin n) : ℕ) : ℝ) := by
      rw [hr]
      exact_mod_cast hle
    have hchain : ((2:ℝ) ^ a') ^ r ≤ ((gameT n (Smin n) : ℕ) : ℝ) := le_trans hpow hlecast
    -- take logarithms
    have hTpos : (0:ℝ) < ((gameT n (Smin n) : ℕ) : ℝ) := by
      have := two_le_gameT_Smin hn4
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (by omega)
    have hyr : (0:ℝ) < ((2:ℝ) ^ a') ^ r := by positivity
    have hlogle : Real.log (((2:ℝ) ^ a') ^ r) ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ) :=
      Real.log_le_log hyr hchain
    have hlogy : Real.log ((2:ℝ) ^ a') = a' * Real.log 2 :=
      Real.log_rpow (by norm_num : (0:ℝ) < 2) a'
    rw [Real.log_pow, hlogy] at hlogle
    -- and divide
    obtain ⟨hlo, hhi⟩ := log_n_bounds hn4
    have hlogn0 : (0:ℝ) < Real.log n := by
      have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have := Real.log_le_log (by norm_num) h2
      linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
    have hSpos : (0:ℝ) < (Smin n : ℝ) := by
      have : (3:ℝ) ≤ (Smin n : ℝ) := by exact_mod_cast h3
      linarith
    have hrcast : ((r : ℕ) : ℝ) = (Smin n : ℝ) - 3 := by
      have : (Smin n : ℝ) = (r : ℝ) + 3 := by exact_mod_cast hr
      linarith
    have hnum : 0 ≤ (r : ℝ) * (a' * Real.log 2) := by positivity
    have hstep1 : (r : ℝ) * (a' * Real.log 2) / ((Smin n : ℝ) * Real.log 2)
        ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ) / Real.log n := by
      have hd1 : (r : ℝ) * (a' * Real.log 2) / ((Smin n : ℝ) * Real.log 2)
          ≤ (r : ℝ) * (a' * Real.log 2) / Real.log n := by
        apply div_le_div_of_nonneg_left hnum hlogn0
        linarith
      have hd2 : (r : ℝ) * (a' * Real.log 2) / Real.log n
          ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ) / Real.log n := by
        have hsub0 : 0 ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ)
            - (r : ℝ) * (a' * Real.log 2) := by linarith
        have := div_nonneg hsub0 (le_of_lt hlogn0)
        rw [sub_div] at this
        linarith
      linarith
    have hval : (r : ℝ) * (a' * Real.log 2) / ((Smin n : ℝ) * Real.log 2)
        = a' * ((Smin n : ℝ) - 3) / (Smin n : ℝ) := by
      rw [hrcast]
      field_simp
    have hgt : a < a' * ((Smin n : ℝ) - 3) / (Smin n : ℝ) := by
      rw [lt_div_iff₀ hSpos]
      nlinarith [hSbig]
    rw [hval] at hstep1
    linarith
  · -- ## the upper half
    intro b hb
    have hgrow := RevPebbling.GrowthRate.tendsto_logSeq
      RevPebbling.BlockSim.submult_fRow RevPebbling.GrowthClosedForm.pos_fRow
    have hg : Tendsto (fun k : ℕ =>
        Real.log (4 * (fRow (k + 1) : ℝ)) / ((k : ℝ) * Real.log 2)) atTop
        (𝓝 (Real.log RevPebbling.BlockSim.c / Real.log 2)) := by
      have hden : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
        Filter.Tendsto.atTop_mul_const hlog2 tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun k : ℕ => Real.log 4 / ((k : ℝ) * Real.log 2)) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds hden
      have h2 : Tendsto (fun k : ℕ =>
          (RevPebbling.GrowthRate.logSeq fRow k / (k : ℝ)) / Real.log 2) atTop
          (𝓝 (Real.log RevPebbling.BlockSim.c / Real.log 2)) := hgrow.div_const _
      have hsum := h1.add h2
      rw [zero_add] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hf : (0:ℝ) < (fRow (k + 1) : ℝ) := by
        have := fRow_pos (k + 1)
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have hk0 : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hlogmul : Real.log (4 * (fRow (k + 1) : ℝ))
          = Real.log 4 + Real.log (fRow (k + 1) : ℝ) :=
        Real.log_mul (by norm_num) (ne_of_gt hf)
      show Real.log 4 / ((k : ℝ) * Real.log 2)
          + (RevPebbling.GrowthRate.logSeq fRow k / (k : ℝ)) / Real.log 2
          = Real.log (4 * (fRow (k + 1) : ℝ)) / ((k : ℝ) * Real.log 2)
      rw [hlogmul]
      show _ + (Real.log (fRow (k + 1) : ℝ) / (k : ℝ)) / Real.log 2 = _
      field_simp
    have hgb := hg.eventually (eventually_lt_nhds hb)
    have hsm : Tendsto (fun n : ℕ => Smin n - 1) atTop atTop :=
      (Filter.tendsto_sub_atTop_nat 1).comp tendsto_Smin
    filter_upwards [hsm.eventually hgb, eventually_ge_atTop 4] with n hgn hn4
    have h3 := three_le_Smin hn4
    have hn1 : 1 ≤ n := by omega
    have hkS : Smin n - 1 + 1 = Smin n := by omega
    rw [hkS] at hgn
    have hcastsub : ((Smin n - 1 : ℕ) : ℝ) = (Smin n : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ Smin n)]
      ring
    rw [hcastsub] at hgn
    -- the pointwise bound
    obtain ⟨hlo, hhi⟩ := log_n_bounds hn4
    have hT2 := two_le_gameT_Smin hn4
    have hTpos : (0:ℝ) < ((gameT n (Smin n) : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (by omega)
    have hTle : ((gameT n (Smin n) : ℕ) : ℝ) ≤ 4 * (fRow (Smin n) : ℝ) := by
      have := gameT_Smin_le hn1
      exact_mod_cast this
    have hlogle : Real.log ((gameT n (Smin n) : ℕ) : ℝ)
        ≤ Real.log (4 * (fRow (Smin n) : ℝ)) := Real.log_le_log hTpos hTle
    have hlogT0 : 0 ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ) := by
      have h2 : (1:ℝ) ≤ ((gameT n (Smin n) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ gameT n (Smin n))
      exact Real.log_nonneg h2
    have hSm1 : (0:ℝ) < (Smin n : ℝ) - 1 := by
      have : (3:ℝ) ≤ (Smin n : ℝ) := by exact_mod_cast h3
      linarith
    have hden0 : (0:ℝ) < ((Smin n : ℝ) - 1) * Real.log 2 := by positivity
    have hlogn0 : (0:ℝ) < Real.log n := lt_of_lt_of_le hden0 hlo
    have hd1 : Real.log ((gameT n (Smin n) : ℕ) : ℝ) / Real.log n
        ≤ Real.log ((gameT n (Smin n) : ℕ) : ℝ) / (((Smin n : ℝ) - 1) * Real.log 2) :=
      div_le_div_of_nonneg_left hlogT0 hden0 hlo
    have hd2 : Real.log ((gameT n (Smin n) : ℕ) : ℝ) / (((Smin n : ℝ) - 1) * Real.log 2)
        ≤ Real.log (4 * (fRow (Smin n) : ℝ)) / (((Smin n : ℝ) - 1) * Real.log 2) := by
      have hsub0 : 0 ≤ Real.log (4 * (fRow (Smin n) : ℝ))
          - Real.log ((gameT n (Smin n) : ℕ) : ℝ) := by linarith
      have := div_nonneg hsub0 (le_of_lt hden0)
      rw [sub_div] at this
      linarith
    linarith

-- ==================================================================
-- Numerical consistency checks
-- ==================================================================

/-- The capacity is one short of the left endpoint, which is what makes
the pigeonhole fire. -/
example : ((List.range 6).all fun r =>
    decide (cap (r + 3) (2 ^ r) = 2 ^ (r + 2) - 1)) = true := by decide

/-- The right endpoint values `H(2^S − 1, S) = Σ_{i≤S} f_i`. -/
example : sumF 1 = 1 ∧ sumF 2 = 4 ∧ sumF 3 = 13 ∧ sumF 4 = 38 ∧
    sumF 5 = 109 ∧ sumF 6 = 302 := by decide

/-- The pigeonhole bound sits below the right endpoint, as it must
(`F(2^r+1, r+3) ≤ H(2^{r+2}, r+3) ≤ H(2^{r+3}−1, r+3) = Σ_{i≤r+3} f_i`).
The left-hand values are `5, 9, 23, 53` for `r = 1,2,3,4`. -/
example : Fpre (rowIter 2) (2 ^ 1 + 1) = 5 ∧ Fpre (rowIter 3) (2 ^ 2 + 1) = 9 ∧
    Fpre (rowIter 4) (2 ^ 3 + 1) = 23 ∧ Fpre (rowIter 5) (2 ^ 4 + 1) = 53 := by decide

example : ((List.range 4).all fun r =>
    decide (Fpre (rowIter (r + 2)) (2 ^ (r + 1) + 1) ≤ sumF (r + 4))) = true := by decide

end RevPebbling.RateTransferLow
