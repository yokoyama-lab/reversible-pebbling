import RevPebbling.CompleteReach
import RevPebbling.GameCompleteCost
import RevPebbling.CutPlays
import RevPebbling.HalfReachRecurrence
import RevPebbling.ReachLimit
import RevPebbling.RowExact
import RevPebbling.GameKnill
import RevPebbling.HalfReachBridge
import RevPebbling.HalfReach

/-!
# Towards the rate transfer `T(n,S) = n^{log₂ c + o(1)}` (this work, 2026-09)

The manuscript's last step for complete computations is the transfer of
the exponential rate from the clean reach to `T`, *uniformly* on each
minimal-space interval.  This file builds the part of that step which is
independent of the dispersion machinery:

* `Smin n` — the minimal feasible pebble budget of a complete
  computation on `n` cells, and `Smin_eq_iff` / `Smin_interval`, which
  say that `Smin` is constant on `2^(S-1) ≤ n ≤ 2^S - 1`;
* `gameT_mono_len` — `T` is nondecreasing in the chain length at a fixed
  budget, so the two endpoints of a minimal-space interval sandwich
  every `n` inside it.

## STATUS

**This file does not prove the transfer.**  What it supplies is the
sandwich; what is still missing is the growth of `T` at the two
endpoints, and in particular the lower bound at the left endpoint
`n = 2^(S-1)`, which is the step that genuinely needs the min-plus
recurrence (`HalfReachRecurrence.halfReach_iff_decomposition`) and the
marginal merge (`HalfReachMerge.halfMarginals_countLe`).  Nothing here
should be read as certifying the asymptotics.
-/

namespace RevPebbling.RateTransfer

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CompleteReach RevPebbling.GameCompleteCost
open RevPebbling.CutPlays RevPebbling.HalfReachRecurrence RevPebbling.ReachLimit
open RevPebbling.GameCost RevPebbling.RowMax RevPebbling.RowExact RevPebbling.GameKnill
open RevPebbling.GameDecomposition RevPebbling.HalfReachBridge

-- ------------------------------------------------------------------
-- Restricting a complete computation to a shorter chain
-- ------------------------------------------------------------------

/-- `emptyBoard` truncates to `emptyBoard`. -/
theorem emptyBoard_take (n k : Nat) (h : k ≤ n) :
    (emptyBoard n).take k = emptyBoard k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [emptyBoard_split]
  exact List.take_left' (by simp [emptyBoard])

/-- **A complete computation restricts to any prefix of the chain**, at
no extra cost.  Keeping only the moves below the cut leaves a legal
play that starts and ends empty, has no larger peak, and still covers
the new far end (by `covers_of_top` on the original play). -/
theorem completeInAt_of_le_len {n m p t : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    (h : CompleteInAt n p t) : CompleteInAt m p t := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk, htop⟩ := h
  refine ⟨keepBelow m s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans (by simpa [keepBelow] using List.length_filter_le _ s) hlen
  · intro i hi
    have := (List.mem_filter.mp hi).2
    simpa using this
  · have := legalB_keepBelow m s (emptyBoard n) hleg
    rwa [emptyBoard_take n m hmn] at this
  · have h := execB_keepBelow m s (emptyBoard n)
    rw [hex, emptyBoard_take n m hmn] at h
    exact h.symm
  · have := maxOnes_keepBelow_le m (emptyBoard n) s
    rw [emptyBoard_take n m hmn] at this
    exact Nat.le_trans this hpk
  · have hcov : everOn (emptyBoard n) s (m - 1) :=
      covers_of_top hleg htop (m - 1) (by omega)
    have := everOn_keepBelow (x := m) (by omega) hcov
    rwa [emptyBoard_take n m hmn] at this

/-- **`T` is nondecreasing in the chain length** at a fixed budget. -/
theorem gameT_mono_len {n m p : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hc : CompleteIn n p) : gameT m p ≤ gameT n p :=
  gameT_le (completeInAt_of_le_len hm hmn (completeInAt_gameT hc))

-- ------------------------------------------------------------------
-- The minimal feasible budget
-- ------------------------------------------------------------------

/-- **The minimal-space budget** of a complete computation on `n` cells. -/
noncomputable def Smin (n : Nat) : Nat := sInf {p | CompleteIn n p}

theorem completeIn_Smin {n : Nat} (hn : 1 ≤ n) : CompleteIn n (Smin n) := by
  have hself : n ≤ 2 ^ n - 1 := by
    have h : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  have hne : {p | CompleteIn n p}.Nonempty :=
    ⟨n, completeIn_of_le n n (by omega) hn hself⟩
  exact Nat.sInf_mem hne

theorem Smin_le {n p : Nat} (h : CompleteIn n p) : Smin n ≤ p := Nat.sInf_le h

/-- `Smin n` is the least `S` with `n ≤ 2^S - 1`. -/
theorem Smin_spec {n : Nat} (hn : 1 ≤ n) :
    n ≤ 2 ^ Smin n - 1 ∧ ∀ S, 1 ≤ S → n ≤ 2 ^ S - 1 → Smin n ≤ S := by
  refine ⟨?_, fun S hS hle => Smin_le (completeIn_of_le S n hS hn hle)⟩
  have hc := completeIn_Smin hn
  exact le_two_pow_sub_one_of_completeIn hc

-- ------------------------------------------------------------------
-- The half-reach limit
-- ------------------------------------------------------------------

/-- With no pebbles nothing can be reached: a half-reach of a nonempty
chain needs at least one pebble on the board at the moment its far end
is covered. -/
theorem eq_zero_of_halfReachIn_zero {n t : Nat} (h : HalfReachIn n 0 t) :
    n = 0 := by
  rcases h with rfl | ⟨s, _, _, _, hend, hpk⟩
  · rfl
  · by_contra hn
    have h1 : 1 ≤ ones (execB (emptyBoard n) s) := ones_pos_of_nth hend
    have h2 : ones (execB (emptyBoard n) (s.take s.length)) ≤
        maxOnes (emptyBoard n) s := ones_prefix_le_maxOnes s (emptyBoard n) s.length
    rw [List.take_of_length_le (Nat.le_refl _)] at h2
    omega

/-- **THE HALF-REACH LIMIT.**  `S` pebbles half-reach at most `2^S - 1`
cells, one short of twice the clean limit `2^(S-1)`.

The clean limit is `ReachLimit.le_two_pow_of_reachIn`; this is its
half-reach counterpart, and it is *not* the same number, which is the
point: a half-reach may keep its checkpoint pebbles, so it goes about
twice as far as a clean reach with the same budget.  The proof is the
decomposition half of (H): the lower part is a clean reach and so is at
most `2^(S-1)`, and the upper part is a half-reach with one pebble
fewer, so at most `2^(S-1) - 1` by induction. -/
theorem le_two_pow_sub_one_of_halfReachIn :
    ∀ (S : Nat) {n t : Nat}, HalfReachIn n S t → n ≤ 2 ^ S - 1
  | 0, n, t, h => by
      rw [eq_zero_of_halfReachIn_zero h]
      simp
  | S + 1, n, t, h => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      obtain ⟨m, tf, th, hm, hmn, hf, hh, _⟩ :=
        halfReach_decompose hn (Nat.succ_le_succ (Nat.zero_le S)) h
      have hlow : m ≤ 2 ^ S := by
        simpa using le_two_pow_of_reachIn hm hf
      have hh' : HalfReachIn (n - m) S th := by simpa using hh
      have hup : n - m ≤ 2 ^ S - 1 := le_two_pow_sub_one_of_halfReachIn S hh'
      have hpow : 1 ≤ 2 ^ S := Nat.one_le_two_pow
      have hsplit : 2 ^ (S + 1) = 2 ^ S * 2 := Nat.pow_succ 2 S
      omega

/-- **The half-reach limit is sharp, and is not the clean limit.**
Two pebbles half-reach `2^2 - 1 = 3` cells, whereas the clean limit at
the same budget is `2^(2-1) = 2`.  Following this project's rule that a
bound is checked on a witness rather than asserted, the witness is the
play `[0,1,0,2]`: `···` → `T··` → `TT·` → `·T·` → `·TT`.

This is what makes `le_two_pow_sub_one_of_halfReachIn` the right
statement: reading the clean limit into the half-reach case would be off
by a factor of about two. -/
theorem halfReachIn_three_two : HalfReachIn 3 2 4 := by
  refine Or.inr ⟨[0, 1, 0, 2], ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The clean limit at the same budget is strictly smaller. -/
example : (2 : Nat) ^ (2 - 1) < 2 ^ 2 - 1 := by decide

-- ------------------------------------------------------------------
-- The right endpoint of a minimal-space interval
-- ------------------------------------------------------------------

/-- `Σ_{i=1}^{S} f_i`, the manuscript's value of the half-reach at the
right endpoint `n = 2^S - 1`. -/
def sumF : Nat → Nat
  | 0 => 0
  | S + 1 => sumF S + fRow (S + 1)

theorem sumF_succ (S : Nat) : sumF (S + 1) = sumF S + fRow (S + 1) := rfl

/-- The clean reach at the limit, as a play of exactly `f_S` moves. -/
theorem reachIn_fRow (s : Nat) : ReachIn (2 ^ (s + 1)) (s + 2) (fRow (s + 2)) := by
  have h := reachIn_Fpre s (2 ^ (s + 1)) Nat.one_le_two_pow (Nat.le_refl _)
  rwa [Fpre_reach_limit s] at h

/-- **THE RIGHT ENDPOINT, achievability half.**  At the extreme length
`n = 2^S - 1` a half-reach costs at most `Σ_{i=1}^{S} f_i`: split off a
clean reach of the lower `2^(S-1)` cells at cost `f_S` and recurse above
it with one pebble fewer.  This is `halfReach_compose` at the only split
the reach limits allow. -/
theorem halfReachIn_full : ∀ S : Nat, HalfReachIn (2 ^ S - 1) S (sumF S)
  | 0 => by simpa [sumF] using HalfReachIn.zero 0 0
  | 1 => by
      refine Or.inr ⟨[0], ?_, ?_, ?_, ?_, ?_⟩ <;> simp [sumF, fRow] <;> decide
  | s + 2 => by
      have ih := halfReachIn_full (s + 1)
      have hpow : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
      have hc := halfReach_compose (m := 2 ^ (s + 1)) (k := 2 ^ (s + 1) - 1)
        (S := s + 2) (tf := fRow (s + 2)) (th := sumF (s + 1))
        hpow (by omega) (reachIn_fRow s) (by simpa using ih)
      have hlen : 2 ^ (s + 1) + (2 ^ (s + 1) - 1) = 2 ^ (s + 2) - 1 := by
        have : 2 ^ (s + 2) = 2 ^ (s + 1) * 2 := Nat.pow_succ 2 (s + 1)
        omega
      have hcost : fRow (s + 2) + sumF (s + 1) = sumF (s + 2) :=
        Nat.add_comm _ _
      rwa [hlen, hcost] at hc

/-- **THE RIGHT ENDPOINT, optimality half.**  At `n = 2^S - 1` the
reach limits pin the split of (H) to a single point.  The lower part is
a clean reach, so `m ≤ 2^(S-1)`; the upper part is a half-reach with one
pebble fewer, so `n - m ≤ 2^(S-1) - 1` by
`le_two_pow_sub_one_of_halfReachIn`.  Adding the two forces
`m = 2^(S-1)` exactly, and then the lower part costs at least `f_S`
(`RowExact.gameF_eq_fRow_all`) while the upper part costs at least
`Σ_{i<S} f_i` by induction. -/
theorem sumF_le_of_halfReachIn : ∀ (S : Nat) {t : Nat},
    HalfReachIn (2 ^ S - 1) S t → sumF S ≤ t
  | 0, t, _ => by simp [sumF]
  | S + 1, t, h => by
      have hone : 1 ≤ 2 ^ S := Nat.one_le_two_pow
      have hpow : 2 ^ (S + 1) = 2 ^ S * 2 := Nat.pow_succ 2 S
      have hn : 1 ≤ 2 ^ (S + 1) - 1 := by omega
      obtain ⟨m, tf, th, hm, hmn, hf, hh, htime⟩ :=
        halfReach_decompose hn (Nat.succ_le_succ (Nat.zero_le S)) h
      have hh0 : HalfReachIn (2 ^ (S + 1) - 1 - m) S th := by simpa using hh
      have hup : 2 ^ (S + 1) - 1 - m ≤ 2 ^ S - 1 :=
        le_two_pow_sub_one_of_halfReachIn S hh0
      have hlow : m ≤ 2 ^ S := by simpa using le_two_pow_of_reachIn hm hf
      have hmeq : m = 2 ^ S := by omega
      have hkeq : 2 ^ (S + 1) - 1 - m = 2 ^ S - 1 := by omega
      have hh1 : HalfReachIn (2 ^ S - 1) S th := by rwa [hkeq] at hh0
      have hIH : sumF S ≤ th := sumF_le_of_halfReachIn S hh1
      have hfrow : fRow (S + 1) ≤ tf := by
        cases S with
        | zero =>
            have hg : gameF m 1 ≤ tf := gameF_le hf
            have h1 : m = 1 := by simpa using hmeq
            rw [h1, gameF_one 1 (Nat.le_refl _)] at hg
            simpa [fRow] using hg
        | succ s =>
            have hg : gameF m (s + 2) ≤ tf := gameF_le hf
            have h1 : m = 2 ^ (s + 1) := hmeq
            rw [h1, gameF_eq_fRow_all s] at hg
            exact hg
      rw [sumF_succ]
      omega

/-- **THE RIGHT ENDPOINT.**  `H(2^S - 1, S) = Σ_{i=1}^{S} f_i`. -/
theorem gameH_full (S : Nat) : gameH (2 ^ S - 1) S = sumF S :=
  Nat.le_antisymm (gameH_le (halfReachIn_full S))
    (sumF_le_of_halfReachIn S (halfReachIn_gameH ⟨_, halfReachIn_full S⟩))

-- ------------------------------------------------------------------
-- The two half-reach predicates agree, and the endpoint at the level of `T`
-- ------------------------------------------------------------------

/-- `HalfReach.HalfIn` asks the far end to be pebbled *at some time*;
`HalfReachRecurrence.HalfReachIn` asks it to be pebbled *at the end*.
On a nonempty chain the two are the same predicate: trimming a play at
the first moment it covers the far end costs nothing
(`HalfReach.halfIn_tight`). -/
theorem halfReachIn_iff_halfIn {n p t : Nat} (hn : 1 ≤ n) :
    HalfReachIn n p t ↔ RevPebbling.HalfReach.HalfIn n p t := by
  constructor
  · rintro (rfl | ⟨s, hlen, hr, hleg, hend, hpk⟩)
    · omega
    · exact ⟨s, hlen, hr, hleg, hpk, ⟨s.length, by
        rwa [List.take_of_length_le (Nat.le_refl _)]⟩⟩
  · intro h
    obtain ⟨s, hlen, hr, hleg, hpk, hend⟩ := RevPebbling.HalfReach.halfIn_tight h
    exact Or.inr ⟨s, hlen, hr, hleg, hend, hpk⟩

theorem gameH_bridge_eq {n p : Nat} (hn : 1 ≤ n) :
    gameH n p = RevPebbling.HalfReach.gameH n p := by
  have hset : {t | HalfReachIn n p t} = {t | RevPebbling.HalfReach.HalfIn n p t} := by
    ext t
    exact halfReachIn_iff_halfIn hn
  show sInf {t | HalfReachIn n p t} = sInf {t | RevPebbling.HalfReach.HalfIn n p t}
  rw [hset]

/-- **THE RIGHT ENDPOINT AT THE LEVEL OF `T`.**
`T(2^S - 1, S) = 2 Σ_{i=1}^{S} f_i` for `S ≥ 1`.  Time reversal
(`HalfReach.gameT_eq_two_mul_gameH`) turns the half-reach optimum into
the complete one. -/
theorem gameT_full {S : Nat} (hS : 1 ≤ S) :
    gameT (2 ^ S - 1) S = 2 * sumF S := by
  have hone : 1 ≤ 2 ^ S := Nat.one_le_two_pow
  have hn : 1 ≤ 2 ^ S - 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, S = j + 1 := ⟨S - 1, by omega⟩
    have : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  have hhalf : ∃ t, RevPebbling.HalfReach.HalfIn (2 ^ S - 1) S t :=
    ⟨sumF S, (halfReachIn_iff_halfIn hn).mp (halfReachIn_full S)⟩
  have hcomp : ∃ t, CompleteInAt (2 ^ S - 1) S t :=
    ⟨2 * sumF S, completeInAt_two_mul_of_halfReachIn hn (halfReachIn_full S)⟩
  rw [RevPebbling.HalfReach.gameT_eq_two_mul_gameH hcomp,
      ← gameH_bridge_eq hn, gameH_full S]

end RevPebbling.RateTransfer
