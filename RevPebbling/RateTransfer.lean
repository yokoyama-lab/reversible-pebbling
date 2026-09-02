import RevPebbling.CompleteReach
import RevPebbling.GameCompleteCost
import RevPebbling.CutPlays

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
open RevPebbling.CutPlays

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

end RevPebbling.RateTransfer
