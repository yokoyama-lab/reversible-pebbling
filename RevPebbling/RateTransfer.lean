import RevPebbling.CompleteReach
import RevPebbling.GameCompleteCost
import RevPebbling.CutPlays
import RevPebbling.HalfReachRecurrence
import RevPebbling.ReachLimit

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

end RevPebbling.RateTransfer
