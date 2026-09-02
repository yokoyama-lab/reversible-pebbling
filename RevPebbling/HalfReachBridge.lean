import RevPebbling.GameCompleteCost
import RevPebbling.HalfReachRecurrence

/-!
# The exact constructive bridge from half-reach to completion

This file assigns a numerical optimum to `HalfReachIn` and proves, in
full generality, the paper's inequality `T(n,p) ≤ 2 H(n,p)`: append the
reverse of an optimal half-reach.  The proof uses no bounded search.
-/

namespace RevPebbling.HalfReachBridge

open RevPebbling.PebblingFoundations
open RevPebbling.HalfReachRecurrence
open RevPebbling.GameCompleteCost

/-- The least number of moves in a half-reach of the last cell. -/
noncomputable def gameH (n p : Nat) : Nat := sInf {t | HalfReachIn n p t}

theorem gameH_le {n p t : Nat} (h : HalfReachIn n p t) : gameH n p ≤ t :=
  Nat.sInf_le h

theorem halfReachIn_gameH {n p : Nat} (h : ∃ t, HalfReachIn n p t) :
    HalfReachIn n p (gameH n p) :=
  Nat.sInf_mem h

/-- Reversing a half-reach produces a complete computation of at most
twice the length and with the same pebble bound. -/
theorem completeInAt_two_mul_of_halfReachIn {n p t : Nat} (hn : 1 ≤ n)
    (h : HalfReachIn n p t) : CompleteInAt n p (2 * t) := by
  rcases h with hzero | ⟨s, hlen, hr, hleg, hend, hpk⟩
  · omega
  · obtain ⟨hlegal, hexec, hpeak, hcover⟩ :=
      roundtrip_complete n s (n - 1) hleg hend
    refine ⟨s ++ s.reverse, ?_, ?_, hlegal, hexec, ?_, ?_⟩
    · simp only [List.length_append, List.length_reverse]
      omega
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hr i hi
      · exact hr i (by simpa using hi)
    · simpa [RevPebbling.GameReach.emptyBoard] using hpeak.trans_le hpk
    · simpa [RevPebbling.GameReach.emptyBoard] using
        hcover (n - 1) (Nat.le_refl _)

/-- **THE CONSTRUCTIVE HALF-REACH/COMPLETE BRIDGE.**  Whenever a
half-reach is feasible, the optimal complete computation uses at most
twice as many moves. -/
theorem gameT_le_two_mul_gameH {n p : Nat} (hn : 1 ≤ n)
    (h : ∃ t, HalfReachIn n p t) : gameT n p ≤ 2 * gameH n p := by
  exact gameT_le (completeInAt_two_mul_of_halfReachIn hn (halfReachIn_gameH h))

end RevPebbling.HalfReachBridge
