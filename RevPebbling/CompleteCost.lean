import RevPebbling.GameStructure

/-!
# What a *complete* computation costs, in general (this work)

Several bounded checks of `PebblingTheory` are about Královič's variant
`T(n,p)`: a computation that starts and ends on the empty chain but
**covers** every cell on the way (`exact_complete_times`,
`kralovic_time_recurrence`, `bridge_linear_regime`,
`complete_can_beat_reach`).  The artifact has a general upper-bound tool
for that variant (`PebblingFoundations.complete_bound`, the middle-vertex
induction) but nothing general about its *cost*.

This file supplies the cost side, for every `n` and every peak:

* `two_mul_le_length_of_complete` — a complete computation that ever
  reaches the far end makes at least `2n` moves;
* `length_even_of_complete` — and its number of moves is even.

Both are the exact analogues of `GameLinearLower.two_mul_sub_one_le_length`
and `GameStructure.length_odd_of_reach` for the complete variant, and
they come from the same counting: every cell must be toggled, and here
*every* cell — the far end included — returns to empty, so every count is
even, hence at least two.

## The `T = F + 1` bridge

`PebblingTheory.bridge_linear_regime` checks `T(n,p) = F(n,p) + 1` on the
grid `p = 4, n = 1..7`.  On the part of that regime where the pebbles are
not the binding constraint — `n ≤ S`, Knill's Obs 2.2(i) range — both
sides are now general and exact:

* `GameLinearLower.gameF_linear` : `F(n,S) = 2n - 1`;
* `complete_linear` : the up-and-down walk `[0,…,n-1] ++ [n-1,…,0]` costs
  `2n`, covers the chain, keeps peak `n`, and **nothing shorter works**.

So `T(n,S) = F(n,S) + 1` for every `n` and every `S ≥ n`.  The checked
grid also covers `n = 5,6,7` at `p = 4`, which is *outside* `n ≤ S` and
outside what is proved here — there `F(n,4)` is no longer `2n - 1` and
the bridge, if it holds, needs a different argument.

-/

namespace RevPebbling.CompleteCost

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.GameLinearLower
open RevPebbling.GameStructure

/-- A cell that starts empty and is ever pebbled must be toggled. -/
theorem mem_of_everOn {n : Nat} {s : List Nat} {v : Nat}
    (h : everOn (emptyBoard n) s v) : v ∈ s := by
  by_contra hc
  obtain ⟨k, hk⟩ := h
  have hnot : v ∉ s.take k := fun hm => hc (List.mem_of_mem_take hm)
  rw [nth_exec_of_not_mem _ _ _ hnot, nth_emptyBoard] at hk
  exact Bool.noConfusion hk

/-- In a computation that returns to the empty chain, every cell is
toggled an even number of times. -/
theorem count_even_of_complete {n : Nat} {s : List Nat} (i : Nat) (hi : i < n)
    (hex : execB (emptyBoard n) s = emptyBoard n) : s.count i % 2 = 0 := by
  have hlen : i < (emptyBoard n).length := by rw [emptyBoard_length]; exact hi
  have hp := nth_execB_parity s (emptyBoard n) i hlen
  rw [hex] at hp
  simp only [nth_emptyBoard] at hp
  by_cases hc : s.count i % 2 = 1
  · rw [if_pos hc] at hp
    exact absurd hp (by simp)
  · omega

/-- **A COMPLETE COMPUTATION HAS EVEN LENGTH.** -/
theorem length_even_of_complete {n : Nat} {s : List Nat}
    (hr : ∀ i ∈ s, i < n) (hex : execB (emptyBoard n) s = emptyBoard n) :
    s.length % 2 = 0 := by
  have hself : s.filter (fun i => decide (i < n)) = s :=
    List.filter_eq_self.mpr (fun i hi => by simpa using hr i hi)
  have heven := length_filter_even s n
    (fun i hi => count_even_of_complete i hi hex)
  rwa [hself] at heven

/-- **A COMPLETE COMPUTATION COSTS AT LEAST `2n`.**  Any legal
computation that starts and ends on the empty chain of `n` cells and
ever pebbles the far end makes at least `2n` moves — whatever its peak.

Compare `GameLinearLower.two_mul_sub_one_le_length`: a computation that
merely *reaches* the far end and stops there saves exactly the one move
that would take the last pebble off. -/
theorem two_mul_le_length_of_complete {n : Nat} (hn : 1 ≤ n) {s : List Nat}
    (hr : ∀ i ∈ s, i < n) (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = emptyBoard n)
    (htop : everOn (emptyBoard n) s (n - 1)) :
    2 * n ≤ s.length := by
  have htopmem : (n - 1) ∈ s := mem_of_everOn htop
  -- every cell is toggled: nothing above an untoggled cell is ever legal
  have hall : ∀ i, i < n → i ∈ s := by
    intro i hi
    by_contra hc
    exact not_mem_above s n i hleg hc (n - 1 - i)
      (by rw [show i + (n - 1 - i) = n - 1 by omega]; exact htopmem)
  -- and evenly, hence at least twice
  have hcount : ∀ i, i < n → 2 ≤ s.count i := by
    intro i hi
    have heven := count_even_of_complete i hi hex
    have hpos : 1 ≤ s.count i := by
      rcases Nat.eq_zero_or_pos (s.count i) with h0 | hp
      · exact absurd (hall i hi) (List.count_eq_zero.mp h0)
      · exact hp
    omega
  have hself : s.filter (fun i => decide (i < n)) = s :=
    List.filter_eq_self.mpr (fun i hi => by simpa using hr i hi)
  have hlow := two_mul_le_length_filter s n hcount
  rwa [hself] at hlow

/-- **THE `T ≥ F + 1` HALF OF THE BRIDGE, in general.**  In the linear
regime (`n ≤ S`) the game optimum for reaching is exactly `2n - 1`, so
any complete computation costs at least one move more.  This is the
general, one-sided form of `PebblingTheory.bridge_linear_regime`. -/
theorem complete_ge_reach_succ {n S : Nat} (hn : 1 ≤ n) (hS : n ≤ S)
    {s : List Nat} (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = emptyBoard n)
    (htop : everOn (emptyBoard n) s (n - 1)) :
    gameF n S + 1 ≤ s.length := by
  have hg := gameF_linear hn hS
  have hc := two_mul_le_length_of_complete hn hr hleg hex htop
  omega

-- ------------------------------------------------------------------
-- The matching construction: the up-and-down walk
-- ------------------------------------------------------------------

/-- The board after the ascending walk has pebbled the first `k` cells
of a chain of `k + m`. -/
def walkBoard (k m : Nat) : Board :=
  List.replicate k true ++ List.replicate m false

theorem nth_walkBoard : ∀ (k m i : Nat), nth (walkBoard k m) i = decide (i < k)
  | 0, _, i => by simp [walkBoard, nth_replicate]
  | _ + 1, _, 0 => by simp [walkBoard, List.replicate_succ, nth]
  | k + 1, m, i + 1 => by
      have ih := nth_walkBoard k m i
      simp only [walkBoard, List.replicate_succ, List.cons_append] at ih ⊢
      simpa [nth] using ih

theorem set_walkBoard : ∀ (k m : Nat),
    (walkBoard k (m + 1)).set k true = walkBoard (k + 1) m
  | 0, m => by simp [walkBoard, List.replicate_succ]
  | k + 1, m => by
      have ih := set_walkBoard k m
      simp only [walkBoard, List.replicate_succ, List.cons_append,
        List.set_cons_succ] at ih ⊢
      rw [ih]

theorem ones_walkBoard : ∀ (k m : Nat), ones (walkBoard k m) = k
  | 0, m => by simp [walkBoard, ones_replicate]
  | k + 1, m => by
      have ih := ones_walkBoard k m
      simp only [walkBoard, List.replicate_succ, List.cons_append] at ih ⊢
      simp [ones, ih, List.count_cons] at *
      omega

/-- The ascending walk pebbles the cells from the bottom up. -/
theorem exec_range_walk (n : Nat) : ∀ k, k ≤ n →
    execB (emptyBoard n) (List.range k) = walkBoard k (n - k)
  | 0, _ => by simp [walkBoard, emptyBoard, execB]
  | k + 1, h => by
      have ih := exec_range_walk n k (by omega)
      rw [List.range_succ, exec_append, ih]
      have hk : nth (walkBoard k (n - k)) k = false := by
        rw [nth_walkBoard]; simp
      show toggle (walkBoard k (n - k)) k = walkBoard (k + 1) (n - (k + 1))
      unfold toggle
      rw [hk]
      simp only [Bool.not_false]
      have hm : n - k = (n - (k + 1)) + 1 := by omega
      rw [hm, set_walkBoard]

/-- …and it is legal: each move stands on the pebble the previous one
left. -/
theorem legal_range_walk (n : Nat) : ∀ k, k ≤ n →
    legalB (emptyBoard n) (List.range k) = true
  | 0, _ => rfl
  | k + 1, h => by
      have ih := legal_range_walk n k (by omega)
      rw [List.range_succ, legal_append, ih, exec_range_walk n k (by omega)]
      simp only [legalB, Bool.true_and, Bool.and_true, okMove, nth_walkBoard]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : k - 1 < k := by omega
        simp [this]

/-- The ascending walk never holds more than `n` pebbles. -/
theorem maxOnes_range_walk (n : Nat) :
    maxOnes (emptyBoard n) (List.range n) ≤ n := by
  refine maxOnes_le_of_prefixes _ _ n ?_
  intro j
  rw [List.take_range, exec_range_walk n (min j n) (Nat.min_le_right _ _),
      ones_walkBoard]
  omega

/-- **`2n` MOVES SUFFICE**, with `n` pebbles: walk up placing a pebble on
every cell, then walk back down taking them off.  Legality of the
descent, and the return to the empty chain, are
`PebblingFoundations.reverse_append_roundtrip`. -/
theorem complete_walk (n : Nat) :
    legalB (emptyBoard n) (List.range n ++ (List.range n).reverse) = true ∧
    execB (emptyBoard n) (List.range n ++ (List.range n).reverse)
      = emptyBoard n ∧
    maxOnes (emptyBoard n) (List.range n ++ (List.range n).reverse) ≤ n ∧
    (List.range n ++ (List.range n).reverse).length = 2 * n ∧
    (∀ v, v < n → everOn (emptyBoard n) (List.range n ++ (List.range n).reverse) v) := by
  obtain ⟨hleg, hex, hpk⟩ :=
    reverse_append_roundtrip (emptyBoard n) (List.range n)
      (legal_range_walk n n (Nat.le_refl _))
  refine ⟨hleg, hex, by rw [hpk]; exact maxOnes_range_walk n, by simp; omega, ?_⟩
  intro v hv
  refine ⟨v + 1, ?_⟩
  have htake : (List.range n ++ (List.range n).reverse).take (v + 1)
      = List.range (v + 1) := by
    rw [List.take_append_of_le_length (by simp; omega), List.take_range,
        Nat.min_eq_left (by omega)]
  rw [htake, exec_range_walk n (v + 1) (by omega), nth_walkBoard]
  simp

/-- **THE LINEAR REGIME OF THE COMPLETE VARIANT, EXACTLY.**  With at
least as many pebbles as cells, a complete computation covering the whole
chain costs exactly `2n` moves — the walk achieves it and
`two_mul_le_length_of_complete` forbids anything shorter.

Together with `GameLinearLower.gameF_linear` (`F(n,S) = 2n - 1`) this is
`PebblingTheory.bridge_linear_regime` — `T = F + 1` in the linear
regime — for every `n` and every `S ≥ n`, instead of the checked grid
`p = 4, n ≤ 7`. -/
theorem complete_linear (n : Nat) (hn : 1 ≤ n) :
    ∃ s : List Nat, (∀ i ∈ s, i < n) ∧
      legalB (emptyBoard n) s = true ∧
      execB (emptyBoard n) s = emptyBoard n ∧
      maxOnes (emptyBoard n) s ≤ n ∧
      (∀ v, v < n → everOn (emptyBoard n) s v) ∧
      s.length = 2 * n ∧
      (∀ t : List Nat, (∀ i ∈ t, i < n) →
        legalB (emptyBoard n) t = true →
        execB (emptyBoard n) t = emptyBoard n →
        everOn (emptyBoard n) t (n - 1) → s.length ≤ t.length) := by
  obtain ⟨hleg, hex, hpk, hlen, hcov⟩ := complete_walk n
  refine ⟨_, ?_, hleg, hex, hpk, hcov, hlen, ?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · simpa using List.mem_range.mp h
    · simpa using List.mem_range.mp (List.mem_reverse.mp h)
  · intro t hr hlegt hext htop
    rw [hlen]
    exact two_mul_le_length_of_complete hn hr hlegt hext htop

end RevPebbling.CompleteCost
