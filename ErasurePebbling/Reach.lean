import ErasurePebbling.Sweep

/-!
# Theorem B1: `reach(p, e) ≥ (e + 2)·2^(p−2)` (RC-02 §5)

Bennett's binary schedule (`RevPebbling.PebblingFoundations.bin`,
correct by `bennett_general`) reaches cell `2^(p−1) − 1` from the empty
board with peak `p`.  From a board carrying a single pebble on cell
`x ≥ 1`, the schedule lifted to `x + 1` climbs `2^(p−2)` further cells
with `p − 1` pebbles on top of the stone `x` (peak `p`), after which the
stone is erased – irreversibly, since cell `x − 1` is empty.  Repeating
the second phase `e` times reaches `2^(p−1) + e·2^(p−2) = (e+2)·2^(p−2)`.
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-- Every move of `bin base k` lies in `[base, base + 2^k)`. -/
theorem bin_mem : ∀ (k base i : Nat), i ∈ bin base k → base ≤ i ∧ i < base + 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro base i h
      simp [bin] at h
      subst h; simp
  | succ k ih =>
      intro base i h
      simp only [bin, List.mem_append, List.mem_reverse] at h
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      rcases h with h | h | h
      · have := ih base i h; omega
      · have := ih (base + 2 ^ k) i h; omega
      · have := ih base i h; omega

theorem set_empty_eq_blk (n x : Nat) (hx : x < n) : (empty n).set x true = blk n x 1 n := by
  apply List.ext_getElem?
  intro i
  unfold blk
  rw [getElem?_mk, empty, List.getElem?_set, List.getElem?_replicate, List.length_replicate]
  by_cases h : x = i
  · subst h; simp [hx]
  · rw [if_neg h]
    split <;> simp <;> omega

theorem set_blk_eq_blk (n x y : Nat) (hy : y < n) : (blk n x 1 n).set y true = blk n x 1 y := by
  apply List.ext_getElem?
  intro i
  unfold blk
  rw [getElem?_mk, List.getElem?_set, getElem?_mk, length_mk]
  by_cases h : y = i
  · subst h; simp [hy]
  · rw [if_neg h]
    split
    · have hin : ¬ i = n := by omega
      simp [hin, Ne.symm h]
    · rfl

/-- Phase 0: Bennett from the empty board to a single pebble on cell `2^(p−1) − 1`. -/
theorem bennett_seg (n p : Nat) (hp : 1 ≤ p) (hn : 2 ^ (p - 1) ≤ n) :
    Seg n (empty n) (blk n (2 ^ (p - 1) - 1) 1 n) p 0 (bin 0 (p - 1)).length (bin 0 (p - 1)) := by
  have h := bennett_general (p - 1) 0 (empty n) (by rw [length_empty]; omega) (Or.inl rfl)
    (fun j _ _ => nth_empty n j)
  have hpos : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  refine ⟨legalE_of_legalB _ _ h.1, ?_, ?_, erasures_of_legalB _ _ h.1, rfl, ?_⟩
  · rw [h.2.1, Nat.zero_add, set_empty_eq_blk n _ (by omega)]
  · have := h.2.2; rw [ones_empty] at this; omega
  · intro i hi
    have := bin_mem (p - 1) 0 i hi
    omega

/-- One erasure phase: from a stone on `x ≥ 1`, climb `2^(p−2)` cells with the
lifted Bennett schedule and erase the stone. -/
theorem phase_seg (n p x : Nat) (hp : 2 ≤ p) (hx : 1 ≤ x) (hn : x + 2 ^ (p - 2) < n) :
    Seg n (blk n x 1 n) (blk n (x + 2 ^ (p - 2)) 1 n) p 1
      ((bin (x + 1) (p - 2)).length + 1) (bin (x + 1) (p - 2) ++ [x]) := by
  have hq : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  have hxn : x < n := by omega
  have h := bennett_general (p - 2) (x + 1) (blk n x 1 n) (by rw [length_blk]; omega)
    (Or.inr (by simp only [Nat.add_sub_cancel]; rw [nth_blk _ _ _ hxn]; simp))
    (fun j hj1 hj2 => by
      rw [nth_blk _ _ _ (by omega)]
      simp; omega)
  have hones : ones (blk n x 1 n) ≤ 1 := ones_blk_le_of_ge n x 1 n (Nat.le_refl _)
  have e1 : x + 1 + 2 ^ (p - 2) - 1 = x + 2 ^ (p - 2) := by omega
  have h1 : Seg n (blk n x 1 n) (blk n x 1 (x + 2 ^ (p - 2))) p 0 (bin (x + 1) (p - 2)).length
      (bin (x + 1) (p - 2)) := by
    refine ⟨legalE_of_legalB _ _ h.1, ?_, ?_, erasures_of_legalB _ _ h.1, rfl, ?_⟩
    · rw [h.2.1, e1, set_blk_eq_blk n x _ hn]
    · have hp2 : p - 2 + 1 + 1 = p := by omega
      refine Nat.le_trans h.2.2 ?_
      omega
    · intro i hi
      have := bin_mem (p - 2) (x + 1) i hi
      omega
  have h2 := (erase_step n x (x + 2 ^ (p - 2)) hx (by omega) hn).peak_mono
    (q' := p) (by omega)
  exact h1.append h2

/-- `e` phases in a row. -/
theorem phases_seg (n p : Nat) (hp : 2 ≤ p) : ∀ (e x : Nat), 1 ≤ x → x + e * 2 ^ (p - 2) < n →
    ∃ l t, Seg n (blk n x 1 n) (blk n (x + e * 2 ^ (p - 2)) 1 n) p e l t := by
  intro e
  induction e with
  | zero =>
      intro x hx hn
      refine ⟨0, [], ?_⟩
      simp only [Nat.zero_mul, Nat.add_zero]
      exact Seg.nil (Nat.le_trans (ones_blk_le_of_ge n x 1 n (Nat.le_refl _)) (by omega))
  | succ e ih =>
      intro x hx hn
      have hq : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
      have em : (e + 1) * 2 ^ (p - 2) = e * 2 ^ (p - 2) + 2 ^ (p - 2) := Nat.succ_mul e _
      rw [em] at hn
      have hstep := phase_seg n p x hp hx (by omega)
      obtain ⟨l, t, ht⟩ := ih (x + 2 ^ (p - 2)) (by omega) (by omega)
      have e2 : x + 2 ^ (p - 2) + e * 2 ^ (p - 2) = x + (e + 1) * 2 ^ (p - 2) := by
        rw [em]; omega
      rw [e2] at ht
      have := hstep.append ht
      rw [Nat.add_comm 1 e] at this
      exact ⟨_, _, this⟩

/-- **Theorem B1.**  For `p ≥ 2` the chain of length `(e + 2)·2^(p−2)` admits a
clean plan with peak `p` and `e` irreversible removals. -/
theorem theoremB1 (p e : Nat) (hp : 2 ≤ p) : Reachable ((e + 2) * 2 ^ (p - 2)) p e := by
  have hpos : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  have hpow : 2 ^ (p - 1) = 2 ^ (p - 2) + 2 ^ (p - 2) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have hmul : (e + 2) * 2 ^ (p - 2) = e * 2 ^ (p - 2) + 2 ^ (p - 2) + 2 ^ (p - 2) := by
    rw [Nat.add_mul]; omega
  have hn1 : 2 ^ (p - 1) ≤ (e + 2) * 2 ^ (p - 2) := by rw [hpow, hmul]; omega
  have h0 := bennett_seg _ p (by omega) hn1
  have hx : 1 ≤ 2 ^ (p - 1) - 1 := by rw [hpow]; omega
  have hend : 2 ^ (p - 1) - 1 + e * 2 ^ (p - 2) = (e + 2) * 2 ^ (p - 2) - 1 := by
    rw [hpow, hmul]; omega
  obtain ⟨l, t, ht⟩ := phases_seg ((e + 2) * 2 ^ (p - 2)) p hp e (2 ^ (p - 1) - 1) hx
    (by rw [hend, hmul]; omega)
  rw [hend] at ht
  have h := h0.append ht
  have h' := h.cast (blk_single_eq_target _ (by rw [hmul]; omega))
  exact ⟨_, ⟨h'.bounds, h'.legal, h'.peak, by rw [h'.eras, Nat.zero_add]; exact Nat.le_refl _, h'.exec⟩⟩

end ErasurePebbling
