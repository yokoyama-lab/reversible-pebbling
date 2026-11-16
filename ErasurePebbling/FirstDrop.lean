import ErasurePebbling.Sweep
import ErasurePebbling.Saturation
import ErasurePebbling.Compression

/-!
# The first drop is exactly two moves

`drop_threshold` (`Conjectures.lean`) shows that at `n = (p−1)(e+1)+2` the
budget `e+1` attains the floor `2n−1` while every plan with budget `e` is
strictly longer.  Here the strict inequality is made exact:

* `length_odd`: every clean plan has an odd number of moves (each cell but
  the last is toggled an even number of times, the last an odd number);
* `drop_construction`: for `p ≥ 3` there is a plan with budget `e` and
  exactly `2n+1` moves – reach cell `p` (0-indexed) with `2p+3` moves and no
  erasure by holding cell `1` as a stepping stone, then sweep in blocks of
  `p−1` with one erasure each (`sweep_spec`);
* `first_drop`: `M*(n,p,e) = 2n+1` and `M*(n,p,e+1) = 2n−1`.

As a corollary the whole table for `p = 3` is closed
(`mstar_p3_floor`, `mstar_p3_drop`, `unreachable_p3`), and for `p = 2` the
reachable range is exactly the floor range (`mstar_p2`).

(Paper proof: the 2026-11-11 notes `消去ペブリング_最初の短縮点の厳密落差2`
and `消去ペブリング_小空間全域分類と課金最適性`; this file is their
machine-checked version.)
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-! ## Parity of the length -/

theorem rsum_count_mod_two (n : Nat) (s : List Nat)
    (hpar : ∀ j, j < n → (s.count j % 2 = 1 ↔ j = n - 1)) :
    ∀ k, k ≤ n → rsum k (fun j => s.count j) % 2 = (if k = n ∧ 0 < n then 1 else 0) := by
  intro k
  induction k with
  | zero => intro _; simp [rsum]; omega
  | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hkn : ¬ (k = n ∧ 0 < n) := by omega
      rw [if_neg hkn] at h1
      have h2 := hpar k (by omega)
      simp only [rsum]
      by_cases hl : k = n - 1
      · have hc : s.count k % 2 = 1 := h2.mpr hl
        rw [if_pos (by omega)]
        omega
      · have hc : s.count k % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (s.count k) with h | h
          · exact h
          · exact absurd (h2.mp h) hl
        rw [if_neg (by omega)]
        omega

/-- **Parity.**  Every clean plan has an odd number of moves. -/
theorem length_odd (n p e : Nat) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s) :
    s.length % 2 = 1 := by
  have hpar : ∀ j, j < n → (s.count j % 2 = 1 ↔ j = n - 1) := by
    intro j hj
    have := nth_execB_parity s (empty n) j (by rw [length_empty]; exact hj)
    rw [h.final, nth_target n j hn, nth_empty] at this
    have h' : decide (j = n - 1) = decide (s.count j % 2 = 1) := by simpa using this
    simpa using h'.symm
  have := rsum_count_mod_two n s hpar n (Nat.le_refl _)
  rw [rsum_count n s h.bounds, if_pos ⟨rfl, by omega⟩] at this
  exact this

/-! ## The construction -/

/-- Placing cell `0` under a stone on cell `1` (with a further stone on `t`). -/
theorem place_bottom_step (n t q : Nat) (ht : 1 < t) (hn : t < n) (hq : 3 ≤ q) :
    Seg n (blk n 1 1 t) (blk n 0 2 t) q 0 1 [0] := by
  have h0 : 0 < n := by omega
  have hok : okMove (blk n 1 1 t) 0 = true := by simp [okMove]
  have htog : toggle (blk n 1 1 t) 0 = blk n 0 2 t := by
    unfold blk
    rw [toggle_mk _ h0]
    apply mk_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    by_cases hi' : i = 0
    · subst hi'; simp; omega
    · simp [hi']; omega
  have h := Seg.single (n := n) (q := q) (okE_of_okMove hok)
    (Nat.le_trans (ones_blk_le n 1 1 t) (by omega))
    (by rw [htog]; exact Nat.le_trans (ones_blk_le n 0 2 t) (by omega)) h0
  rw [isErase_eq_false_of_okMove hok] at h
  simpa [htog] using h

/-- The opening for `p ≥ 3`: from the empty board to a single stone on cell `p`
with `2p + 3` moves, peak `p` and no erasure.  Cell `1` is held as a stepping
stone while cells `2, …, p` are climbed and descended, then cells `0, 1`
are cleared reversibly. -/
theorem opening_spec (n p : Nat) (hp : 3 ≤ p) (hn : p < n) :
    ∃ t, Seg n (empty n) (blk n p 1 n) p 0 (2 * p + 3) t := by
  -- +0, +1, −0 : a stone on cell 1
  obtain ⟨t1, h1⟩ := first_block_spec n 2 (by omega) (by omega)
  have h1' := h1.peak_mono (q' := p) (by omega)
  -- climb cells 2, …, p
  have h2 := (up_spec n 1 (p - 1) (by omega)).cast (blk_top n 1 (p - 1) (by omega))
  have e2 : p - 1 + 1 = p := by omega
  rw [e2] at h2
  have e3 : 1 + (p - 1) = p := by omega
  rw [e3] at h2
  -- descend cells p−1, …, 2 (the stone on p is the extra cell)
  have h3 := down_spec n 1 p (by omega) (p - 2) (by omega)
  have e4 : p - 2 + 1 = p - 1 := by omega
  have e5 : p - 2 + 2 = p := by omega
  rw [e4, e5] at h3
  -- +0, −1, −0
  have h4 := place_bottom_step n p p (by omega) hn hp
  have h5 := remove_top_step n 0 1 p p (by omega) (Nat.le_refl _) (by omega)
    (Nat.le_trans (ones_blk_le n 0 2 p) (by omega))
    (Nat.le_trans (ones_blk_le n 0 1 p) (by omega))
  have h5' : Seg n (blk n 0 2 p) (blk n 0 1 p) p 0 1 [1] := by simpa using h5
  have h6 := (remove_free_step n p (by omega) hn).peak_mono (q' := p) (by omega)
  have h := (((((h1'.append h2).append h3).append h4).append h5').append h6)
  have hl : 2 * 2 - 1 + (p - 1) + (p - 2) + 1 + 1 + 1 = 2 * p + 3 := by omega
  rw [hl] at h
  exact ⟨_, h.cast_src (by simp)⟩

/-- **Construction.**  For `p ≥ 3` and `n = (p−1)(e+1)+2` there is a clean plan
with peak `p`, at most `e` erasures and exactly `2n + 1` moves. -/
theorem drop_construction (p e : Nat) (hp : 3 ≤ p) :
    ∃ s, IsPlay ((p - 1) * (e + 1) + 2) p e s ∧
      s.length = 2 * ((p - 1) * (e + 1) + 2) + 1 := by
  have hpe : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := by rw [Nat.mul_add, Nat.mul_one]
  have hge : p < (p - 1) * (e + 1) + 2 := by omega
  obtain ⟨t1, h1⟩ := opening_spec ((p - 1) * (e + 1) + 2) p hp hge
  obtain ⟨t2, h2⟩ := sweep_spec ((p - 1) * (e + 1) + 2) p (by omega)
    ((p - 1) * e) p (by omega) (by omega)
  have h := (h1.append h2).cast (blk_single_eq_target _ (by omega))
  have he : 0 + ((p - 1) * e + p - 2) / (p - 1) = e := by
    have : (p - 1) * e + p - 2 = (p - 2) + (p - 1) * e := by omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  have hl : 2 * p + 3 + 2 * ((p - 1) * e) = 2 * ((p - 1) * (e + 1) + 2) + 1 := by
    rw [hpe]; omega
  rw [he, hl] at h
  exact ⟨_, ⟨h.bounds, h.legal, h.peak, Nat.le_of_eq h.eras, h.exec⟩, h.len⟩

/-! ## The exact drop -/

/-- **The first drop is exactly two.**  For `p ≥ 3` and `n = (p−1)(e+1)+2`:
`M*(n, p, e) = 2n + 1` and `M*(n, p, e+1) = 2n − 1`. -/
theorem first_drop (p e : Nat) (hp : 3 ≤ p) :
    MstarIs ((p - 1) * (e + 1) + 2) p e (2 * ((p - 1) * (e + 1) + 2) + 1) ∧
    MstarIs ((p - 1) * (e + 1) + 2) p (e + 1) (2 * ((p - 1) * (e + 1) + 2) - 1) := by
  obtain ⟨_, ⟨h3, h4⟩⟩ := drop_threshold p e (by omega)
  refine ⟨⟨drop_construction p e hp, ?_⟩, h3⟩
  intro s hs
  have hlt := h4 s hs
  have hodd := length_odd _ p e (by omega) s hs
  omega

/-! ## Corollary: the complete tables for `p = 2` and `p = 3` -/

/-- `p = 2`: the floor `2n − 1` is attained exactly on the reachable range
`n ≤ e + 2`; beyond it nothing is reachable. -/
theorem mstar_p2 (n e : Nat) (hn : 1 ≤ n) :
    (n ≤ e + 2 → MstarIs n 2 e (2 * n - 1)) ∧ (e + 2 < n → ¬ Reachable n 2 e) := by
  refine ⟨fun h => (theoremA n 2 e (Nat.le_refl _) hn).mpr ?_, fun h hr => ?_⟩
  · unfold estar; omega
  · have := Compression.reach_le 2 e (Nat.le_refl _) n hr
    simp at this
    omega

/-- `p = 3`, floor range: `M*(n, 3, e) = 2n − 1` for `n ≤ 2e + 3`. -/
theorem mstar_p3_floor (n e : Nat) (hn : 1 ≤ n) (h : n ≤ 2 * e + 3) :
    MstarIs n 3 e (2 * n - 1) :=
  (theoremA n 3 e (by omega) hn).mpr (by unfold estar; omega)

/-- `p = 3`, the last reachable cell: `M*(2e + 4, 3, e) = 2(2e + 4) + 1 = 4e + 9`. -/
theorem mstar_p3_drop (e : Nat) : MstarIs (2 * e + 4) 3 e (4 * e + 9) := by
  have h := (first_drop 3 e (Nat.le_refl _)).1
  have e1 : (3 - 1) * (e + 1) + 2 = 2 * e + 4 := by omega
  have e2 : 2 * (2 * e + 4) + 1 = 4 * e + 9 := by omega
  rw [e1, e2] at h
  exact h

/-- `p = 3`, beyond the reach `2e + 4`: unreachable. -/
theorem unreachable_p3 (n e : Nat) (h : 2 * e + 4 < n) : ¬ Reachable n 3 e := by
  intro hr
  have := Compression.reach_le 3 e (by omega) n hr
  have e1 : (e + 2) * 2 ^ (3 - 2) = 2 * e + 4 := by simp; omega
  omega

end ErasurePebbling
