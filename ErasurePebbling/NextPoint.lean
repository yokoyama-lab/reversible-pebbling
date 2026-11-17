import ErasurePebbling.Triangular

/-!
# One past the triangular frontier: two candidates

`Triangular.mstar_exact` settles `M*(n, p, e)` for `n ≤ T(p) + e·T(p−1)`.
At the next length `n = T(p) + e·T(p−1) + 1` (`p ≥ 4`) the contraction bound
gives `L₀ = 2n − 1 + 2(n − A)`; here a plan with `L₀ + 2` moves is built, so
by parity `M*(n, p, e) ∈ {L₀, L₀ + 2}`:

* `seed_p4`: a 25-move plan for `n = 8`, `p = 4`, `e = 0` (checked by `decide`);
* `lift`: a plan on `b` cells with peak `q` lifts to `a + b` cells with peak
  `q + 1` (`1 ≤ a ≤ q`), at the cost of `2(2a − 1)` moves – sweep to a stone
  on cell `a − 1`, run the plan above it, undo the sweep;
* `block`: an erasure block of `b ∈ [p−1, T(p−1)]` cells (`Triangular.tri_spec`
  above a held stone, then the stone is erased);
* `next_point`: `L₀ ≤ M*` and a plan with `L₀ + 2` moves exist; every plan
  has length `L₀` or at least `L₀ + 2`.  For `p = 4`, `n = 4e + 8`:
  `23 + 10e ≤ M* ≤ 25 + 10e` with `M* ≠ 24 + 10e` (`p4_endpoint`).

Whether `L₀` itself is attained is **not** decided here.

(Paper proof: the 2026-11-11 note `消去ペブリング_三角数次点2候補`;
this file is the machine-checked version of its upper bound.)
-/

namespace ErasurePebbling
namespace NextPoint

open RevPebbling.PebblingFoundations
open Triangular

/-- The 25-move seed (0-indexed form of the note's
`1,2,3,4,3,5,2,6,5,7,1,8,7,5,6,1,5,2,1,3,4,1,3,2,1`). -/
def seed : List Nat :=
  [0, 1, 2, 3, 2, 4, 1, 5, 4, 6, 0, 7, 6, 4, 5, 0, 4, 1, 0, 2, 3, 0, 2, 1, 0]

theorem seed_p4 : Seg 8 (empty 8) (target 8) 4 0 25 seed :=
  ⟨by decide, by decide, by decide, by decide, rfl, by decide⟩

/-- **Lift.**  A plan on `b ≥ 1` cells with peak `q` and no erasure becomes a
plan on `a + b` cells with peak `q + 1`, for `1 ≤ a ≤ q`. -/
theorem lift (q a b L : Nat) (t : List Nat) (ha1 : 1 ≤ a) (haq : a ≤ q) (hb : 1 ≤ b)
    (h2 : Seg b (empty b) (target b) q 0 L t) :
    ∃ t', Seg (a + b) (empty (a + b)) (target (a + b)) (q + 1) 0 (2 * (2 * a - 1) + L) t' := by
  have hn1 : 1 ≤ a + b := by omega
  obtain ⟨t1, h1⟩ := first_block_spec (a + b) a ha1 (by omega)
  have h2w := window_seg (x := a) (K := 1) (B := blk (a + b) (a - 1) 1 (a + b)) h2
    (length_empty _) (length_blk _ _ _ _) (by omega)
    (by intro i hi; rw [nth_blk _ _ _ (by omega), nth_empty]; simp; omega)
    (Or.inr (by rw [nth_blk _ _ _ (by omega)]; simp; try omega))
    (by rw [ones_empty]; exact ones_blk_le_of_ge (a + b) (a - 1) 1 (a + b) (Nat.le_refl _))
  have hb2' : mk (a + b) (fun j => if a ≤ j ∧ j < a + b then nth (target b) (j - a)
      else nth (blk (a + b) (a - 1) 1 (a + b)) j) = blk (a + b) (a - 1) 1 (a + b - 1) := by
    unfold blk
    apply mk_congr
    intro j hj
    split
    · rw [nth_target _ _ (by omega)]
      apply Bool.eq_iff_iff.mpr; simp; omega
    · rw [nth_mk_of_lt hj]
      apply Bool.eq_iff_iff.mpr; simp; omega
  have h2w' := h2w.cast hb2'
  obtain ⟨t3, h3⟩ := first_block_spec a a ha1 (Nat.le_refl _)
  have h3w := window_seg (x := 0) (K := 1) (B := blk (a + b) (a - 1) 1 (a + b - 1)) (Seg.reverse h3)
    (length_blk _ _ _ _) (length_blk _ _ _ _) (by omega)
    (by
      intro i hi
      rw [nth_blk _ _ _ (by omega), nth_blk _ _ _ (by omega)]
      apply Bool.eq_iff_iff.mpr; simp; omega)
    (Or.inl rfl)
    (by
      have hc1 : 1 ≤ ones (blk a (a - 1) 1 a) := by
        unfold blk; rw [ones_or_single, ones_run]; split <;> omega
      exact Nat.le_trans (ones_blk_le (a + b) (a - 1) 1 (a + b - 1)) (by omega))
  have hb3 : mk (a + b) (fun j => if 0 ≤ j ∧ j < 0 + a then nth (empty a) (j - 0)
      else nth (blk (a + b) (a - 1) 1 (a + b - 1)) j) = target (a + b) := by
    rw [target_eq_mk (a + b) hn1]
    apply mk_congr
    intro j hj
    split
    · rw [nth_empty]; apply Bool.eq_iff_iff.mpr; simp; omega
    · rw [nth_blk _ _ _ hj]; apply Bool.eq_iff_iff.mpr; simp; omega
  have h3w' := h3w.cast hb3
  have h := ((h1.peak_mono (q' := q + 1) (by omega)).append
    (h2w'.peak_mono (q' := q + 1) (by omega))).append
    (h3w'.peak_mono (q' := q + 1) (by omega))
  have el : 2 * a - 1 + L + (2 * a - 1) = 2 * (2 * a - 1) + L := by omega
  rw [el] at h
  exact ⟨_, h⟩

/-- **Erasure block.**  Append `b ∈ [p−1, T(p−1)]` cells: run the
`(p−1)`-plan of `tri_spec` above the held last stone, then erase it. -/
theorem block (p n' b k L : Nat) (t : List Nat) (hp : 3 ≤ p) (hn' : 2 ≤ n')
    (hb1 : p - 1 ≤ b) (hb2 : b ≤ tri (p - 1))
    (h1 : Seg n' (empty n') (target n') p k L t) :
    ∃ t', Seg (n' + b) (empty (n' + b)) (target (n' + b)) p (k + 1)
      (L + (4 * b - 2 * (p - 1) - 1) + 1) t' := by
  have hn1 : 1 ≤ n' + b := by omega
  have h1w := window_seg (x := 0) (K := 0) (B := empty (n' + b)) h1
    (length_empty _) (length_empty _) (by omega)
    (by intro i hi; rw [nth_empty, nth_empty])
    (Or.inl rfl) (by rw [ones_empty]; exact Nat.zero_le _)
  have hb1' : mk (n' + b) (fun j => if 0 ≤ j ∧ j < 0 + n' then nth (target n') (j - 0)
      else nth (empty (n' + b)) j) = blk (n' + b) (n' - 1) 1 (n' + b) := by
    unfold blk
    apply mk_congr
    intro j hj
    split
    · rw [nth_target _ _ (by omega)]; apply Bool.eq_iff_iff.mpr; simp; omega
    · rw [nth_empty]; apply Bool.eq_iff_iff.mpr; simp; omega
  have h1w' := (h1w.cast hb1').peak_mono (q' := p) (by omega)
  obtain ⟨t2, ht2⟩ := tri_spec (p - 1) (by omega) b hb1 hb2
  have h2w := window_seg (x := n') (K := 1) (B := blk (n' + b) (n' - 1) 1 (n' + b)) ht2
    (length_empty _) (length_blk _ _ _ _) (by omega)
    (by intro i hi; rw [nth_blk _ _ _ (by omega), nth_empty]; simp; omega)
    (Or.inr (by rw [nth_blk _ _ _ (by omega)]; simp; try omega))
    (by rw [ones_empty]; exact ones_blk_le_of_ge (n' + b) (n' - 1) 1 (n' + b) (Nat.le_refl _))
  have hb2' : mk (n' + b) (fun j => if n' ≤ j ∧ j < n' + b then nth (target b) (j - n')
      else nth (blk (n' + b) (n' - 1) 1 (n' + b)) j) = blk (n' + b) (n' - 1) 1 (n' + b - 1) := by
    unfold blk
    apply mk_congr
    intro j hj
    split
    · rw [nth_target _ _ (by omega)]
      apply Bool.eq_iff_iff.mpr; simp; omega
    · rw [nth_mk_of_lt hj]
      apply Bool.eq_iff_iff.mpr; simp; omega
  have h2w' := (h2w.cast hb2').peak_mono (q' := p) (by omega)
  have h3 := (erase_step (n' + b) (n' - 1) (n' + b - 1) (by omega) (by omega) (by omega)).peak_mono
    (q' := p) (by omega)
  have h := ((h1w'.append h2w').append h3).cast (blk_single_eq_target (n' + b) hn1)
  exact ⟨_, by simpa using h⟩

/-! ## The construction -/

/-- Without erasure: a plan to `T(p) + 1` with peak `p` and `4(T(p)+1) − 2p + 1`
moves, for `p ≥ 4`. -/
theorem base_spec : ∀ p, 4 ≤ p →
    ∃ t, Seg (tri p + 1) (empty (tri p + 1)) (target (tri p + 1)) p 0
      (4 * (tri p + 1) - 2 * p + 1) t := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ q ih =>
    intro hp
    rcases Nat.lt_or_ge q 4 with hq | hq
    · have e1 : q = 3 := by omega
      subst e1
      exact ⟨seed, by simpa [tri] using seed_p4⟩
    · obtain ⟨t, ht⟩ := ih hq
      have hge := tri_ge q
      obtain ⟨t', ht'⟩ := lift q q (tri q + 1) _ t (by omega) (Nat.le_refl _) (by omega) ht
      have e1 : q + (tri q + 1) = tri (q + 1) + 1 := by simp only [tri]; omega
      have e2 : 2 * (2 * q - 1) + (4 * (tri q + 1) - 2 * q + 1) =
          4 * (tri (q + 1) + 1) - 2 * (q + 1) + 1 := by simp only [tri]; omega
      rw [e1, e2] at ht'
      exact ⟨t', ht'⟩

/-- With `e` erasure blocks of length `T(p−1)`: a plan to
`n = T(p) + e·T(p−1) + 1` with `4n − 2(p−1)(e+1) − 1` moves. -/
theorem next_spec (p : Nat) (hp : 4 ≤ p) : ∀ e,
    ∃ t, Seg (tri p + e * tri (p - 1) + 1) (empty (tri p + e * tri (p - 1) + 1))
      (target (tri p + e * tri (p - 1) + 1)) p e
      (4 * (tri p + e * tri (p - 1) + 1) - 2 * ((p - 1) * (e + 1)) - 1) t := by
  have hu := tri_ge (p - 1)
  have hv := tri_ge p
  intro e
  induction e with
  | zero =>
    obtain ⟨t, ht⟩ := base_spec p hp
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_one]
    have el : 4 * (tri p + 1) - 2 * p + 1 = 4 * (tri p + 1) - 2 * (p - 1) - 1 := by omega
    rw [el] at ht
    exact ⟨t, ht⟩
  | succ e ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨t', ht'⟩ := block p _ (tri (p - 1)) e _ t (by omega) (by omega) hu (Nat.le_refl _) ht
    have hV : (e + 1) * tri (p - 1) = e * tri (p - 1) + tri (p - 1) := Nat.succ_mul _ _
    have hW : (p - 1) * (e + 1 + 1) = (p - 1) * (e + 1) + (p - 1) := Nat.mul_succ _ _
    have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
    have hle : (p - 1) * e ≤ e * tri (p - 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
    have e1 : tri p + e * tri (p - 1) + 1 + tri (p - 1) = tri p + (e + 1) * tri (p - 1) + 1 := by
      rw [hV]; omega
    rw [e1] at ht'
    have e2 : 4 * (tri p + e * tri (p - 1) + 1) - 2 * ((p - 1) * (e + 1)) - 1 +
        (4 * tri (p - 1) - 2 * (p - 1) - 1) + 1 =
        4 * (tri p + (e + 1) * tri (p - 1) + 1) - 2 * ((p - 1) * (e + 1 + 1)) - 1 := by
      rw [hV, hW]; omega
    rw [e2] at ht'
    exact ⟨t', ht'⟩

/-! ## Two candidates -/

/-- **One past the frontier.**  For `p ≥ 4` and `n = T(p) + e·T(p−1) + 1`, with
`L₀ = 2n − 1 + 2(n − A)`: some plan has `L₀ + 2` moves, and every plan has
`L₀` moves or at least `L₀ + 2`. -/
theorem next_point (p e : Nat) (hp : 4 ≤ p) :
    MstarLe (tri p + e * tri (p - 1) + 1) p e
      (2 * (tri p + e * tri (p - 1) + 1) - 1 +
        2 * (tri p + e * tri (p - 1) + 1 - ((p - 1) * (e + 1) + 1)) + 2) ∧
    ∀ s, IsPlay (tri p + e * tri (p - 1) + 1) p e s →
      s.length = 2 * (tri p + e * tri (p - 1) + 1) - 1 +
        2 * (tri p + e * tri (p - 1) + 1 - ((p - 1) * (e + 1) + 1)) ∨
      2 * (tri p + e * tri (p - 1) + 1) - 1 +
        2 * (tri p + e * tri (p - 1) + 1 - ((p - 1) * (e + 1) + 1)) + 2 ≤ s.length := by
  have hu := tri_ge (p - 1)
  have hv := tri_ge p
  have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
  have hle : (p - 1) * e ≤ e * tri (p - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
  have htp : tri p = tri (p - 1) + (p - 1) := by
    cases p with
    | zero => omega
    | succ q => simp [tri]
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := next_spec p hp e
    refine ⟨t, ⟨ht.bounds, ht.legal, ht.peak, Nat.le_of_eq ht.eras, ht.exec⟩, ?_⟩
    rw [ht.len]; omega
  · intro s hs
    have h1 := Contraction.length_ge _ p e (by omega) (by omega) s hs
    have h2 := length_odd _ p e (by omega) s hs
    omega

/-- `p = 4`, the last reachable length `n = 4e + 8 = reach(4, e)`:
`23 + 10e ≤ M*(4e+8, 4, e) ≤ 25 + 10e`, and `24 + 10e` is impossible. -/
theorem p4_endpoint (e : Nat) :
    MstarLe (4 * e + 8) 4 e (25 + 10 * e) ∧
    ∀ s, IsPlay (4 * e + 8) 4 e s → s.length = 23 + 10 * e ∨ 25 + 10 * e ≤ s.length := by
  have h := next_point 4 e (Nat.le_refl _)
  have en : tri 4 + e * tri (4 - 1) + 1 = 4 * e + 8 := by simp [tri]; omega
  rw [en] at h
  have el : 2 * (4 * e + 8) - 1 + 2 * (4 * e + 8 - ((4 - 1) * (e + 1) + 1)) = 23 + 10 * e := by
    omega
  rw [el, show 23 + 10 * e + 2 = 25 + 10 * e by omega] at h
  exact h

end NextPoint
end ErasurePebbling
