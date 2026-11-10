import ErasurePebbling.UpperBound

/-!
# Conjecture B2 is a theorem: the upper bound by compression

`UpperBound.lean` reduced the upper bound `reach(p, e) ≤ (e + 2)·2^(p−2)` of
Conjecture B2 to `RemovalLemma p` ("a reversible removal never raises the
gap potential `phi`"), which is still unproved.  This file proves the upper
bound **without** that lemma, by replacing `phi` with a smaller potential
for which the missing step is easy.

## The idea

Give every cell `i` of the chain a *width* `w i` (a natural number; the
real chain has `w ≡ 1`).  The weighted gap `wgap w b z` of a pebble is the
total width of the cells from the previous pebble up to `z`, and
`wphi p w b` is the potential of `UpperBound.lean` computed with weighted
gaps (least total excess over all removal orders).  A board is *flat* for
`w` if `wphi p w b = 0`.

The quantity that is tracked along a play is **how many cells have to be
squeezed out of the chain (width `1 → 0`) to make the current board flat**:

* a legal placement keeps a flat board flat, for the same widths
  (`wphi_toggle_le_of_place`: the new pebble has weighted gap `w x ≤ 1`);
* a reversible removal keeps a flat board flat, for the same widths
  (`wphi_zero_of_free`).  This is the removal lemma **on flat boards only**,
  where the first-step induction closes: the pebble removed first by a
  zero-cost order has gap at most the threshold, so the merged gap is at most
  the doubled threshold.  (The case that blocks the lemma for `phi` — the
  predecessor is removed first *with positive excess* — does not exist at
  cost zero.)
* an erasure raises `wphi` from `0` to at most `2^(p−2)`
  (`wphi_toggle_le_of_remove`, the weighted copy of
  `UpperBound.phi_toggle_le_of_remove`), and a board of potential `k` becomes
  flat after squeezing at most `k` cells (`compress`: a positive excess can
  always be lowered by one by shrinking one cell of the offending gap, and
  shrinking never raises the potential);
* the target `{n}` is flat only if the total width of the chain is at most
  `2^(p−1)` (`wphi_target`).

Hence after `e` erasures at most `e·2^(p−2)` of the `n` cells have been
squeezed and the remaining width is at most `2^(p−1)`:
`n ≤ 2^(p−1) + e·2^(p−2) = (e + 2)·2^(p−2)` (`reach_le`).  With `theoremB1`
this is `conjB2 : 2 ≤ p → ConjB2 p e`.

The squeezing number is a different potential from `phi`: it is at most
`phi` (`compress`) and can be strictly smaller (see the `#guard`s at the
end: the board `{2, 5, 7}` with `p = 3` has `phi = 2` but becomes flat after
squeezing one cell).  `RemovalLemma p` itself stays open; it is no longer
needed for Conjecture B2.

No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace ErasurePebbling
namespace Compression

open RevPebbling.PebblingFoundations
open UpperBound

/-! ## Weighted gaps -/

/-- Total width of the empty cells directly below cell `z`, down to the
previous pebble (or the entrance). -/
def below (w : Nat → Nat) (b : Board) : Nat → Nat
  | 0 => 0
  | z + 1 => if nth b z then 0 else w z + below w b z

/-- Weighted gap of cell `z`: the width of `z` and of the empty cells below it. -/
def wgap (w : Nat → Nat) (b : Board) (z : Nat) : Nat := w z + below w b z

/-- Weighted excess of the pebble on `z` at the current count of `b`. -/
def wexc (p : Nat) (w : Nat → Nat) (b : Board) (z : Nat) : Nat := wgap w b z - thr p (ones b)

/-- The weighted potential, with explicit fuel (`fuel ≥ ones b` suffices). -/
def wphiF (p : Nat) (w : Nat → Nat) : Nat → Board → Nat
  | 0, _ => 0
  | f + 1, b => listMin ((cells b).map fun z => wexc p w b z + wphiF p w f (toggle b z))

/-- The weighted potential: least total weighted excess over all removal orders. -/
def wphi (p : Nat) (w : Nat → Nat) (b : Board) : Nat := wphiF p w (ones b) b

/-- Total width of the first `N` cells. -/
def tot (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => tot w N + w N

/-- Shrink cell `i` by one. -/
def dec (w : Nat → Nat) (i : Nat) : Nat → Nat := fun j => if j = i then w j - 1 else w j

/-! ## The potential: fuel, unfolding, the two basic facts -/

theorem wphiF_fuel (p : Nat) (w : Nat → Nat) :
    ∀ (f : Nat) (b : Board), ones b ≤ f → wphiF p w f b = wphiF p w (ones b) b
  | 0, b, h => by
      have : ones b = 0 := by omega
      rw [this]
  | f + 1, b, h => by
      cases hk : ones b with
      | zero =>
          simp only [wphiF]
          rw [cells_eq_nil_of_ones_zero hk]
          rfl
      | succ m =>
          simp only [wphiF]
          congr 1
          apply List.map_congr_left
          intro z hz
          obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
          have hm : ones (toggle b z) = m := by
            have := ones_toggle_of_true hzn hzl; omega
          rw [wphiF_fuel p w f (toggle b z) (by omega), hm]

theorem wphi_unfold (p : Nat) (w : Nat → Nat) (b : Board) :
    wphi p w b = listMin ((cells b).map fun z => wexc p w b z + wphi p w (toggle b z)) := by
  unfold wphi
  cases hk : ones b with
  | zero =>
      simp only [wphiF]
      rw [cells_eq_nil_of_ones_zero hk]
      rfl
  | succ m =>
      simp only [wphiF]
      congr 1
      apply List.map_congr_left
      intro z hz
      obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
      have hm : ones (toggle b z) = m := by
        have := ones_toggle_of_true hzn hzl; omega
      rw [hm]

/-- Removing a pebble first is one of the options. -/
theorem wphi_le {p : Nat} {w : Nat → Nat} {b : Board} {z : Nat} (hz : nth b z = true)
    (hl : z < b.length) : wphi p w b ≤ wexc p w b z + wphi p w (toggle b z) := by
  rw [wphi_unfold]
  apply listMin_le_of_mem
  exact List.mem_map.mpr ⟨z, (mem_cells b z).mpr ⟨hl, hz⟩, rfl⟩

/-- The minimum is attained by some pebble. -/
theorem wphi_attained {p : Nat} {w : Nat → Nat} {b : Board} (h : 0 < ones b) :
    ∃ z, z < b.length ∧ nth b z = true ∧ wphi p w b = wexc p w b z + wphi p w (toggle b z) := by
  rw [wphi_unfold]
  have hne : (cells b).map (fun z => wexc p w b z + wphi p w (toggle b z)) ≠ [] := by
    intro hc
    exact cells_ne_nil_of_ones_pos h (List.map_eq_nil_iff.mp hc)
  obtain ⟨z, hz, hv⟩ := List.mem_map.mp (listMin_mem _ hne)
  obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
  exact ⟨z, hzl, hzn, hv.symm⟩

theorem wphi_of_ones_zero {p : Nat} {w : Nat → Nat} {b : Board} (h : ones b = 0) :
    wphi p w b = 0 := by
  rw [wphi_unfold, cells_eq_nil_of_ones_zero h]
  rfl

/-! ## Weighted gaps under a move -/

/-- Cells at or above `x` do not influence `below · z` for `z ≤ x`. -/
theorem below_set_of_le (w : Nat → Nat) (b : Board) (x : Nat) (v : Bool) :
    ∀ z, z ≤ x → below w (b.set x v) z = below w b z
  | 0, _ => rfl
  | z + 1, h => by
      simp only [below]
      rw [nth_set_ne b x z v (by omega), below_set_of_le w b x v z (by omega)]

theorem below_toggle_of_le (w : Nat → Nat) (b : Board) (x z : Nat) (h : z ≤ x) :
    below w (toggle b x) z = below w b z :=
  below_set_of_le w b x _ z h

theorem wgap_toggle_of_le (w : Nat → Nat) (b : Board) (x z : Nat) (h : z ≤ x) :
    wgap w (toggle b x) z = wgap w b z := by
  unfold wgap; rw [below_toggle_of_le w b x z h]

/-- Removing a pebble never lowers `below`. -/
theorem below_le_below_toggle_of_true (w : Nat → Nat) (b : Board) {x : Nat}
    (hx : nth b x = true) : ∀ z, below w b z ≤ below w (toggle b x) z
  | 0 => Nat.le_refl _
  | z + 1 => by
      simp only [below]
      by_cases hzx : z = x
      · subst hzx
        rw [hx]
        simp
      · rw [nth_toggle_ne b (Ne.symm hzx)]
        have := below_le_below_toggle_of_true w b hx z
        split
        · exact Nat.le_refl _
        · omega

theorem wgap_le_wgap_toggle_of_true (w : Nat → Nat) (b : Board) {x : Nat}
    (hx : nth b x = true) (z : Nat) : wgap w b z ≤ wgap w (toggle b x) z := by
  unfold wgap
  have := below_le_below_toggle_of_true w b hx z
  omega

theorem below_toggle_of_between (w : Nat → Nat) (b : Board) (x : Nat) :
    ∀ z, x < z → Between b x z → below w (toggle b x) z = below w b z
  | 0, h, _ => by omega
  | z + 1, _, ⟨j, hxj, hjz, hj⟩ => by
      simp only [below]
      have hzx : z ≠ x := by omega
      rw [nth_toggle_ne b (Ne.symm hzx)]
      cases hn : nth b z with
      | true => rfl
      | false =>
          have hjz' : j < z := by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjz) with h | h
            · exact h
            · subst h; rw [hn] at hj; simp at hj
          simp only [Bool.false_eq_true, if_false]
          rw [below_toggle_of_between w b x z (by omega) ⟨j, hxj, hjz', hj⟩]

theorem wgap_toggle_of_between (w : Nat → Nat) (b : Board) {x z : Nat} (hxz : x < z)
    (hb : Between b x z) : wgap w (toggle b x) z = wgap w b z := by
  unfold wgap; rw [below_toggle_of_between w b x z hxz hb]

theorem below_toggle_of_not_between (w : Nat → Nat) (b : Board) {x : Nat}
    (hx : nth b x = true) :
    ∀ z, x < z → ¬ Between b x z → below w (toggle b x) z = below w b z + wgap w b x
  | 0, h, _ => by omega
  | z + 1, h, hnb => by
      simp only [below]
      by_cases hzx : z = x
      · subst hzx
        rw [UpperBound.nth_toggle_self (nth_true_lt_length hx), hx]
        simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, Nat.zero_add]
        rw [below_toggle_of_le w b z z (Nat.le_refl _)]
        rfl
      · have hn : nth b z = false := by
          cases hn : nth b z with
          | true => exact absurd ⟨z, by omega, by omega, hn⟩ hnb
          | false => rfl
        rw [nth_toggle_ne b (Ne.symm hzx), hn]
        simp only [Bool.false_eq_true, if_false]
        rw [below_toggle_of_not_between w b hx z (by omega)
          (fun ⟨j, h1, h2, h3⟩ => hnb ⟨j, h1, by omega, h3⟩)]
        omega

/-- Removing `x` merges its weighted gap into the gap of its successor. -/
theorem wgap_toggle_of_not_between (w : Nat → Nat) (b : Board) {x z : Nat}
    (hx : nth b x = true) (hxz : x < z) (hnb : ¬ Between b x z) :
    wgap w (toggle b x) z = wgap w b z + wgap w b x := by
  show w z + below w (toggle b x) z = w z + below w b z + wgap w b x
  rw [below_toggle_of_not_between w b hx z hxz hnb]
  omega

/-- In every case the gap of another pebble grows by at most the gap of the
removed one. -/
theorem wgap_toggle_le (w : Nat → Nat) (b : Board) {x z : Nat} (hx : nth b x = true)
    (hzx : z ≠ x) : wgap w (toggle b x) z ≤ wgap w b z + wgap w b x := by
  rcases Nat.lt_or_ge z x with hlt | hge
  · rw [wgap_toggle_of_le w b x z (Nat.le_of_lt hlt)]; omega
  · have hgt : x < z := by omega
    rcases Classical.em (Between b x z) with hb | hnb
    · rw [wgap_toggle_of_between w b hgt hb]; omega
    · rw [wgap_toggle_of_not_between w b hx hgt hnb]; omega

/-- A cell whose predecessor is pebbled (or the entrance cell) has nothing below. -/
theorem below_eq_zero_of_okMove (w : Nat → Nat) (b : Board) {x : Nat}
    (hok : okMove b x = true) : below w b x = 0 := by
  cases x with
  | zero => rfl
  | succ v =>
      have hv : nth b v = true := by simpa [okMove] using hok
      simp [below, hv]

/-- Below the lowest pebble, `below` is the total width. -/
theorem below_eq_tot (w : Nat → Nat) (b : Board) :
    ∀ z, (∀ j, j < z → nth b j = false) → below w b z = tot w z
  | 0, _ => rfl
  | z + 1, h => by
      simp only [below, tot]
      rw [h z (Nat.lt_succ_self z)]
      simp only [Bool.false_eq_true, if_false]
      rw [below_eq_tot w b z (fun j hj => h j (by omega))]
      omega

/-! ## Monotonicity in the widths -/

theorem below_mono {w w' : Nat → Nat} (h : ∀ i, w' i ≤ w i) (b : Board) :
    ∀ z, below w' b z ≤ below w b z
  | 0 => Nat.le_refl _
  | z + 1 => by
      simp only [below]
      have h1 := below_mono h b z
      have h2 := h z
      split
      · exact Nat.le_refl _
      · omega

theorem wgap_mono {w w' : Nat → Nat} (h : ∀ i, w' i ≤ w i) (b : Board) (z : Nat) :
    wgap w' b z ≤ wgap w b z := by
  unfold wgap
  have h1 := below_mono h b z
  have h2 := h z
  omega

/-- Shrinking cells never raises the potential. -/
theorem wphi_mono (p : Nat) {w w' : Nat → Nat} (h : ∀ i, w' i ≤ w i) :
    ∀ (k : Nat) (b : Board), ones b = k → wphi p w' b ≤ wphi p w b := by
  intro k
  induction k with
  | zero =>
      intro b hk
      rw [wphi_of_ones_zero hk, wphi_of_ones_zero hk]
      exact Nat.le_refl _
  | succ k ih =>
      intro b hk
      obtain ⟨z, hzl, hz, hphi⟩ := wphi_attained (p := p) (w := w) (b := b) (by omega)
      have h1 := wphi_le (p := p) (w := w') hz hzl
      have hkz := ones_toggle_of_true hz hzl
      have h2 := ih (toggle b z) (by omega)
      have h3 : wexc p w' b z ≤ wexc p w b z := by
        unfold wexc
        have := wgap_mono h b z
        omega
      omega

/-! ## Placement, reversible removal on flat boards, erasure -/

/-- A legal placement on a cell of width at most one never raises the potential. -/
theorem wphi_toggle_le_of_place (p : Nat) (w : Nat → Nat) {b : Board} {x : Nat}
    (hx : nth b x = false) (hok : okMove b x = true) (hl : x < b.length) (hw : w x ≤ 1) :
    wphi p w (toggle b x) ≤ wphi p w b := by
  have h1 : nth (toggle b x) x = true := by rw [UpperBound.nth_toggle_self hl, hx]; rfl
  have h2 := wphi_le (p := p) (w := w) h1 (by rw [length_toggle]; exact hl)
  rw [toggle_toggle] at h2
  have h3 : wexc p w (toggle b x) x = 0 := by
    unfold wexc
    rw [wgap_toggle_of_le w b x x (Nat.le_refl _)]
    unfold wgap
    rw [below_eq_zero_of_okMove w b hok]
    have := one_le_thr p (ones (toggle b x))
    omega
  rw [h3] at h2
  simpa using h2

/-- **The removal lemma on flat boards.**  If the potential is zero and the
weighted gap of `x` is at most the current threshold, the potential is still
zero after `x` is removed. -/
theorem wphi_zero_of_free (p : Nat) (w : Nat → Nat) :
    ∀ (k : Nat) (b : Board) (x : Nat), ones b = k → ones b ≤ p → nth b x = true →
      x < b.length → wgap w b x ≤ thr p (ones b) → wphi p w b = 0 →
      wphi p w (toggle b x) = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro b x hk hkp hx hl hfree h0
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨z, hzl, hz, hphi⟩ := wphi_attained (p := p) (w := w) hpos
  rw [h0] at hphi
  have hez : wexc p w b z = 0 := by omega
  have h0z : wphi p w (toggle b z) = 0 := by omega
  by_cases hzx : z = x
  · rw [hzx] at h0z; exact h0z
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have hxzl : x < (toggle b z).length := by rw [length_toggle]; exact hl
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have hzxl : z < (toggle b x).length := by rw [length_toggle]; exact hzl
  have hcomm : toggle (toggle b x) z = toggle (toggle b z) x := toggle_comm b (Ne.symm hzx)
  have hk2 : 2 ≤ ones b := two_le_ones hx hz (Ne.symm hzx)
  have hTz : thr p (ones (toggle b z)) = 2 * thr p (ones b) := by
    have := thr_pred p (k := ones b) (by omega) hkp
    rw [← this]; congr 1; omega
  have hTx : thr p (ones (toggle b x)) = 2 * thr p (ones b) := by
    have := thr_pred p (k := ones b) (by omega) hkp
    rw [← this]; congr 1; omega
  have hgz : wgap w b z ≤ thr p (ones b) := by
    unfold wexc at hez; omega
  -- `x` is still free after `z` is removed
  have hfree' : wgap w (toggle b z) x ≤ thr p (ones (toggle b z)) := by
    have := wgap_toggle_le w b hz (Ne.symm hzx)
    omega
  have h1 := ih (ones (toggle b z)) (by omega) (toggle b z) x rfl (by omega) hxz hxzl hfree' h0z
  -- `z` costs nothing after `x` is removed
  have h2 := wphi_le (p := p) (w := w) hzx' hzxl
  rw [hcomm, h1] at h2
  have h3 : wexc p w (toggle b x) z = 0 := by
    unfold wexc
    have := wgap_toggle_le w b hx hzx
    omega
  omega

/-- Removing any pebble raises the weighted potential by at most `2^(p−2)`
(the erasure step; weighted copy of `UpperBound.phi_toggle_le_of_remove`). -/
theorem wphi_toggle_le_of_remove (p : Nat) (w : Nat → Nat) :
    ∀ (k : Nat) (b : Board) (x : Nat), ones b = k → ones b ≤ p → nth b x = true →
      x < b.length → wphi p w (toggle b x) ≤ wphi p w b + 2 ^ (p - 2) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro b x hk hkp hx hl
  have hQ1 : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨z, hzl, hz, hphi⟩ := wphi_attained (p := p) (w := w) hpos
  by_cases hzx : z = x
  · rw [hzx] at hphi
    omega
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have hxzl : x < (toggle b z).length := by rw [length_toggle]; exact hl
  have hcomm : toggle (toggle b x) z = toggle (toggle b z) x := toggle_comm b (Ne.symm hzx)
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have hzxl : z < (toggle b x).length := by rw [length_toggle]; exact hzl
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hthr : thr p (ones b) ≤ thr p (ones (toggle b x)) := thr_le_thr_of_le p (by omega)
  -- Case A: the gap of `z` is unchanged by removing `x`.
  have caseA : wgap w (toggle b x) z = wgap w b z →
      wphi p w (toggle b x) ≤ wphi p w b + 2 ^ (p - 2) := by
    intro hg
    have h1 := wphi_le (p := p) (w := w) hzx' hzxl
    rw [hcomm] at h1
    have h2 := ih (ones (toggle b z)) (by omega) (toggle b z) x rfl (by omega) hxz hxzl
    have h3 : wexc p w (toggle b x) z ≤ wexc p w b z := by
      unfold wexc; rw [hg]; omega
    omega
  rcases Nat.lt_or_ge z x with hlt | hge
  · exact caseA (wgap_toggle_of_le w b x z (Nat.le_of_lt hlt))
  · have hgt : x < z := by omega
    rcases Classical.em (Between b x z) with hb | hnb
    · exact caseA (wgap_toggle_of_between w b hgt hb)
    -- Case B: `z` is the successor `s` of `x`; look one level deeper.
    have hgs : wgap w (toggle b x) z = wgap w b z + wgap w b x :=
      wgap_toggle_of_not_between w b hx hgt hnb
    have hk2 : 2 ≤ ones b := two_le_ones hx hz (Ne.symm hzx)
    have hT2 : thr p (ones (toggle b x)) = 2 * thr p (ones b) := by
      have := thr_pred p (k := ones b) (by omega) hkp
      rw [← this]; congr 1; omega
    have hTQ : thr p (ones b) ≤ 2 ^ (p - 2) := thr_le_Q p hk2
    have hpos1 : 0 < ones (toggle b z) := ones_pos_of_nth hxz
    obtain ⟨z', hz'l, hz', hphi1⟩ := wphi_attained (p := p) (w := w) hpos1
    have hT1 : thr p (ones (toggle b z)) = 2 * thr p (ones b) := by
      have := thr_pred p (k := ones b) (by omega) hkp
      rw [← this]; congr 1; omega
    by_cases hz'x : z' = x
    · -- (i) after `s`, the optimal order removes `x`
      rw [hz'x] at hphi1
      have h1 := wphi_le (p := p) (w := w) hzx' hzxl
      rw [hcomm] at h1
      have hgx : wgap w (toggle b z) x = wgap w b x :=
        wgap_toggle_of_le w b z x (Nat.le_of_lt hgt)
      have e1 : wexc p w (toggle b x) z = (wgap w b z + wgap w b x) - 2 * thr p (ones b) := by
        unfold wexc; rw [hgs, hT2]
      have e2 : wexc p w b z = wgap w b z - thr p (ones b) := rfl
      have e3 : wexc p w (toggle b z) x = wgap w b x - 2 * thr p (ones b) := by
        unfold wexc; rw [hgx, hT1]
      omega
    · -- (ii) after `s`, the optimal order removes some other `z'`
      have hz'z : z' ≠ z := by
        intro h; subst h; simp [UpperBound.nth_toggle_self hzl, hz] at hz'
      have hz'b : nth b z' = true := by
        rw [nth_toggle_ne b (Ne.symm hz'z)] at hz'; exact hz'
      have hz'bl : z' < b.length := by rw [length_toggle] at hz'l; exact hz'l
      have hz'tx : nth (toggle b x) z' = true := by
        rw [nth_toggle_ne b (Ne.symm hz'x)]; exact hz'b
      have h1 := wphi_le (p := p) (w := w) hz'tx (by rw [length_toggle]; exact hz'bl)
      rw [toggle_comm b (Ne.symm hz'x)] at h1
      have hkz' : ones (toggle b z') + 1 = ones b := ones_toggle_of_true hz'b hz'bl
      have hxz' : nth (toggle b z') x = true := by rw [nth_toggle_ne b hz'x]; exact hx
      have h2 := ih (ones (toggle b z')) (by omega) (toggle b z') x rfl (by omega) hxz'
        (by rw [length_toggle]; exact hl)
      have hztz' : nth (toggle b z') z = true := by rw [nth_toggle_ne b hz'z]; exact hz
      have h3 := wphi_le (p := p) (w := w) hztz' (by rw [length_toggle]; exact hzl)
      rw [toggle_comm b hz'z] at h3
      have hz'pos : z' < x ∨ z < z' := by
        rcases Nat.lt_or_ge z' x with h | h
        · exact Or.inl h
        · rcases Nat.lt_or_ge z z' with h' | h'
          · exact Or.inr h'
          · exfalso
            have : x < z' := by omega
            exact hnb ⟨z', this, by omega, hz'b⟩
      have hgz' : wgap w (toggle b x) z' = wgap w b z' := by
        rcases hz'pos with h | h
        · exact wgap_toggle_of_le w b x z' (Nat.le_of_lt h)
        · exact wgap_toggle_of_between w b (by omega) ⟨z, hgt, h, hz⟩
      have hgs' : wgap w (toggle b z') z = wgap w b z := by
        rcases hz'pos with h | h
        · exact wgap_toggle_of_between w b (by omega) ⟨x, h, hgt, hx⟩
        · exact wgap_toggle_of_le w b z' z (Nat.le_of_lt h)
      have hgz'1 : wgap w b z' ≤ wgap w (toggle b z) z' := wgap_le_wgap_toggle_of_true w b hz z'
      have hT1' : thr p (ones (toggle b z')) = 2 * thr p (ones b) := by
        have := thr_pred p (k := ones b) (by omega) hkp
        rw [← this]; congr 1; omega
      have e1 : wexc p w (toggle b x) z' = wgap w b z' - 2 * thr p (ones b) := by
        unfold wexc; rw [hgz', hT2]
      have e2 : wexc p w (toggle b z') z = wgap w b z - 2 * thr p (ones b) := by
        unfold wexc; rw [hgs', hT1']
      have e3 : wexc p w b z = wgap w b z - thr p (ones b) := rfl
      have e4 : wexc p w (toggle b z) z' = wgap w (toggle b z) z' - 2 * thr p (ones b) := by
        unfold wexc; rw [hT1]
      omega

/-! ## Squeezing: a board of potential `k` is `k` cells away from flat -/

theorem dec_le (w : Nat → Nat) (i j : Nat) : dec w i j ≤ w j := by
  unfold dec; split <;> omega

theorem tot_dec (w : Nat → Nat) (i : Nat) :
    ∀ N, (N ≤ i → tot (dec w i) N = tot w N) ∧ tot w N ≤ tot (dec w i) N + 1
  | 0 => ⟨fun _ => rfl, Nat.zero_le _⟩
  | N + 1 => by
      obtain ⟨h1, h2⟩ := tot_dec w i N
      simp only [tot]
      by_cases hN : N = i
      · have h3 : dec w i N = w N - 1 := by unfold dec; simp [hN]
        have h4 := h1 (by omega)
        exact ⟨fun h => by omega, by omega⟩
      · have h3 : dec w i N = w N := by unfold dec; simp [hN]
        exact ⟨fun h => by have := h1 (by omega); omega, by omega⟩

/-- A positive `below` can be lowered by one by shrinking one cell under `z`. -/
theorem below_dec_exists (w : Nat → Nat) (b : Board) :
    ∀ z, 0 < below w b z → ∃ i, i < z ∧ below (dec w i) b z + 1 ≤ below w b z
  | 0, h => by simp [below] at h
  | z + 1, h => by
      cases hn : nth b z with
      | true => simp [below, hn] at h
      | false =>
          have hb : ∀ v : Nat → Nat, below v b (z + 1) = v z + below v b z := by
            intro v; simp [below, hn]
          rw [hb] at h
          by_cases hwz : 0 < w z
          · refine ⟨z, by omega, ?_⟩
            rw [hb, hb]
            have h1 : dec w z z = w z - 1 := by unfold dec; simp
            have h2 := below_mono (dec_le w z) b z
            omega
          · obtain ⟨i, hi, hlt⟩ := below_dec_exists w b z (by omega)
            refine ⟨i, by omega, ?_⟩
            rw [hb, hb]
            have h1 : dec w i z = w z := by
              unfold dec; simp; omega
            omega

/-- A positive weighted gap can be lowered by one by shrinking one cell. -/
theorem wgap_dec_exists (w : Nat → Nat) (b : Board) (z : Nat) (h : 0 < wgap w b z) :
    ∃ i, wgap (dec w i) b z + 1 ≤ wgap w b z := by
  unfold wgap at h
  by_cases hwz : 0 < w z
  · refine ⟨z, ?_⟩
    unfold wgap
    have h1 : dec w z z = w z - 1 := by unfold dec; simp
    have h2 := below_mono (dec_le w z) b z
    omega
  · obtain ⟨i, hi, hlt⟩ := below_dec_exists w b z (by omega)
    refine ⟨i, ?_⟩
    unfold wgap
    have h1 : dec w i z = w z := by
      unfold dec; simp; omega
    omega

/-- A positive potential can be lowered by one by shrinking one cell. -/
theorem wphi_dec_exists (p : Nat) :
    ∀ (k : Nat) (w : Nat → Nat) (b : Board), ones b = k → 0 < wphi p w b →
      ∃ i, wphi p (dec w i) b + 1 ≤ wphi p w b := by
  intro k
  induction k with
  | zero =>
      intro w b hk hpos
      rw [wphi_of_ones_zero hk] at hpos
      omega
  | succ k ih =>
      intro w b hk hpos
      obtain ⟨z, hzl, hz, hphi⟩ := wphi_attained (p := p) (w := w) (b := b) (by omega)
      have hkz := ones_toggle_of_true hz hzl
      by_cases hez : 0 < wexc p w b z
      · have hT := one_le_thr p (ones b)
        have hg : 0 < wgap w b z := by unfold wexc at hez; omega
        obtain ⟨i, hi⟩ := wgap_dec_exists w b z hg
        refine ⟨i, ?_⟩
        have h1 := wphi_le (p := p) (w := dec w i) hz hzl
        have h2 := wphi_mono p (dec_le w i) (ones (toggle b z)) (toggle b z) rfl
        have h3 : wexc p (dec w i) b z + 1 ≤ wexc p w b z := by
          unfold wexc at hez ⊢; omega
        omega
      · have hpos' : 0 < wphi p w (toggle b z) := by omega
        obtain ⟨i, hi⟩ := ih w (toggle b z) (by omega) hpos'
        refine ⟨i, ?_⟩
        have h1 := wphi_le (p := p) (w := dec w i) hz hzl
        have h3 : wexc p (dec w i) b z ≤ wexc p w b z := by
          unfold wexc
          have := wgap_mono (dec_le w i) b z
          omega
        omega

/-- **Compression.**  A board of weighted potential at most `k` becomes flat
after shrinking cells by a total of at most `k`. -/
theorem compress (p : Nat) :
    ∀ (k : Nat) (w : Nat → Nat) (b : Board), wphi p w b ≤ k →
      ∃ w', (∀ i, w' i ≤ w i) ∧ wphi p w' b = 0 ∧ ∀ N, tot w N ≤ tot w' N + k
  | 0, w, b, h => ⟨w, fun _ => Nat.le_refl _, by omega, fun _ => Nat.le_refl _⟩
  | k + 1, w, b, h => by
      by_cases h0 : wphi p w b = 0
      · exact ⟨w, fun _ => Nat.le_refl _, h0, fun _ => by omega⟩
      · obtain ⟨i, hi⟩ := wphi_dec_exists p (ones b) w b rfl (by omega)
        obtain ⟨w', hw', hz', ht'⟩ := compress p k (dec w i) b (by omega)
        refine ⟨w', fun j => Nat.le_trans (hw' j) (dec_le w i j), hz', fun N => ?_⟩
        have h1 := (tot_dec w i N).2
        have h2 := ht' N
        omega

/-! ## The target and the main induction -/

theorem tot_one : ∀ N, tot (fun _ => 1) N = N
  | 0 => rfl
  | N + 1 => by simp only [tot]; rw [tot_one N]

/-- The target `{n}` has potential at least (total width) − `2^(p−1)`. -/
theorem wphi_target (p : Nat) (w : Nat → Nat) (n : Nat) (hn : 1 ≤ n) :
    tot w n - 2 ^ (p - 1) ≤ wphi p w (target n) := by
  have hl : n - 1 < (List.replicate n false).length := by simp; omega
  have hone : ones (target n) = 1 := by
    have := ones_set (List.replicate n false) (n - 1) true hl
    rw [nth_replicate, ones_replicate] at this
    simpa [target] using this
  have hlow : ∀ j, j < n - 1 → nth (target n) j = false := by
    intro j hj
    unfold target
    rw [nth_set_ne _ _ _ _ (by omega), nth_replicate]
  have hgap : wgap w (target n) (n - 1) = tot w n := by
    unfold wgap
    rw [below_eq_tot w (target n) (n - 1) hlow]
    have h : tot w (n - 1 + 1) = tot w (n - 1) + w (n - 1) := rfl
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at h
    omega
  rw [wphi_unfold]
  apply le_listMin
  · intro hc
    exact cells_ne_nil_of_ones_pos (by omega) (List.map_eq_nil_iff.mp hc)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hzl, hzn⟩ := (mem_cells _ z).mp hz
    have hzeq : z = n - 1 := by
      rcases Nat.lt_or_ge z (n - 1) with h | h
      · rw [hlow z h] at hzn; simp at hzn
      · rw [length_target] at hzl; omega
    subst hzeq
    have : wexc p w (target n) (n - 1) = tot w n - thr p 1 := by
      unfold wexc; rw [hgap, hone]
    unfold thr at this
    rw [this]
    omega

/-- **Main induction.**  Along a legal play with peak `p`, a flat board stays
flat if `2^(p−2)` cells are squeezed out per erasure. -/
theorem flat_execB (p : Nat) :
    ∀ (s : List Nat) (b : Board) (w : Nat → Nat), legalE b s = true →
      (∀ k, ones (execB b (s.take k)) ≤ p) → (∀ i ∈ s, i < b.length) →
      (∀ i, w i ≤ 1) → wphi p w b = 0 →
      ∃ w', (∀ i, w' i ≤ 1) ∧ wphi p w' (execB b s) = 0 ∧
        ∀ N, tot w N ≤ tot w' N + 2 ^ (p - 2) * erasures b s
  | [], b, w, _, _, _, hw, h0 =>
      ⟨w, hw, by simpa [execB] using h0, fun N => by simp [erasures]⟩
  | i :: rest, b, w, hleg, hpk, hbd, hw, h0 => by
      have hex : execB b (i :: rest) = execB (toggle b i) rest := rfl
      have hleg' : okE b i = true ∧ legalE (toggle b i) rest = true := by
        simpa [Bool.and_eq_true] using hleg
      have hil : i < b.length := hbd i (List.mem_cons_self ..)
      have hone : ones b ≤ p := by simpa [execB] using hpk 0
      have hpk' : ∀ k, ones (execB (toggle b i) (rest.take k)) ≤ p := by
        intro k; simpa [execB] using hpk (k + 1)
      have hbd' : ∀ j ∈ rest, j < (toggle b i).length := by
        intro j hj; rw [length_toggle]; exact hbd j (List.mem_cons_of_mem _ hj)
      rw [hex]
      simp only [erasures_cons]
      cases hn : nth b i with
      | false =>
          -- placement
          have hok : okMove b i = true := by
            have := hleg'.1; unfold okE at this; rw [hn] at this; simpa using this
          have hst : wphi p w (toggle b i) = 0 := by
            have := wphi_toggle_le_of_place p w hn hok hil (hw i); omega
          have hie : isErase b i = false := by simp [isErase, hn]
          obtain ⟨w', hw', h0', htot⟩ :=
            flat_execB p rest (toggle b i) w hleg'.2 hpk' hbd' hw hst
          refine ⟨w', hw', h0', fun N => ?_⟩
          rw [hie]
          simp only [Bool.false_eq_true, if_false, Nat.zero_add]
          exact htot N
      | true =>
          cases hok : okMove b i with
          | true =>
              -- reversible removal
              have hfree : wgap w b i ≤ thr p (ones b) := by
                unfold wgap
                rw [below_eq_zero_of_okMove w b hok]
                have := hw i
                have := one_le_thr p (ones b)
                omega
              have hst := wphi_zero_of_free p w (ones b) b i rfl hone hn hil hfree h0
              have hie : isErase b i = false := by simp [isErase, hn, hok]
              obtain ⟨w', hw', h0', htot⟩ :=
                flat_execB p rest (toggle b i) w hleg'.2 hpk' hbd' hw hst
              refine ⟨w', hw', h0', fun N => ?_⟩
              rw [hie]
              simp only [Bool.false_eq_true, if_false, Nat.zero_add]
              exact htot N
          | false =>
              -- erasure: at most `2^(p−2)` above flat, squeeze that many cells
              have hst := wphi_toggle_le_of_remove p w (ones b) b i rfl hone hn hil
              rw [h0] at hst
              obtain ⟨w₁, hw₁, h0₁, htot₁⟩ :=
                compress p (2 ^ (p - 2)) w (toggle b i) (by omega)
              have hie : isErase b i = true := by simp [isErase, hn, hok]
              obtain ⟨w', hw', h0', htot⟩ :=
                flat_execB p rest (toggle b i) w₁ hleg'.2 hpk' hbd'
                  (fun j => Nat.le_trans (hw₁ j) (hw j)) h0₁
              refine ⟨w', hw', h0', fun N => ?_⟩
              rw [hie]
              have h1 := htot₁ N
              have h2 := htot N
              simp only [if_true, Nat.mul_add, Nat.mul_one]
              omega

/-- **The upper bound of Conjecture B2.**  Every clean plan with peak `p` and
at most `e` erasures has `n ≤ (e + 2)·2^(p−2)`. -/
theorem reach_le (p e : Nat) (hp : 2 ≤ p) (n : Nat) (h : Reachable n p e) :
    n ≤ (e + 2) * 2 ^ (p - 2) := by
  obtain ⟨s, hs⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.zero_le _
  have hpk : ∀ k, ones (execB (empty n) (s.take k)) ≤ p :=
    fun k => Nat.le_trans (ones_prefix_le_maxOnes s (empty n) k) hs.peak
  have hbd : ∀ i ∈ s, i < (empty n).length := by
    intro i hi; rw [length_empty]; exact hs.bounds i hi
  have h0 : wphi p (fun _ => 1) (empty n) = 0 := wphi_of_ones_zero (ones_empty n)
  obtain ⟨w', _, h0', htot⟩ :=
    flat_execB p s (empty n) (fun _ => 1) hs.legal hpk hbd (fun _ => Nat.le_refl 1) h0
  rw [hs.final] at h0'
  have h1 := htot n
  rw [tot_one] at h1
  have h2 := wphi_target p w' n hn
  have h3 : 2 ^ (p - 2) * erasures (empty n) s ≤ 2 ^ (p - 2) * e :=
    Nat.mul_le_mul_left _ hs.budget
  have hpow : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have : n ≤ 2 ^ (p - 1) + 2 ^ (p - 2) * e := by omega
  rw [hpow] at this
  calc n ≤ 2 * 2 ^ (p - 2) + 2 ^ (p - 2) * e := this
    _ = (e + 2) * 2 ^ (p - 2) := by rw [Nat.add_mul, Nat.mul_comm (2 ^ (p - 2)) e]; omega

/-- **Conjecture B2 of RC-02 is a theorem**: `reach(p, e) = (e + 2)·2^(p−2)`
for every `p ≥ 2` and every `e` (lower bound `theoremB1`, upper bound
`reach_le`). -/
theorem conjB2 (p e : Nat) (hp : 2 ≤ p) : ConjB2 p e :=
  ⟨theoremB1 p e hp, fun n hn => reach_le p e hp n hn⟩

/-! ## Sanity anchors (evaluated at elaboration time)

With unit widths the weighted potential is the potential of
`UpperBound.lean` on these boards, and the squeezing number can be strictly
smaller: `{2, 5, 7}` with `p = 3` has `phi = 2`, but squeezing the entrance
cell alone makes it flat. -/

/-- The board with pebbles on nodes 2, 5, 7 (cells 1, 4, 6). -/
def ex257 : Board := [false, true, false, false, true, false, true]

#guard phi 3 ex257 = 2
#guard wphi 3 (fun _ => 1) ex257 = 2
#guard wphi 3 (fun i => if i = 0 then 0 else 1) ex257 = 0

/- The erasure step is tight (`p = 4`, pebbles on nodes 8 and 12): erasing
the lower pebble raises the weighted potential from 0 to `2^(p−2) = 4`. -/
#guard wphi 4 (fun _ => 1) ((empty 12).set 7 true |>.set 11 true) = 0
#guard wphi 4 (fun _ => 1) ((empty 12).set 11 true) = 4

end Compression
end ErasurePebbling
