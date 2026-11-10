import ErasurePebbling.RemovalCases

/-!
# The removal lemma reduced to its boundary case (sliding the predecessor)

`RemovalCases.lean` states `FreeRemoval p` (R′): a pebble `x` whose gap is at
most the threshold at the current count can be removed without raising
`phi`.  Together with `conjB2_of_removalLemma` it would give Conjecture B2.
The induction on the pebble count through the recursion of `phi` closes
unless the pebble `v` just below `x` is the first pebble removed by *every*
optimal order and `gap v + gap x` exceeds the doubled threshold.

This file removes one more degree of freedom from that open case.

## The sliding argument

Let `v` be the predecessor of `x`, `gap v > thr`, `gap x < thr` (strictly),
and assume an optimal order removes `v` first.  Let `b'` be the board with
`v` moved *down* by one cell.  Then

* `b' − v' = b − v` (the same board), and `v'` pays one unit less, so
  `phi b' ≤ phi b − 1`;
* `x` is still free in `b'` (its gap grew by one), and `b'` has the same
  pebble count and a lower predecessor, so `phi (b' − x) ≤ phi b'` by an
  inner induction on the position of the predecessor;
* `b − x` is `b' − x` with `v'` moved *up* by one cell, and moving a pebble
  up by one cell raises `phi` by at most one (`phi_moveUp_le`: only the
  block of the moved pebble grows).

Hence `phi (b − x) ≤ phi (b' − x) + 1 ≤ phi b' + 1 ≤ phi b`.  The slide stops
exactly when `gap x = thr`.

## What is proved (no `sorry`, standard axioms)

* `phi_moveUp_le`: moving a pebble up by one cell raises `phi` by at most 1;
* `freeRemoval_of_boundaryStep`: `FreeRemoval p` follows from
  `BoundaryStep p`, the single remaining case:
  `x` sits **exactly at the threshold** (`gap x = thr`), its predecessor `v`
  is not free (`gap v > thr`), removing `v` first is optimal, and removing
  any other pebble first is strictly worse; the statement may use
  `FreeRemoval` on all boards with fewer pebbles and on all boards with the
  same count and a lower predecessor;
* `conjB2_of_boundaryStep`: Conjecture B2 follows from `BoundaryStep p`.

## What is not proved

`BoundaryStep p` itself.  Computer evidence (`data/erasure/slide_check.py`):
in every enumerated board the premises of `BoundaryStep` are never satisfied
together (whenever `v` first is optimal at the boundary, `x` first is optimal
too), and `v` first is optimal there only when `thr < gap v ≤ 2·thr`.  The
boundary step would follow from the move-down inequality checked in
`data/erasure/move_down_check.py`; `NOTES.md` §3 (third attempt) records
where its induction stops.
-/

namespace ErasurePebbling
namespace UpperBound

open RevPebbling.PebblingFoundations

/-! ## Moving a pebble up by one cell -/

/-- The pebble on cell `w` is moved to cell `w + 1`. -/
def moveUp (c : Board) (w : Nat) : Board := toggle (toggle c w) (w + 1)

theorem length_moveUp (c : Board) (w : Nat) : (moveUp c w).length = c.length := by
  simp [moveUp, toggle]

theorem nth_moveUp_self {c : Board} {w : Nat} (hw : nth c w = true) (hl : w < c.length) :
    nth (moveUp c w) w = false := by
  unfold moveUp
  rw [nth_toggle_ne (toggle c w) (by omega : w + 1 ≠ w), nth_toggle_self hl, hw]
  rfl

theorem nth_moveUp_succ {c : Board} {w : Nat} (hw1 : nth c (w + 1) = false)
    (hl : w + 1 < c.length) : nth (moveUp c w) (w + 1) = true := by
  unfold moveUp
  rw [nth_toggle_self (by rw [length_toggle]; exact hl),
    nth_toggle_ne c (by omega : w ≠ w + 1), hw1]
  rfl

theorem nth_moveUp_ne (c : Board) {w j : Nat} (h1 : j ≠ w) (h2 : j ≠ w + 1) :
    nth (moveUp c w) j = nth c j := by
  unfold moveUp
  rw [nth_toggle_ne (toggle c w) (Ne.symm h2), nth_toggle_ne c (Ne.symm h1)]

theorem ones_moveUp {c : Board} {w : Nat} (hw : nth c w = true) (hw1 : nth c (w + 1) = false)
    (hl : w + 1 < c.length) : ones (moveUp c w) = ones c := by
  have h1 := ones_toggle_of_true hw (by omega : w < c.length)
  have h2 : nth (toggle c w) (w + 1) = false := by
    rw [nth_toggle_ne c (by omega : w ≠ w + 1)]; exact hw1
  have h3 := ones_toggle_of_false h2 (by rw [length_toggle]; exact hl)
  unfold moveUp
  omega

/-- Removing the moved pebble gives the same board as removing the original one. -/
theorem toggle_moveUp_succ (c : Board) (w : Nat) : toggle (moveUp c w) (w + 1) = toggle c w := by
  unfold moveUp
  exact toggle_toggle (toggle c w) (w + 1)

/-- Moving `w` up commutes with removing another pebble. -/
theorem moveUp_toggle_comm (c : Board) {w z : Nat} (h1 : z ≠ w) (h2 : z ≠ w + 1) :
    moveUp (toggle c z) w = toggle (moveUp c w) z := by
  unfold moveUp
  rw [toggle_comm c h1, toggle_comm (toggle c w) h2]

theorem lastOn_moveUp_of_le (c : Board) (w z : Nat) (h : z ≤ w) :
    lastOn (moveUp c w) z = lastOn c z := by
  unfold moveUp
  rw [lastOn_toggle_of_le (toggle c w) (w + 1) z (by omega), lastOn_toggle_of_le c w z h]

/-- Above the moved pebble, `lastOn` does not decrease. -/
theorem lastOn_le_lastOn_moveUp {c : Board} {w : Nat} (hw1 : nth c (w + 1) = false)
    (hl : w + 1 < c.length) : ∀ z, w + 1 < z → lastOn c z ≤ lastOn (moveUp c w) z
  | 0, h => by omega
  | z + 1, h => by
      simp only [lastOn]
      by_cases hz : z = w + 1
      · subst hz
        rw [nth_moveUp_succ hw1 hl, hw1]
        simp
        exact Nat.le_trans (lastOn_le c (w + 1)) (Nat.le_succ _)
      · rw [nth_moveUp_ne c (by omega : z ≠ w) hz]
        split
        · exact Nat.le_refl _
        · exact lastOn_le_lastOn_moveUp hw1 hl z (by omega)

/-- The gap of any other pebble does not grow when `w` moves up. -/
theorem gap_moveUp_le {c : Board} {w z : Nat} (hw1 : nth c (w + 1) = false)
    (hl : w + 1 < c.length) (h1 : z ≠ w) (h2 : z ≠ w + 1) : gap (moveUp c w) z ≤ gap c z := by
  unfold gap
  rcases Nat.lt_or_ge z w with h | h
  · rw [lastOn_moveUp_of_le c w z (Nat.le_of_lt h)]
    exact Nat.le_refl _
  · have := lastOn_le_lastOn_moveUp hw1 hl z (by omega)
    omega

/-- The gap of the moved pebble grows by exactly one. -/
theorem gap_moveUp_succ {c : Board} {w : Nat} (hw : nth c w = true) (hl : w < c.length) :
    gap (moveUp c w) (w + 1) = gap c w + 1 := by
  unfold gap
  have h1 : lastOn (moveUp c w) (w + 1) = lastOn c w := by
    simp only [lastOn]
    rw [nth_moveUp_self hw hl]
    simp
    exact lastOn_moveUp_of_le c w w (Nat.le_refl _)
  rw [h1]
  have := lastOn_le c w
  omega

/-- **Moving a pebble up by one cell raises `phi` by at most one.**
Follow an optimal order of `c`: every other pebble keeps or shrinks its gap,
and the moved pebble pays at most one unit more when it is removed. -/
theorem phi_moveUp_le (p : Nat) :
    ∀ (k : Nat) (c : Board) (w : Nat), ones c = k → nth c w = true → nth c (w + 1) = false →
      w + 1 < c.length → phi p (moveUp c w) ≤ phi p c + 1 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro c w hk hw hw1 hl
  have hwl : w < c.length := by omega
  have hpos : 0 < ones c := ones_pos_of_nth hw
  obtain ⟨z, hzl, hz, hphi⟩ := phi_attained (p := p) hpos
  have hones : ones (moveUp c w) = ones c := ones_moveUp hw hw1 hl
  by_cases hzw : z = w
  · subst hzw
    have h1 : nth (moveUp c z) (z + 1) = true := nth_moveUp_succ hw1 hl
    have h2 := phi_le (p := p) h1 (by rw [length_moveUp]; exact hl)
    rw [toggle_moveUp_succ] at h2
    have h3 : exc p (moveUp c z) (z + 1) ≤ exc p c z + 1 := by
      unfold exc
      rw [gap_moveUp_succ hw hwl, hones]
      omega
    omega
  · have hzw1 : z ≠ w + 1 := by
      intro h
      rw [h, hw1] at hz
      cases hz
    have h1 : nth (moveUp c w) z = true := by rw [nth_moveUp_ne c hzw hzw1]; exact hz
    have h2 := phi_le (p := p) h1 (by rw [length_moveUp]; exact hzl)
    rw [← moveUp_toggle_comm c hzw hzw1] at h2
    have hkz : ones (toggle c z) + 1 = ones c := ones_toggle_of_true hz hzl
    have hwz : nth (toggle c z) w = true := by rw [nth_toggle_ne c hzw]; exact hw
    have hw1z : nth (toggle c z) (w + 1) = false := by rw [nth_toggle_ne c hzw1]; exact hw1
    have h3 := ih (ones (toggle c z)) (by omega) (toggle c z) w rfl hwz hw1z
      (by rw [length_toggle]; exact hl)
    have h4 : exc p (moveUp c w) z ≤ exc p c z := by
      unfold exc
      rw [hones]
      have := gap_moveUp_le hw1 hl hzw hzw1
      omega
    omega

/-! ## The closing cases of the induction -/

/-- `FreeRemoval p` on all boards with fewer than `k` pebbles. -/
def FRBelow (p k : Nat) : Prop :=
  ∀ (c : Board) (y : Nat), ones c < k → y < c.length → nth c y = true → ones c ≤ p →
    gap c y ≤ thr p (ones c) → phi p (toggle c y) ≤ phi p c

/-- Removing a pebble enlarges the gap of another pebble by at most its own gap. -/
theorem gap_toggle_le_add (b : Board) {x z : Nat} (hx : nth b x = true) (hzx : z ≠ x) :
    gap (toggle b x) z ≤ gap b z + gap b x := by
  rcases Nat.lt_or_ge z x with h | h
  · rw [gap_toggle_of_le b x z (Nat.le_of_lt h)]
    omega
  · have hxz : x < z := by omega
    rcases Classical.em (Between b x z) with hb | hnb
    · rw [gap_toggle_of_between b hxz hb]
      omega
    · rw [gap_toggle_of_not_between b hx hxz hnb]
      exact Nat.le_refl _

/-- If the first pebble `z` of an optimal order is not `x` and leaves `x` free
(its gap stays within the doubled threshold), the induction closes. -/
theorem free_step_of_still_free {p : Nat} {b : Board} {x z : Nat} (ih : FRBelow p (ones b))
    (hl : x < b.length) (hx : nth b x = true) (hkp : ones b ≤ p)
    (hg : gap b x ≤ thr p (ones b)) (hzl : z < b.length) (hz : nth b z = true) (hzx : z ≠ x)
    (hphi : phi p b = exc p b z + phi p (toggle b z))
    (hfree : gap (toggle b z) x ≤ 2 * thr p (ones b)) : phi p (toggle b x) ≤ phi p b := by
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hk2 : 2 ≤ ones b := two_le_ones hx hz (Ne.symm hzx)
  have hTz : thr p (ones (toggle b z)) = 2 * thr p (ones b) := by
    have := thr_pred p (k := ones b) (by omega) hkp
    rw [← this]; congr 1; omega
  have hTx : thr p (ones (toggle b x)) = 2 * thr p (ones b) := by
    have := thr_pred p (k := ones b) (by omega) hkp
    rw [← this]; congr 1; omega
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have h2 := ih (toggle b z) x (by omega) (by rw [length_toggle]; exact hl) hxz (by omega)
    (by rw [hTz]; exact hfree)
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have h1 := phi_le (p := p) hzx' (by rw [length_toggle]; exact hzl)
  rw [toggle_comm b (Ne.symm hzx)] at h1
  have hga := gap_toggle_le_add b hx hzx
  have h3 : exc p (toggle b x) z ≤ exc p b z := by
    unfold exc
    rw [hTx]
    omega
  omega

/-! ## The remaining case and the reduction -/

/-- **The boundary step** — the only case of `FreeRemoval` that the induction
with the sliding argument does not close.  The pebble `x` sits exactly at the
threshold, its predecessor `v` is not free, removing `v` first is optimal and
removing any other pebble first is strictly worse.  `FreeRemoval` may be used
on all boards with fewer pebbles, and on all boards with the same number of
pebbles whose free pebble has a lower predecessor (e.g. the board with `v`
and `x` both moved down by one cell). -/
def BoundaryStep (p : Nat) : Prop :=
  ∀ (b : Board) (x v : Nat), FRBelow p (ones b) →
    (∀ (c : Board) (y : Nat), ones c = ones b → lastOn c y < lastOn b x → y < c.length →
      nth c y = true → gap c y ≤ thr p (ones c) → phi p (toggle c y) ≤ phi p c) →
    x < b.length → nth b x = true → ones b ≤ p →
    gap b x = thr p (ones b) →
    v < x → nth b v = true → ¬ Between b v x →
    thr p (ones b) < gap b v →
    phi p b = exc p b v + phi p (toggle b v) →
    (∀ z, z < b.length → nth b z = true → z ≠ v →
      phi p b < exc p b z + phi p (toggle b z)) →
    phi p (toggle b x) ≤ phi p b

/-- The induction: strong induction on the pebble count, and for a fixed
count on the position of the predecessor of `x` (the sliding argument). -/
theorem freeRemoval_aux {p : Nat} (hB : BoundaryStep p) :
    ∀ (k L : Nat) (b : Board) (x : Nat), ones b = k → lastOn b x = L → x < b.length →
      nth b x = true → ones b ≤ p → gap b x ≤ thr p (ones b) →
      phi p (toggle b x) ≤ phi p b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro L
  induction L using Nat.strongRecOn with
  | _ L ihL =>
  intro b x hk hL hl hx hkp hg
  have ih : FRBelow p (ones b) := by
    intro c y hc hyl hy hcp hgy
    exact ihk (ones c) (by omega) (lastOn c y) c y rfl rfl hyl hy hcp hgy
  have hT1 : 1 ≤ thr p (ones b) := one_le_thr p (ones b)
  -- Is there an optimal first step that is `x` itself or leaves `x` free?
  by_cases hex : ∃ z, z < b.length ∧ nth b z = true ∧
      phi p b = exc p b z + phi p (toggle b z) ∧
      (z = x ∨ gap (toggle b z) x ≤ 2 * thr p (ones b))
  · obtain ⟨z, hzl, hz, hphi, hc⟩ := hex
    by_cases hzx : z = x
    · rw [hzx] at hphi
      omega
    · rcases hc with h | hfree
      · exact absurd h hzx
      · exact free_step_of_still_free ih hl hx hkp hg hzl hz hzx hphi hfree
  -- Otherwise every optimal first step is the predecessor `v` of `x`, and the
  -- merged gap exceeds the doubled threshold.
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨v, hvl, hv, hphi⟩ := phi_attained (p := p) hpos
  have hvx : v ≠ x := fun h => hex ⟨v, hvl, hv, hphi, Or.inl h⟩
  have hnf : 2 * thr p (ones b) < gap (toggle b v) x := by
    rcases Nat.lt_or_ge (2 * thr p (ones b)) (gap (toggle b v) x) with h | h
    · exact h
    · exact absurd ⟨v, hvl, hv, hphi, Or.inr h⟩ hex
  have hvlt : v < x := by
    rcases Nat.lt_or_ge v x with h | h
    · exact h
    · have : gap (toggle b v) x = gap b x := gap_toggle_of_le b v x h
      omega
  have hnb : ¬ Between b v x := by
    intro hb
    have : gap (toggle b v) x = gap b x := gap_toggle_of_between b hvlt hb
    omega
  have hgs : gap (toggle b v) x = gap b x + gap b v := gap_toggle_of_not_between b hv hvlt hnb
  have hav : thr p (ones b) < gap b v := by omega
  have huniq : ∀ z, z < b.length → nth b z = true → z ≠ v →
      phi p b < exc p b z + phi p (toggle b z) := by
    intro z hzl hz hzv
    have hle := phi_le (p := p) hz hzl
    rcases Nat.lt_or_ge (phi p b) (exc p b z + phi p (toggle b z)) with h | h
    · exact h
    · exfalso
      have heq : phi p b = exc p b z + phi p (toggle b z) := by omega
      by_cases hzx : z = x
      · exact hex ⟨z, hzl, hz, heq, Or.inl hzx⟩
      · apply hex
        refine ⟨z, hzl, hz, heq, Or.inr ?_⟩
        have hgz : gap (toggle b z) x = gap b x := by
          rcases Nat.lt_or_ge z x with h1 | h1
          · rcases Nat.lt_or_ge z v with h2 | h2
            · exact gap_toggle_of_between b h1 ⟨v, h2, hvlt, hv⟩
            · exact absurd ⟨z, by omega, h1, hz⟩ hnb
          · exact gap_toggle_of_le b z x h1
        omega
  rcases Nat.lt_or_ge (gap b x) (thr p (ones b)) with hlt | hge
  · -- The sliding argument: move `v` down by one cell.
    -- `v = v' + 1` and cell `v'` is empty, because `gap v ≥ 2`.
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := by
      cases v with
      | zero =>
          exfalso
          have : gap b 0 = 1 := rfl
          omega
      | succ v' => exact ⟨v', rfl⟩
    have hv'f : nth b v' = false := by
      cases hn : nth b v' with
      | false => rfl
      | true =>
          exfalso
          have : gap b (v' + 1) = 1 := by
            unfold gap
            simp [lastOn, hn]
          omega
    have hv'l : v' < b.length := by omega
    -- the slid board
    have hb'def : moveUp (toggle (toggle b (v' + 1)) v') v' = b := by
      unfold moveUp
      rw [toggle_toggle, toggle_toggle]
    -- name it
    let b' : Board := toggle (toggle b (v' + 1)) v'
    have hb' : moveUp b' v' = b := hb'def
    have hlen' : b'.length = b.length := by
      show (toggle (toggle b (v' + 1)) v').length = b.length
      rw [length_toggle, length_toggle]
    have hnv' : nth b' v' = true := by
      show nth (toggle (toggle b (v' + 1)) v') v' = true
      rw [nth_toggle_self (by rw [length_toggle]; exact hv'l),
        nth_toggle_ne b (by omega : v' + 1 ≠ v'), hv'f]
      rfl
    have hnv : nth b' (v' + 1) = false := by
      show nth (toggle (toggle b (v' + 1)) v') (v' + 1) = false
      rw [nth_toggle_ne (toggle b (v' + 1)) (by omega : v' ≠ v' + 1), nth_toggle_self hvl, hv]
      rfl
    have hnj : ∀ j, j ≠ v' → j ≠ v' + 1 → nth b' j = nth b j := by
      intro j h1 h2
      show nth (toggle (toggle b (v' + 1)) v') j = nth b j
      rw [nth_toggle_ne (toggle b (v' + 1)) (Ne.symm h1), nth_toggle_ne b (Ne.symm h2)]
    have hones' : ones b' = ones b := by
      have h1 := ones_toggle_of_true hv hvl
      have h2 : nth (toggle b (v' + 1)) v' = false := by
        rw [nth_toggle_ne b (by omega : v' + 1 ≠ v')]; exact hv'f
      have h3 := ones_toggle_of_false h2 (by rw [length_toggle]; exact hv'l)
      show ones (toggle (toggle b (v' + 1)) v') = ones b
      omega
    have htog' : toggle b' v' = toggle b (v' + 1) := by
      show toggle (toggle (toggle b (v' + 1)) v') v' = toggle b (v' + 1)
      exact toggle_toggle _ _
    have hx' : nth b' x = true := by rw [hnj x (by omega) (by omega)]; exact hx
    -- gaps on the slid board
    have hlast_v' : lastOn b' v' = lastOn b v' := by
      show lastOn (toggle (toggle b (v' + 1)) v') v' = lastOn b v'
      rw [lastOn_toggle_of_le (toggle b (v' + 1)) v' v' (Nat.le_refl _),
        lastOn_toggle_of_le b (v' + 1) v' (by omega)]
    have hlast_v : lastOn b (v' + 1) = lastOn b v' := by
      simp [lastOn, hv'f]
    have hgv' : gap b' v' + 1 = gap b (v' + 1) := by
      unfold gap
      rw [hlast_v', hlast_v]
      have := lastOn_le b v'
      omega
    have hnb' : ¬ Between b' v' x := by
      rintro ⟨j, h1, h2, h3⟩
      by_cases hj : j = v' + 1
      · rw [hj, hnv] at h3
        cases h3
      · rw [hnj j (by omega) hj] at h3
        exact hnb ⟨j, by omega, h2, h3⟩
    have hlastx' : lastOn b' x = v' + 1 := lastOn_of_not_between b' hnv' x (by omega) hnb'
    have hlastx : lastOn b x = v' + 1 + 1 := lastOn_of_not_between b hv x hvlt hnb
    have hgx' : gap b' x = gap b x + 1 := by
      unfold gap
      rw [hlastx', hlastx]
      omega
    -- inner induction: `x` is still free on the slid board
    have hR : phi p (toggle b' x) ≤ phi p b' :=
      ihL (lastOn b' x) (by omega) b' x (by omega) rfl (by omega) hx' (by omega)
        (by rw [hgx', hones']; omega)
    -- the slid pebble pays one unit less
    have hP := phi_le (p := p) hnv' (by omega : v' < b'.length)
    rw [htog'] at hP
    have e1 : exc p b (v' + 1) = gap b (v' + 1) - thr p (ones b) := rfl
    have e2 : exc p b' v' = gap b' v' - thr p (ones b) := by
      unfold exc
      rw [hones']
    -- moving the pebble back up costs at most one
    have hxv' : x ≠ v' := by omega
    have hxv : x ≠ v' + 1 := by omega
    have hM := phi_moveUp_le p (ones (toggle b' x)) (toggle b' x) v' rfl
      (by rw [nth_toggle_ne b' hxv']; exact hnv')
      (by rw [nth_toggle_ne b' hxv]; exact hnv)
      (by rw [length_toggle]; omega)
    rw [moveUp_toggle_comm b' hxv' hxv, hb'] at hM
    omega
  · -- The boundary: `gap x = thr`.
    have ihsame : ∀ (c : Board) (y : Nat), ones c = ones b → lastOn c y < lastOn b x →
        y < c.length → nth c y = true → gap c y ≤ thr p (ones c) →
        phi p (toggle c y) ≤ phi p c := by
      intro c y hc hlt hyl hy hgy
      exact ihL (lastOn c y) (by omega) c y (by omega) rfl hyl hy (by omega) hgy
    exact hB b x v ih ihsame hl hx hkp (by omega) hvlt hv hnb hav hphi huniq

/-- **Reduction to the boundary step.** -/
theorem freeRemoval_of_boundaryStep {p : Nat} (hB : BoundaryStep p) : FreeRemoval p := by
  intro b x hl hx hk hg
  exact freeRemoval_aux hB (ones b) (lastOn b x) b x rfl rfl hl hx hk hg

theorem removalLemma_of_boundaryStep {p : Nat} (hB : BoundaryStep p) : RemovalLemma p :=
  removalLemma_of_freeRemoval (freeRemoval_of_boundaryStep hB)

/-- Conjecture B2 follows from the boundary step. -/
theorem conjB2_of_boundaryStep (p e : Nat) (hp : 2 ≤ p) (hB : BoundaryStep p) : ConjB2 p e :=
  conjB2_of_removalLemma p e hp (removalLemma_of_boundaryStep hB)

/-! ## Computational anchors

`moveUpCheck p n` evaluates `phi_moveUp_le` on all boards of length `n`
(sanity check of the statement, including its tightness: the bound `+ 1`
cannot be dropped). -/

def moveUpCheck (p n : Nat) (slack : Nat) : Bool :=
  (allBoards n).all fun c =>
    !(decide (ones c ≤ p)) ||
      (List.range (n - 1)).all fun w =>
        !(nth c w && !nth c (w + 1)) || decide (phi p (moveUp c w) ≤ phi p c + slack)

#guard moveUpCheck 3 9 1
#guard moveUpCheck 4 10 1
#guard !moveUpCheck 3 9 0

end UpperBound
end ErasurePebbling
