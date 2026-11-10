import ErasurePebbling.Conjectures

/-!
# Towards the upper bound of Conjecture B2: a gap potential on boards

Conjecture B2 of RC-02 states `reach(p, e) = (e + 2)·2^(p−2)`.  The lower
bound is `theoremB1`; the case `e = 0` is `reachIs_zero`.  This file
reduces the missing upper bound `reach(p, e) ≤ (e + 2)·2^(p−2)` to a
single combinatorial lemma about a *potential* `phi p b` of a board.

## The potential

For a board `b` write `k = ones b` for its pebble count and `T_k = 2^(p−k)`
for the *threshold* at count `k`.  The *gap* of a pebble on cell `z` is the
distance from node `z + 1` to the highest pebbled node below it (the free
source `0` if none), and its *excess* is `gap − T_k` (truncated).  The
potential is the least total excess over all orders of removing the
pebbles one by one:

  `phi p b = min over pebbled z of (exc p b z + phi p (toggle b z))`,
  `phi p ∅ = 0`.

(Equivalently: the least total excess over all orders of *inserting* the
pebbles, each insertion being measured against the threshold at the
count it creates.  Reading the thresholds as the reach of the free pebbles,
`phi` measures how far a board is from being reversibly buildable from the
empty board.)

## What is proved here (no `sorry`, standard axioms)

* `phi_toggle_le_of_place`: a legal placement never increases `phi`
  (`okMove b x → phi p (toggle b x) ≤ phi p b`);
* `phi_toggle_le_of_remove`: removing *any* pebble raises `phi` by at most
  `2^(p−2)` — this is the erasure step;
* `phi_empty = 0` and `phi (target n) ≥ n − 2^(p−1)`;
* `reach_le_of_removalLemma`: **if** moreover a *reversible* removal never
  increases `phi` (`RemovalLemma p` below), then every clean plan with peak
  `p` and `e` erasures has `n ≤ (e + 2)·2^(p−2)`, i.e. Conjecture B2
  (`conjB2_of_removalLemma`).

## What is not proved

`RemovalLemma p` (a pebble with its predecessor pebbled can be removed
without increasing `phi`) is the whole remaining content of Conjecture B2.
It was checked exhaustively by computer for `p ≤ 5` on all boards with at
most `p` pebbles among the first 22–40 nodes (`scratchpad/lev.py`), and the
companion statements used in the search (`phi` is the exact charged value
of the erasure game, i.e. `max_e (reach_e − e·2^(p−2))`, for `p ≤ 4`) were
verified against the exhaustive tables of `data/erasure/`.  A paper proof
is open; see the worker report for the state of the attempts.

**Update (2026-11-10).**  Conjecture B2 is proved in `Compression.lean`
without `RemovalLemma`, with a smaller potential (the number of cells that
must be squeezed out of the chain to make the weighted `phi` vanish).
`RemovalLemma p` remains open but is no longer needed.
-/

namespace ErasurePebbling
namespace UpperBound

open RevPebbling.PebblingFoundations

/-! ## Predecessor, gap, excess -/

/-- Node (`j + 1`) of the highest pebbled cell `j` strictly below cell `z`,
or `0` (the free source) if there is none. -/
def lastOn (b : Board) : Nat → Nat
  | 0 => 0
  | z + 1 => if nth b z then z + 1 else lastOn b z

/-- Gap of cell `z`: distance from node `z + 1` down to the previous pebbled
node (or the source). -/
def gap (b : Board) (z : Nat) : Nat := z + 1 - lastOn b z

/-- Threshold at pebble count `k`: the clean reach of `p − k` free pebbles. -/
def thr (p k : Nat) : Nat := 2 ^ (p - k)

/-- Excess of the pebble on `z`, measured at the current count of `b`. -/
def exc (p : Nat) (b : Board) (z : Nat) : Nat := gap b z - thr p (ones b)

/-- The pebbled cells of a board. -/
def cells (b : Board) : List Nat := (List.range b.length).filter (fun i => nth b i)

/-- Minimum of a list (`0` for the empty list). -/
def listMin : List Nat → Nat
  | [] => 0
  | [a] => a
  | a :: c :: rest => min a (listMin (c :: rest))

/-- The potential, with explicit fuel (`fuel ≥ ones b` suffices). -/
def phiF (p : Nat) : Nat → Board → Nat
  | 0, _ => 0
  | f + 1, b => listMin ((cells b).map fun z => exc p b z + phiF p f (toggle b z))

/-- The potential of a board. -/
def phi (p : Nat) (b : Board) : Nat := phiF p (ones b) b

/-! ## Lists -/

theorem listMin_le_of_mem : ∀ (l : List Nat) (a : Nat), a ∈ l → listMin l ≤ a
  | [], a, h => by simp at h
  | [c], a, h => by
      simp at h; subst h; exact Nat.le_refl _
  | c :: d :: rest, a, h => by
      simp only [listMin]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (listMin_le_of_mem (d :: rest) a h)

theorem listMin_mem : ∀ (l : List Nat), l ≠ [] → listMin l ∈ l
  | [], h => absurd rfl h
  | [c], _ => by simp [listMin]
  | c :: d :: rest, _ => by
      simp only [listMin]
      rcases Nat.le_total c (listMin (d :: rest)) with h | h
      · rw [Nat.min_eq_left h]; exact List.mem_cons_self ..
      · rw [Nat.min_eq_right h]
        exact List.mem_cons_of_mem _ (listMin_mem (d :: rest) (by simp))

theorem le_listMin (l : List Nat) (c : Nat) (hne : l ≠ []) (h : ∀ a ∈ l, c ≤ a) :
    c ≤ listMin l :=
  h _ (listMin_mem l hne)

/-! ## Cells and counts -/

theorem mem_cells (b : Board) (z : Nat) : z ∈ cells b ↔ z < b.length ∧ nth b z = true := by
  simp [cells, List.mem_filter, List.mem_range]

theorem exists_nth_of_ones_pos : ∀ (b : Board), 0 < ones b → ∃ z, z < b.length ∧ nth b z = true
  | [], h => by simp [ones] at h
  | a :: t, h => by
      cases a with
      | true => exact ⟨0, by simp, rfl⟩
      | false =>
          have ht : 0 < ones t := by simpa [ones] using h
          obtain ⟨z, hz, hn⟩ := exists_nth_of_ones_pos t ht
          exact ⟨z + 1, by simp; omega, by simpa [nth] using hn⟩

theorem cells_ne_nil_of_ones_pos {b : Board} (h : 0 < ones b) : cells b ≠ [] := by
  obtain ⟨z, hz, hn⟩ := exists_nth_of_ones_pos b h
  intro hc
  have : z ∈ cells b := (mem_cells b z).mpr ⟨hz, hn⟩
  rw [hc] at this
  simp at this

theorem cells_eq_nil_of_ones_zero {b : Board} (h : ones b = 0) : cells b = [] := by
  cases hc : cells b with
  | nil => rfl
  | cons z rest =>
      have hz : z ∈ cells b := by rw [hc]; exact List.mem_cons_self ..
      have := ones_pos_of_nth ((mem_cells b z).mp hz).2
      omega

theorem ones_toggle_of_true {b : Board} {z : Nat} (hz : nth b z = true) (hl : z < b.length) :
    ones (toggle b z) + 1 = ones b := by
  have := ones_set b z (!(nth b z)) hl
  rw [hz] at this
  simpa [toggle, hz] using this

theorem ones_toggle_of_false {b : Board} {z : Nat} (hz : nth b z = false) (hl : z < b.length) :
    ones (toggle b z) = ones b + 1 := by
  have := ones_set b z (!(nth b z)) hl
  rw [hz] at this
  simpa [toggle, hz] using this

theorem length_toggle (b : Board) (z : Nat) : (toggle b z).length = b.length := by
  simp [toggle]

theorem nth_toggle_self {b : Board} {z : Nat} (hl : z < b.length) :
    nth (toggle b z) z = !(nth b z) := nth_set_eq b z _ hl

theorem nth_toggle_ne (b : Board) {z w : Nat} (h : z ≠ w) : nth (toggle b z) w = nth b w :=
  nth_set_ne b z w _ h

theorem toggle_comm (b : Board) {x z : Nat} (h : x ≠ z) :
    toggle (toggle b x) z = toggle (toggle b z) x := by
  unfold toggle
  rw [nth_set_ne b x z _ h, nth_set_ne b z x _ (Ne.symm h)]
  exact set_comm b x z _ _ h

/-- Two distinct pebbles give a count of at least two. -/
theorem two_le_ones {b : Board} {x z : Nat} (hx : nth b x = true) (hz : nth b z = true)
    (hxz : x ≠ z) : 2 ≤ ones b := by
  have hl : z < b.length := nth_true_lt_length hz
  have h1 := ones_toggle_of_true hz hl
  have h2 : nth (toggle b z) x = true := by rw [nth_toggle_ne b (Ne.symm hxz)]; exact hx
  have := ones_pos_of_nth h2
  omega

/-! ## The potential: fuel, unfolding, the two basic facts -/

theorem phiF_fuel (p : Nat) : ∀ (f : Nat) (b : Board), ones b ≤ f → phiF p f b = phiF p (ones b) b
  | 0, b, h => by
      have : ones b = 0 := by omega
      rw [this]
  | f + 1, b, h => by
      cases hk : ones b with
      | zero =>
          simp only [phiF]
          rw [cells_eq_nil_of_ones_zero hk]
          rfl
      | succ m =>
          simp only [phiF]
          congr 1
          apply List.map_congr_left
          intro z hz
          obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
          have hm : ones (toggle b z) = m := by
            have := ones_toggle_of_true hzn hzl; omega
          rw [phiF_fuel p f (toggle b z) (by omega), hm]

theorem phi_unfold (p : Nat) (b : Board) :
    phi p b = listMin ((cells b).map fun z => exc p b z + phi p (toggle b z)) := by
  unfold phi
  cases hk : ones b with
  | zero =>
      simp only [phiF]
      rw [cells_eq_nil_of_ones_zero hk]
      rfl
  | succ m =>
      simp only [phiF]
      congr 1
      apply List.map_congr_left
      intro z hz
      obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
      have hm : ones (toggle b z) = m := by
        have := ones_toggle_of_true hzn hzl; omega
      rw [hm]

/-- (F1) Removing a pebble first is one of the options. -/
theorem phi_le {p : Nat} {b : Board} {z : Nat} (hz : nth b z = true) (hl : z < b.length) :
    phi p b ≤ exc p b z + phi p (toggle b z) := by
  rw [phi_unfold]
  apply listMin_le_of_mem
  exact List.mem_map.mpr ⟨z, (mem_cells b z).mpr ⟨hl, hz⟩, rfl⟩

/-- The minimum is attained by some pebble. -/
theorem phi_attained {p : Nat} {b : Board} (h : 0 < ones b) :
    ∃ z, z < b.length ∧ nth b z = true ∧ phi p b = exc p b z + phi p (toggle b z) := by
  rw [phi_unfold]
  have hne : (cells b).map (fun z => exc p b z + phi p (toggle b z)) ≠ [] := by
    intro hc
    exact cells_ne_nil_of_ones_pos h (List.map_eq_nil_iff.mp hc)
  obtain ⟨z, hz, hv⟩ := List.mem_map.mp (listMin_mem _ hne)
  obtain ⟨hzl, hzn⟩ := (mem_cells b z).mp hz
  exact ⟨z, hzl, hzn, hv.symm⟩

theorem phi_of_ones_zero {p : Nat} {b : Board} (h : ones b = 0) : phi p b = 0 := by
  rw [phi_unfold, cells_eq_nil_of_ones_zero h]
  rfl

/-! ## Gaps under a move -/

theorem lastOn_le (b : Board) : ∀ z, lastOn b z ≤ z
  | 0 => Nat.le_refl _
  | z + 1 => by
      simp only [lastOn]
      split
      · exact Nat.le_refl _
      · exact Nat.le_trans (lastOn_le b z) (Nat.le_succ _)

/-- Cells at or above `x` do not influence `lastOn · z` for `z ≤ x`. -/
theorem lastOn_set_of_le (b : Board) (x : Nat) (v : Bool) : ∀ z, z ≤ x → lastOn (b.set x v) z = lastOn b z
  | 0, _ => rfl
  | z + 1, h => by
      simp only [lastOn]
      rw [nth_set_ne b x z v (by omega), lastOn_set_of_le b x v z (by omega)]

theorem lastOn_toggle_of_le (b : Board) (x z : Nat) (h : z ≤ x) :
    lastOn (toggle b x) z = lastOn b z :=
  lastOn_set_of_le b x _ z h

theorem gap_toggle_of_le (b : Board) (x z : Nat) (h : z ≤ x) : gap (toggle b x) z = gap b z := by
  unfold gap; rw [lastOn_toggle_of_le b x z h]

/-- Removing a pebble never raises `lastOn`. -/
theorem lastOn_toggle_le_of_true (b : Board) {x : Nat} (hx : nth b x = true) :
    ∀ z, lastOn (toggle b x) z ≤ lastOn b z
  | 0 => Nat.le_refl _
  | z + 1 => by
      simp only [lastOn]
      by_cases hzx : z = x
      · subst hzx
        have hl : z < b.length := nth_true_lt_length hx
        rw [nth_toggle_self hl, hx]
        simp
        exact Nat.le_trans (lastOn_toggle_le_of_true b hx z) (Nat.le_trans (lastOn_le b z) (Nat.le_succ _))
      · rw [nth_toggle_ne b (Ne.symm hzx)]
        split
        · exact Nat.le_refl _
        · exact lastOn_toggle_le_of_true b hx z

theorem gap_le_gap_toggle_of_true (b : Board) {x : Nat} (hx : nth b x = true) (z : Nat) :
    gap b z ≤ gap (toggle b x) z := by
  unfold gap
  have := lastOn_toggle_le_of_true b hx z
  omega

/-- A pebble strictly between `x` and `z`. -/
def Between (b : Board) (x z : Nat) : Prop := ∃ j, x < j ∧ j < z ∧ nth b j = true

theorem lastOn_toggle_of_between (b : Board) (x : Nat) :
    ∀ z, x < z → Between b x z → lastOn (toggle b x) z = lastOn b z
  | 0, h, _ => by omega
  | z + 1, _, ⟨j, hxj, hjz, hj⟩ => by
      simp only [lastOn]
      have hzx : z ≠ x := by omega
      rw [nth_toggle_ne b (Ne.symm hzx)]
      cases hn : nth b z with
      | true => rfl
      | false =>
          have hjz' : j < z := by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjz) with h | h
            · exact h
            · subst h; rw [hn] at hj; simp at hj
          exact lastOn_toggle_of_between b x z (by omega) ⟨j, hxj, hjz', hj⟩

theorem gap_toggle_of_between (b : Board) {x z : Nat} (hxz : x < z) (hb : Between b x z) :
    gap (toggle b x) z = gap b z := by
  unfold gap; rw [lastOn_toggle_of_between b x z hxz hb]

/-- No pebble between `x` and `z`: the predecessor of `z` is `x`. -/
theorem lastOn_of_not_between (b : Board) {x : Nat} (hx : nth b x = true) :
    ∀ z, x < z → ¬ Between b x z → lastOn b z = x + 1
  | 0, h, _ => by omega
  | z + 1, h, hnb => by
      simp only [lastOn]
      by_cases hzx : z = x
      · subst hzx; rw [hx]; rfl
      · have hn : nth b z = false := by
          cases hn : nth b z with
          | true => exact absurd ⟨z, by omega, by omega, hn⟩ hnb
          | false => rfl
        rw [hn]
        simp only [Bool.false_eq_true, if_false]
        exact lastOn_of_not_between b hx z (by omega)
          (fun ⟨j, h1, h2, h3⟩ => hnb ⟨j, h1, by omega, h3⟩)

theorem lastOn_toggle_of_not_between (b : Board) {x : Nat} (hx : nth b x = true) :
    ∀ z, x < z → ¬ Between b x z → lastOn (toggle b x) z = lastOn b x
  | 0, h, _ => by omega
  | z + 1, h, hnb => by
      simp only [lastOn]
      by_cases hzx : z = x
      · subst hzx
        rw [nth_toggle_self (nth_true_lt_length hx), hx]
        simp
        exact lastOn_toggle_of_le b z z (Nat.le_refl _)
      · have hn : nth b z = false := by
          cases hn : nth b z with
          | true => exact absurd ⟨z, by omega, by omega, hn⟩ hnb
          | false => rfl
        rw [nth_toggle_ne b (Ne.symm hzx), hn]
        simp only [Bool.false_eq_true, if_false]
        exact lastOn_toggle_of_not_between b hx z (by omega)
          (fun ⟨j, h1, h2, h3⟩ => hnb ⟨j, h1, by omega, h3⟩)

/-- Removing `x` merges its gap into the gap of its successor. -/
theorem gap_toggle_of_not_between (b : Board) {x z : Nat} (hx : nth b x = true) (hxz : x < z)
    (hnb : ¬ Between b x z) : gap (toggle b x) z = gap b z + gap b x := by
  unfold gap
  rw [lastOn_toggle_of_not_between b hx z hxz hnb, lastOn_of_not_between b hx z hxz hnb]
  have := lastOn_le b x
  omega

theorem lastOn_eq_zero (b : Board) : ∀ z, (∀ j, j < z → nth b j = false) → lastOn b z = 0
  | 0, _ => rfl
  | z + 1, h => by
      simp only [lastOn]
      rw [h z (Nat.lt_succ_self z)]
      simp only [Bool.false_eq_true, if_false]
      exact lastOn_eq_zero b z (fun j hj => h j (by omega))

/-- A move with its predecessor pebbled (or at the entrance) has gap `1`,
before and after the move. -/
theorem gap_eq_one_of_okMove (b : Board) {x : Nat} (hok : okMove b x = true) : gap b x = 1 := by
  unfold gap
  cases x with
  | zero => rfl
  | succ w =>
      have hw : nth b w = true := by simpa [okMove] using hok
      simp [lastOn, hw]

theorem gap_toggle_self_of_okMove (b : Board) {x : Nat} (hok : okMove b x = true) :
    gap (toggle b x) x = 1 := by
  rw [gap_toggle_of_le b x x (Nat.le_refl _)]
  exact gap_eq_one_of_okMove b hok

/-! ## Thresholds -/

theorem one_le_thr (p k : Nat) : 1 ≤ thr p k := Nat.one_le_two_pow

theorem thr_le_thr_of_le (p : Nat) {k k' : Nat} (h : k' ≤ k) : thr p k ≤ thr p k' :=
  Nat.pow_le_pow_right (by decide) (by omega)

theorem thr_pred (p : Nat) {k : Nat} (hk1 : 1 ≤ k) (hkp : k ≤ p) : thr p (k - 1) = 2 * thr p k := by
  unfold thr
  have : p - (k - 1) = (p - k) + 1 := by omega
  rw [this, Nat.pow_succ]; omega

theorem thr_le_Q (p : Nat) {k : Nat} (hk : 2 ≤ k) : thr p k ≤ 2 ^ (p - 2) :=
  thr_le_thr_of_le p hk

/-! ## The two provable move steps -/

/-- A legal placement never increases the potential. -/
theorem phi_toggle_le_of_place (p : Nat) {b : Board} {x : Nat} (hx : nth b x = false)
    (hok : okMove b x = true) (hl : x < b.length) : phi p (toggle b x) ≤ phi p b := by
  have h1 : nth (toggle b x) x = true := by rw [nth_toggle_self hl, hx]; rfl
  have h2 := phi_le (p := p) h1 (by rw [length_toggle]; exact hl)
  rw [toggle_toggle] at h2
  have h3 : exc p (toggle b x) x = 0 := by
    unfold exc
    rw [gap_toggle_self_of_okMove b hok]
    have := one_le_thr p (ones (toggle b x))
    omega
  rw [h3] at h2
  simpa using h2

/-- Removing any pebble raises the potential by at most `2^(p−2)`
(the erasure step).  Induction on the pebble count through the recursive
definition of `phi`; the only delicate case is the removal of the
predecessor of the pebble chosen first by the optimal order. -/
theorem phi_toggle_le_of_remove (p : Nat) :
    ∀ (k : Nat) (b : Board) (x : Nat), ones b = k → ones b ≤ p → nth b x = true → x < b.length →
      phi p (toggle b x) ≤ phi p b + 2 ^ (p - 2) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro b x hk hkp hx hl
  have hQ1 : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  have hpos : 0 < ones b := ones_pos_of_nth hx
  obtain ⟨z, hzl, hz, hphi⟩ := phi_attained (p := p) hpos
  by_cases hzx : z = x
  · rw [hzx] at hphi
    omega
  -- `ones (toggle b z) = k - 1`
  have hkz : ones (toggle b z) + 1 = ones b := ones_toggle_of_true hz hzl
  have hxz : nth (toggle b z) x = true := by rw [nth_toggle_ne b hzx]; exact hx
  have hxzl : x < (toggle b z).length := by rw [length_toggle]; exact hl
  -- the removal of `z` from `toggle b x`, and of `x` from `toggle b z`, commute
  have hcomm : toggle (toggle b x) z = toggle (toggle b z) x := toggle_comm b (Ne.symm hzx)
  have hzx' : nth (toggle b x) z = true := by rw [nth_toggle_ne b (Ne.symm hzx)]; exact hz
  have hzxl : z < (toggle b x).length := by rw [length_toggle]; exact hzl
  have hkx : ones (toggle b x) + 1 = ones b := ones_toggle_of_true hx hl
  have hthr : thr p (ones b) ≤ thr p (ones (toggle b x)) := thr_le_thr_of_le p (by omega)
  -- Case A: the gap of `z` is unchanged by removing `x`.
  have caseA : gap (toggle b x) z = gap b z →
      phi p (toggle b x) ≤ phi p b + 2 ^ (p - 2) := by
    intro hg
    have h1 := phi_le (p := p) hzx' hzxl
    rw [hcomm] at h1
    have h2 := ih (ones (toggle b z)) (by omega) (toggle b z) x rfl (by omega) hxz hxzl
    have h3 : exc p (toggle b x) z ≤ exc p b z := by
      unfold exc; rw [hg]; omega
    omega
  rcases Nat.lt_or_ge z x with hlt | hge
  · exact caseA (gap_toggle_of_le b x z (Nat.le_of_lt hlt))
  · have hgt : x < z := by omega
    rcases Classical.em (Between b x z) with hb | hnb
    · exact caseA (gap_toggle_of_between b hgt hb)
    -- Case B: `z` is the successor `s` of `x`; look one level deeper.
    have hgs : gap (toggle b x) z = gap b z + gap b x := gap_toggle_of_not_between b hx hgt hnb
    have hk2 : 2 ≤ ones b := two_le_ones hx hz (Ne.symm hzx)
    have hT2 : thr p (ones (toggle b x)) = 2 * thr p (ones b) := by
      have := thr_pred p (k := ones b) (by omega) hkp
      rw [← this]; congr 1; omega
    have hTQ : thr p (ones b) ≤ 2 ^ (p - 2) := thr_le_Q p hk2
    -- the board after removing `s = z`
    have hpos1 : 0 < ones (toggle b z) := ones_pos_of_nth hxz
    obtain ⟨z', hz'l, hz', hphi1⟩ := phi_attained (p := p) hpos1
    have hT1 : thr p (ones (toggle b z)) = 2 * thr p (ones b) := by
      have := thr_pred p (k := ones b) (by omega) hkp
      rw [← this]; congr 1; omega
    by_cases hz'x : z' = x
    · -- (i) after `s`, the optimal order removes `x`
      rw [hz'x] at hphi1
      have h1 := phi_le (p := p) hzx' hzxl
      rw [hcomm] at h1
      have hgx : gap (toggle b z) x = gap b x := gap_toggle_of_le b z x (Nat.le_of_lt hgt)
      have e1 : exc p (toggle b x) z = (gap b z + gap b x) - 2 * thr p (ones b) := by
        unfold exc; rw [hgs, hT2]
      have e2 : exc p b z = gap b z - thr p (ones b) := rfl
      have e3 : exc p (toggle b z) x = gap b x - 2 * thr p (ones b) := by
        unfold exc; rw [hgx, hT1]
      omega
    · -- (ii) after `s`, the optimal order removes some other `z'`
      have hz'b : nth b z' = true := by
        rw [nth_toggle_ne b (Ne.symm ?_)] at hz'
        · exact hz'
        · intro h; subst h; exact (by simp [nth_toggle_self hzl, hz] at hz')
      have hz'z : z' ≠ z := by
        intro h; subst h; simp [nth_toggle_self hzl, hz] at hz'
      have hz'bl : z' < b.length := by rw [length_toggle] at hz'l; exact hz'l
      -- removing `z'` from `toggle b x` ...
      have hz'tx : nth (toggle b x) z' = true := by rw [nth_toggle_ne b (Ne.symm hz'x)]; exact hz'b
      have h1 := phi_le (p := p) hz'tx (by rw [length_toggle]; exact hz'bl)
      rw [toggle_comm b (Ne.symm hz'x)] at h1
      -- ... then `x` from `toggle b z'` (induction) ...
      have hkz' : ones (toggle b z') + 1 = ones b := ones_toggle_of_true hz'b hz'bl
      have hxz' : nth (toggle b z') x = true := by rw [nth_toggle_ne b hz'x]; exact hx
      have h2 := ih (ones (toggle b z')) (by omega) (toggle b z') x rfl (by omega) hxz'
        (by rw [length_toggle]; exact hl)
      -- ... and `s` from `toggle b z'`
      have hztz' : nth (toggle b z') z = true := by rw [nth_toggle_ne b hz'z]; exact hz
      have h3 := phi_le (p := p) hztz' (by rw [length_toggle]; exact hzl)
      rw [toggle_comm b hz'z] at h3
      -- gaps: `z'` is below `x` or above `s`
      have hz'pos : z' < x ∨ z < z' := by
        rcases Nat.lt_or_ge z' x with h | h
        · exact Or.inl h
        · rcases Nat.lt_or_ge z z' with h' | h'
          · exact Or.inr h'
          · exfalso
            have : x < z' := by omega
            exact hnb ⟨z', this, by omega, hz'b⟩
      have hgz' : gap (toggle b x) z' = gap b z' := by
        rcases hz'pos with h | h
        · exact gap_toggle_of_le b x z' (Nat.le_of_lt h)
        · exact gap_toggle_of_between b (by omega) ⟨z, hgt, h, hz⟩
      have hgs' : gap (toggle b z') z = gap b z := by
        rcases hz'pos with h | h
        · exact gap_toggle_of_between b (by omega) ⟨x, h, hgt, hx⟩
        · exact gap_toggle_of_le b z' z (Nat.le_of_lt h)
      have hgz'1 : gap b z' ≤ gap (toggle b z) z' := gap_le_gap_toggle_of_true b hz z'
      have hT1' : thr p (ones (toggle b z')) = 2 * thr p (ones b) := by
        have := thr_pred p (k := ones b) (by omega) hkp
        rw [← this]; congr 1; omega
      have e1 : exc p (toggle b x) z' = gap b z' - 2 * thr p (ones b) := by
        unfold exc; rw [hgz', hT2]
      have e2 : exc p (toggle b z') z = gap b z - 2 * thr p (ones b) := by
        unfold exc; rw [hgs', hT1']
      have e3 : exc p b z = gap b z - thr p (ones b) := rfl
      have e4 : exc p (toggle b z) z' = gap (toggle b z) z' - 2 * thr p (ones b) := by
        unfold exc; rw [hT1]
      omega

/-! ## The remaining lemma, and the reduction -/

/-- **The open lemma.**  A *reversible* removal (the predecessor of `x` is
pebbled, or `x` is the entrance cell) never increases the potential.
Together with `phi_toggle_le_of_place` this says that `phi` is invariant on
the reversible components of the game; it is the whole missing content of
Conjecture B2 (checked by computer for `p ≤ 5`, see the module docstring). -/
def RemovalLemma (p : Nat) : Prop :=
  ∀ (b : Board) (x : Nat), x < b.length → nth b x = true → okMove b x = true → ones b ≤ p →
    phi p (toggle b x) ≤ phi p b

/-- Along a legal play the potential grows by at most `2^(p−2)` per erasure. -/
theorem phi_execB_le (p : Nat) (hR : RemovalLemma p) :
    ∀ (s : List Nat) (b : Board), legalE b s = true →
      (∀ k, ones (execB b (s.take k)) ≤ p) → (∀ i ∈ s, i < b.length) →
      phi p (execB b s) ≤ phi p b + 2 ^ (p - 2) * erasures b s
  | [], b, _, _, _ => by simp [execB, erasures]
  | i :: rest, b, hleg, hpk, hbd => by
      have hex : execB b (i :: rest) = execB (toggle b i) rest := rfl
      have hleg' : okE b i = true ∧ legalE (toggle b i) rest = true := by
        simpa [Bool.and_eq_true] using hleg
      have hil : i < b.length := hbd i (List.mem_cons_self ..)
      have hone : ones b ≤ p := by simpa [execB] using hpk 0
      have hpk' : ∀ k, ones (execB (toggle b i) (rest.take k)) ≤ p := by
        intro k; simpa [execB] using hpk (k + 1)
      have hbd' : ∀ j ∈ rest, j < (toggle b i).length := by
        intro j hj; rw [length_toggle]; exact hbd j (List.mem_cons_of_mem _ hj)
      have hrest := phi_execB_le p hR rest (toggle b i) hleg'.2 hpk' hbd'
      have hQ1 : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
      rw [hex]
      simp only [erasures_cons]
      cases hn : nth b i with
      | false =>
          have hok : okMove b i = true := by
            have := hleg'.1; unfold okE at this; rw [hn] at this; simpa using this
          have hst : phi p (toggle b i) ≤ phi p b := phi_toggle_le_of_place p hn hok hil
          have hie : isErase b i = false := by simp [isErase, hn]
          rw [hie]
          simp only [Bool.false_eq_true, if_false, Nat.zero_add]
          omega
      | true =>
          cases hok : okMove b i with
          | true =>
              have hst : phi p (toggle b i) ≤ phi p b := hR b i hil hn hok hone
              have hie : isErase b i = false := by simp [isErase, hn, hok]
              rw [hie]
              simp only [Bool.false_eq_true, if_false, Nat.zero_add]
              omega
          | false =>
              have hst := phi_toggle_le_of_remove p (ones b) b i rfl hone hn hil
              have hie : isErase b i = true := by simp [isErase, hn, hok]
              rw [hie]
              simp only [if_true, Nat.mul_add, Nat.mul_one]
              omega

theorem phi_empty (p n : Nat) : phi p (empty n) = 0 :=
  phi_of_ones_zero (ones_empty n)

theorem phi_target (p n : Nat) (hn : 1 ≤ n) : n - 2 ^ (p - 1) ≤ phi p (target n) := by
  have hl : n - 1 < (List.replicate n false).length := by simp; omega
  have hone : ones (target n) = 1 := by
    have := ones_set (List.replicate n false) (n - 1) true hl
    rw [nth_replicate, ones_replicate] at this
    simpa [target] using this
  have hnth : nth (target n) (n - 1) = true := by
    unfold target; rw [nth_set_eq _ _ _ hl]
  have hlow : ∀ j, j < n - 1 → nth (target n) j = false := by
    intro j hj
    unfold target
    rw [nth_set_ne _ _ _ _ (by omega), nth_replicate]
  have hgap : gap (target n) (n - 1) = n := by
    unfold gap; rw [lastOn_eq_zero (target n) (n - 1) hlow]; omega
  rw [phi_unfold]
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
    have : exc p (target n) (n - 1) = n - thr p 1 := by
      unfold exc; rw [hgap, hone]
    unfold thr at this
    rw [this]
    omega

/-- **The reduction.**  Given `RemovalLemma p`, every clean plan with peak `p`
and at most `e` erasures reaches at most `(e + 2)·2^(p−2)`. -/
theorem reach_le_of_removalLemma (p e : Nat) (hp : 2 ≤ p) (hR : RemovalLemma p) (n : Nat)
    (h : Reachable n p e) : n ≤ (e + 2) * 2 ^ (p - 2) := by
  obtain ⟨s, hs⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact Nat.zero_le _
  have hpk : ∀ k, ones (execB (empty n) (s.take k)) ≤ p :=
    fun k => Nat.le_trans (ones_prefix_le_maxOnes s (empty n) k) hs.peak
  have hbd : ∀ i ∈ s, i < (empty n).length := by
    intro i hi; rw [length_empty]; exact hs.bounds i hi
  have h1 := phi_execB_le p hR s (empty n) hs.legal hpk hbd
  have hQ1 : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
  rw [hs.final, phi_empty] at h1
  have h2 := phi_target p n hn
  have h3 : 2 ^ (p - 2) * erasures (empty n) s ≤ 2 ^ (p - 2) * e :=
    Nat.mul_le_mul_left _ hs.budget
  have hpow : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have : n ≤ 2 ^ (p - 1) + 2 ^ (p - 2) * e := by omega
  rw [hpow] at this
  calc n ≤ 2 * 2 ^ (p - 2) + 2 ^ (p - 2) * e := this
    _ = (e + 2) * 2 ^ (p - 2) := by rw [Nat.add_mul, Nat.mul_comm (2 ^ (p - 2)) e]; omega

/-- Conjecture B2 follows from the removal lemma (upper bound here, lower
bound `theoremB1`). -/
theorem conjB2_of_removalLemma (p e : Nat) (hp : 2 ≤ p) (hR : RemovalLemma p) : ConjB2 p e :=
  ⟨theoremB1 p e hp, fun n hn => reach_le_of_removalLemma p e hp hR n hn⟩

/-! ## Computational anchors for the open lemma (small boards)

These `#guard`s evaluate `RemovalLemma p` on *all* boards of a given length
at elaboration time; they are sanity checks, not proofs. -/

/-- All boards of length `n`. -/
def allBoards : Nat → List Board
  | 0 => [[]]
  | n + 1 => (allBoards n).flatMap fun b => [false :: b, true :: b]

/-- `RemovalLemma p` restricted to boards of length `n` (decided by evaluation). -/
def removalCheck (p n : Nat) : Bool :=
  (allBoards n).all fun b =>
    !(decide (ones b ≤ p)) ||
      (List.range n).all fun x =>
        !(nth b x && okMove b x) || decide (phi p (toggle b x) ≤ phi p b)

#guard removalCheck 2 8
#guard removalCheck 3 9
#guard removalCheck 4 10

/- The erasure step `phi_toggle_le_of_remove` is tight: on the board
`{2^(p−1), 2^(p−1) + 2^(p−2)}` (p = 4: cells 7 and 11) erasing the lower
pebble raises `phi` by exactly `2^(p−2)`. -/
#guard phi 4 ((empty 12).set 7 true |>.set 11 true) = 0
#guard phi 4 ((empty 12).set 11 true) = 4

end UpperBound
end ErasurePebbling
