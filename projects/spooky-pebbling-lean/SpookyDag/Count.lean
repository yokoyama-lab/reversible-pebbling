/-
# 手数 = 2 × 置く手 − 1（一般のグラフ）

`SpookyTree/Count.lean` と同じ。各手はペブル数をちょうど 1 変え、始状態 0・終状態 1 なので
置く手の数 = 外す手の数 + 1。
-/
import SpookyDag.Game

namespace SpookyDag

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- 時刻 `< t` の置く手の数。 -/
def nPlace (ms : ℕ → Move V) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun i => IsPlace (ms i))).card

theorem pcount_update_up {c : Config V} {v : V} (h0 : c v ≠ .pebble) :
    pcount (Function.update c v .pebble) = pcount c + 1 := by
  unfold pcount
  have : Finset.univ.filter (fun l => Function.update c v Cell.pebble l = Cell.pebble) =
      insert v (Finset.univ.filter (fun l => c l = Cell.pebble)) := by
    ext l
    by_cases hl : l = v
    · subst hl; simp
    · simp [Function.update, hl]
  rw [this, Finset.card_insert_of_notMem (by simp [h0])]

theorem pcount_update_down {c : Config V} {v : V} (h0 : c v = .pebble) {x : Cell}
    (hx : x ≠ .pebble) : pcount (Function.update c v x) + 1 = pcount c := by
  unfold pcount
  have : Finset.univ.filter (fun l => c l = Cell.pebble) =
      insert v (Finset.univ.filter (fun l => Function.update c v x l = Cell.pebble)) := by
    ext l
    by_cases hl : l = v
    · subst hl; simp [h0]
    · simp [Function.update, hl]
  rw [this, Finset.card_insert_of_notMem (by simp [hx])]

/-- 妥当な手順では、時刻 `t ≤ T` で ペブル数 + (t − 置く手) = 置く手。 -/
theorem pcount_balance {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms) :
    ∀ t ≤ T, pcount (st ms t) + (t - nPlace ms t) = nPlace ms t ∧ nPlace ms t ≤ t := by
  intro t ht
  induction t with
  | zero => simp [nPlace, pcount, st]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hL := hV.legal t (by omega)
    unfold Legal at hL
    have hNP : nPlace ms (t + 1) = nPlace ms t + (if IsPlace (ms t) then 1 else 0) := by
      unfold nPlace
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hp
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    have hst : st ms (t + 1) = Function.update (st ms t) (ms t).v (result (ms t).op) := rfl
    cases hop : (ms t).op with
    | pebble =>
      rw [hop] at hL
      have hp : IsPlace (ms t) := Or.inl hop
      rw [hNP, if_pos hp, hst, hop]
      simp only at hL
      have := pcount_update_up (c := st ms t) (v := (ms t).v) (by rw [hL.1]; decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | unghost =>
      rw [hop] at hL
      have hp : IsPlace (ms t) := Or.inr hop
      rw [hNP, if_pos hp, hst, hop]
      simp only at hL
      have := pcount_update_up (c := st ms t) (v := (ms t).v) (by rw [hL.1]; decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | unpebble =>
      rw [hop] at hL
      have hp : ¬ IsPlace (ms t) := by unfold IsPlace; rw [hop]; decide
      rw [hNP, if_neg hp, hst, hop]
      simp only at hL
      have := pcount_update_down hL.1 (x := Cell.empty) (by decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | ghost =>
      rw [hop] at hL
      have hp : ¬ IsPlace (ms t) := by unfold IsPlace; rw [hop]; decide
      rw [hNP, if_neg hp, hst, hop]
      simp only at hL
      have := pcount_update_down hL (x := Cell.ghost) (by decide)
      simp only [result] at this ⊢
      constructor <;> omega

theorem pcount_final {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms) :
    pcount (st ms T) = 1 := by
  unfold pcount
  have : Finset.univ.filter (fun l => st ms T l = Cell.pebble) = {G.root} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      by_contra hne
      rw [hV.others l hne] at hp; exact absurd hp (by decide)
    · rintro rfl; exact hV.root
  rw [this, Finset.card_singleton]

/-- **手数 = 2 × 置く手 − 1**（`T + 1 = 2 · nPlace T`）。 -/
theorem moves_eq {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms) :
    T + 1 = 2 * nPlace ms T := by
  obtain ⟨h1, h2⟩ := pcount_balance hV T le_rfl
  rw [pcount_final hV] at h1
  omega

end SpookyDag
