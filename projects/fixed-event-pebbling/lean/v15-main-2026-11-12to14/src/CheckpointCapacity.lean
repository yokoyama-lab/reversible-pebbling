import Std
namespace CheckpointCapacity
universe u

theorem nodup_subset_length_le {α : Type u} [DecidableEq α]
    (xs ys : List α) (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have hn' := List.nodup_cons.mp hn
    have ha : a ∈ ys := hs (by simp)
    have hsub : xs ⊆ ys.erase a := by
      intro x hx
      have hxa : x ≠ a := by intro eq; subst x; exact hn'.1 hx
      exact (List.mem_erase_of_ne hxa).mpr (hs (by simp [hx]))
    have h := ih (ys.erase a) hn'.2 hsub
    have he := List.length_erase_of_mem ha
    have hy := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A capacity bound and a saturated distinct forced set leave no other vertices. -/
theorem saturated_board {α : Type u} [DecidableEq α]
    (forced board : List α) (distinct : forced.Nodup)
    (present : forced ⊆ board) (capacity : board.length ≤ forced.length) :
    ∀ v, v ∈ board ↔ v ∈ forced := by
  intro v
  constructor
  · intro hv
    by_cases hnot : v ∈ forced
    · exact hnot
    exfalso
    have hd : (v :: forced).Nodup := List.nodup_cons.mpr ⟨hnot,distinct⟩
    have hs : (v :: forced) ⊆ board := by
      intro x hx
      rcases List.mem_cons.mp hx with he | hm
      · subst x; exact hv
      · exact present hm
    have h := nodup_subset_length_le (v :: forced) board hd hs
    simp only [List.length_cons] at h
    omega
  · intro hv
    exact present hv

def forcedVertices (s : Nat) : List Nat := [s,s+2,s+4,s+5,s+6]

theorem forcedVertices_distinct (s : Nat) : (forcedVertices s).Nodup := by
  simp [forcedVertices, List.nodup_cons]

theorem five_forced_board (s : Nat) (board : List Nat)
    (capacity : board.length ≤ 5)
    (present : ∀ v ∈ forcedVertices s, v ∈ board) :
    ∀ v, v ∈ board ↔ v = s ∨ v = s+2 ∨ v = s+4 ∨ v = s+5 ∨ v = s+6 := by
  have h := saturated_board (forcedVertices s) board (forcedVertices_distinct s)
    present (by simpa [forcedVertices] using capacity)
  intro v
  simpa [forcedVertices] using h v

/-- Birth/removal are zero-based event positions; tau is the number of executed events. -/
def Alive (birth removal tau : Nat) : Prop := birth < tau ∧ tau ≤ removal

theorem alive_after_event (birth removal q : Nat)
    (hb : birth ≤ q) (hr : q < removal) : Alive birth removal (q+1) := by
  unfold Alive
  omega

/-- This assumes, rather than derives, the single-lifetime interpretation of the trace. -/
theorem lifetime_saturation {α : Type u} [DecidableEq α]
    (forced : List α) (boardAt : Nat → List α) (birth removal : α → Nat) (q : Nat)
    (distinct : forced.Nodup)
    (lifetime : ∀ v ∈ forced, v ∈ boardAt (q+1) ↔ Alive (birth v) (removal v) (q+1))
    (born : ∀ v ∈ forced, birth v ≤ q)
    (not_removed : ∀ v ∈ forced, q < removal v)
    (capacity : (boardAt (q+1)).length ≤ forced.length) :
    ∀ v, v ∈ boardAt (q+1) ↔ v ∈ forced := by
  apply saturated_board forced (boardAt (q+1)) distinct
  · intro v hv
    exact (lifetime v hv).mpr (alive_after_event _ _ q (born v hv) (not_removed v hv))
  · exact capacity

theorem checkpoint_from_order_chain (s q rc2 ra2 : Nat)
    (boardAt : Nat → List Nat) (birth removal : Nat → Nat)
    (lifetime : ∀ v ∈ forcedVertices s,
      v ∈ boardAt (q+1) ↔ Alive (birth v) (removal v) (q+1))
    (born : ∀ v ∈ forcedVertices s, birth v ≤ q)
    (h0 : q < removal (s+5))
    (h1 : removal (s+5) < removal (s+4))
    (h2 : removal (s+4) < rc2)
    (h3 : rc2 < removal (s+2))
    (h4 : removal (s+2) < ra2)
    (h5 : ra2 < removal s)
    (ht : q < removal (s+6))
    (capacity : (boardAt (q+1)).length ≤ 5) :
    ∀ v, v ∈ boardAt (q+1) ↔ v ∈ forcedVertices s := by
  apply lifetime_saturation (forcedVertices s) boardAt birth removal q
    (forcedVertices_distinct s) lifetime born
  · intro v hv
    simp only [forcedVertices, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h <;> subst v <;> omega
  · simpa [forcedVertices] using capacity

#print axioms nodup_subset_length_le
#print axioms saturated_board
#print axioms forcedVertices_distinct
#print axioms five_forced_board
#print axioms alive_after_event
#print axioms lifetime_saturation
#print axioms checkpoint_from_order_chain
end CheckpointCapacity
