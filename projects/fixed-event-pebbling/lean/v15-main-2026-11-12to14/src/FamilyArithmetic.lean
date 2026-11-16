import Std
namespace ChainFamilyArithmetic

def placementCount (v : Nat) : Nat :=
  if v ≤ 5 then 1 else if v % 6 = 0 ∨ v % 6 = 2 then 2 else 1

def IsErasure (k v : Nat) : Prop := ∃ i, i < k ∧ v = 5 + 6*i

theorem block_placement_counts (j : Nat) :
    placementCount (5+6*j) = 1 ∧
    placementCount (5+6*j+1) = 2 ∧
    placementCount (5+6*j+2) = 1 ∧
    placementCount (5+6*j+3) = 2 ∧
    placementCount (5+6*j+4) = 1 ∧
    placementCount (5+6*j+5) = 1 ∧
    placementCount (5+6*j+6) = 1 := by
  simp [placementCount, Nat.add_mod]
  omega

theorem repeated_predecessor_single (v : Nat) (hv : 0 < v)
    (h : placementCount v = 2) : 1 < v ∧ placementCount (v-1) = 1 := by
  simp only [placementCount] at h ⊢
  split at h <;> simp_all
  omega

theorem interior_not_erasure (j k d : Nat) (hd : 1 ≤ d) (hd5 : d ≤ 5) :
    ¬ IsErasure k (5+6*j+d) := by
  rintro ⟨i,_,he⟩
  omega

theorem block_interior_not_erasure (j k : Nat) :
    ¬ IsErasure k (5+6*j+1) ∧ ¬ IsErasure k (5+6*j+2) ∧
    ¬ IsErasure k (5+6*j+3) ∧ ¬ IsErasure k (5+6*j+4) ∧
    ¬ IsErasure k (5+6*j+5) := by
  exact ⟨interior_not_erasure j k 1 (by decide) (by decide),
    interior_not_erasure j k 2 (by decide) (by decide),
    interior_not_erasure j k 3 (by decide) (by decide),
    interior_not_erasure j k 4 (by decide) (by decide),
    interior_not_erasure j k 5 (by decide) (by decide)⟩

#print axioms block_placement_counts
#print axioms repeated_predecessor_single
#print axioms interior_not_erasure
#print axioms block_interior_not_erasure
end ChainFamilyArithmetic
