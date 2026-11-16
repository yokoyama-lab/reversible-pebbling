import GlobalStateCandidates
namespace ChainPrefixSetConcat

def setOf (n : Nat) (u : List Nat) : List Nat := (List.range n).filter u.contains

theorem setOf_concat (n m : Nat) (u v : List Nat)
    (hu : ∀a∈u,a<n) :
    setOf (n+m) (u ++ v.map (fun i=>n+i)) =
      setOf n u ++ (setOf m v).map (fun i=>n+i) := by
  unfold setOf
  rw [List.range_add,List.filter_append,List.filter_map]
  congr 1
  · apply List.filter_congr
    intro x hx
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem,List.mem_append]
    constructor
    · intro h
      cases h with
      | inl h => exact h
      | inr h =>
        obtain ⟨a,ha,he⟩ := List.mem_map.mp h
        have := List.mem_range.mp hx
        omega
    · exact Or.inl
  · congr 1
    apply List.filter_congr
    intro x hx
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def,List.contains_iff_mem,List.mem_append,List.mem_map]
    constructor
    · intro h
      cases h with
      | inl h => have hh := hu (n+x) h; omega
      | inr h =>
        obtain ⟨a,ha,he⟩ := h
        have : a=x := by omega
        simpa [this] using ha
    · intro h
      exact Or.inr ⟨x,h,rfl⟩

theorem setOf_full (n : Nat) (u : List Nat) (hp : u.Perm (List.range n)) :
    setOf n u=List.range n := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact List.contains_iff_mem.mpr (hp.mem_iff.mpr hx)

theorem setOf_bounds (n : Nat) (u : List Nat) (x : Nat) :
    x ∈ setOf n u ↔ x<n ∧ x∈u := by
  simp [setOf]

/-- Prefix sets of a block concatenation split at the actual first-block length. -/
theorem prefix_concat_cases (n m : Nat) (u v : List Nat)
    (hp : u.Perm (List.range n)) (t : Nat) :
    (t ≤ n ∧ setOf (n+m) ((u ++ v.map (fun i=>n+i)).take t)=setOf n (u.take t)) ∨
    (n < t ∧ setOf (n+m) ((u ++ v.map (fun i=>n+i)).take t)=
      List.range n ++ (setOf m (v.take (t-n))).map (fun i=>n+i)) := by
  have hl : u.length=n := by simpa using hp.length_eq
  have hb : ∀a∈u,a<n := fun a ha => List.mem_range.mp (hp.mem_iff.mp ha)
  by_cases ht : t≤n
  · refine Or.inl ⟨ht,?_⟩
    rw [List.take_append_of_le_length (by omega)]
    have h := setOf_concat n m (u.take t) [] (fun a ha => hb a (List.mem_of_mem_take ha))
    have hz : setOf m [] = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      simp
    simpa only [List.map_nil,List.append_nil,hz] using h
  · refine Or.inr ⟨by omega,?_⟩
    rw [List.take_append,List.take_of_length_le (by omega),← List.map_take,hl]
    rw [setOf_concat n m u (v.take (t-n)) hb,setOf_full n u hp]

#print axioms setOf_concat
#print axioms setOf_full
#print axioms prefix_concat_cases
end ChainPrefixSetConcat
