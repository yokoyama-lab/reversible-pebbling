import PrefixStateCorrectness
namespace ChainPrefixStates
theorem nodup_membership_perm {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α)
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ v, v ∈ xs ↔ v ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y rest =>
        have hh := (hm y).mpr (by simp)
        simp at hh
    subst ys
    exact List.Perm.nil
  | cons a xs ih =>
    have hx' := List.nodup_cons.mp hx
    have ha : a ∈ ys := (hm a).mp (by simp)
    have hmem : ∀ v, v ∈ xs ↔ v ∈ ys.erase a := by
      intro v
      rw [hy.mem_erase_iff]
      constructor
      · intro hv
        refine ⟨?_,(hm v).mp (List.mem_cons_of_mem a hv)⟩
        intro heq; subst v; exact hx'.1 hv
      · rintro ⟨hne,hv⟩
        rcases List.mem_cons.mp ((hm v).mpr hv) with h | h
        · exact False.elim (hne h)
        · exact h
    have hi := ih (ys.erase a) hx'.2 (hy.erase a) hmem
    exact (List.Perm.cons a hi).trans (List.perm_cons_erase ha).symm

end ChainPrefixStates
