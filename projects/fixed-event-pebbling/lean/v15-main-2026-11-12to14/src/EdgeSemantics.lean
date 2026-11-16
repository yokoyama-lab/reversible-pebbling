import EdgeCore
namespace ChainLocalEdges
open ChainPrefixStates LocalCertificate

theorem i_edges_exact (e : Edge) : e∈iEdges ↔
    ∃w,I.Legal w ∧ ∃t,t<w.length ∧ edgeAt 10 w t=e := by
  rw [iEdges,mem_edges_iff]
  have h (w : List Nat) : w∈UpperCertificate.I.physicalWords ↔ I.Legal w :=
    EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures w
  simp only [h]
theorem m_edges_exact (e : Edge) : e∈mEdges ↔
    ∃w,M.Legal w ∧ ∃t,t<w.length ∧ edgeAt 12 w t=e := by
  rw [mEdges,mem_edges_iff]
  have h (w : List Nat) : w∈UpperCertificate.M.physicalWords ↔ M.Legal w :=
    EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures w
  simp only [h]

theorem edge_source_is_state (n : Nat) (words : List (List Nat)) (e : Edge)
    (he : e∈edges n words) : e.1∈states n words := by
  obtain ⟨w,hw,t,ht,rfl⟩ := (mem_edges_iff n words e).mp he
  exact (mem_states_iff n words _).mpr ⟨w,hw,t,by omega,rfl⟩

theorem edge_target_is_state (n : Nat) (words : List (List Nat)) (w : List Nat)
    (hw : w∈words) (t : Nat) (ht : t<w.length) :
    (edgeAt n w (t+1)).1∈states n words :=
  (mem_states_iff n words _).mpr ⟨w,hw,t+1,by omega,rfl⟩

theorem edge_target_union (n : Nat) (w : List Nat)
    (bounds : ∀a∈w,a<n) (t : Nat) (ht : t<w.length) (a : Nat) :
    a∈(edgeAt n w (t+1)).1 ↔ a∈(edgeAt n w t).1 ∨ a=(edgeAt n w t).2 := by
  have hget : w.getD t 0=w[t] := by simp [List.getD_eq_getElem?_getD,ht]
  have hb := bounds w[t] (List.getElem_mem ht)
  simp only [edgeAt,List.mem_filter,List.mem_range,List.contains_iff_mem,
    List.take_succ_eq_append_getElem ht,List.mem_append,List.mem_singleton,hget]
  constructor
  · rintro ⟨ha,hm⟩
    cases hm with
    | inl h => exact Or.inl ⟨ha,h⟩
    | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact ⟨h.1,Or.inl h.2⟩
    | inr h => exact ⟨h ▸ hb,Or.inr h⟩
#print axioms i_edges_exact
#print axioms m_edges_exact
#print axioms edge_target_union
end ChainLocalEdges
