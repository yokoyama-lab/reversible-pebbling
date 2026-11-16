import FamilyCut
namespace RawSwapVertex
open LocalCertificate ChainTrace

theorem first_step {E board final : List Nat} {a : Event} {tail : List Event}
 (h : run E board (a::tail)=some final) : ∃mid,step true E board a=some mid := by
 cases hs : step true E board a with
 | none => simp [run,hs] at h
 | some mid => exact ⟨mid,rfl⟩

theorem same_vertex_first_steps {E board x y : List Nat} {a b : Event}
 (ha : step true E board a=some x) (hb : step true E board b=some y)
 (hv : a.vertex=b.vertex) : a=b := by
 have hp : a.place=b.place := by
  cases hpa : a.place <;> cases hpb : b.place
  · rfl
  · have present := removal_requires_present E board x a hpa ha
    have absent := ((placement_step E board y b hpb).mp hb).1
    exact False.elim (absent (hv ▸ present))
  · have absent := ((placement_step E board x a hpa).mp ha).1
    have present := removal_requires_present E board y b hpb hb
    exact False.elim (absent (hv.symm ▸ present))
  · rfl
 cases a;cases b;simp_all

theorem legal_swap_distinct_or_equal {E board f g : List Nat} {pre post : List Event} {a b : Event}
 (h : run E board (pre++a::b::post)=some f)
 (h' : run E board (pre++b::a::post)=some g) : a.vertex≠b.vertex ∨ a=b := by
 rw [run_append] at h h'
 cases hr : run E board pre with
 | none => simp [hr] at h
 | some mid =>
  have hh : run E mid (a::b::post)=some f := by simpa [hr] using h
  have hh' : run E mid (b::a::post)=some g := by simpa [hr] using h'
  obtain ⟨x,hx⟩ := first_step hh
  obtain ⟨y,hy⟩ := first_step hh'
  by_cases hv : a.vertex=b.vertex
  · exact Or.inr (same_vertex_first_steps hx hy hv)
  · exact Or.inl hv

theorem trace_swap_distinct_or_equal {k : Nat} {E : List Nat} {pre post : List Event} {a b : Event}
 (h : FamilyCut.Trace k E (pre++a::b::post))
 (h' : FamilyCut.Trace k E (pre++b::a::post)) : a.vertex≠b.vertex ∨ a=b :=
 legal_swap_distinct_or_equal h.legal h'.legal
#print axioms legal_swap_distinct_or_equal
#print axioms trace_swap_distinct_or_equal
end RawSwapVertex
