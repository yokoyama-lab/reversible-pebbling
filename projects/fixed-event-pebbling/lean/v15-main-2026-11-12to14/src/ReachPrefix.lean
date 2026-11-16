import ChainTrace
namespace ReachPrefix
open LocalCertificate ChainTrace

/-- Reaching any event at or beyond v implies that v was placed somewhere
in this empty-start pre. This is uniform in the chain length. -/
theorem reached_vertex_requires_placement
    (erasures after : List Nat) (pre : List Event) (v : Nat)
    (hv : 0 < v) (hr : run erasures [] pre = some after)
    (e : Event) (he : e ∈ pre) (hlarge : v ≤ e.vertex) :
    ∃ f ∈ pre, f.place = true ∧ f.vertex = v := by
  by_cases hx : ∃ f ∈ pre, f.place = true ∧ f.vertex = v
  · exact hx
  · have hn : ∀ f ∈ pre, f.place = true → f.vertex ≠ v := by
      intro f hf hp hfv
      exact hx ⟨f,hf,hp,hfv⟩
    have hb : ∀ x ∈ ([] : List Nat), x < v := by simp
    have hbound := (before_first_placement erasures [] after pre v hv hb hn hr).1 e he
    omega

/-- The placement of t itself is included in this pre, so every
positive vertex at most t has already been placed at its after-board. -/
theorem after_placement_all_predecessors_seen
    (erasures before after : List Nat) (pre : List Event) (t : Event)
    (v : Nat) (hv : 0 < v) (hlt : v ≤ t.vertex)
    (hr : run erasures [] pre = some before)
    (hs : step true erasures before t = some after) :
    ∃ f ∈ pre ++ [t], f.place = true ∧ f.vertex = v := by
  apply reached_vertex_requires_placement erasures after (pre ++ [t]) v hv _ t (by simp) hlt
  rw [run_append]
  simp [hr,run,hs]
#print axioms reached_vertex_requires_placement
#print axioms after_placement_all_predecessors_seen
end ReachPrefix
