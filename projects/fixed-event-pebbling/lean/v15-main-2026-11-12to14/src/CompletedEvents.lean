import TwoCutCounts
import TwoPlacementOrder
namespace CompletedEvents
open LocalCertificate ChainTrace ChainUniqueLifetime ChainTwoLifetimeExact ChainCutPresence

/-- A one-placement vertex already seen and absent at the cut has no
future event of either kind. -/
theorem absent_single_vertex_completed
    (erasures initial cut final : List Nat) (pre post : List Event) (v : Nat)
    (seen : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (budget : (pre ++ post).countP (isPlacement v) ≤ 1)
    (absent : v ∉ cut) (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ post) = some final) :
    ∀ e ∈ post, e.vertex ≠ v := by
  have noP := prefix_placement_exhausts_one pre post v seen budget
  have hs : run erasures cut post = some final := by rw [run_append,hp] at hr; exact hr
  have hz := absent_no_placement_no_removal erasures cut final post v absent noP hs
  intro e he hev
  cases hep : e.place with
  | true => exact noP e he hep hev
  | false =>
    have hn := List.countP_eq_zero.mp hz e he
    exact hn (by simp [isRemoval,hep,hev])

/-- The repeated successor of a finished one-placement predecessor is
also finished, provided the successor is not an erasure site. -/
theorem absent_single_predecessor_completes_successor
    (erasures initial cut final : List Nat) (pre post : List Event) (v : Nat)
    (hv : 0 < v) (he : v+1 ∉ erasures)
    (seen : ∃ e ∈ pre, e.place = true ∧ e.vertex = v)
    (budget : (pre ++ post).countP (isPlacement v) ≤ 1)
    (absent : v ∉ cut) (hp : run erasures initial pre = some cut)
    (hr : run erasures initial (pre ++ post) = some final) :
    ∀ e ∈ post, e.vertex ≠ v+1 := by
  have noP := prefix_placement_exhausts_one pre post v seen budget
  have hs : run erasures cut post = some final := by rw [run_append,hp] at hr; exact hr
  exact (absent_predecessor_blocks_successor erasures cut final post v hv absent he noP hs).1

/-- The sole placement of t is a hard boundary: all preceding events
are strictly left of t; including that placement, none is right of t. -/
theorem sole_placement_bounds_prefix
    (erasures final : List Nat) (pre post : List Event) (t : Event)
    (ht : 0 < t.vertex) (htp : t.place = true)
    (budget : (pre ++ t :: post).countP (isPlacement t.vertex) ≤ 1)
    (hr : run erasures [] (pre ++ t :: post) = some final) :
    (∀ e ∈ pre, e.vertex < t.vertex) ∧
    (∀ e ∈ pre ++ [t], e.vertex ≤ t.vertex) := by
  have hz : pre.countP (isPlacement t.vertex) = 0 := by
    simp only [List.countP_append,List.countP_cons] at budget
    have hpv : isPlacement t.vertex t = true := by simp [isPlacement,htp]
    simp only [hpv, ite_true] at budget
    omega
  have hn := zero_placements t.vertex pre hz
  rw [run_append] at hr
  cases hs : run erasures [] pre with
  | none => simp [hs] at hr
  | some before =>
    have hb := (before_first_placement erasures [] before pre t.vertex ht (by simp) hn hs).1
    refine ⟨hb,?_⟩
    intro e he
    rcases List.mem_append.mp he with hpre | htmem
    · exact Nat.le_of_lt (hb e hpre)
    · have : e = t := by simpa using htmem
      subst e; exact Nat.le_refl _
#print axioms absent_single_vertex_completed
#print axioms absent_single_predecessor_completes_successor
#print axioms sole_placement_bounds_prefix
end CompletedEvents
