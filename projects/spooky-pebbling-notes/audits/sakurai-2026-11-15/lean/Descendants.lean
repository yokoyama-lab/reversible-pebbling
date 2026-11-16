import RootCut
namespace Descendants
open SpookyRound TraceBridge

theorem split_mem (ha : a ∈ xs) : ∃ pre post, xs = pre ++ a :: post := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with h | h
    · subst x; exact ⟨[],xs,rfl⟩
    · obtain ⟨pre,post,hp⟩ := ih h
      exact ⟨x::pre,post,by simp [hp]⟩

theorem cleanup_propagates {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (v u : Fin n)
    (hne : v ≠ u) (he : pred v u = true) (hf : kind r.state u = .empty)
    (hv : ∃ a ∈ as, firstAt a v ≠ .idle) :
    ∃ a ∈ as, firstAt a u = .unpebble := by
  obtain ⟨a,ha,hactive⟩ := hv
  obtain ⟨xs,ys,hh⟩ := split_mem ha
  subst as
  obtain ⟨b,hb,hu⟩ := cleanup_after_occurrence xs ys h v u hne hactive he hf
  exact ⟨b,by simp [hb],hu⟩

-- The final-empty condition is explicit at each edge: for a tree ending
-- root-only it follows from a path that never returns to root.
inductive Path (pred : Fin n → Fin n → Bool) (final : Config n) :
    Fin n → Fin n → Prop
 | refl (v) : Path pred final v v
 | step : Path pred final v w → w ≠ u → pred w u = true →
     kind final u = .empty → Path pred final v u

theorem descendant_cleanup {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (path : Path pred r.state v u)
    (hv : ∃ a ∈ as, firstAt a v = .unpebble) :
    ∃ a ∈ as, firstAt a u = .unpebble := by
  induction path with
  | refl => exact hv
  | step path hne he hf ih =>
    apply cleanup_propagates h _ _ hne he hf
    obtain ⟨a,ha,hh⟩ := ih
    exact ⟨a,ha,by simp [hh]⟩

theorem descendant_counts {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) (path : Path pred r.state v u)
    (hv : ∃ a ∈ as, firstAt a v = .unpebble)
    (hq : kind q u ≠ .pebble) :
    let c := CutBound.count .compute (events u as)
    let k := CutBound.count .uncompute (events u as)
    1 ≤ c ∧ 1 ≤ k ∧ RootCut.bad (c,k) ≤ RootCut.extra (c,k) :=
  RootCut.actual_suffix_charge h u hq (descendant_cleanup h path hv)
theorem actual_work_sum {pred : Fin n → Fin n → Bool}
    (h : ActionRuns pred q as r) :
    r.work = (as.map roundWork).sum := by
  induction h with
  | nil q => rfl
  | cons hm hg hl ht ih =>
    simp only [SpookyDP.prepend,edge,List.map_cons,List.sum_cons]
    rw [ih]
#print axioms actual_work_sum
#print axioms cleanup_propagates
#print axioms descendant_cleanup
#print axioms descendant_counts
end Descendants
