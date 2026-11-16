import LowerProjection
import CleanHandoffMeasure
namespace ProjectionSuffixHelpers
open LocalCertificate TerminalProjection VisitMeasure CleanHandoffMeasure

theorem low_eq_self {m : Nat} {b : List Nat} (hb : ∀v∈b,v≤m) : LowerProjection.low m b=b := by
 apply List.filter_eq_self.mpr
 intro v hv
 simpa using hb v hv

theorem projected_run_same_end {p m b es P c r}
 (hr : Run p b es P c r) (bound : ∀v∈P,v≤m) :
 ∃d s,Run p (LowerProjection.low m b) (LowerProjection.moves m es) P d s ∧
 d≤c ∧ s≤r ∧ (∀e∈LowerProjection.moves m es,e.vertex≤m) := by
 obtain ⟨d,s,h,hc,hs⟩ := LowerProjection.run_low (m:=m) hr
 rw [low_eq_self bound] at h
 refine ⟨d,s,h,hc,hs,?_⟩
 intro e he
 simpa only [LowerProjection.moves,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp he).2

theorem projected_empty_prefix {p m es P c r}
 (hr : Run p [] es P c r) (bound : ∀v∈P,v≤m) :
 ∃d s,Run p [] (LowerProjection.moves m es) P d s ∧
 d≤c ∧ s≤r ∧ (∀e∈LowerProjection.moves m es,e.vertex≤m) := by
 simpa [LowerProjection.low] using projected_run_same_end hr bound

theorem suffix_bad_property {n b pre post} {prop : Nat→Prop}
 (h : ∀j∈bad n b (pre++post),prop j) :
 ∀j∈bad n (evolve b pre) post,prop j := by
 intro j hj
 apply h j
 rw [bad_append]
 exact List.mem_append_right _ hj

theorem run_suffix_bad_property {p n b pre P c r post} {prop : Nat→Prop}
 (hr : Run p b pre P c r) (h : ∀j∈bad n b (pre++post),prop j) :
 ∀j∈bad n P post,prop j := by
 simpa only [run_evolve hr] using suffix_bad_property h

theorem run_suffix_bad_le {p n m b pre P c r post}
 (hr : Run p b pre P c r) (h : ∀j∈bad n b (pre++post),j≤m) :
 ∀j∈bad n P post,j≤m := run_suffix_bad_property hr h

theorem run_suffix_bad_lt {p n m b pre P c r post}
 (hr : Run p b pre P c r) (h : ∀j∈bad n b (pre++post),j<m) :
 ∀j∈bad n P post,j<m := run_suffix_bad_property hr h

theorem projected_singleton_run {p n es c r}
 (hr : Run p [] es [n] c r) :
 ∃d s,Run p [] (LowerProjection.moves n es) [n] d s ∧
 d≤c ∧ s≤r ∧ (∀e∈LowerProjection.moves n es,e.vertex≤n) := by
 apply projected_empty_prefix hr
 intro v hv
 have he : v=n := by simpa using hv
 omega

#print axioms projected_singleton_run
#print axioms low_eq_self
#print axioms projected_run_same_end
#print axioms projected_empty_prefix
#print axioms suffix_bad_property
#print axioms run_suffix_bad_property
#print axioms run_suffix_bad_le
#print axioms run_suffix_bad_lt
end ProjectionSuffixHelpers
