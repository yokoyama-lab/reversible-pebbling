import MLargeExact
import MSmallExact
import SwapGraphBasics
import ComponentCompleteness
namespace MAllSwap
open SwapComponents LocalCertificate
theorem disjoint : ∀v∈MSmallSwap.component,v∉MLargeSwap.component :=
 SwapGraphBasics.disjoint_by_roots MSmallSwap.exact MLargeSwap.tree (by decide)
theorem covers (w : List Nat) : M.Legal w ↔ w∈MLargeSwap.component ∨ w∈MSmallSwap.component := by
 have hn : (MLargeSwap.component++MSmallSwap.component).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨MLargeSwap.unique,MSmallSwap.unique,?_⟩
  intro a ha b hb eq
  subst b
  exact disjoint a hb ha
 have len : (MLargeSwap.component++MSmallSwap.component).length=584 := by
  rw [List.length_append,MLargeSwap.size,MSmallSwap.size]
 have sound : ∀u∈MLargeSwap.component++MSmallSwap.component,M.Legal u := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact SwapGraphBasics.reach_legal (MLargeSwap.tree u hu)
  · exact SwapGraphBasics.reach_legal (MSmallSwap.tree u hu)
 have h := ComponentCompleteness.middle_complete _ hn len sound w
 simpa using h
theorem exactly_two (w : List Nat) : M.Legal w ↔
 Reach M.Legal MLargeSwap.w0 w ∨ Reach M.Legal MSmallSwap.w0 w := by
 rw [MLargeSwap.exact,MSmallSwap.exact]
 exact covers w
#print axioms exactly_two
end MAllSwap
