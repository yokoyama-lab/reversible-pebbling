import ComponentCovers
import MAllExact
namespace MComponentCover
open LocalCertificate ErasureCover SwapComponents LocalUpperBridge

theorem small_iff_reach (w) : Small w ↔ Reach M.Legal MSmallSwap.w0 w := by
 rw [MSmallSwap.exact]
 exact ⟨fun h=>h.2,fun h=>⟨SwapGraphBasics.reach_legal (MSmallSwap.tree w h),h⟩⟩

theorem large_iff_reach (w) : Large w ↔ Reach M.Legal MLargeSwap.w0 w := by
 rw [MLargeSwap.exact]
 constructor
 · intro h
   rcases (MAllSwap.covers w).mp h.1 with hlarge | hsmall
   · exact hlarge
   · exact False.elim (h.2 hsmall)
 · intro h
   exact ⟨SwapGraphBasics.reach_legal (MLargeSwap.tree w h),fun hs=>MAllSwap.disjoint w hs h⟩

theorem component_28_cover_exact :
 (∀i,Strict (relationM (smallCover i))) ∧
 (∀i,Sound M.S (Reach M.Legal MSmallSwap.w0) (relationM (smallCover i))) ∧
 (∀w,Reach M.Legal MSmallSwap.w0 w→∃i,Extends M.S (relationM (smallCover i)) w) ∧
 (∀n (R : Fin n→Fin 12→Fin 12→Prop),
  (∀i,Sound M.S (Reach M.Legal MSmallSwap.w0) (R i)) →
  (∀w,Reach M.Legal MSmallSwap.w0 w→∃i,Extends M.S (R i) w) → 2≤n) := by
 refine ⟨small_upper.1,?_,?_,?_⟩
 · intro i w hw;exact (small_iff_reach w).mp (small_upper.2.1 i w hw)
 · intro w hw;exact small_upper.2.2 w ((small_iff_reach w).mpr hw)
 · intro n R hs hc
   exact small_lower n R (fun i w hw=>(small_iff_reach w).mpr (hs i w hw))
    (fun w hw=>hc w ((small_iff_reach w).mp hw))

theorem component_556_cover_exact :
 (∀i,Strict (relationM (largeCover i))) ∧
 (∀i,Sound M.S (Reach M.Legal MLargeSwap.w0) (relationM (largeCover i))) ∧
 (∀w,Reach M.Legal MLargeSwap.w0 w→∃i,Extends M.S (relationM (largeCover i)) w) ∧
 (∀n (R : Fin n→Fin 12→Fin 12→Prop),
  (∀i,Sound M.S (Reach M.Legal MLargeSwap.w0) (R i)) →
  (∀w,Reach M.Legal MLargeSwap.w0 w→∃i,Extends M.S (R i) w) → 12≤n) := by
 refine ⟨large_upper.1,?_,?_,?_⟩
 · intro i w hw;exact (large_iff_reach w).mp (large_upper.2.1 i w hw)
 · intro w hw;exact large_upper.2.2 w ((large_iff_reach w).mpr hw)
 · intro n R hs hc
   exact large_lower n R (fun i w hw=>(large_iff_reach w).mpr (hs i w hw))
    (fun w hw=>hc w ((large_iff_reach w).mp hw))
#print axioms small_iff_reach
#print axioms large_iff_reach
#print axioms component_28_cover_exact
#print axioms component_556_cover_exact
end MComponentCover
