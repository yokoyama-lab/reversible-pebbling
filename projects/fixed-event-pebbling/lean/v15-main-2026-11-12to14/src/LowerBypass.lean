import TerminalProjection
namespace LowerBypass
open TerminalProjection LocalCertificate
-- Local rewrite used by the lower-block bypass argument.
-- With actual (rather than elective) erasures, cost can decrease when q=2.
theorem swap_disposal_add_one (m q p : Nat) (hq : 2≤q) (hqm : q<m) (hp : 3≤p) :
 Run p [m,q] [⟨false,q⟩,⟨true,1⟩] [1,m] 10 1 ∧
 ∃c r,Run p [m,q] [⟨true,1⟩,⟨false,q⟩] [1,m] c r ∧ c≤10 ∧ r≤1 := by
 have hqm' : q≠m := by omega
 have hmq : m≠q := by omega
 have hq1 : q≠1 := by omega
 have hm1 : m≠1 := by omega
 have hq0 : q-1≠m := by omega
 have hqself : q-1≠q := by omega
 have sr : Step p [m,q] ⟨false,q⟩ [m] := by simp [Step,hmq];omega
 have sp : Step p [m] ⟨true,1⟩ [1,m] := by simp [Step,pred,hm1.symm];omega
 have feeR : fee [m,q] ⟨false,q⟩=9 := by simp [fee,pred,hq1,hq0,hqself]
 have eraR : erasure [m,q] ⟨false,q⟩=1 := by simp [erasure,pred,hq1,hq0,hqself]
 constructor
 · have h := Run.cons sr (Run.cons sp (Run.nil [1,m]))
   rw [feeR,eraR] at h
   simpa [fee,erasure] using h
 · have sp' : Step p [m,q] ⟨true,1⟩ [1,m,q] := by simp [Step,pred,hm1.symm,hq1.symm];omega
   have sr' : Step p [1,m,q] ⟨false,q⟩ [1,m] := by simp [Step,hq1.symm,hmq];omega
   refine ⟨1+fee [1,m,q] ⟨false,q⟩,erasure [1,m,q] ⟨false,q⟩,?_,?_,?_⟩
   · have h := Run.cons sp' (Run.cons sr' (Run.nil [1,m]))
     simpa [fee,erasure] using h
   · simp only [fee,Bool.false_eq_true,↓reduceIte]
     split <;> omega
   · simp only [erasure,Bool.false_eq_true,↓reduceIte]
     split <;> omega
#print axioms swap_disposal_add_one
end LowerBypass
