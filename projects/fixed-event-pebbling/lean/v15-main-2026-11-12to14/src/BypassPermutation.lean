import ReversibleCleanup
import VisitMeasure
namespace BypassPermutation
open TerminalProjection LocalCertificate VisitMeasure
theorem general_swap {p m q b} (hq : 2≤q) (hqm : q<m) (hp : 3≤p)
 (hb : b.Perm [m,q]) :
 ∃c r,Run p b [⟨true,1⟩,⟨false,q⟩] [1,m] c r ∧ c≤10 ∧ r≤1 ∧
 (frames b [⟨false,q⟩,⟨true,1⟩]).count [m] =
 (frames b [⟨true,1⟩,⟨false,q⟩]).count [m]+1 := by
 have hmq : m≠q := by omega
 have hm1 : m≠1 := by omega
 have hq1 : q≠1 := by omega
 have hn : 1∉b := by
   intro h
   have hh := hb.mem_iff.mp h
   simp at hh
   omega
 have hqb : q∈b := hb.mem_iff.mpr (by simp)
 have hl : b.length=2 := by simpa using hb.length_eq
 have he : b.erase q=[m] := by
   have h := hb.erase q
   simpa [hmq] using h
 have sp : Step p b ⟨true,1⟩ (1::b) := by simp [Step,pred,hn,hl];omega
 have sr : Step p (1::b) ⟨false,q⟩ [1,m] := by
   simp [Step,hqb,hq1.symm,he];omega
 refine ⟨1+fee (1::b) ⟨false,q⟩,erasure (1::b) ⟨false,q⟩,?_,?_,?_,?_⟩
 · have hh := Run.cons sp (Run.cons sr (Run.nil [1,m]))
   simpa [fee,erasure] using hh
 · simp only [fee,Bool.false_eq_true,↓reduceIte];split <;> omega
 · simp only [erasure,Bool.false_eq_true,↓reduceIte];split <;> omega
 · have hbn : 1::b≠[m] := by intro h;have hh:=congrArg List.length h;simp [hl] at hh
   simp [frames,update,he,hq1.symm,hbn]
#print axioms general_swap
end BypassPermutation
