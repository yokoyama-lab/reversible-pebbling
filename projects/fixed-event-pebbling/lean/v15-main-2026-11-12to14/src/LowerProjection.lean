import TerminalProjection
namespace LowerProjection
open TerminalProjection LocalCertificate
def low (m : Nat) (b : List Nat) := b.filter (fun v => decide (v≤m))
def moves (m : Nat) (es : List Event) := es.filter (fun e => decide (e.vertex≤m))
theorem mem_low {m b v} : v∈low m b ↔ v∈b ∧ v≤m := by simp [low]
theorem pred_low {m b v} (hv : v≤m) : pred (low m b) v ↔ pred b v := by
 have h : v-1≤m := by omega
 simp [pred,mem_low,h]
theorem low_erase (m v) (b : List Nat) : low m (b.erase v)=(low m b).erase v := List.erase_filter.symm
theorem step_low {p m b a e} (h : Step p b e a) (hv : e.vertex≤m) :
 Step p (low m b) e (low m a) := by
 refine ⟨h.1,Nat.le_trans (List.length_filter_le _ _) h.2.1,?_⟩
 cases hp : e.place with
 | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
   simp only [↓reduceIte]
   refine ⟨fun hm => he.1 (mem_low.mp hm).1,(pred_low hv).mpr he.2.1,?_⟩
   rw [he.2.2];simp [low,hv]
 | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
   simp only [Bool.false_eq_true,↓reduceIte]
   exact ⟨mem_low.mpr ⟨he.1,hv⟩,by rw [he.2,low_erase]⟩
theorem upper_step_disappears {p m b a e} (h : Step p b e a) (hv : m<e.vertex) : low m a=low m b := by
 cases hp : e.place with
 | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
   rw [he.2.2];simp [low,show ¬ e.vertex≤m by omega]
 | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
   rw [he.2,low_erase]
   apply List.erase_of_not_mem
   simp [low,show ¬e.vertex≤m by omega]
theorem fee_low {m b e} (hv : e.vertex≤m) : fee (low m b) e=fee b e := by simp [fee,pred_low hv]
theorem erasure_low {m b e} (hv : e.vertex≤m) : erasure (low m b) e=erasure b e := by simp [erasure,pred_low hv]
theorem run_low {p m b es z c r} (h : Run p b es z c r) :
 ∃c' r',Run p (low m b) (moves m es) (low m z) c' r' ∧ c'≤c ∧ r'≤r := by
 induction h with
 | nil b => exact ⟨0,0,by simpa [moves] using Run.nil (p:=p) (low m b),by omega,by omega⟩
 | @cons b a z es c r e hs hr ih =>
   obtain ⟨c',r',ht,hc,he⟩ := ih
   by_cases hn : e.vertex≤m
   · refine ⟨fee b e+c',erasure b e+r',?_,by omega,by omega⟩
     have hh := Run.cons (step_low hs hn) ht
     simpa [moves,hn,fee_low hn,erasure_low hn] using hh
   · have ha := upper_step_disappears hs (by omega : m<e.vertex)
     refine ⟨c',r',?_,by omega,by omega⟩
     simpa [moves,hn,ha] using ht
#print axioms step_low
#print axioms upper_step_disappears
#print axioms run_low
end LowerProjection
