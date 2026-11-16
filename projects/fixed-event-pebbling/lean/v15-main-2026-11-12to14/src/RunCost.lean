import TerminalExistence
import PricedRecurrence
namespace PhysicalRunCost
open TerminalProjection
theorem fee_identity (b : List Nat) (e : LocalCertificate.Event) : fee b e = 1+8*erasure b e := by
 cases hp : e.place <;> by_cases h : pred b e.vertex <;> simp [fee,erasure,hp,h]
theorem run_cost_identity {p b es z c r} (h : Run p b es z c r) : c=es.length+8*r := by
 induction h with
 | nil => rfl
 | @cons b a z es c r e hs hr ih =>
   have hf := fee_identity b e
   simp only [List.length_cons]
   omega
-- This explicit interface is the remaining external recurrence-completeness obligation.
def RecurrenceEmbedding : Prop :=
 ∀ n es c r, Run 5 [] es [n] c r → (∀e∈es,e.vertex≤n) →
 (∀e∈es,e.vertex=n → e.place=true) →
 ∃cost,PricedRecurrence.C n 5 cost ∧ cost≤c
-- Conditional assembly, not a proof of RecurrenceEmbedding.
theorem lower_if_recurrence_embedding (embed : RecurrenceEmbedding)
 {k es c r} (hr : Run 5 [] es [5+6*k] c r)
 (hb : ∀e∈es,e.vertex≤5+6*k) (budget : r≤k) : 16*k+9≤es.length := by
 obtain ⟨es',c',r',hh,hc,he,hl,hn⟩ := TerminalExistence.terminal_normal_form hr hb
 -- Projection only removes events, so preserve the original bound directly.
 -- The generic normal-form theorem currently omits that output property;
 -- use its concrete final-placement construction to retain it.
 obtain ⟨pre,post,b,a,c1,r1,c2,r2,hw,hpre,hs,hpost,hcost,her,hno⟩ :=
   TerminalExistence.final_placement_decomposition hr
 have hpb : ∀e∈pre,e.vertex≤5+6*k := by
   intro e he;apply hb e;rw [hw];simp [he]
 obtain ⟨cn,rn,hRun,hcn,hrn,hlen,hnorem⟩ := normalize_terminal hpre hs hpost hpb hno
 have hnBound : ∀e∈keep (5+6*k) pre ++ ⟨true,5+6*k⟩::post,e.vertex≤5+6*k := by
   intro e hm
   rcases List.mem_append.mp hm with hm | hm
   · exact hpb e (List.mem_filter.mp hm).1
   · rcases List.mem_cons.mp hm with h | h
     · simp [h]
     · apply hb e;rw [hw];simp [h]
 obtain ⟨cost,hC,hcc⟩ := embed _ _ _ _ hRun hnBound hnorem
 have bound := PricedRecurrence.C_affine hC (by omega)
 have hcOriginal := run_cost_identity hr
 omega
#print axioms fee_identity
#print axioms run_cost_identity
#print axioms lower_if_recurrence_embedding
end PhysicalRunCost
