import LabelledCount
import TerminalProjection
namespace ActualFamilyWitness
open LocalCertificate TerminalProjection ChainAssembledTrace ChainGlobalReassembly

def marked (e : Event) : Bool := !e.place && (e.vertex%6==5)

theorem erased_le_marked {E b a e}
 (he : ∀v,v∈E → v%6=5) (hs : step true E b e=some a) :
 erasure b e≤if marked e then 1 else 0 := by
 cases hp : e.place with
 | true => simp [erasure,marked,hp]
 | false =>
  by_cases hpred : pred b e.vertex
  · simp [erasure,hp,hpred]
  · have member : e.vertex∈E := by
     apply Classical.byContradiction
     intro no
     exact hpred (ChainTrace.nonerasure_requires_predecessor E b a e no hs)
    have mod := he _ member
    simp [erasure,hp,hpred,marked,mod]

theorem run_refines {E b es z}
 (he : ∀v,v∈E → v%6=5)
 (bounds : ∀e∈es,1≤e.vertex)
 (hr : ChainTrace.run E b es=some z) :
 ∃c r,Run 5 b es z c r ∧ r≤es.countP marked := by
 induction es generalizing b with
 | nil => simp [ChainTrace.run] at hr;subst z;exact ⟨0,0,Run.nil _,by simp⟩
 | cons e es ih =>
  cases hs : step true E b e with
  | none => simp [ChainTrace.run,hs] at hr
  | some a =>
   have tail : ChainTrace.run E a es=some z := by simpa [ChainTrace.run,hs] using hr
   obtain ⟨c,r,run,rb⟩ := ih (by intro f hf;exact bounds f (by simp [hf])) tail
   have step := existing_step_refines (bounds e (by simp)) hs
   have eb := erased_le_marked he hs
   refine ⟨_,_,Run.cons step run,?_⟩
   simp only [List.countP_cons]
   split <;> simp_all <;> omega

theorem table_stats (r : Nat) :
 (fullTable r).length=25+16*r ∧ (fullTable r).countP marked=r+1 := by
 have pre : (preTable r).length=17+16*r ∧ (preTable r).countP marked=r := by
  induction r with
  | zero => decide
  | succ r ih =>
   have pe : preTable (r+1)=preTable r++midTable r := by simp [preTable,assemble,List.append_assoc]
   rw [pe]
   simp only [List.length_append,List.countP_append,ih.1,ih.2]
   simp [midTable,MiddleDifference.events,marked,Nat.add_mod]
   omega
 simp only [fullTable,List.length_append,List.countP_append,pre.1,pre.2]
 simp [TailActual.events,marked,Nat.add_mod]
 omega

theorem physical_actual {r E} (w : ChainWholeBijection.Physical r E) :
 ∃c e,Run 5 [] w.val [5+6*(r+1)] c e ∧ e≤r+1 ∧ w.val.length=16*(r+1)+9 := by
 have he := w.property.erasure_sites
 obtain ⟨lab,decode⟩ := ChainLabelledCount.raw_lift_exists E he w
 have perm := ChainDecodedPerm.decode_perm (fullTable r) lab.val w.val lab.property.1 decode
 have mod : ∀v,v∈E → v%6=5 := by
  intro v hv
  obtain ⟨i,hi,eq⟩ := (he v).mp hv
  simp [eq,Nat.add_mod]
 obtain ⟨c,e,run,eb⟩ := run_refines mod (by intro ev hv;exact (w.property.bounded ev hv).1) w.property.legal
 have cnt := perm.countP_eq marked
 have stats := table_stats r
 refine ⟨c,e,run,?_,?_⟩
 · rw [cnt,stats.2] at eb;exact eb
 · have len := perm.length_eq;rw [stats.1] at len;omega
def sites (k : Nat) := (List.range k).map (fun i => 5+6*i)
theorem sites_spec (k v : Nat) : v∈sites k ↔ ChainFamilyArithmetic.IsErasure k v := by
 simp only [sites,List.mem_map,List.mem_range,ChainFamilyArithmetic.IsErasure]
 constructor
 · rintro ⟨i,hi,eq⟩;exact ⟨i,hi,eq.symm⟩
 · rintro ⟨i,hi,eq⟩;exact ⟨i,hi,eq.symm⟩

theorem actual_witness (r : Nat) :
 ∃word c e,Run 5 [] word [5+6*(r+1)] c e ∧ e≤r+1 ∧ word.length=16*(r+1)+9 := by
 let digits : ChainWordCounts.Digits r := ((⟨0,by decide⟩,fun _ => ⟨0,by decide⟩),⟨0,by decide⟩)
 let tuple := ChainWordCounts.ofDigits digits
 let w := ChainWholeBijection.toPhysical (sites (r+1)) (sites_spec (r+1)) tuple
 obtain ⟨c,e,run,bound,len⟩ := physical_actual w
 exact ⟨w.val,c,e,run,bound,len⟩

/-- k>=1 is explicit: the fixed family is indexed by r=k-1. -/
theorem actual_witness_k (k : Nat) (hk : 1≤k) :
 ∃word c e,Run 5 [] word [5+6*k] c e ∧ e≤k ∧ word.length=16*k+9 := by
 have eq : k-1+1=k := by omega
 simpa only [eq] using actual_witness (k-1)
#print axioms actual_witness
#print axioms actual_witness_k
#print axioms run_refines
#print axioms table_stats
#print axioms physical_actual
end ActualFamilyWitness
