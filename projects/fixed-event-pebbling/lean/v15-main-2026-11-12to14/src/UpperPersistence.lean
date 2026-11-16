import ActualSeparator
import CleanHandoffFinal
namespace UpperPersistence
open LocalCertificate TerminalProjection VisitMeasure LowerProjection HandoffNontrivial
open SeparatorOccupancy

theorem strict_low {p m b es z c r} (hr : Run p b es z c r)
 (upper : ∃e∈es,m<e.vertex) :
 ∃d s,Run p (low m b) (moves m es) (low m z) d s ∧ d<c ∧ s≤r := by
 induction hr with
 | nil => simp at upper
 | @cons b a z es c r e hs ht ih =>
  by_cases he : e.vertex≤m
  · have tail : ∃f∈es,m<f.vertex := by
     obtain ⟨f,hf,hv⟩ := upper
     rcases List.mem_cons.mp hf with rfl | hf
     · omega
     · exact ⟨f,hf,hv⟩
    obtain ⟨d,s,run,dc,sr⟩ := ih tail
    have run' := Run.cons (step_low hs he) run
    refine ⟨fee b e+d,erasure b e+s,?_,by omega,by omega⟩
    simpa [moves,he,fee_low he,erasure_low he] using run'
  · obtain ⟨d,s,run,dc,sr⟩ := run_low (m:=m) ht
    have eq := upper_step_disappears hs (by omega : m<e.vertex)
    have pos := fee_positive b e
    refine ⟨d,s,?_,by omega,by omega⟩
    simpa [moves,he,eq] using run

/-- Once an upper event occurs, every later cut in a minimum-cost run
 still has an upper pebble. This includes the final cut. -/
theorem no_upper_return {p m n pre post P c cp rp ct rt}
 (minimal : CostMinimal p [] [n] c)
 (hp : Run p [] pre P cp rp) (ht : Run p P post [n] ct rt)
 (cost : c=cp+ct) (upper : ∃e∈pre,m<e.vertex) :
 ∃v∈P,m<v := by
 apply Classical.byContradiction
 intro no
 have bound : ∀v∈P,v≤m := by intro v hv;have h : ¬m<v := fun hgt => no ⟨v,hv,hgt⟩;omega
 obtain ⟨d,s,run,dc,sr⟩ := strict_low hp upper
 have eq := ProjectionSuffixHelpers.low_eq_self bound
 have run' : Run p [] (moves m pre) P d s := by rw [eq] at run; simpa [low] using run
 have new := run_append run' ht
 have min := minimal _ _ _ new
 omega

theorem singleton_cut_impossible {p n m pre suffix c r d s}
 (hp : Run p [] pre [m] c r) (ht : Run p [m] suffix [n] d s)
 (clean : CleanHandoffMeasure.bad n [] (pre++suffix)=[])
 (mn : m<n)
 (last : ∀Q∈(frames [m] suffix).dropLast,leftmost Q<m) : False := by
 cases suffix with
 | nil => cases ht;omega
 | cons e es =>
  cases ht with
  | @cons b a z es d s e hs ht =>
   have ev := CleanHandoffFinal.clean_next_is_successor clean rfl hp hs mn
   subst e
   have board : a=[m+1,m] := by simpa using hs.2.2.2.2
   have rest : es≠[] := by
    intro he;subst es;cases ht;simp at board
   have mem : a∈(frames [m] (⟨true,m+1⟩::es)).dropLast := by
    cases es with
    | nil => exact False.elim (rest rfl)
    | cons f fs => simp [frames,step_update hs]
   have less := last a mem
   have lm : leftmost a=m := by rw [board];simp [leftmost,Nat.min_eq_right (by omega : m≤m+1)]
   omega
theorem occupied_at_last_cut {p n m pre suffix Q c r d s}
 (hp : Run p [] pre Q c r) (ht : Run p Q suffix [n] d s)
 (clean : CleanHandoffMeasure.bad n [] (pre++suffix)=[])
 (mn : m<n) (lm : leftmost Q=m) (nonempty : Q≠[])
 (last : ∀R∈(frames Q suffix).dropLast,leftmost R<m) :
 ∃v∈Q,m<v := by
 apply Classical.byContradiction
 intro no
 have bound : ∀v∈Q,v≤m := by
  intro v hv;have hh : ¬m<v := fun hgt => no ⟨v,hv,hgt⟩;omega
 have nd := TerminalExistence.run_nodup (by simp : ([] : List Nat).Nodup) hp
 have all : ∀v∈Q,v=m := by
  intro v hv;have lo := leftmost_le hv;have hi:=bound v hv;omega
 have eq : Q=[m] := by
  cases Q with
  | nil => exact False.elim (nonempty rfl)
  | cons a xs =>
   have am := all a (by simp)
   cases xs with
   | nil => simp [am]
   | cons b xs =>
    have bm := all b (by simp)
    exact False.elim ((List.nodup_cons.mp nd).1 (by simp [am,bm]))
 subst Q
 exact singleton_cut_impossible hp ht clean mn last

/-- Any later cut, not merely intermediate after-move cuts. -/
theorem persistent_from_occupied_cut {p n m pre middle post Q P c c1 r1 c2 r2 c3 r3}
 (minimal : CostMinimal p [] [n] c)
 (hp : Run p [] pre Q c1 r1) (hm : Run p Q middle P c2 r2)
 (ht : Run p P post [n] c3 r3) (cost : c=c1+c2+c3)
 (occupied : ∃v∈Q,m<v) : ∃v∈P,m<v := by
 obtain ⟨v,hv,mv⟩ := occupied
 have upper := LastBad.upper_exists hp (by simp) hv mv
 have allupper : ∃e∈pre++middle,m<e.vertex := by
  obtain ⟨e,he,hgt⟩ := upper
  exact ⟨e,List.mem_append_left _ he,hgt⟩
 exact no_upper_return minimal (run_append hp hm) ht cost allupper
#print axioms occupied_at_last_cut
#print axioms persistent_from_occupied_cut
#print axioms strict_low
#print axioms no_upper_return
#print axioms singleton_cut_impossible
end UpperPersistence
