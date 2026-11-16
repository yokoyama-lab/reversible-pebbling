import SeparatorOccupancy
import OptimalIntermediate
namespace ActualSeparator
open LocalCertificate TerminalProjection VisitMeasure SeparatorOccupancy WinningMinimum HandoffNontrivial

theorem intermediate_split {b Q : List Nat} {es : List Event}
 (h : Q∈(frames b es).dropLast) :
 ∃pre post,es=pre++post ∧ pre≠[] ∧ post≠[] ∧ evolve b pre=Q := by
 induction es generalizing b with
 | nil => simp [frames] at h
 | cons e es ih =>
  cases es with
  | nil => simp [frames] at h
  | cons f fs =>
   have hh : Q=update b e ∨ Q∈(frames (update b e) (f::fs)).dropLast := by
    simpa only [frames,List.dropLast_cons_cons,List.mem_cons] using h
   rcases hh with eq | hh
   · exact ⟨[e],f::fs,rfl,by simp,by simp,by simpa [evolve] using eq.symm⟩
   · obtain ⟨pre,post,hw,hl,hr,he⟩ := ih hh
     exact ⟨e::pre,post,by simp [hw],by simp,hr,by simpa [evolve] using he⟩

theorem intermediate_valid {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost) {Q : List Nat}
 (h : Q∈intermediate x.word) :
 Q≠[] ∧ Q≠[n] ∧ Q.Nodup ∧ ∀v∈Q,1≤v ∧ v≤n := by
 obtain ⟨pre,post,hw,hl,hr,he⟩ := intermediate_split h
 obtain ⟨P,cp,rp,ct,rt,hp,ht,hc,her,hne,hnf,hnd,hbounds⟩ :=
  OptimalIntermediate.proper_intermediate x minimal hw hl hr
 have eq : P=Q := (run_evolve hp).symm.trans he
 rw [←eq]
 exact ⟨hne,hnf,hnd,hbounds⟩

theorem intermediate_nonempty {p n es c r} (hr : Run p [] es [n] c r)
 (hn : 2≤n) : intermediate es≠[] := by
 cases es with
 | nil => cases hr
 | cons e es =>
  cases es with
  | nil =>
   cases hr with
   | cons hs ht =>
    cases ht
    have impossible : False := by
     cases hp : e.place with
     | false => simpa [hp] using hs.2.2
     | true =>
      have data : e.vertex∉([] : List Nat) ∧ pred [] e.vertex ∧ [n]=[e.vertex] := by
       simpa [hp] using hs.2.2
      have one : e.vertex=1 := by simpa [pred] using data.2.1
      have eq : n=e.vertex := by simpa using data.2.2
      omega
    exact impossible.elim
  | cons f fs => simp [intermediate,frames]

theorem actual_separator {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost) (hn : 2≤n) :
 ∃m pre Q post,intermediate x.word=pre++Q::post ∧ 1≤m ∧ m<n ∧ leftmost Q=m ∧
 (∀R∈intermediate x.word,leftmost R≤m) ∧
 (∀R∈intermediate x.word,∃v∈R,1≤v ∧ v≤m) ∧
 (∀R∈post,leftmost R<m) ∧ (∀v∈Q,v≤m ↔ v=m) := by
 apply separator_exists (intermediate_nonempty x.run hn)
 · intro Q hQ;exact (intermediate_valid x minimal hQ).1
 · intro Q hQ v hv;exact ((intermediate_valid x minimal hQ).2.2.2 v hv).1
 · intro Q hQ;exact (intermediate_valid x minimal hQ).2.2.1
 · intro Q hQ v hv;exact ((intermediate_valid x minimal hQ).2.2.2 v hv).2
 · intro Q hQ;exact (intermediate_valid x minimal hQ).2.1
#print axioms intermediate_nonempty
#print axioms actual_separator
#print axioms intermediate_split
#print axioms intermediate_valid
end ActualSeparator
