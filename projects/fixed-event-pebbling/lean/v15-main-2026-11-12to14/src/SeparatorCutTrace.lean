import UpperPersistence
namespace SeparatorCutTrace
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure SeparatorOccupancy

theorem frames_split {b Q : List Nat} {es : List Event} {before after : List (List Nat)}
 (h : frames b es=before++Q::after) :
 ∃pre post,es=pre++post ∧ pre≠[] ∧ evolve b pre=Q ∧ frames Q post=after := by
 induction before generalizing b es with
 | nil =>
  cases es with
  | nil => simp [frames] at h
  | cons e es =>
   have eqs : update b e=Q ∧ frames (update b e) es=after := by simpa [frames] using h
   exact ⟨[e],es,rfl,by simp,by simpa [evolve] using eqs.1,by simpa [eqs.1] using eqs.2⟩
 | cons R before ih =>
  cases es with
  | nil => simp [frames] at h
  | cons e es =>
   have eqs : update b e=R ∧ frames (update b e) es=before++Q::after := by simpa [frames] using h
   obtain ⟨pre,post,hw,hne,he,hf⟩ := ih eqs.2
   exact ⟨e::pre,post,by simp [hw],by simp,by simpa [evolve] using he,hf⟩

theorem frames_final {p b es z c r} (hr : Run p b es z c r) (ne : es≠[]) :
 frames b es=(frames b es).dropLast++[z] := by
 induction hr with
 | nil => exact False.elim (ne rfl)
 | @cons b a z es c r e hs ht ih =>
  cases es with
  | nil => cases ht;simp [frames,step_update hs]
  | cons f fs =>
   have ih' := ih (by simp)
   rw [show frames b (e::f::fs)=update b e :: frames (update b e) (f::fs) from rfl]
   rw [step_update hs]
   rw [List.dropLast_cons_of_ne_nil (by simp [frames] : frames a (f::fs)≠[])]
   exact congrArg (List.cons a) ih'

/-- Translate the separator's board-list split to an actual operation cut,
 including exactly the later intermediate boards, excluding completion. -/
theorem actual_cut {p n es c r before Q after}
 (hr : Run p [] es [n] c r)
 (split : intermediate es=before++Q::after) :
 ∃pre post cp rp ct rt,es=pre++post ∧ pre≠[] ∧ post≠[] ∧
 Run p [] pre Q cp rp ∧ Run p Q post [n] ct rt ∧
 c=cp+ct ∧ r=rp+rt ∧ (frames Q post).dropLast=after := by
 have ne : es≠[] := by intro he;subst es;simp [intermediate,frames] at split
 have hf := frames_final hr ne
 have full : frames [] es=before++Q::(after++[[n]]) := by
  rw [show (frames [] es).dropLast=before++Q::after from split] at hf
  simpa [List.append_assoc] using hf
 obtain ⟨pre,post,hw,hn,he,hpost⟩ := frames_split full
 have rr : Run p [] (pre++post) [n] c r := by simpa [←hw] using hr
 obtain ⟨P,cp,rp,ct,rt,hp,ht,hc,her⟩ := run_split rr
 have pq : P=Q := (run_evolve hp).symm.trans he
 rw [pq] at hp ht
 have pn : post≠[] := by intro eq;rw [eq] at hpost;simp [frames] at hpost
 refine ⟨pre,post,cp,rp,ct,rt,hw,hn,pn,hp,ht,hc,her,?_⟩
 rw [hpost];simp
#print axioms actual_cut
end SeparatorCutTrace
