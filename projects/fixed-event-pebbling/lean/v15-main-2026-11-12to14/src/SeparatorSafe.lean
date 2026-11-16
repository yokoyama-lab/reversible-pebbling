import ActualSeparator
import UpperProjectionRun
namespace SeparatorSafe
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure UpperProjectionRun

theorem capacity_two {p n es c r} (hr : Run p [] es [n] c r) (hn : 2≤n) : 2≤p := by
 have upper : ∃e∈es,1<e.vertex := LastBad.upper_exists (n:=n) (m:=1) hr (by simp) (by simp) (by omega)
 obtain ⟨pre,post,Q,a,cp,rp,ct,rt,hw,hp,hs,ht,lo,pb,mem,spare,hc,he⟩ :=
  FirstUpperStructure.first_upper_run (by omega : 1≤1) hr (by simp) upper
 have ne : Q≠[] := by intro h;simpa [h] using mem
 have pos : 0<Q.length := List.length_pos_iff.mpr ne
 omega

theorem frames_last {p b es z c r} (hr : Run p b es z c r) (ne : es≠[]) :
 ∃boards,frames b es=boards++[z] := by
 induction hr with
 | nil => exact False.elim (ne rfl)
 | @cons b a z es c r e hs ht ih =>
  cases es with
  | nil =>
   cases ht
   exact ⟨[],by simp [frames,step_update hs]⟩
  | cons f fs =>
   obtain ⟨boards,hb⟩ := ih (by simp)
   exact ⟨update b e::boards,by simpa only [frames,step_update hs,List.cons_append] using congrArg (List.cons a) hb⟩

theorem intermediate_or_final {p b es z c r} (hr : Run p b es z c r)
 {a : List Nat} (ha : a∈frames b es) : a∈(frames b es).dropLast ∨ a=z := by
 have ne : es≠[] := by intro h;subst es;simp [frames] at ha
 obtain ⟨boards,hb⟩ := frames_last hr ne
 rw [hb] at ha ⊢
 simpa using ha

theorem safe_of_intermediates {p n es c r m}
 (hr : Run p [] es [n] c r) (hp : 2≤p)
 (occupied : ∀a∈(frames [] es).dropLast,∃v∈a,v≤m) : Safe p (p-1) m [] es := by
 apply safe_from_occupied_or_small hp
 intro pre e post b a cp rp hw hpre hs
 have mem : a∈frames [] es := by
  rw [hw,frames_append,run_evolve hpre]
  apply List.mem_append_right
  simp [frames,step_update hs]
 rcases intermediate_or_final hr mem with h | h
 · exact Or.inl (occupied a h)
 · exact Or.inr (by simp [h])
#print axioms capacity_two
#print axioms safe_of_intermediates
end SeparatorSafe
