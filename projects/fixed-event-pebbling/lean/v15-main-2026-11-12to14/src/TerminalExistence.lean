import TerminalProjection
namespace TerminalExistence
open LocalCertificate TerminalProjection
theorem step_nodup {p b e a} (hb : b.Nodup) (hs : Step p b e a) : a.Nodup := by
 cases hp : e.place with
 | true =>
  have h : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
  rw [h.2.2];exact List.nodup_cons.mpr ⟨h.1,hb⟩
 | false =>
  have h : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
  rw [h.2];exact hb.erase _
theorem run_nodup {p b es a c r} (hb : b.Nodup) (hr : Run p b es a c r) : a.Nodup := by
 induction hr with
 | nil => exact hb
 | cons hs hr ih => exact ih (step_nodup hb hs)
theorem step_other {p b e a n} (hs : Step p b e a) (hn : e.vertex≠n) : n∈a ↔ n∈b := by
 cases hp : e.place with
 | true =>
  have h : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using hs.2.2
  rw [h.2.2];simp [Ne.symm hn]
 | false =>
  have h : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
  rw [h.2];exact List.mem_erase_of_ne (Ne.symm hn)
theorem run_other {p b es a c r n} (hr : Run p b es a c r)
 (hn : ∀e∈es,e.vertex≠n) : n∈a ↔ n∈b := by
 induction hr with
 | nil => rfl
 | cons hs hr ih =>
  exact (ih (fun e he => hn e (by simp [he]))).trans (step_other hs (hn _ (by simp)))
theorem last_event (es : List Event) (n : Nat) (hm : ∃e∈es,e.vertex=n) :
 ∃pre e post,es=pre++e::post ∧ e.vertex=n ∧ (∀f∈post,f.vertex≠n) := by
 induction es with
 | nil => simp at hm
 | cons e es ih =>
  by_cases ht : ∃f∈es,f.vertex=n
  · obtain ⟨pre,f,post,he,hf,hp⟩ := ih ht
    exact ⟨e::pre,f,post,by simp [he],hf,hp⟩
  · have he : e.vertex=n := by simpa [ht] using hm
    exact ⟨[],e,es,rfl,he,by intro f hf hn;exact ht ⟨f,hf,hn⟩⟩
theorem run_split {p b z xs ys c r} (hr : Run p b (xs++ys) z c r) :
 ∃a c1 r1 c2 r2,Run p b xs a c1 r1 ∧ Run p a ys z c2 r2 ∧ c=c1+c2 ∧ r=r1+r2 := by
 induction xs generalizing b c r with
 | nil => exact ⟨b,0,0,c,r,Run.nil b,by simpa using hr,by omega,by omega⟩
 | cons e xs ih =>
  cases hr with
  | cons hs ht =>
   obtain ⟨a,c1,r1,c2,r2,h1,h2,hc,hr⟩ := ih ht
   exact ⟨a,_,_,c2,r2,Run.cons hs h1,h2,by omega,by omega⟩
theorem final_placement_decomposition {p n es c r} (hr : Run p [] es [n] c r) :
 ∃pre post b a c1 r1 c2 r2,es=pre++⟨true,n⟩::post ∧
 Run p [] pre b c1 r1 ∧ Step p b ⟨true,n⟩ a ∧ Run p a post [n] c2 r2 ∧
 c=c1+1+c2 ∧ r=r1+r2 ∧ (∀f∈post,f.vertex≠n) := by
 have hm : ∃e∈es,e.vertex=n := by
  apply Classical.byContradiction
  intro h
  have no : ∀e∈es,e.vertex≠n := by intro e he hv;exact h ⟨e,he,hv⟩
  have hh := (run_other hr no).mp (by simp : n∈[n])
  simp at hh
 obtain ⟨pre,e,post,hword,hev,hpost⟩ := last_event es n hm
 rw [hword] at hr
 obtain ⟨b,c1,r1,c2,r2,hpre,hrest,hc,he⟩ := run_split hr
 cases hrest with
 | @cons b a z es d t ev hs ht =>
  have hb := run_nodup (by simp : ([] : List Nat).Nodup) hpre
  have hp : e.place=true := by
   cases hp : e.place with
   | true => rfl
   | false =>
    have ha : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using hs.2.2
    have hn : n∉a := by
     rw [ha.2,hev]
     intro hm; exact (hb.mem_erase_iff.mp hm).1 rfl
    have hh := (run_other ht hpost).mp (by simp : n∈[n])
    exact False.elim (hn hh)
  have evEq : e=⟨true,n⟩ := by cases e; simp_all
  subst e
  refine ⟨pre,post,b,a,c1,r1,d,t,?_,hpre,hs,ht,?_,?_,hpost⟩
  · exact hword
  · simp [fee] at hc;omega
  · simpa [erasure] using he
theorem terminal_normal_form {p n es c r} (hr : Run p [] es [n] c r)
 (hbound : ∀e∈es,e.vertex≤n) :
 ∃es' c' r',Run p [] es' [n] c' r' ∧ c'≤c ∧ r'≤r ∧ es'.length≤es.length ∧
 (∀e∈es',e.vertex=n → e.place=true) := by
 obtain ⟨pre,post,b,a,c1,r1,c2,r2,hword,hpre,hs,hpost,hc,he,hno⟩ := final_placement_decomposition hr
 have hprebound : ∀e∈pre,e.vertex≤n := by
  intro e he
  apply hbound e
  rw [hword];simp [he]
 obtain ⟨c',r',hnorm,hcl,hrl,hlen,hnorem⟩ := normalize_terminal hpre hs hpost hprebound hno
 refine ⟨keep n pre ++ ⟨true,n⟩::post,c',r',hnorm,?_,?_,?_,hnorem⟩
 · omega
 · omega
 · simpa [hword] using hlen
#print axioms terminal_normal_form
#print axioms final_placement_decomposition
end TerminalExistence
