import BypassOptimal
namespace GeneralTerminal
open LocalCertificate TerminalProjection TerminalExistence SingletonVisit ProtectionClosure
theorem general_final_placement_decomposition {p n es c r P} (hr : Run p [] es P c r) (member : n∈P) :
 ∃pre post b a c1 r1 c2 r2,es=pre++⟨true,n⟩::post ∧
 Run p [] pre b c1 r1 ∧ Step p b ⟨true,n⟩ a ∧ Run p a post P c2 r2 ∧
 c=c1+1+c2 ∧ r=r1+r2 ∧ (∀f∈post,f.vertex≠n) := by
 have hm : ∃e∈es,e.vertex=n := by
  apply Classical.byContradiction
  intro h
  have no : ∀e∈es,e.vertex≠n := by intro e he hv;exact h ⟨e,he,hv⟩
  have hh := (run_other hr no).mp member
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
    have hh := (run_other ht hpost).mp member
    exact False.elim (hn hh)
  have evEq : e=⟨true,n⟩ := by cases e; simp_all
  subst e
  refine ⟨pre,post,b,a,c1,r1,d,t,?_,hpre,hs,ht,?_,?_,hpost⟩
  · exact hword
  · simp [fee] at hc;omega
  · simpa [erasure] using he
theorem normalize_general_terminal {p n pre post b a c r d t P}
 (hp : Run p [] pre b c r)
 (hs : Step p b ⟨true,n⟩ a)
 (ht : Run p a post P d t)
 (hbound : ∀e∈pre,e.vertex≤n)
 (hpost : ∀e∈post,e.vertex≠n) :
 ∃c' r', Run p [] (keep n pre ++ ⟨true,n⟩::post) P c' r' ∧
 c'≤c+1+d ∧ r'≤r+t ∧
 (keep n pre ++ ⟨true,n⟩::post).length≤(pre++⟨true,n⟩::post).length ∧
 (∀e∈keep n pre ++ ⟨true,n⟩::post,e.vertex=n → e.place=true) := by
 obtain ⟨cp,rp,hr,hc,he⟩ := run_project hp hbound
 have hab : n∉b := by simpa [Step] using hs.2.2.1
 have hb := project_absent hab
 have hr' : Run p [] (keep n pre) b cp rp := by
   rw [hb] at hr
   simpa only [project,List.filter_nil] using hr
 have ht' : Run p b (⟨true,n⟩::post) P (1+d) t := by
   simpa [fee,erasure] using Run.cons hs ht
 refine ⟨cp+(1+d),rp+t,run_append hr' ht',by omega,by omega,?_,?_⟩
 · have hl := List.length_filter_le (fun e : Event => e.vertex != n) pre
   simp only [List.length_append,List.length_cons]
   dsimp [keep] at *
   omega
 · intro e hm hn
   rcases List.mem_append.mp hm with hm | hm
   · have hv : e.vertex≠n := by simpa [keep] using (List.mem_filter.mp hm).2
     exact False.elim (hv hn)
   · rcases List.mem_cons.mp hm with heq | hm
     · simp [heq]
     · exact False.elim (hpost e hm hn)
/-- Exact final list P is preserved, not merely its membership set. -/
theorem general_terminal_normal_form {p n es c r P}
 (hr : Run p [] es P c r) (member : n∈P)
 (bound : ∀e∈es,e.vertex≤n) :
 ∃es' c' r',Run p [] es' P c' r' ∧ c'≤c ∧ r'≤r ∧ es'.length≤es.length ∧
 (∀e∈es',e.vertex≤n) ∧
 (∀e∈es',e.vertex=n → e.place=true) ∧ Protected p n [] es' := by
 obtain ⟨pre,post,b,a,c1,r1,c2,r2,hw,hpre,hs,hpost,hc,he,hno⟩ :=
   general_final_placement_decomposition hr member
 have prebound : ∀e∈pre,e.vertex≤n := by
  intro e hh; apply bound e; rw [hw]; simp [hh]
 obtain ⟨cn,rn,run,cl,rl,len,no⟩ := normalize_general_terminal hpre hs hpost prebound hno
 have sub : ∀e∈keep n pre ++ ⟨true,n⟩::post,e∈es := by
  intro e hh; rw [hw]
  rcases List.mem_append.mp hh with hh | hh
  · exact List.mem_append_left _ ((List.mem_filter.mp hh).1)
  · exact List.mem_append_right _ hh
 refine ⟨_,cn,rn,run,by omega,by omega,by simpa [hw] using len,?_,no,?_⟩
 · intro e hh; exact bound e (sub e hh)
 · intro pr e po b a cp rp word hprefix hstep en
   have mem : e∈keep n pre ++ ⟨true,n⟩::post := by rw [word]; simp
   have place := no e mem en
   simp [erasure,place]
/-- A protected, singleton-avoiding replacement of any bounded prefix.
No erasure-count bound for the optimal bypass is claimed. -/
theorem bounded_prefix_bypass {p n es c r P}
 (hr : Run p [] es P c r) (member : n∈P)
 (bound : ∀e∈es,e.vertex≤n) (hn : 2≤n)
 (spare : P.length≤p-1) (nontrivial : ¬P.Perm [n]) :
 ∃word final cost erased, Run p [] word final cost erased ∧ final.Perm P ∧
 cost≤c ∧ (∀e∈word,e.vertex≤n) ∧ Protected p n [] word ∧
 (VisitMeasure.frames [] word).count [n]=0 := by
 obtain ⟨w,cn,rn,run,cl,_,_,bounds,_,guard⟩ := general_terminal_normal_form hr member bound
 obtain ⟨v,z,cv,rv,hv,hz,hb,hg,ha,hmin⟩ :=
   BypassOptimal.lemma2_price9 p n P hn member spare nontrivial ⟨w,cn,rn,run,bounds,guard⟩
 have hcost := hmin w P cn rn run (List.Perm.refl _) bounds guard
 exact ⟨v,z,cv,rv,hv,hz,by omega,hb,hg,ha⟩
#print axioms bounded_prefix_bypass
#print axioms general_final_placement_decomposition
#print axioms normalize_general_terminal
#print axioms general_terminal_normal_form
end GeneralTerminal
