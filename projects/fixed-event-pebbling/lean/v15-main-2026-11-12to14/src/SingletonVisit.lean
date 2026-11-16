import BypassContext
import BypassPermutation
namespace SingletonVisit
open LocalCertificate TerminalProjection VisitMeasure
theorem visit_pair {p initial es final c r m}
 (hr : Run p initial es final c r) (visit : [m]∈frames initial es) (end_ne : final≠[m]) :
 ∃pre e f post b a cp rp ct rt,
 es=pre++e::f::post ∧ Run p initial pre b cp rp ∧ Step p b e [m] ∧ Step p [m] f a ∧
 Run p a post final ct rt ∧ c=cp+fee b e+fee [m] f+ct ∧ r=rp+erasure b e+erasure [m] f+rt := by
 induction hr with
 | nil b => simp [frames] at visit
 | @cons initial a final es c r e hs ht ih =>
  have v : [m]=a ∨ [m]∈frames a es := by simpa [frames,step_update hs] using visit
  rcases v with ha|hv
  · subst a
    cases ht with
    | nil => exact False.elim (end_ne rfl)
    | @cons _ a final post ct rt f hf hpost =>
      exact ⟨[],e,f,post,initial,a,0,0,ct,rt,rfl,Run.nil _,hs,hf,hpost,by omega,by omega⟩
  · obtain ⟨pre,ep,f,post,b,after,cp,rp,ct,rt,hw,hpre,hep,hf,hpost,hc,he⟩ := ih hv end_ne
    refine ⟨e::pre,ep,f,post,b,after,fee initial e+cp,erasure initial e+rp,ct,rt,?_,Run.cons hs hpre,hep,hf,hpost,?_,?_⟩
    · simp [hw]
    · omega
    · omega
theorem before_singleton {p m b e} (hm : 2≤m) (nd : b.Nodup)
 (hs : Step p b e [m]) : e.place=false ∧ e.vertex≠m ∧ b.Perm [m,e.vertex] := by
 have hmb : m∈b := by
  cases hp : e.place with
  | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ [m]=e.vertex::b := by simpa [hp] using hs.2.2
   have hv : m=e.vertex := (List.cons.inj he.2.2).1
   have hb : []=b := (List.cons.inj he.2.2).2
   have hp := he.2.1
   simp [pred,←hv,←hb] at hp
   omega
  | false =>
   have he : e.vertex∈b ∧ [m]=b.erase e.vertex := by simpa [hp] using hs.2.2
   exact List.mem_of_mem_erase (by rw [←he.2];simp)
 have h := BypassContext.singleton_previous hmb nd hs
 exact ⟨h.1,h.2.1,h.2.2.trans (List.Perm.swap _ _ [])⟩
theorem run_perm {p b es z c r} (hr : Run p b es z c r) {b'} (hb : b.Perm b') :
 ∃z',Run p b' es z' c r ∧ z.Perm z' := by
 induction hr generalizing b' with
 | nil b => exact ⟨b',Run.nil b',hb⟩
 | @cons b a z es c r e hs ht ih =>
  obtain ⟨a',hs',ha⟩ := ReversibleCleanup.step_perm hs hb
  obtain ⟨z',ht',hz⟩ := ih ha
  refine ⟨z',?_,hz⟩
  have h := Run.cons hs' ht'
  simpa only [←ReversibleCleanup.fee_perm hb,←ReversibleCleanup.erasure_perm hb] using h
theorem delete_q1_context {p m initial final pre post cp rp ct rt b}
 (hb : b.Perm [1,m]) (hpre : Run p initial pre b cp rp)
 (hpost : Run p [1,m] post final ct rt) :
 ∃final',Run p initial (pre++post) final' (cp+ct) (rp+rt) ∧ final'.Perm final ∧ cp+ct<cp+2+ct := by
 obtain ⟨final',hp,hf⟩ := run_perm hpost hb.symm
 exact ⟨final',run_append hpre hp,hf.symm,by omega⟩
def Protected (p m : Nat) (initial : List Nat) (es : List Event) : Prop :=
 ∀pre e post b a cp rp,es=pre++e::post → Run p initial pre b cp rp → Step p b e a →
 e.vertex=m → erasure b e=0
theorem classified_visit {p initial es final c r m}
 (hr : Run p initial es final c r) (nd : initial.Nodup) (hm : 2≤m)
 (visit : [m]∈frames initial es) (end_ne : final≠[m])
 (bound : ∀e∈es,e.vertex≤m) (protect : Protected p m initial es) :
 ∃pre post b q cp rp ct rt,1≤q ∧ q<m ∧ b.Perm [m,q] ∧
 es=pre++⟨false,q⟩::⟨true,1⟩::post ∧ Run p initial pre b cp rp ∧
 Step p b ⟨false,q⟩ [m] ∧ Run p [1,m] post final ct rt ∧
 c=cp+fee b ⟨false,q⟩+1+ct ∧ r=rp+erasure b ⟨false,q⟩+rt := by
 obtain ⟨pre,e,f,post,b,a,cp,rp,ct,rt,hw,hpre,hs,hf,hpost,hc,he⟩ := visit_pair hr visit end_ne
 have nb := TerminalExistence.run_nodup nd hpre
 have prev := before_singleton hm nb hs
 have fb : f.vertex≤m := bound f (by rw [hw];simp)
 have no : f.vertex=m → erasure [m] f=0 := by
  apply protect (pre++[e]) f post [m] a (cp+fee b e) (rp+erasure b e)
  · simpa [List.append_assoc] using hw
  · have one : Run p b [e] [m] (fee b e) (erasure b e) := by simpa using Run.cons hs (Run.nil [m])
    exact run_append hpre one
  · exact hf
 have next := BypassContext.singleton_next hm hf fb no
 have eb : e.vertex≤m := bound e (by rw [hw];simp)
 have ee : e=⟨false,e.vertex⟩ := by cases e;simp_all
 obtain ⟨fEq,aEq⟩ := next
 subst f;subst a
 refine ⟨pre,post,b,e.vertex,cp,rp,ct,rt,hs.1,by omega,prev.2.2,?_,hpre,?_,hpost,?_,?_⟩
 · simpa only [←ee] using hw
 · simpa only [←ee] using hs
 · simpa [fee,prev.1] using hc
 · simpa [erasure,prev.1] using he
theorem disposal_price {m q b} (hq : 1≤q) (hqm : q<m) (hb : b.Perm [m,q]) :
 fee b ⟨false,q⟩=(if q=1 then 1 else 9) ∧ erasure b ⟨false,q⟩=(if q=1 then 0 else 1) := by
 have hpred : pred b q ↔ q=1 := by
  simp only [pred]; rw [hb.mem_iff]; simp only [List.mem_cons,List.not_mem_nil,or_false]
  omega
 simp [fee,erasure,hpred]
theorem swap_pair_context {p m q initial final pre post cp rp ct rt b}
 (hq : 2≤q) (hqm : q<m) (hp : 3≤p) (hb : b.Perm [m,q])
 (hpre : Run p initial pre b cp rp)
 (old : Run p b [⟨false,q⟩,⟨true,1⟩] [1,m] 10 1)
 (hpost : Run p [1,m] post final ct rt) :
 ∃c r,Run p initial (pre++[⟨true,1⟩,⟨false,q⟩]++post) final c r ∧
 c≤cp+10+ct ∧ r≤rp+1+rt ∧
 (frames initial (pre++[⟨false,q⟩,⟨true,1⟩]++post)).count [m]=
 (frames initial (pre++[⟨true,1⟩,⟨false,q⟩]++post)).count [m]+1 := by
 obtain ⟨cn,rn,hn,hc,hr,hvisit⟩ := BypassPermutation.general_swap hq hqm hp hb
 have context := BypassContext.context_replace hpre old hn hpost hc hr
 refine ⟨cp+cn+ct,rp+rn+rt,context.2.1,context.2.2.1,context.2.2.2,?_⟩
 have ep := run_evolve hpre
 have eo := run_evolve old
 have en := run_evolve hn
 simp only [frames_append,evolve_append,ep,eo,en,List.count_append]
 omega
theorem delete_q1_strict {p m initial final pre post cp rp ct rt b c r}
 (hb : b.Perm [m,1]) (hpre : Run p initial pre b cp rp)
 (hpost : Run p [1,m] post final ct rt) (hm : 2≤m)
 (hc : c=cp+fee b ⟨false,1⟩+1+ct)
 (he : r=rp+erasure b ⟨false,1⟩+rt) :
 ∃final',Run p initial (pre++post) final' (cp+ct) (rp+rt) ∧ final'.Perm final ∧ cp+ct<c ∧ rp+rt≤r := by
 have hbp := hb.trans (List.Perm.swap _ _ [])
 obtain ⟨final',hnew,hf,hlt⟩ := delete_q1_context hbp hpre hpost
 have price := disposal_price (q:=1) (by omega) (by omega : 1<m) hb
 simp only [if_pos rfl] at price
 exact ⟨final',hnew,hf,by omega,by omega⟩
#print axioms swap_pair_context
#print axioms delete_q1_strict
#print axioms classified_visit
#print axioms disposal_price
#print axioms visit_pair
#print axioms before_singleton
#print axioms run_perm
#print axioms delete_q1_context
end SingletonVisit
