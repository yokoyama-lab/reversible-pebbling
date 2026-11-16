import ChainTrace
namespace TerminalProjection
open LocalCertificate
def pred (b : List Nat) (v : Nat) : Prop := v=1 ∨ v-1∈b
instance (b) (v) : Decidable (pred b v) := inferInstanceAs (Decidable (_ ∨ _))
def Step (p : Nat) (b : List Nat) (e : Event) (a : List Nat) : Prop :=
 1≤e.vertex ∧ a.length≤p ∧
 if e.place then e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b
 else e.vertex∈b ∧ a=b.erase e.vertex
def project (n : Nat) (b : List Nat) := b.filter (fun v => v != n)
def keep (n : Nat) (es : List Event) := es.filter (fun e => e.vertex != n)
def fee (b : List Nat) (e : Event) : Nat := if e.place then 1 else if pred b e.vertex then 1 else 9
def erasure (b : List Nat) (e : Event) : Nat := if e.place then 0 else if pred b e.vertex then 0 else 1
inductive Run (p : Nat) : List Nat → List Event → List Nat → Nat → Nat → Prop
| nil (b) : Run p b [] b 0 0
| cons {b a z es c r e} : Step p b e a → Run p a es z c r →
    Run p b (e::es) z (fee b e+c) (erasure b e+r)
theorem mem_project {n b v} : v∈project n b ↔ v∈b ∧ v≠n := by simp [project]
theorem pred_project {n b v} (hv : v<n) : pred (project n b) v ↔ pred b v := by
 have h : v-1≠n := by omega
 simp [pred,mem_project,h]
theorem project_erase (n v) (b : List Nat) : project n (b.erase v) = (project n b).erase v := by
 exact List.erase_filter.symm
theorem step_lower {p n b a e} (h : Step p b e a) (hv : e.vertex<n) :
 Step p (project n b) e (project n a) := by
 refine ⟨h.1, Nat.le_trans (List.length_filter_le _ _) h.2.1,?_⟩
 cases hp : e.place with
 | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
   simp only [↓reduceIte]
   refine ⟨fun hm => he.1 (mem_project.mp hm).1,(pred_project hv).mpr he.2.1,?_⟩
   rw [he.2.2]; simp [project,show e.vertex≠n by omega]
 | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
   simp only [Bool.false_eq_true, ↓reduceIte]
   exact ⟨mem_project.mpr ⟨he.1,by omega⟩,by rw [he.2,project_erase]⟩
theorem top_step_disappears {p n b a e} (h : Step p b e a) (hv : e.vertex=n) :
 project n a=project n b := by
 cases hp : e.place with
 | true =>
   have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
   rw [he.2.2];simp [project,hv]
 | false =>
   have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
   rw [he.2,hv,project_erase]
   exact List.erase_of_not_mem (by simp [project])
theorem fee_lower {n b e} (hv : e.vertex<n) : fee (project n b) e=fee b e := by
 simp [fee,pred_project hv]
theorem erasure_lower {n b e} (hv : e.vertex<n) : erasure (project n b) e=erasure b e := by
 simp [erasure,pred_project hv]
theorem run_project {p n b es z c r} (h : Run p b es z c r)
 (hb : ∀e∈es,e.vertex≤n) :
 ∃c' r', Run p (project n b) (keep n es) (project n z) c' r' ∧ c'≤c ∧ r'≤r := by
 induction h with
 | nil b => exact ⟨0,0,by simpa [keep] using Run.nil (p:=p) (project n b),by omega,by omega⟩
 | @cons b a z es c r e hs hr ih =>
   obtain ⟨c',r',ht,hc,he⟩ := ih (fun f hf => hb f (by simp [hf]))
   have hv := hb e (by simp)
   by_cases hn : e.vertex=n
   · have ha := top_step_disappears hs hn
     refine ⟨c',r',?_,by omega,by omega⟩
     simpa [keep,hn,ha] using ht
   · have hl : e.vertex<n := by omega
     refine ⟨fee b e+c',erasure b e+r',?_,by omega,by omega⟩
     have hh := Run.cons (step_lower hs hl) ht
     simpa [keep,hn,fee_lower hl,erasure_lower hl] using hh
theorem run_append {p b a z xs ys c r d t}
 (hx : Run p b xs a c r) (hy : Run p a ys z d t) :
 Run p b (xs++ys) z (c+d) (r+t) := by
 induction hx with
 | nil => simpa using hy
 | cons hs hr ih => simpa [Nat.add_assoc] using Run.cons hs (ih hy)
theorem project_absent {n b} (h : n∉b) : project n b=b := by
 apply List.filter_eq_self.mpr
 intro v hv
 simp only [bne_iff_ne]
 intro he
 exact h (he ▸ hv)
-- Deletes all earlier terminal activity before a supplied final placement.
-- Existence of this decomposition for every successful run is a separate obligation.
theorem normalize_terminal {p n pre post b a c r d t}
 (hp : Run p [] pre b c r)
 (hs : Step p b ⟨true,n⟩ a)
 (ht : Run p a post [n] d t)
 (hbound : ∀e∈pre,e.vertex≤n)
 (hpost : ∀e∈post,e.vertex≠n) :
 ∃c' r', Run p [] (keep n pre ++ ⟨true,n⟩::post) [n] c' r' ∧
 c'≤c+1+d ∧ r'≤r+t ∧
 (keep n pre ++ ⟨true,n⟩::post).length≤(pre++⟨true,n⟩::post).length ∧
 (∀e∈keep n pre ++ ⟨true,n⟩::post,e.vertex=n → e.place=true) := by
 obtain ⟨cp,rp,hr,hc,he⟩ := run_project hp hbound
 have hab : n∉b := by simpa [Step] using hs.2.2.1
 have hb := project_absent hab
 have hr' : Run p [] (keep n pre) b cp rp := by
   rw [hb] at hr
   simpa only [project,List.filter_nil] using hr
 have ht' : Run p b (⟨true,n⟩::post) [n] (1+d) t := by
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
theorem existing_step_refines {E b a e} (hv : 1≤e.vertex)
 (hs : LocalCertificate.step true E b e=some a) : Step 5 b e a := by
 cases hp : e.place with
 | true =>
   have h := (ChainTrace.placement_step E b a e hp).mp hs
   refine ⟨hv,?_,?_⟩
   · simpa [h.2.2.2] using h.2.2.1
   · simpa [hp,pred] using And.intro h.1 (And.intro h.2.1 h.2.2.2)
 | false =>
   have ha := ChainTrace.removal_step_after E b a e hp hs
   have hm := ChainTrace.removal_requires_present E b a e hp hs
   refine ⟨hv,?_,by simpa [hp] using And.intro hm ha⟩
   simp [LocalCertificate.step,hp] at hs
   rw [ha]
   omega
#print axioms existing_step_refines
#print axioms run_append
#print axioms normalize_terminal
#print axioms step_lower
#print axioms top_step_disappears
#print axioms run_project
end TerminalProjection
