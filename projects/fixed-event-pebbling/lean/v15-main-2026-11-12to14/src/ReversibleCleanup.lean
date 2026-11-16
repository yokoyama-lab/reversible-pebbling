import TerminalExistence
namespace ReversibleCleanup
open LocalCertificate TerminalProjection
def flip (e : Event) : Event := ⟨!e.place,e.vertex⟩
theorem pred_perm {a b : List Nat} (h : a.Perm b) (v : Nat) : pred a v ↔ pred b v := by
 simp [pred,h.mem_iff]
theorem fee_perm {a b : List Nat} (h : a.Perm b) (e : Event) : fee a e=fee b e := by
 simp [fee,pred_perm h]
theorem erasure_perm {a b : List Nat} (h : a.Perm b) (e : Event) : erasure a e=erasure b e := by
 simp [erasure,pred_perm h]
theorem step_perm {p b a b' e} (h : Step p b e a) (hb : b.Perm b') :
 ∃a',Step p b' e a' ∧ a.Perm a' := by
 cases hp : e.place with
 | true =>
  have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
  refine ⟨e.vertex::b',⟨h.1,?_,?_⟩,?_⟩
  · have hl := h.2.1;rw [he.2.2] at hl;simpa [hb.length_eq] using hl
  · simp only [hp, ↓reduceIte]
    exact ⟨fun hm => he.1 (hb.mem_iff.mpr hm),(pred_perm hb _).mp he.2.1,True.intro⟩
  · rw [he.2.2];exact hb.cons _
 | false =>
  have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
  refine ⟨b'.erase e.vertex,⟨h.1,?_,?_⟩,?_⟩
  · have hl := h.2.1;rw [he.2] at hl;simpa [(hb.erase e.vertex).length_eq] using hl
  · simp only [hp,Bool.false_eq_true,↓reduceIte];exact ⟨hb.mem_iff.mp he.1,True.intro⟩
  · rw [he.2];exact hb.erase _
theorem reverse_step {p b a e} (h : Step p b e a) (nd : b.Nodup) (cap : b.length≤p)
 (zero : erasure b e=0) :
 ∃b',Step p a (flip e) b' ∧ b'.Perm b ∧ fee a (flip e)=fee b e ∧ erasure a (flip e)=0 := by
 have pos := h.1
 cases hp : e.place with
 | true =>
  have he : e.vertex∉b ∧ pred b e.vertex ∧ a=e.vertex::b := by simpa [hp] using h.2.2
  have hpred : pred a e.vertex := by
   rw [he.2.2];rcases he.2.1 with h1|hm
   · exact Or.inl h1
   · exact Or.inr (by simp [hm])
  refine ⟨b,⟨pos,cap,?_⟩,List.Perm.refl _,?_,?_⟩
  · simp [flip,hp,he.2.2]
  · simp [flip,hp,fee,hpred]
  · simp [flip,hp,erasure,hpred]
 | false =>
  have he : e.vertex∈b ∧ a=b.erase e.vertex := by simpa [hp] using h.2.2
  have hpresent : pred b e.vertex := by
   by_cases ht : pred b e.vertex
   · exact ht
   · simp [erasure,hp,ht] at zero
  have absent : e.vertex∉a := by
   rw [he.2];intro hm;exact (nd.mem_erase_iff.mp hm).1 rfl
  have hpred : pred a e.vertex := by
   rcases hpresent with h1|hm
   · exact Or.inl h1
   · right;rw [he.2];exact (nd.mem_erase_iff).mpr ⟨by omega,hm⟩
  have hb : (e.vertex::a).Perm b := by rw [he.2];exact (List.perm_cons_erase he.1).symm
  refine ⟨e.vertex::a,⟨pos,?_,?_⟩,hb,?_,?_⟩
  · simpa [hb.length_eq] using cap
  · simp only [flip,hp,Bool.not_false,↓reduceIte]
    exact ⟨absent,hpred,True.intro⟩
  · simp [flip,hp,fee,hpresent]
  · simp [flip,hp,erasure]
theorem reverse_run_aux {p b es z c r} (hr : Run p b es z c r)
 (nd : b.Nodup) (cap : b.length≤p) (zero : r=0) :
 ∃b',Run p z (es.reverse.map flip) b' c 0 ∧ b'.Perm b := by
 induction hr with
 | nil b => exact ⟨b,Run.nil b,List.Perm.refl _⟩
 | @cons b a z es c r e hs ht ih =>
  have ze : erasure b e=0 := by omega
  have zr : r=0 := by omega
  obtain ⟨a',hrev,ha⟩ := ih (TerminalExistence.step_nodup nd hs) hs.2.1 zr
  obtain ⟨b',hstep,hb,hfee,herase⟩ := reverse_step hs nd cap ze
  obtain ⟨b'',hstep',hb'⟩ := step_perm hstep ha.symm
  have hf : fee a' (flip e)=fee b e := (fee_perm ha (flip e)).trans hfee
  have he : erasure a' (flip e)=0 := (erasure_perm ha (flip e)).trans herase
  have one : Run p a' [flip e] b'' (fee b e) 0 := by
   simpa [hf,he] using Run.cons hstep' (Run.nil b'')
  have all := run_append hrev one
  refine ⟨b'',?_,hb'.symm.trans hb⟩
  simpa [List.reverse_cons,List.map_append,Nat.add_comm] using all
theorem reverse_run {p b es z c} (hr : Run p b es z c 0)
 (nd : b.Nodup) (cap : b.length≤p) :
 ∃b',Run p z (es.reverse.map flip) b' c 0 ∧ b'.Perm b :=
 reverse_run_aux hr nd cap rfl
theorem cleanup_reverse {p m es c} (hr : Run p [m] es [] c 0) (cap : 1≤p) :
 Run p [] (es.reverse.map flip) [m] c 0 := by
 obtain ⟨b,hb,hp⟩ := reverse_run hr (by simp) (by simpa using cap)
 have he : b=[m] := by simpa using hp
 simpa [he] using hb
#print axioms reverse_run
#print axioms cleanup_reverse
#print axioms reverse_step
end ReversibleCleanup
