import FillUpper
namespace FrameUpper
open SpookyRound TraceBridge BatchUpper

def frame (F : Fin n → Bool) (q : Config n) : Config n :=
 ⟨fun v=>q.peb v||F v,fun v=>q.ghost v && !F v⟩
def Avoids (F : Fin n → Bool) (a : Action) :=
 ∀v,F v=true → firstAt a v=.idle ∧ ghostAt a v=false

theorem frame_first (F : Fin n → Bool) (q : Config n) (a : Action) (h : Avoids F a) :
 afterFirst (frame F q) a=frame F (afterFirst q a) := by
 apply SpookyReverse.config_ext <;> intro v
 · by_cases hf : F v=true
   · have hh := (h v hf).1; simp [frame,afterFirst,hf,hh]
   · cases hm : firstAt a v <;> simp [frame,afterFirst,hf,hm]
 · by_cases hf : F v=true
   · have hh := (h v hf).1; simp [frame,afterFirst,hf,hh]
   · cases hm : firstAt a v <;> simp [frame,afterFirst,hf,hm]

theorem frame_round (F : Fin n → Bool) (q : Config n) (a : Action) (h : Avoids F a) :
 afterRound (frame F q) a=frame F (afterRound q a) := by
 apply SpookyReverse.config_ext <;> intro v
 · by_cases hf : F v=true
   · have hh := h v hf; simp [afterRound,afterFirst,frame,hf,hh.1,hh.2]
   · cases hm : firstAt a v <;> simp [afterRound,afterFirst,frame,hf,hm]
 · by_cases hf : F v=true
   · have hh := h v hf; simp [afterRound,afterFirst,frame,hf,hh.1,hh.2]
   · cases hm : firstAt a v <;> simp [afterRound,afterFirst,frame,hf,hm]

theorem frame_legal (h : Legal pred q a) (ha : Avoids F a) : Legal pred (frame F q) a := by
 refine ⟨?_,?_,?_,?_,h.2.2.2.2.1,?_⟩
 · intro v
   have hh := h.1 v
   cases hf : F v <;> simp_all [frame]
 · intro v hv
   have hf : F v=false := by
     cases hf : F v with
     | false => rfl
     | true => have hh := (ha v hf).1; rw [hh] at hv; contradiction
   simp [frame,hf,h.2.1 v hv]
 · intro v hv; simp [frame,h.2.2.1 v hv]
 · intro v hv u hu; simp [frame,h.2.2.2.1 v hv u hu]
 · intro v hv
   rw [frame_first _ _ _ ha]
   simp [frame,h.2.2.2.2.2 v hv]

theorem card_union (P F : Fin n → Bool) : card (fun v=>P v||F v)≤card P+card F := by
 rw [FillUpper.card_sum,FillUpper.card_sum,FillUpper.card_sum,←HeapPath.sum_add]
 apply Exceptions.sum_le
 intro v hv
 cases P v <;> cases F v <;> decide

theorem frame_space (ha : Avoids F a) : roundSpace (frame F q) a≤roundSpace q a+card F := by
 have he : roundSpace (frame F q) a = card (fun v=>(q.peb v||(afterFirst q a).peb v)||F v) := by
   unfold roundSpace card
   rw [frame_first _ _ _ ha]
   congr 1
   apply List.filter_congr
   intro v hv
   simp [frame,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]
 rw [he]
 exact card_union _ _

theorem frame_actions (h : ActionRuns pred q as r)
 (ha : ∀a∈as,Avoids F a) :
 ∃t,ActionRuns pred (frame F q) as t ∧ t.state=frame F r.state ∧
 t.work=r.work ∧ t.space≤r.space+card F := by
 induction h with
 | nil q => exact ⟨_,ActionRuns.nil _,rfl,rfl,by simp⟩
 | @cons q a as r hm hg hl ht ih =>
   have hf := ha a (by simp)
   obtain ⟨t,hr,hs,hw,hsp⟩ := ih (fun b hb=>ha b (by simp [hb]))
   have hr' : ActionRuns pred (afterRound (frame F q) a) as t := by
     rw [frame_round _ _ _ hf]; exact hr
   refine ⟨_,ActionRuns.cons hm hg (frame_legal hl hf) hr',hs,?_,?_⟩
   · simp [SpookyDP.prepend,edge,hw]
   · change max (roundSpace (frame F q) a) t.space≤max (roundSpace q a) r.space+card F
     have hh := frame_space (q:=q) hf
     apply Nat.max_le.mpr
     constructor
     · exact Nat.le_trans hh (Nat.add_le_add_right (Nat.le_max_left _ _) _)
     · exact Nat.le_trans hsp (Nat.add_le_add_right (Nat.le_max_right _ _) _)

theorem actions_paper (h : ActionRuns pred q as r) : PaperRuns pred as.length q r := by
 induction h with
 | nil q => exact PaperRuns.zero q
 | cons hm hg hl ht ih => exact PaperRuns.step ⟨_,hm,hg,hl,rfl⟩ ih

theorem protected_run (h : ActionRuns pred q as r) (ha : ∀a∈as,Avoids F a) :
 ∃t,PaperRuns pred as.length (frame F q) t ∧ t.state=frame F r.state ∧
 t.work=r.work ∧ t.space≤r.space+card F := by
 obtain ⟨t,ht,hs,hw,hsp⟩ := frame_actions h ha
 exact ⟨t,actions_paper ht,hs,hw,hsp⟩
theorem singleton_card (root : Fin n) : card (fun v=>decide (v=root))=1 := by
 rw [FillUpper.card_sum]
 simp only [decide_eq_true_eq]
 rw [Exceptions.indicator_count]
 exact (List.nodup_finRange n).count_of_mem (List.mem_finRange root)

theorem protected_root {pred : Fin n → Fin n → Bool} {q : Config n} {r : SpookyDP.Result (Config n)} (h : ActionRuns pred q as r) (root : Fin n)
 (ha : ∀a∈as,firstAt a root=.idle ∧ ghostAt a root=false) :
 ∃t,PaperRuns pred as.length (frame (fun v=>decide (v=root)) q) t ∧
 t.state=frame (fun v=>decide (v=root)) r.state ∧ t.state.peb root=true ∧
 t.work=r.work ∧ t.space≤r.space+1 := by
 have hv : ∀a∈as,Avoids (fun v=>decide (v=root)) a := by
   intro a ha' v he
   have he' : v=root := by simpa using he
   subst v; exact ha a ha'
 obtain ⟨t,ht,hs,hw,hsp⟩ := protected_run h hv
 rw [singleton_card] at hsp
 refine ⟨t,ht,hs,?_,hw,hsp⟩
 rw [hs]; simp [frame]
#print axioms protected_root
#print axioms protected_run
end FrameUpper
