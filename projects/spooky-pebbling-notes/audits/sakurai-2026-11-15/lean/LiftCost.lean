import FringeEmbed
namespace LiftCost
open SpookyRound FringeEmbed

theorem weighted_hit [DecidableEq α] (xs : List α) (a : α) (w : Nat) :
 (xs.map fun x=>if x=a then w else 0).sum=w*xs.count a := by
 induction xs with
 | nil => simp
 | cons x xs ih => by_cases he : x=a <;> simp [he,ih,Nat.mul_add,Nat.add_comm]

theorem fin_hit (f : Fin n → Nat) (i : Fin n) :
 ((List.finRange n).map fun j=>if j=i then f j else 0).sum=f i := by
 have he : ((List.finRange n).map fun j=>if j=i then f j else 0)=
   ((List.finRange n).map fun j=>if j=i then f i else 0) := by
   apply List.map_congr_left
   intro j hj; by_cases he : j=i <;> simp_all
 rw [he,weighted_hit,(List.nodup_finRange n).count_of_mem (List.mem_finRange i),Nat.mul_one]

theorem decode_expand (root : Nat) (v : Fin N) (f : Fin m → Nat) :
 (match decode root m v with |none=>0 |some i=>f i)=
 ((List.finRange m).map fun i=>if decode root m v=some i then f i else 0).sum := by
 cases hd : decode root m v with
 | none => simp [List.map_const',List.sum_replicate_nat]
 | some j => simpa [eq_comm] using (fin_hit f j).symm

theorem fiber_sum (root : Nat) (hb : ∀i : Fin m,embed root i.val<N) (i : Fin m) (w : Nat) :
 ((List.finRange N).map fun v=>if decode root m v=some i then w else 0).sum=w := by
 let v : Fin N := ⟨embed root i.val,hb i⟩
 have he : ∀u : Fin N,decode root m u=some i ↔ u=v := by
   intro u; constructor
   · intro hh; apply Fin.ext; exact (decode_sound root m u i hh).symm
   · intro hh; subst u; exact decode_image root m i v rfl
 simp only [he]
 rw [weighted_hit,(List.nodup_finRange N).count_of_mem (List.mem_finRange v),Nat.mul_one]

theorem decode_sum (root : Nat) (hb : ∀i : Fin m,embed root i.val<N) (f : Fin m → Nat) :
 ((List.finRange N).map fun v=>match decode root m v with |none=>0 |some i=>f i).sum=
 ((List.finRange m).map f).sum := by
 have he : ((List.finRange N).map fun v=>match decode root m v with |none=>0 |some i=>f i)=
   ((List.finRange N).map fun v=>((List.finRange m).map fun i=>if decode root m v=some i then f i else 0).sum) := by
   apply List.map_congr_left; intro v hv; exact decode_expand root v f
 rw [he,HeapPath.exchange]
 congr 1
 apply List.map_congr_left
 intro i hi; exact fiber_sum root hb i (f i)

theorem lift_work (root m N : Nat) (hb : ∀i : Fin m,embed root i.val<N)
 (a : Action) (hm : a.first.length=m) : roundWork (liftAction root m N a)=roundWork a := by
 rw [WorkBridge.indexed_work (n:=N) _ (by simp [liftAction]),WorkBridge.indexed_work a hm]
 have he : ((List.finRange N).map fun v=>WorkBridge.cost (firstAt (liftAction root m N a) v))=
 ((List.finRange N).map fun v=>match decode root m v with |none=>0 |some i=>WorkBridge.cost (firstAt a i)) := by
   apply List.map_congr_left; intro v hv
   cases hd : decode root m v <;> simp [hd,WorkBridge.cost]
 rw [he]; exact decode_sum root hb _

noncomputable def outsideCount (root m : Nat) (outside : Config N) : Nat :=
 ((List.finRange N).map fun v=>match decode root m v with |none=>if outside.peb v then 1 else 0 |some _=>0).sum

theorem lift_space (root : Nat) (hb : ∀i : Fin m,embed root i.val<N)
 (outside : Config N) (q : Config m) (a : Action) :
 roundSpace (liftConfig root outside q) (liftAction root m N a)=roundSpace q a+outsideCount root m outside := by
 unfold roundSpace
 rw [CutSpace.filter_sum,CutSpace.filter_sum]
 unfold outsideCount
 rw [←decode_sum root hb (fun i=>if q.peb i || (afterFirst q a).peb i then 1 else 0),←HeapPath.sum_add]
 congr 1
 apply List.map_congr_left
 intro v hv
 rw [lift_after_first]
 cases hd : decode root m v with
 | none => simp [liftConfig,hd]
 | some i => simp [liftConfig,hd]
theorem lift_actions_cost (root : Nat) (outside : Config N)
 (p : Fin m → Fin m → Bool) (P : Fin N → Fin N → Bool)
 (hc : DepClosed root p P) (ho : FillUpper.consistent outside)
 (hb : ∀i : Fin m,embed root i.val<N)
 (h : TraceBridge.ActionRuns p q as r) :
 ∃t,TraceBridge.ActionRuns P (liftConfig root outside q) (as.map (liftAction root m N)) t ∧
 t.state=liftConfig root outside r.state ∧ t.work=r.work ∧
 t.space≤r.space+outsideCount root m outside := by
 induction h with
 | nil q => exact ⟨_,TraceBridge.ActionRuns.nil _,rfl,rfl,by simp⟩
 | @cons q a as r hm hg hl ht ih =>
   obtain ⟨t,ht',hs,hw,hsp⟩ := ih
   have ht'' : TraceBridge.ActionRuns P (afterRound (liftConfig root outside q) (liftAction root m N a))
       (as.map (liftAction root m N)) t := by rw [lift_after_round]; exact ht'
   refine ⟨_,TraceBridge.ActionRuns.cons (by simp [liftAction]) (by simp [liftAction])
     (lift_legal root outside q p P a hc ho hl) ht'',hs,?_,?_⟩
   · simp [SpookyDP.prepend,edge,lift_work root m N hb a hm,hw]
   · change max (roundSpace (liftConfig root outside q) (liftAction root m N a)) t.space≤
       max (roundSpace q a) r.space+outsideCount root m outside
     rw [lift_space root hb]
     apply Nat.max_le.mpr
     exact ⟨Nat.add_le_add_right (Nat.le_max_left _ _) _,
       Nat.le_trans hsp (Nat.add_le_add_right (Nat.le_max_right _ _) _)⟩

theorem fringe_cleanup_cost (root D h : Nat)
 (hr : 2^D≤root+1 ∧ root+1<2^(D+1)) (outside : Config (2^(D+h)-1))
 (ho : FillUpper.consistent outside) (q : Config (2^h-1))
 (hq : FillUpper.consistent q) (hp : ∀v,q.peb v=false) :
 ∃t,PaperRuns HeapPath.pred (2*h) (liftConfig root outside q) t ∧
 t.state=liftConfig root outside (FillUpper.empty (2^h-1)) ∧ t.work=2*(2^h-1) ∧
 t.space≤(2^h-1)+outsideCount root (2^h-1) outside := by
 obtain ⟨r,hpRun,hstate,hw,hspace⟩ := FillUpper.full_storage_cleanup h q hq hp
 obtain ⟨as,hd,ha⟩ := TraceBridge.extract_actions hpRun
 obtain ⟨t,ht,hs,htw,hts⟩ := lift_actions_cost root outside HeapPath.pred HeapPath.pred
   (fringe_dep_closed root D h hr) ho (fun i=>embed_fin_bound root i.val D h hr i.isLt) ha
 refine ⟨t,?_,?_,htw.trans hw,?_⟩
 · have hh := FrameUpper.actions_paper ht; simpa [hd] using hh
 · rw [hs,hstate]
 · exact Nat.le_trans hts (Nat.add_le_add_right hspace _)
#print axioms fringe_cleanup_cost
#print axioms lift_work
#print axioms lift_space
end LiftCost
