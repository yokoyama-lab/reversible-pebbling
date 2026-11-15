import ParallelMerge
namespace SyncTrace
open SpookyRound FringeEmbed ParallelMerge

def Disjoint (r s m N : Nat) := ∀v : Fin N,∀i j : Fin m,
 decode r m v=some i → decode s m v=some j → False

theorem config_commute (r s : Nat) (outside : Config N) (qa qb : Config m)
 (hd : Disjoint r s m N) :
 liftConfig r (liftConfig s outside qb) qa=liftConfig s (liftConfig r outside qa) qb := by
 apply SpookyReverse.config_ext <;> intro v <;>
 cases hr : decode r m v with
 | none => cases hs : decode s m v <;> simp [liftConfig,hr,hs]
 | some i => cases hs : decode s m v with
   | none => simp [liftConfig,hr,hs]
   | some j => exact False.elim (hd v i j hr hs)

theorem lift_consistent (root : Nat) (outside : Config N) (q : Config m)
 (ho : FillUpper.consistent outside) (hq : FillUpper.consistent q) :
 FillUpper.consistent (liftConfig root outside q) := by
 intro v
 cases hd : decode root m v with
 | none => simpa [liftConfig,hd] using ho v
 | some i => simpa [liftConfig,hd] using hq i

theorem merge_first (a b : Action) (q : Config n) (hs : Apart n a b) :
 afterFirst q (merge n a b)=afterFirst (afterFirst q a) b := by
 apply SpookyReverse.config_ext <;> intro v
 · have hh := hs v
   cases am : firstAt a v <;> cases bm : firstAt b v <;> simp_all [afterFirst,pick]
 · have hh := hs v
   cases am : firstAt a v <;> cases bm : firstAt b v <;> simp_all [afterFirst,pick]

noncomputable def pair (r s : Nat) (outside : Config N) (qa qb : Config m) :=
 liftConfig r (liftConfig s outside qb) qa

variable {r s m N : Nat}

theorem pair_round (outside : Config N) (qa qb : Config m) (a b : Action)
 (hd : Disjoint r s m N) (hap : Apart N (liftAction r m N a) (liftAction s m N b)) :
 afterRound (pair r s outside qa qb) (merge N (liftAction r m N a) (liftAction s m N b))=
 pair r s outside (afterRound qa a) (afterRound qb b) := by
 rw [merge_round _ _ _ hap]
 unfold pair
 rw [lift_after_round,config_commute r s outside (afterRound qa a) qb hd,
   lift_after_round,←config_commute r s outside (afterRound qa a) (afterRound qb b) hd]

theorem pair_first (outside : Config N) (qa qb : Config m) (a b : Action)
 (hd : Disjoint r s m N) (hap : Apart N (liftAction r m N a) (liftAction s m N b)) :
 afterFirst (pair r s outside qa qb) (merge N (liftAction r m N a) (liftAction s m N b))=
 pair r s outside (afterFirst qa a) (afterFirst qb b) := by
 rw [merge_first _ _ _ hap]
 unfold pair
 rw [lift_after_first,config_commute r s outside (afterFirst qa a) qb hd,
   lift_after_first,←config_commute r s outside (afterFirst qa a) (afterFirst qb b) hd]

noncomputable def external (r s m : Nat) (outside : Config N) :=
 ((List.finRange N).map fun v=>match decode r m v,decode s m v with
 |none,none=>if outside.peb v then 1 else 0 |_,_=>0).sum

theorem pair_space (outside : Config N) (qa qb : Config m) (a b : Action)
 (hd : Disjoint r s m N) (hap : Apart N (liftAction r m N a) (liftAction s m N b))
 (hra : ∀i : Fin m,embed r i.val<N) (hrb : ∀i : Fin m,embed s i.val<N) :
 roundSpace (pair r s outside qa qb) (merge N (liftAction r m N a) (liftAction s m N b))=
 roundSpace qa a+roundSpace qb b+external r s m outside := by
 unfold roundSpace
 rw [CutSpace.filter_sum,CutSpace.filter_sum,CutSpace.filter_sum]
 rw [←LiftCost.decode_sum r hra (fun i=>if qa.peb i || (afterFirst qa a).peb i then 1 else 0),
   ←LiftCost.decode_sum s hrb (fun i=>if qb.peb i || (afterFirst qb b).peb i then 1 else 0)]
 unfold external
 rw [←HeapPath.sum_add,←HeapPath.sum_add]
 congr 1
 apply List.map_congr_left
 intro v hv
 rw [pair_first outside qa qb a b hd hap]
 cases hr : decode r m v with
 | none => cases hs : decode s m v <;> simp [pair,liftConfig,hr,hs]
 | some i => cases hs : decode s m v with
   | none => simp [pair,liftConfig,hr,hs]
   | some j => exact False.elim (hd v i j hr hs)

theorem pair_legal (outside : Config N) (qa qb : Config m) (a b : Action)
 (ho : FillUpper.consistent outside) (ha : Legal p qa a) (hb : Legal p qb b)
 (hd : Disjoint r s m N) (hap : Apart N (liftAction r m N a) (liftAction s m N b))
 (hcr : DepClosed r p P) (hcs : DepClosed s p P)
 (hcross : Cross P (liftAction r m N a) (liftAction s m N b)) :
 Legal P (pair r s outside qa qb) (merge N (liftAction r m N a) (liftAction s m N b)) := by
 have hla := lift_legal r (liftConfig s outside qb) qa p P a hcr (lift_consistent s outside qb ho hb.1) ha
 have hlb := lift_legal s (liftConfig r outside qa) qb p P b hcs (lift_consistent r outside qa ho ha.1) hb
 rw [←config_commute r s outside qa qb hd] at hlb
 exact merge_legal hla hlb hap hcross
theorem fringe_sync_actions (r s D h : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (outside : Config (2^(D+h)-1)) (ho : FillUpper.consistent outside)
 {qa qb : Config (2^h-1)} {ra rb : SpookyDP.Result (Config (2^h-1))}
 (ha : TraceBridge.ActionRuns HeapPath.pred qa as ra)
 (hb : TraceBridge.ActionRuns HeapPath.pred qb bs rb) (hlen : as.length=bs.length) :
 ∃t,TraceBridge.ActionRuns HeapPath.pred (pair r s outside qa qb)
   (List.zipWith (fun a b=>merge (2^(D+h)-1) (liftAction r (2^h-1) (2^(D+h)-1) a)
     (liftAction s (2^h-1) (2^(D+h)-1) b)) as bs) t ∧
 t.state=pair r s outside ra.state rb.state ∧ t.work=ra.work+rb.work ∧
 t.space≤ra.space+rb.space+external r s (2^h-1) outside := by
 have hd : Disjoint r s (2^h-1) (2^(D+h)-1) := decode_disjoint r s D hr hs hne
 have hra := fun i : Fin (2^h-1)=>embed_fin_bound r i.val D h hr i.isLt
 have hrb := fun i : Fin (2^h-1)=>embed_fin_bound s i.val D h hs i.isLt
 induction ha generalizing qb bs rb with
 | nil qa =>
   have he : bs=[] := by simpa using hlen.symm
   subst bs
   cases hb with
   | nil qb => exact ⟨_,TraceBridge.ActionRuns.nil _,rfl,rfl,by simp⟩
 | @cons qa a as ra ham hag hal hat ih =>
   cases bs with
   | nil => simp at hlen
   | cons b bs =>
     cases hb with
     | @cons _ _ _ rb hbm hbg hbl hbt =>
       have hl : as.length=bs.length := by simpa using hlen
       obtain ⟨t,ht,hstate,hwork,hspace⟩ := ih hbt hl
       have hap := fringe_apart r s D (2^h-1) (2^h-1) (2^(D+h)-1) hr hs hne a b
       have hcross := fringe_cross r s D h hr hs hne a b
       have legal := pair_legal outside qa qb a b ho hal hbl hd hap
         (fringe_dep_closed r D h hr) (fringe_dep_closed s D h hs) hcross
       have hnext := pair_round outside qa qb a b hd hap
       have ht' : TraceBridge.ActionRuns HeapPath.pred
         (afterRound (pair r s outside qa qb)
           (merge (2^(D+h)-1) (liftAction r (2^h-1) (2^(D+h)-1) a) (liftAction s (2^h-1) (2^(D+h)-1) b)))
         (List.zipWith (fun a b=>merge (2^(D+h)-1) (liftAction r (2^h-1) (2^(D+h)-1) a) (liftAction s (2^h-1) (2^(D+h)-1) b)) as bs) t := by rw [hnext]; exact ht
       refine ⟨_,TraceBridge.ActionRuns.cons (by simp [merge]) (by simp [merge]) legal ht',hstate,?_,?_⟩
       · simp only [SpookyDP.prepend,edge]
         rw [merge_work _ _ (by simp [liftAction]) (by simp [liftAction]) hap,
           LiftCost.lift_work r _ _ hra a ham,LiftCost.lift_work s _ _ hrb b hbm,hwork]
         omega
       · change max (roundSpace (pair r s outside qa qb) _) t.space≤
           max (roundSpace qa a) ra.space+max (roundSpace qb b) rb.space+external r s (2^h-1) outside
         rw [pair_space outside qa qb a b hd hap hra hrb]
         apply Nat.max_le.mpr
         constructor
         · exact Nat.add_le_add_right (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _)) _
         · exact Nat.le_trans hspace (Nat.add_le_add_right (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _)) _)

theorem fringe_sync_paper (r s D h d : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (outside : Config (2^(D+h)-1)) (ho : FillUpper.consistent outside)
 {qa qb : Config (2^h-1)} {ra rb : SpookyDP.Result (Config (2^h-1))}
 (ha : PaperRuns HeapPath.pred d qa ra) (hb : PaperRuns HeapPath.pred d qb rb) :
 ∃t,PaperRuns HeapPath.pred d (pair r s outside qa qb) t ∧
 t.state=pair r s outside ra.state rb.state ∧ t.work=ra.work+rb.work ∧
 t.space≤ra.space+rb.space+external r s (2^h-1) outside := by
 obtain ⟨as,hda,haa⟩ := TraceBridge.extract_actions ha
 obtain ⟨bs,hdb,hbb⟩ := TraceBridge.extract_actions hb
 obtain ⟨t,ht,hstate,hw,hsp⟩ := fringe_sync_actions r s D h hr hs hne outside ho haa hbb (by omega)
 refine ⟨t,?_,hstate,hw,hsp⟩
 have hh := FrameUpper.actions_paper ht
 simpa [List.length_zipWith,hda,hdb] using hh
theorem two_fringe_cleanup (r s D h : Nat)
 (hr : 2^D≤r+1 ∧ r+1<2^(D+1)) (hs : 2^D≤s+1 ∧ s+1<2^(D+1)) (hne : r≠s)
 (outside : Config (2^(D+h)-1)) (ho : FillUpper.consistent outside)
 (qa qb : Config (2^h-1)) (hqa : FillUpper.consistent qa) (hqb : FillUpper.consistent qb)
 (hpa : ∀v,qa.peb v=false) (hpb : ∀v,qb.peb v=false) :
 ∃t,PaperRuns HeapPath.pred (2*h) (pair r s outside qa qb) t ∧
 t.state=pair r s outside (FillUpper.empty (2^h-1)) (FillUpper.empty (2^h-1)) ∧
 t.work=4*(2^h-1) ∧ t.space≤2*(2^h-1)+external r s (2^h-1) outside := by
 obtain ⟨ra,ha,hsa,hwa,hspa⟩ := FillUpper.full_storage_cleanup h qa hqa hpa
 obtain ⟨rb,hb,hsb,hwb,hspb⟩ := FillUpper.full_storage_cleanup h qb hqb hpb
 obtain ⟨t,ht,hst,hw,hsp⟩ := fringe_sync_paper r s D h (2*h) hr hs hne outside ho ha hb
 refine ⟨t,ht,?_,?_,?_⟩
 · rw [hst,hsa,hsb]
 · rw [hw,hwa,hwb]; omega
 · omega
#print axioms two_fringe_cleanup
#print axioms fringe_sync_paper
#print axioms pair_space
#print axioms pair_legal
end SyncTrace
