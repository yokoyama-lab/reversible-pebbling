import BatchedCleanup
namespace RetainRoot
open SpookyRound FillUpper BatchUpper FringeEmbed

def full (n : Nat) : Config n := ⟨fun _=>true,fun _=>false⟩

theorem unfill (H : Nat) : ∃r,PaperRuns HeapPath.pred H (full (2^H-1)) r ∧
 r.state=empty (2^H-1) ∧ r.work=2^H-1 ∧ r.space≤2^H-1 := by
 let n := 2^H-1
 have he : Saturated (empty n) n := by
   refine ⟨?_,?_⟩
   · simp [consistent,empty]
   · intro v; simp [empty,show ¬n≤v.val by omega]
 have hf := fill_correct H (empty n) he
 have hr := reverse_execute (pred:=HeapPath.pred)
   (by intro v; simp [HeapPath.pred]; omega) (layers n H) (empty n)
   (by simp [empty]) (layers_noGhost n H) hf.1
 have hw := fill_work H (empty n) he
 have hz : CutSpace.pebs (empty n)=0 := by simp [CutSpace.pebs,empty,List.map_const',List.sum_replicate_nat]
 rw [hz,Nat.add_zero,pebs_full _ hf.2] at hw
 have hs : (execute (empty n) (layers n H)).state=full n := by
   apply SpookyReverse.config_ext
   · intro v; simpa [full] using hf.2.2 v
   · intro v
     have hp : (execute (empty n) (layers n H)).state.peb v=true := by simpa using hf.2.2 v
     have hc := hf.2.1 v
     cases hg : (execute (empty n) (layers n H)).state.ghost v <;> simp_all [full]
 rw [hs,layer_length] at hr
 exact ⟨_,hr,rfl,hw,fill_space _ _⟩

theorem depth_eq (i t : Nat) (hl : 2^t≤i+1) (hu : i+1<2^(t+1)) : depth i=t := by
 apply Nat.le_antisymm
 · exact Nat.lt_succ_iff.mp ((Nat.log2_lt (n:=i+1) (by omega)).mpr hu)
 · exact (Nat.le_log2 (n:=i+1) (by omega)).mpr hl

theorem child_cover (H v : Nat) (hv : 0<v) (hb : v<2^(1+H)-1) :
 ∃r i,(r=1∨r=2) ∧ i<2^H-1 ∧ embed r i=v := by
 have bd := depth_range v
 have dh : depth v<1+H := (Nat.log2_lt (n:=v+1) (by omega)).mpr (by omega)
 cases ht : depth v with
 | zero => simp [ht] at bd; omega
 | succ t =>
   rw [ht] at bd dh
   have hp : 0<2^t := Nat.pow_pos (by decide)
   have pp : 2^(t+1)=2^t*2 := Nat.pow_succ 2 t
   have pp2 : 2^(t+1+1)=2^t*4 := by rw [Nat.pow_succ,Nat.pow_succ]; omega
   have low : 2*2^t≤v+1 := by simpa [pp,Nat.mul_comm] using bd.1
   have high : v+1<4*2^t := by simpa [pp2,Nat.mul_comm] using bd.2
   have bpow : 2^(t+1)≤2^H := Nat.pow_le_pow_right (n:=2) (by decide) (by omega)
   by_cases mid : v+1<3*2^t
   · let i := v-2^t
     have ib : 2^t≤i+1 ∧ i+1<2^(t+1) := by dsimp [i]; rw [pp]; omega
     have di := depth_eq i t ib.1 ib.2
     refine ⟨1,i,Or.inl rfl,by omega,?_⟩
     simp [embed,di,i]; omega
   · let i := v-2*2^t
     have ib : 2^t≤i+1 ∧ i+1<2^(t+1) := by dsimp [i]; rw [pp]; omega
     have di := depth_eq i t ib.1 ib.2
     refine ⟨2,i,Or.inr rfl,by omega,?_⟩
     simp [embed,di,i]; omega
def rootOnly (n : Nat) : Config n := ⟨fun v=>decide (v.val=0),fun _=>false⟩

theorem pair_full (H : Nat) : SyncTrace.pair 1 2 (rootOnly (2^(1+H)-1))
 (full (2^H-1)) (full (2^H-1))=full (2^(1+H)-1) := by
 apply SpookyReverse.config_ext <;> intro v
 · cases ha : decode 1 (2^H-1) v with
   | some i => simp [SyncTrace.pair,liftConfig,ha,full]
   | none => cases hb : decode 2 (2^H-1) v with
     | some j => simp [SyncTrace.pair,liftConfig,ha,hb,full]
     | none =>
       have hv : v.val=0 := by
         by_cases hz : v.val=0
         · exact hz
         · obtain ⟨r,i,hr,hi,he⟩ := child_cover H v.val (by omega) v.isLt
           have hh := decode_image r (2^H-1) ⟨i,hi⟩ v he
           rcases hr with rfl|rfl <;> simp_all
       simp [SyncTrace.pair,liftConfig,ha,hb,full,rootOnly,hv]
 · cases ha : decode 1 (2^H-1) v <;> cases hb : decode 2 (2^H-1) v <;>
     simp [SyncTrace.pair,liftConfig,ha,hb,full,rootOnly]

theorem pair_empty (H : Nat) : SyncTrace.pair 1 2 (rootOnly (2^(1+H)-1))
 (empty (2^H-1)) (empty (2^H-1))=rootOnly (2^(1+H)-1) := by
 apply SpookyReverse.config_ext <;> intro v
 · have nz : ∀r i,0<r→decode r (2^H-1) v=some i→v.val≠0 := by
     intro r i hr hd hz
     have hh := decode_sound r (2^H-1) v i hd
     exact proper_excludes_root r i.val hr (hh.trans hz)
   cases ha : decode 1 (2^H-1) v with
   | some i => simp [SyncTrace.pair,liftConfig,ha,rootOnly,empty,nz 1 i (by decide) ha]
   | none => cases hb : decode 2 (2^H-1) v with
     | some j => simp [SyncTrace.pair,liftConfig,ha,hb,rootOnly,empty,nz 2 j (by decide) hb]
     | none => simp [SyncTrace.pair,liftConfig,ha,hb]
 · cases ha : decode 1 (2^H-1) v <;> cases hb : decode 2 (2^H-1) v <;>
     simp [SyncTrace.pair,liftConfig,ha,hb,rootOnly,empty]

theorem root_pebs (hn : 0<n) : CutSpace.pebs (rootOnly n)=1 := by
 unfold CutSpace.pebs rootOnly
 have he : (fun v : Fin n=>if decide (v.val=0) then 1 else 0)=(fun v=>if v=⟨0,hn⟩ then 1 else 0) := by
   funext v
   simp [Fin.ext_iff]
 rw [he,Exceptions.indicator_count]
 exact (List.nodup_finRange n).count_of_mem (List.mem_finRange _)

theorem two_external (r s m : Nat) (q : Config N) : SyncTrace.external r s m q≤CutSpace.pebs q := by
 apply Exceptions.sum_le
 intro v _
 cases decode r m v <;> cases decode s m v <;> simp

theorem unfill_keep_root (H : Nat) : ∃t,PaperRuns HeapPath.pred H (full (2^(1+H)-1)) t ∧
 t.state=rootOnly (2^(1+H)-1) ∧ t.work=2*(2^H-1) ∧ t.space≤2^(1+H)-1 := by
 obtain ⟨r,hr,hs,hw,hsp⟩ := unfill H
 obtain ⟨t,ht,hst,hwt,hspt⟩ := SyncTrace.fringe_sync_paper 1 2 1 H H
   (by decide) (by decide) (by decide) (rootOnly (2^(1+H)-1)) (by simp [consistent,rootOnly]) hr hr
 rw [pair_full] at ht
 refine ⟨t,ht,?_,by rw [hwt,hw]; omega,?_⟩
 · rw [hst,hs,pair_empty]
 · have hp : 0<2^H := Nat.pow_pos (by decide)
   have hn : 0<2^(1+H)-1 := by rw [Nat.pow_add]; simp; omega
   have he := two_external 1 2 (2^H-1) (rootOnly (2^(1+H)-1))
   rw [root_pebs hn] at he
   have pp : 2^(1+H)=2*2^H := by rw [Nat.pow_add]
   omega
/-- Arbitrary ghosts, no initial pebbles: clean the whole fringe while retaining its root. -/
theorem prepare_root (H : Nat) (q : Config (2^(1+H)-1))
 (hc : consistent q) (hp : ∀v,q.peb v=false) :
 ∃t,PaperRuns HeapPath.pred (2*H+1) q t ∧ t.state=rootOnly (2^(1+H)-1) ∧
 t.work=2*(2^(1+H)-1)-1 ∧ t.space≤2^(1+H)-1 := by
 obtain ⟨r,hr,hrs,hrw,hrsp⟩ := full_storage_fill (1+H) q hc hp
 have hs : r.state=full (2^(1+H)-1) := by
   apply SpookyReverse.config_ext
   · intro v; exact (hrs v).1
   · intro v; exact (hrs v).2
 obtain ⟨u,hu,hus,huw,husp⟩ := unfill_keep_root H
 rw [←hs] at hu
 have hall := runs_append hr hu
 refine ⟨⟨u.state,r.work+u.work,max r.space u.space⟩,?_,hus,?_,?_⟩
 · have he : 1+H+H=2*H+1 := by omega
   rw [he] at hall; exact hall
 · change r.work+u.work=_
   rw [hrw,huw]
   have pp : 2^(1+H)=2*2^H := by rw [Nat.pow_add]
   have pos : 0<2^H := Nat.pow_pos (by decide)
   omega
 · exact Nat.max_le.mpr ⟨hrsp,husp⟩

/-- Arbitrary K root-retaining fringe preparations in parallel. -/
theorem fringe_prepare (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+(1+h))-1)) (ho : consistent o)
 (q : Fin k→Config (2^(1+h)-1)) (hq : FamilySync.ConsistentFamily q)
 (hp : ∀i v,(q i).peb v=false) :
 ∃t,PaperRuns HeapPath.pred (2*h+1) (FamilyRound.pack (FamilyRound.locate roots (2^(1+h)-1)) o q) t ∧
 t.state=FamilyRound.pack (FamilyRound.locate roots (2^(1+h)-1)) o (fun _=>rootOnly (2^(1+h)-1)) ∧
 t.work=k*(2*(2^(1+h)-1)-1) ∧ t.space≤k*(2^(1+h)-1)+FamilyCost.exterior roots (2^(1+h)-1) o := by
 classical
 have hx := fun i=>prepare_root h (q i) (hq i) (hp i)
 let r := fun i=>Classical.choose (hx i)
 have hh := fun i=>Classical.choose_spec (hx i)
 obtain ⟨t,ht,hs,hw,hsp⟩ := FamilySync.sync_uniform
   (FamilyCost.fringe_product roots D (1+h) hr hi o ho) q r hq
   (fun i=>(hh i).1) (fun i=>(hh i).2.2.1) (fun i=>(hh i).2.2.2)
 refine ⟨t,ht,?_,hw,hsp⟩
 rw [hs]
 change FamilyRound.pack _ o (fun i=>(r i).state)=FamilyRound.pack _ o (fun _=>rootOnly (2^(1+h)-1))
 congr 1
 funext i
 exact (hh i).2.1
#print axioms fringe_prepare
#print axioms prepare_root
#print axioms unfill_keep_root
#print axioms child_cover
#print axioms unfill
end RetainRoot
