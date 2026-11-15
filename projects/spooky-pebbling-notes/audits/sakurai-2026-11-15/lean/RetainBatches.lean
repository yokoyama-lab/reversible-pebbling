import Skeleton
namespace RetainBatches
open SpookyRound BatchUpper FillUpper FringeEmbed RetainRoot
theorem global_prepare (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (q : Config (2^(D+(1+h))-1)) (hq : consistent q)
 (hf : BatchedCleanup.Free roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt) q) :
 ∃t,PaperRuns HeapPath.pred (2*h+1) q t ∧
 t.state=FamilyRound.pack (FamilyRound.locate roots (2^(1+h)-1)) q (fun _=>rootOnly (2^(1+h)-1)) ∧
 t.work=k*(2*(2^(1+h)-1)-1) ∧ t.space≤k*(2^(1+h)-1)+CutSpace.pebs q ∧ CutSpace.pebs t.state≤k+CutSpace.pebs q := by
 let hb := fun i (j : Fin (2^(1+h)-1))=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt
 let qs := BatchedCleanup.restrict roots hb q
 have hqs : FamilySync.ConsistentFamily qs := fun i j=>hq _
 obtain ⟨t,ht,hs,hw,hsp⟩ := fringe_prepare roots D h hr hi q hq qs hqs hf
 have he := BatchedCleanup.exterior_le roots (2^(1+h)-1) q
 refine ⟨t,?_,hs,hw,by omega,?_⟩
 · rw [BatchedCleanup.reconstruct] at ht; exact ht
 · rw [hs,InitialGhost.pack_pebs roots D hr hi hb]
   have pos : 0<2^(1+h)-1 := by
     have hp := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤1+h by omega)
     simp at hp
     omega
   have hc : FamilySync.total (fun _ : Fin k=>CutSpace.pebs (rootOnly (2^(1+h)-1)))=k := by
     simp only [root_pebs pos]
     rw [FamilySync.total_const,Nat.mul_one]
   rw [hc]
   omega
noncomputable def retainState (roots : Fin k→Nat) (m : Nat) (q : Config N) :=
 FamilyRound.pack (FamilyRound.locate roots m) q (fun _=>rootOnly m)

noncomputable def retainMany (m : Nat) (xs : List (Fin k→Nat)) (q : Config N) : Config N :=
 match xs with |[]=>q |r::rs=>retainMany m rs (retainState r m q)

theorem free_after_other (a b : Fin k→Nat) (D h : Nat)
 (ha : ∀i,2^D≤a i+1∧a i+1<2^(D+1))
 (hb : ∀i,2^D≤b i+1∧b i+1<2^(D+1))
 (hd : ∀i j,a i≠b j) (q : Config (2^(D+(1+h))-1))
 (hf : BatchedCleanup.Free b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt) q) :
 BatchedCleanup.Free b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt) (retainState a (2^(1+h)-1) q) := by
 intro i j
 let v : Fin (2^(D+(1+h))-1) := ⟨embed (b i) j.val,embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt⟩
 have hv : decode (b i) (2^(1+h)-1) v=some j := decode_image (b i) (2^(1+h)-1) j v rfl
 have hn : FamilyRound.locate a (2^(1+h)-1) v=none := by
   cases he : FamilyRound.locate a (2^(1+h)-1) v with
   | none => rfl
   | some xy =>
     rcases xy with ⟨x,y⟩
     have hx := FamilyRound.locate_sound a v (x,y) he
     exact False.elim (ParallelMerge.decode_disjoint (a x) (b i) D (ha x) (hb i) (hd x i) v y j hx hv)
 change (retainState a (2^(1+h)-1) q).peb v=false
 simpa [retainState,FamilyRound.pack,hn] using hf i j

theorem retain_batches (D h : Nat) (xs : List (Fin k→Nat))
 (q : Config (2^(D+(1+h))-1)) (hq : consistent q)
 (hx : ∀r∈xs,BatchedCleanup.BatchOK D (1+h) q r)
 (hd : xs.Pairwise (fun a b=>∀i j,a i≠b j)) :
 ∃t,PaperRuns HeapPath.pred (xs.length*(2*h+1)) q t ∧ t.state=retainMany (2^(1+h)-1) xs q ∧
 t.work=xs.length*(k*(2*(2^(1+h)-1)-1)) ∧ t.space≤k*(2^(1+h)-1)+xs.length*k+CutSpace.pebs q ∧
 CutSpace.pebs t.state≤xs.length*k+CutSpace.pebs q := by
 induction xs generalizing q with
 | nil => exact ⟨⟨q,0,0⟩,by simpa using (PaperRuns.zero (pred:=HeapPath.pred) q),rfl,by simp,by simp,by simp⟩
 | cons a xs ih =>
   have ha := hx a (by simp)
   have pair := List.pairwise_cons.mp hd
   obtain ⟨t,ht,hs,hw,hsp,hpc⟩ := global_prepare a D h ha.level ha.unique q hq ha.free
   have next : ∀b∈xs,BatchedCleanup.BatchOK D (1+h) t.state b := by
     intro b hb
     have hz := hx b (by simp [hb])
     refine ⟨hz.level,hz.unique,?_⟩
     rw [hs]
     exact free_after_other a b D h ha.level hz.level (pair.1 b hb) q hz.free
   obtain ⟨u,hu,hus,huw,husp,hup⟩ := ih t.state (BatchedCleanup.consistent_final ht hq) next pair.2
   refine ⟨⟨u.state,t.work+u.work,max t.space u.space⟩,?_,?_,?_,?_,?_⟩
   · have hh := runs_append ht hu
     simpa [List.length_cons,Nat.add_mul,Nat.add_comm] using hh
   · change u.state=retainMany _ (a::xs) q
     rw [hus,hs]; rfl
   · change t.work+u.work=(xs.length+1)*(k*(2*(2^(1+h)-1)-1))
     rw [hw,huw,Nat.add_mul]; omega
   · change max t.space u.space≤k*(2^(1+h)-1)+(xs.length+1)*k+CutSpace.pebs q
     rw [Nat.add_mul]
     apply Nat.max_le.mpr
     constructor <;> omega
   · change CutSpace.pebs u.state≤(xs.length+1)*k+CutSpace.pebs q
     rw [Nat.add_mul]; omega

#print axioms retain_batches

theorem outside (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hv : ∀r∈xs,FamilyRound.locate r m v=none) :
 (retainMany m xs q).peb v=q.peb v ∧ (retainMany m xs q).ghost v=q.ghost v := by
 induction xs generalizing q with
 | nil => exact ⟨rfl,rfl⟩
 | cons a xs ih =>
   have hh := ih (retainState a m q) (fun r hr=>hv r (by simp [hr]))
   simpa [retainMany,retainState,FamilyRound.pack,hv a (by simp)] using hh

theorem selected (D : Nat) (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hl : ∀r∈xs,∀i,2^D≤r i+1∧r i+1<2^(D+1))
 (hd : xs.Pairwise (fun a b=>∀i j,a i≠b j))
 (r : Fin k→Nat) (hr : r∈xs) (i : Fin k) (j : Fin m)
 (hv : FamilyRound.locate r m v=some (i,j)) :
 (retainMany m xs q).peb v=decide (j.val=0) ∧
 (retainMany m xs q).ghost v=false := by
 induction xs generalizing q with
 | nil => simp at hr
 | cons a xs ih =>
   have pair := List.pairwise_cons.mp hd
   have hh : r=a∨r∈xs := by simpa using hr
   rcases hh with rfl|hr
   · have hn : ∀b∈xs,FamilyRound.locate b m v=none := by
       intro b hb
       exact FullPartition.other_none r b D (hl r (by simp)) (hl b (by simp [hb])) (pair.1 b hb) v i j hv
     have ho := outside xs (retainState r m q) v hn
     simpa [retainMany,retainState,FamilyRound.pack,hv,rootOnly] using ho
   · exact ih (retainState a m q) (fun b hb=>hl b (by simp [hb])) pair.2 hr

def staged (D n : Nat) : Config n :=
 ⟨fun v=>decide (v.val=0 ∨ (2^D-1≤v.val ∧ v.val<2^(D+1)-1)),
  fun v=>decide (v.val≠0 ∧ v.val<2^D-1)⟩

theorem groups_prepare (D h B K : Nat) (hD : 0<D) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(2*h+1)) (InitialGhost.rootGhost (2^(D+(1+h))-1)) t ∧
 t.state=retainMany (2^(1+h)-1) (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1)) ∧
 t.work=B*(K*(2*(2^(1+h)-1)-1)) ∧ t.space≤K*(2^(1+h)-1)+2^D+1 ∧ CutSpace.pebs t.state≤2^D+1 := by
 have pos : 0<2^(D+(1+h))-1 := by
   have hp := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤D+(1+h) by omega)
   simp at hp; omega
 have dp : 1<2^D := by
   have hp := Nat.pow_le_pow_right (n:=2) (by decide) hD
   simp at hp; omega
 have hx : ∀r∈FullPartition.groups D B K,BatchedCleanup.BatchOK D (1+h) (InitialGhost.rootGhost (2^(D+(1+h))-1)) r := by
   intro r hr
   obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
   refine ⟨InitialGhost.group_level D (Nat.le_of_eq hsize) b,InitialGhost.group_unique D b,?_⟩
   intro i j
   have hb := InitialGhost.group_level D (Nat.le_of_eq hsize) b i
   have he := root_le_embed (InitialGhost.groupRoot D b i) j.val
   simp only [InitialGhost.rootGhost,decide_eq_false_iff_not]
   omega
 have hq : consistent (InitialGhost.rootGhost (2^(D+(1+h))-1)) := by
   intro v; simp [InitialGhost.rootGhost]
 obtain ⟨t,ht,hs,hw,hsp,hp⟩ := retain_batches D h (FullPartition.groups D B K) _ hq hx FullPartition.groups_pairwise
 have len : (FullPartition.groups D B K).length=B := by simp [FullPartition.groups]
 rw [len] at ht hw hsp hp
 rw [InitialGhost.rootGhost_pebs pos,hsize] at hsp hp
 exact ⟨t,ht,hs,hw,hsp,hp⟩

theorem retained_staged (D h B K : Nat) (hk : 0<K) (hsize : B*K=2^D) :
 retainMany (2^(1+h)-1) (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1))=staged D (2^(D+(1+h))-1) := by
 have all : ∀v : Fin (2^(D+(1+h))-1),
   (retainMany (2^(1+h)-1) (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1))).peb v=(staged D _).peb v ∧
   (retainMany (2^(1+h)-1) (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1))).ghost v=(staged D _).ghost v := by
   intro v
   by_cases hv : v.val<2^D-1
   · have ho := outside (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1)) v
       (fun r hr=>FullPartition.top_none r D (2^(1+h)-1) (FullPartition.groups_level hsize r hr) v hv)
     simpa [staged,InitialGhost.rootGhost,hv,show ¬2^D≤v.val+1 by omega] using ho
   · obtain ⟨b,i,j,ha⟩ := FullPartition.grouped_cover D (1+h) hk hsize v (by omega)
     have mem : InitialGhost.groupRoot D b∈FullPartition.groups D B K := by simp [FullPartition.groups]
     have hs := selected D (FullPartition.groups D B K) (InitialGhost.rootGhost (2^(D+(1+h))-1)) v
       (fun r hr=>FullPartition.groups_level hsize r hr) FullPartition.groups_pairwise _ mem i j ha
     have he := FullPartition.local_root_iff (InitialGhost.groupRoot D b i) D (2^(1+h)-1)
       (InitialGhost.group_level D (Nat.le_of_eq hsize) b i) v j
       (FamilyRound.locate_sound _ v (i,j) ha)
     have hp : 0<2^D := Nat.pow_pos (by decide)
     have ep : (j.val=0)↔(v.val=0 ∨ (2^D-1≤v.val ∧ v.val<2^(D+1)-1)) := by
       rw [Nat.pow_succ] at he ⊢; omega
     constructor
     · exact hs.1.trans (by simp only [staged,ep])
     · simpa [staged,hv] using hs.2
 apply SpookyReverse.config_ext
 · intro v; exact (all v).1
 · intro v; exact (all v).2

theorem prepare_to_staged (D h B K : Nat) (hD : 0<D) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(2*h+1)) (InitialGhost.rootGhost (2^(D+(1+h))-1)) t ∧
 t.state=staged D (2^(D+(1+h))-1) ∧
 t.work=B*(K*(2*(2^(1+h)-1)-1)) ∧ t.space≤K*(2^(1+h)-1)+2^D+1 := by
 obtain ⟨t,ht,hs,hw,hsp,hp⟩ := groups_prepare D h B K hD hk hsize
 exact ⟨t,ht,hs.trans (retained_staged D h B K hk hsize),hw,hsp⟩
#print axioms prepare_to_staged
end RetainBatches
