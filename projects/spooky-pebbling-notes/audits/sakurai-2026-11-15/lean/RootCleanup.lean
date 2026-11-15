import RetainBatches
namespace RootCleanup
open SpookyRound BatchUpper FillUpper FringeEmbed RetainRoot

def ghosts (n : Nat) : Config n := ⟨fun _=>false,fun _=>true⟩

theorem pair_ghosts (H : Nat) : SyncTrace.pair 1 2 (rootOnly (2^(1+H)-1))
 (ghosts (2^H-1)) (ghosts (2^H-1))=InitialGhost.rootGhost (2^(1+H)-1) := by
 have all : ∀v : Fin (2^(1+H)-1),
   (SyncTrace.pair 1 2 (rootOnly (2^(1+H)-1)) (ghosts (2^H-1)) (ghosts (2^H-1))).peb v=decide (v.val=0) ∧
   (SyncTrace.pair 1 2 (rootOnly (2^(1+H)-1)) (ghosts (2^H-1)) (ghosts (2^H-1))).ghost v=decide (v.val≠0) := by
   intro v
   have nz : ∀r i,0<r→decode r (2^H-1) v=some i→v.val≠0 := by
     intro r i hr hd hz
     have hh := decode_sound r (2^H-1) v i hd
     exact proper_excludes_root r i.val hr (hh.trans hz)
   cases ha : decode 1 (2^H-1) v with
   | some i => simp [SyncTrace.pair,liftConfig,ha,ghosts,nz 1 i (by decide) ha]
   | none => cases hb : decode 2 (2^H-1) v with
     | some j => simp [SyncTrace.pair,liftConfig,ha,hb,ghosts,nz 2 j (by decide) hb]
     | none =>
       have hv : v.val=0 := by
         by_cases hz : v.val=0
         · exact hz
         · obtain ⟨r,i,hr,hi,he⟩ := child_cover H v.val (by omega) v.isLt
           have hh := decode_image r (2^H-1) ⟨i,hi⟩ v he
           rcases hr with rfl|rfl <;> simp_all
       simp [SyncTrace.pair,liftConfig,ha,hb,rootOnly,hv]
 apply SpookyReverse.config_ext
 · intro v; exact (all v).1
 · intro v; exact (all v).2

theorem cleanup (h : Nat) :
 ∃t,PaperRuns HeapPath.pred (2*h+1) (InitialGhost.rootGhost (2^(1+h)-1)) t ∧
 t.state=empty (2^(1+h)-1) ∧ t.work=2*(2^(1+h)-1)-1 ∧ t.space≤2^(1+h)-1 := by
 obtain ⟨r,hr,hrs,hw,hsp⟩ := full_storage_fill h (ghosts (2^h-1)) (by simp [consistent,ghosts]) (by simp [ghosts])
 have rs : r.state=full (2^h-1) := by
   apply SpookyReverse.config_ext
   · intro v; exact (hrs v).1
   · intro v; exact (hrs v).2
 obtain ⟨t,ht,hts,htw,htsp⟩ := SyncTrace.fringe_sync_paper 1 2 1 h h
   (by decide) (by decide) (by decide) (rootOnly (2^(1+h)-1)) (by simp [consistent,rootOnly]) hr hr
 rw [pair_ghosts] at ht
 have ts : t.state=full (2^(1+h)-1) := by rw [hts,rs,pair_full]
 obtain ⟨u,hu,hus,huw,husp⟩ := unfill (1+h)
 rw [←ts] at hu
 have hp : 0<2^h := Nat.pow_pos (by decide)
 have hn : 0<2^(1+h)-1 := by rw [Nat.pow_add]; simp; omega
 have he := two_external 1 2 (2^h-1) (rootOnly (2^(1+h)-1))
 rw [root_pebs hn] at he
 have pp : 2^(1+h)=2*2^h := by rw [Nat.pow_add]
 refine ⟨⟨u.state,t.work+u.work,max t.space u.space⟩,?_,hus,?_,Nat.max_le.mpr ⟨?_,husp⟩⟩
 · have hh := runs_append ht hu
   simpa [Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
 · change t.work+u.work=2*(2^(1+h)-1)-1
   rw [htw,hw,huw]; omega
 · omega

#print axioms cleanup


theorem fringe_cleanup (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+(1+h))-1)) (ho : consistent o) :
 ∃t,PaperRuns HeapPath.pred (2*h+1)
 (FamilyRound.pack (FamilyRound.locate roots (2^(1+h)-1)) o (fun _=>InitialGhost.rootGhost (2^(1+h)-1))) t ∧
 t.state=BatchedCleanup.clear roots (2^(1+h)-1) o ∧
 t.work=k*(2*(2^(1+h)-1)-1) ∧ t.space≤k*(2^(1+h)-1)+FamilyCost.exterior roots (2^(1+h)-1) o := by
 obtain ⟨r,hrun,hrs,hrw,hrsp⟩ := cleanup h
 have hc : FamilySync.ConsistentFamily (fun _ : Fin k=>InitialGhost.rootGhost (2^(1+h)-1)) := by
   intro i j; simp [InitialGhost.rootGhost]
 obtain ⟨t,ht,hs,hw,hsp⟩ := FamilySync.sync_uniform
   (FamilyCost.fringe_product roots D (1+h) hr hi o ho) (fun _=>InitialGhost.rootGhost (2^(1+h)-1)) (fun _=>r) hc
   (fun _=>hrun) (fun _=>hrw) (fun _=>hrsp)
 refine ⟨t,ht,?_,hw,hsp⟩
 rw [hs]
 change FamilyRound.pack _ o (fun _=>r.state)=BatchedCleanup.clear roots _ o
 rw [hrs]; rfl

def Seeded (roots : Fin k→Nat) (hb : ∀i j,embed (roots i) (j : Fin m).val<N) (q : Config N) :=
 BatchedCleanup.restrict roots hb q = (fun _=>InitialGhost.rootGhost m)

theorem clear_pebs_le (roots : Fin k→Nat) (m : Nat) (q : Config N) :
 CutSpace.pebs (BatchedCleanup.clear roots m q)≤CutSpace.pebs q := by
 apply Exceptions.sum_le
 intro v _
 cases hv : FamilyRound.locate roots m v <;> simp [BatchedCleanup.clear,FamilyRound.pack,hv,empty]

theorem global_cleanup (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (q : Config (2^(D+(1+h))-1)) (hq : consistent q)
 (hf : Seeded roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt) q) :
 ∃t,PaperRuns HeapPath.pred (2*h+1) q t ∧ t.state=BatchedCleanup.clear roots (2^(1+h)-1) q ∧
 t.work=k*(2*(2^(1+h)-1)-1) ∧ t.space≤k*(2^(1+h)-1)+CutSpace.pebs q ∧ CutSpace.pebs t.state≤CutSpace.pebs q := by
 obtain ⟨t,ht,hs,hw,hsp⟩ := fringe_cleanup roots D h hr hi q hq
 unfold Seeded at hf
 rw [←hf,BatchedCleanup.reconstruct] at ht
 have he := BatchedCleanup.exterior_le roots (2^(1+h)-1) q
 exact ⟨t,ht,hs,hw,by omega,by rw [hs]; exact clear_pebs_le roots _ q⟩

theorem seeded_after_other (a b : Fin k→Nat) (D h : Nat)
 (ha : ∀i,2^D≤a i+1∧a i+1<2^(D+1))
 (hb : ∀i,2^D≤b i+1∧b i+1<2^(D+1)) (hd : ∀i j,a i≠b j)
 (q : Config (2^(D+(1+h))-1))
 (hf : Seeded b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt) q) :
 Seeded b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt) (BatchedCleanup.clear a (2^(1+h)-1) q) := by
 have he : BatchedCleanup.restrict b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt)
   (BatchedCleanup.clear a (2^(1+h)-1) q)=BatchedCleanup.restrict b (fun i j=>embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt) q := by
   funext i
   have hn : ∀j : Fin (2^(1+h)-1),FamilyRound.locate a (2^(1+h)-1) ⟨embed (b i) j.val,embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt⟩=none := by
     intro j
     let v : Fin (2^(D+(1+h))-1) := ⟨embed (b i) j.val,embed_fin_bound (b i) j.val D (1+h) (hb i) j.isLt⟩
     have hv : decode (b i) (2^(1+h)-1) v=some j := decode_image (b i) _ j v rfl
     cases hl : FamilyRound.locate a (2^(1+h)-1) v with
     | none => rfl
     | some xy =>
       rcases xy with ⟨x,y⟩
       have hx := FamilyRound.locate_sound a v (x,y) hl
       exact False.elim (ParallelMerge.decode_disjoint (a x) (b i) D (ha x) (hb i) (hd x i) v y j hx hv)
   apply SpookyReverse.config_ext <;> intro j <;> simp [BatchedCleanup.restrict,BatchedCleanup.clear,FamilyRound.pack,hn j]
 exact he.trans hf

structure BatchOK (D h : Nat) (q : Config (2^(D+(1+h))-1)) (roots : Fin k→Nat) : Prop where
 level : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1)
 unique : ∀i j,roots i=roots j→i=j
 seeded : Seeded roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (level i) j.isLt) q

theorem batches (D h : Nat) (xs : List (Fin k→Nat)) (q : Config (2^(D+(1+h))-1))
 (hq : consistent q) (hx : ∀r∈xs,BatchOK D h q r)
 (hd : xs.Pairwise (fun a b=>∀i j,a i≠b j)) :
 ∃t,PaperRuns HeapPath.pred (xs.length*(2*h+1)) q t ∧ t.state=BatchedCleanup.cleaned (2^(1+h)-1) xs q ∧
 t.work=xs.length*(k*(2*(2^(1+h)-1)-1)) ∧ t.space≤k*(2^(1+h)-1)+CutSpace.pebs q ∧ CutSpace.pebs t.state≤CutSpace.pebs q := by
 induction xs generalizing q with
 | nil => exact ⟨⟨q,0,0⟩,by simpa using (PaperRuns.zero (pred:=HeapPath.pred) q),rfl,by simp,by simp,by simp⟩
 | cons a xs ih =>
   have ha := hx a (by simp)
   have pair := List.pairwise_cons.mp hd
   obtain ⟨t,ht,hs,hw,hsp,hpc⟩ := global_cleanup a D h ha.level ha.unique q hq ha.seeded
   have next : ∀b∈xs,BatchOK D h t.state b := by
     intro b hb
     have hz := hx b (by simp [hb])
     refine ⟨hz.level,hz.unique,?_⟩
     rw [hs]
     exact seeded_after_other a b D h ha.level hz.level (pair.1 b hb) q hz.seeded
   obtain ⟨u,hu,hus,huw,husp,hup⟩ := ih t.state (BatchedCleanup.consistent_final ht hq) next pair.2
   refine ⟨⟨u.state,t.work+u.work,max t.space u.space⟩,?_,?_,?_,?_,by change CutSpace.pebs u.state≤CutSpace.pebs q; omega⟩
   · have hh := runs_append ht hu
     simpa [List.length_cons,Nat.add_mul,Nat.add_comm] using hh
   · change u.state=BatchedCleanup.cleaned _ (a::xs) q
     rw [hus,hs]; rfl
   · change t.work+u.work=(xs.length+1)*(k*(2*(2^(1+h)-1)-1))
     rw [hw,huw,Nat.add_mul]; omega
   · exact Nat.max_le.mpr ⟨hsp,by omega⟩
#print axioms global_cleanup
#print axioms batches


def held (D n : Nat) : Config n :=
 ⟨fun v=>decide (v.val=0 ∨ (2^D-1≤v.val ∧ v.val<2^(D+1)-1)),
  fun v=>decide (2^(D+1)-1≤v.val)⟩

theorem held_seeded (roots : Fin k→Nat) (D h : Nat) (hD : 0<D)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1)) :
 Seeded roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt) (held D (2^(D+(1+h))-1)) := by
 funext i
 have dp : 1<2^D := by
   have hp := Nat.pow_le_pow_right (n:=2) (by decide) hD
   simp at hp; omega
 have both : ∀j : Fin (2^(1+h)-1),
   (BatchedCleanup.restrict roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt) (held D (2^(D+(1+h))-1)) i).peb j=(InitialGhost.rootGhost _).peb j ∧
   (BatchedCleanup.restrict roots (fun i j=>embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt) (held D (2^(D+(1+h))-1)) i).ghost j=(InitialGhost.rootGhost _).ghost j := by
   intro j
   let v : Fin (2^(D+(1+h))-1) := ⟨embed (roots i) j.val,embed_fin_bound (roots i) j.val D (1+h) (hr i) j.isLt⟩
   have hi := hr i
   have low := root_le_embed (roots i) j.val
   have he := FullPartition.local_root_iff (roots i) D (2^(1+h)-1) hi v j (decode_image (roots i) _ j v rfl)
   have ep : (embed (roots i) j.val=0 ∨ (2^D-1≤embed (roots i) j.val ∧ embed (roots i) j.val<2^(D+1)-1))↔j.val=0 := by
     change (j.val=0↔(2^D≤embed (roots i) j.val+1 ∧ embed (roots i) j.val+1<2^(D+1))) at he
     omega
   have eg : (2^(D+1)-1≤embed (roots i) j.val)↔j.val≠0 := by
     change (j.val=0↔(2^D≤embed (roots i) j.val+1 ∧ embed (roots i) j.val+1<2^(D+1))) at he
     omega
   simp only [BatchedCleanup.restrict,held,InitialGhost.rootGhost,ep,eg,and_self]
 apply SpookyReverse.config_ext
 · intro j; exact (both j).1
 · intro j; exact (both j).2

theorem clear_no_new_peb (roots : Fin k→Nat) (m : Nat) (q : Config N) (v : Fin N)
 (hv : q.peb v=false) : (BatchedCleanup.clear roots m q).peb v=false := by
 cases hl : FamilyRound.locate roots m v <;> simp_all [BatchedCleanup.clear,FamilyRound.pack,empty]

theorem cleaned_no_new_peb (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hv : q.peb v=false) : (BatchedCleanup.cleaned m xs q).peb v=false := by
 induction xs generalizing q with
 | nil => exact hv
 | cons r rs ih => exact ih (BatchedCleanup.clear r m q) (clear_no_new_peb r m q v hv)

theorem cleaned_selected_peb (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (r : Fin k→Nat) (hr : r∈xs) (i : Fin k) (j : Fin m)
 (hv : FamilyRound.locate r m v=some (i,j)) : (BatchedCleanup.cleaned m xs q).peb v=false := by
 induction xs generalizing q with
 | nil => simp at hr
 | cons a xs ih =>
   have hh : r=a∨r∈xs := by simpa using hr
   rcases hh with rfl|hr
   · exact cleaned_no_new_peb xs (BatchedCleanup.clear r m q) v (by simp [BatchedCleanup.clear,FamilyRound.pack,hv,empty])
   · exact ih (BatchedCleanup.clear a m q) hr

theorem outside (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hv : ∀r∈xs,FamilyRound.locate r m v=none) :
 (BatchedCleanup.cleaned m xs q).peb v=q.peb v ∧ (BatchedCleanup.cleaned m xs q).ghost v=q.ghost v := by
 induction xs generalizing q with
 | nil => exact ⟨rfl,rfl⟩
 | cons a xs ih =>
   have hh := ih (BatchedCleanup.clear a m q) (fun r hr=>hv r (by simp [hr]))
   simpa [BatchedCleanup.cleaned,BatchedCleanup.clear,FamilyRound.pack,hv a (by simp)] using hh

theorem held_cleaned (D h B K : Nat) (hD : 0<D) (hk : 0<K) (hsize : B*K=2^D) :
 BatchedCleanup.cleaned (2^(1+h)-1) (FullPartition.groups D B K) (held D (2^(D+(1+h))-1))=rootOnly (2^(D+(1+h))-1) := by
 have dp : 1<2^D := by
   have hp := Nat.pow_le_pow_right (n:=2) (by decide) hD
   simp at hp; omega
 have both : ∀v : Fin (2^(D+(1+h))-1),
   (BatchedCleanup.cleaned (2^(1+h)-1) (FullPartition.groups D B K) (held D (2^(D+(1+h))-1))).peb v=(rootOnly _).peb v ∧
   (BatchedCleanup.cleaned (2^(1+h)-1) (FullPartition.groups D B K) (held D (2^(D+(1+h))-1))).ghost v=false := by
   intro v
   by_cases hv : v.val<2^D-1
   · have ho := outside (FullPartition.groups D B K) (held D (2^(D+(1+h))-1)) v
       (fun r hr=>FullPartition.top_none r D (2^(1+h)-1) (FullPartition.groups_level hsize r hr) v hv)
     have hU : ¬2^(D+1)-1≤v.val := by rw [Nat.pow_succ]; omega
     simpa [held,rootOnly,show ¬2^(D+1)≤v.val+1 by omega,show ¬2^D≤v.val+1 by omega] using ho
   · obtain ⟨b,i,j,ha⟩ := FullPartition.grouped_cover D (1+h) hk hsize v (by omega)
     have mem : InitialGhost.groupRoot D b∈FullPartition.groups D B K := by simp [FullPartition.groups]
     have hp := cleaned_selected_peb (FullPartition.groups D B K) (held D (2^(D+(1+h))-1)) v _ mem i j ha
     have hg := BatchedCleanup.cleaned_selected (FullPartition.groups D B K) (held D (2^(D+(1+h))-1)) v _ mem i j ha
     exact ⟨hp.trans (by simp [rootOnly,show v.val≠0 by omega]),hg⟩
 apply SpookyReverse.config_ext
 · intro v; exact (both v).1
 · intro v; exact (both v).2

#print axioms held_seeded
#print axioms held_cleaned


theorem held_consistent (D n : Nat) : consistent (held D n) := by
 have hp : 0<2^D := Nat.pow_pos (by decide)
 intro v
 simp only [held,decide_eq_true_eq]
 rw [Nat.pow_succ]
 omega

theorem held_pebs (D n : Nat) : CutSpace.pebs (held D n)≤2^(D+1)-1 := by
 have hp : 0<2^D := Nat.pow_pos (by decide)
 have hc := Skeleton.card_cap (held D n).peb (2^(D+1)-1) (by
   intro v hv
   simp only [held,decide_eq_true_eq] at hv
   rw [Nat.pow_succ] at hv ⊢
   omega)
 simpa only [FillUpper.card_sum,CutSpace.pebs] using hc

theorem held_to_clean (D h B K : Nat) (hD : 0<D) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(2*h+1)) (held D (2^(D+(1+h))-1)) t ∧
 t.state=rootOnly (2^(D+(1+h))-1) ∧
 t.work=B*(K*(2*(2^(1+h)-1)-1)) ∧ t.space≤K*(2^(1+h)-1)+(2^(D+1)-1) := by
 have hx : ∀r∈FullPartition.groups D B K,BatchOK D h (held D (2^(D+(1+h))-1)) r := by
   intro r hr
   obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
   refine ⟨InitialGhost.group_level D (Nat.le_of_eq hsize) b,InitialGhost.group_unique D b,?_⟩
   exact held_seeded _ D h hD (InitialGhost.group_level D (Nat.le_of_eq hsize) b)
 obtain ⟨t,ht,hs,hw,hsp,hpc⟩ := batches D h (FullPartition.groups D B K) _ (held_consistent _ _) hx FullPartition.groups_pairwise
 have len : (FullPartition.groups D B K).length=B := by simp [FullPartition.groups]
 rw [len] at ht hw
 have hp := held_pebs D (2^(D+(1+h))-1)
 exact ⟨t,ht,hs.trans (held_cleaned D h B K hD hk hsize),hw,by omega⟩
#print axioms held_to_clean
end RootCleanup
