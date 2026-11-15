import RetainRoot
namespace InitialGhost
open SpookyRound BatchUpper FillUpper FringeEmbed RetainRoot

def rootGhost (n : Nat) : Config n := ⟨fun v=>decide (v.val=0),fun v=>decide (v.val≠0)⟩

theorem ghost_nonroot (n : Nat) : PaperRuns HeapPath.pred 1 (full n) ⟨rootGhost n,0,n⟩ := by
 let C : Fin n→Bool := fun _=>false
 let G : Fin n→Bool := fun v=>decide (v.val≠0)
 have hr : Ready HeapPath.pred (full n) C G := by
   refine ⟨?_,?_,?_,?_,?_⟩ <;> simp [full,C]
 have hs := batch_step hr
 have es : evolve (full n) C G=rootGhost n := by
   apply SpookyReverse.config_ext <;> intro v <;> simp [evolve,full,C,G,rootGhost]
 have wc : card C=0 := by simp [card,C]
 have sp : card (fun v=>(full n).peb v||C v)=n := by
   simp only [card,full,C,Bool.or_false]
   rw [List.filter_eq_self.mpr (by simp)]
   simp
 rw [es,wc,sp] at hs
 have hh := PaperRuns.step hs (PaperRuns.zero (rootGhost n))
 simpa [SpookyDP.prepend] using hh

theorem init_fringe (H : Nat) (q : Config (2^H-1))
 (hc : consistent q) (hp : ∀v,q.peb v=false) :
 ∃t,PaperRuns HeapPath.pred (H+1) q t ∧ t.state=rootGhost (2^H-1) ∧
 t.work=2^H-1 ∧ t.space≤2^H-1 := by
 obtain ⟨r,hr,hrs,hw,hsp⟩ := full_storage_fill H q hc hp
 have hs : r.state=full (2^H-1) := by
   apply SpookyReverse.config_ext
   · intro v; exact (hrs v).1
   · intro v; exact (hrs v).2
 have hg := ghost_nonroot (2^H-1)
 rw [←hs] at hg
 have ht := runs_append hr hg
 refine ⟨_,ht,rfl,?_,?_⟩
 · simpa using hw
 · change max r.space (2^H-1)≤2^H-1
   exact Nat.max_le.mpr ⟨hsp,Nat.le_refl _⟩

theorem fringe_init_fringe (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+h)-1)) (ho : consistent o)
 (q : Fin k→Config (2^h-1)) (hq : FamilySync.ConsistentFamily q) (hp : ∀i v,(q i).peb v=false) :
 ∃t,PaperRuns HeapPath.pred (h+1) (FamilyRound.pack (FamilyRound.locate roots (2^h-1)) o q) t ∧
 t.state=FamilyRound.pack (FamilyRound.locate roots (2^h-1)) o (fun _=>rootGhost (2^h-1)) ∧
 t.work=k*(2^h-1) ∧ t.space≤k*(2^h-1)+FamilyCost.exterior roots (2^h-1) o := by
 classical
 have hx := fun i=>init_fringe h (q i) (hq i) (hp i)
 let r := fun i=>Classical.choose (hx i)
 have hh := fun i=>Classical.choose_spec (hx i)
 obtain ⟨t,ht,hs,hw,hsp⟩ := FamilySync.sync_uniform
   (FamilyCost.fringe_product roots D h hr hi o ho) q r hq
   (fun i=>(hh i).1) (fun i=>(hh i).2.2.1) (fun i=>(hh i).2.2.2)
 refine ⟨t,ht,?_,hw,hsp⟩
 rw [hs]
 change FamilyRound.pack _ o (fun i=>(r i).state)=FamilyRound.pack _ o (fun _=>rootGhost (2^h-1))
 congr 1
 funext i
 exact (hh i).2.1
theorem idle_space (q : Config n) (a : Action) (hi : ∀v : Fin n,firstAt a v=.idle) :
 roundSpace q a=CutSpace.pebs q := by
 unfold roundSpace CutSpace.pebs
 rw [CutSpace.filter_sum]
 congr 1
 apply List.map_congr_left
 intro v _
 simp [afterFirst,hi]

theorem pack_pebs (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (hb : ∀i j,embed (roots i) (j : Fin m).val<N)
 (o : Config N) (q : Fin k→Config m) :
 CutSpace.pebs (FamilyRound.pack (FamilyRound.locate roots m) o q)=
 FamilySync.total (fun i=>CutSpace.pebs (q i))+FamilyCost.exterior roots m o := by
 let a : Fin k→Action := fun _=>batch (fun _ : Fin m=>false) (fun _=>false)
 have hs := FamilyCost.space roots D hr hi hb o q a
 have hz : ∀v : Fin N,firstAt (FamilyRound.action (N:=N) (FamilyRound.locate roots m) a) v=.idle := by
   intro v
   cases hv : FamilyRound.locate roots m v with
   | none => simp [hv]
   | some ij => rcases ij with ⟨i,j⟩; simp [hv,a]
 rw [idle_space _ _ hz] at hs
 have hl : ∀i,roundSpace (q i) (a i)=CutSpace.pebs (q i) := by
   intro i
   exact idle_space _ _ (by intro v; simp [a])
 simpa only [hl] using hs

theorem rootGhost_pebs (hn : 0<n) : CutSpace.pebs (rootGhost n)=1 := by
 exact root_pebs hn

theorem global_init (roots : Fin k→Nat) (D h : Nat) (hh : 0<h)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (q : Config (2^(D+h)-1)) (hq : consistent q)
 (hf : BatchedCleanup.Free roots (fun i j=>embed_fin_bound (roots i) j.val D h (hr i) j.isLt) q) :
 ∃t,PaperRuns HeapPath.pred (h+1) q t ∧
 t.state=FamilyRound.pack (FamilyRound.locate roots (2^h-1)) q (fun _=>rootGhost (2^h-1)) ∧
 t.work=k*(2^h-1) ∧ t.space≤k*(2^h-1)+CutSpace.pebs q ∧ CutSpace.pebs t.state≤k+CutSpace.pebs q := by
 let hb := fun i (j : Fin (2^h-1))=>embed_fin_bound (roots i) j.val D h (hr i) j.isLt
 let qs := BatchedCleanup.restrict roots hb q
 have hqs : FamilySync.ConsistentFamily qs := fun i j=>hq _
 obtain ⟨t,ht,hs,hw,hsp⟩ := fringe_init_fringe roots D h hr hi q hq qs hqs hf
 have he := BatchedCleanup.exterior_le roots (2^h-1) q
 refine ⟨t,?_,hs,hw,by omega,?_⟩
 · rw [BatchedCleanup.reconstruct] at ht; exact ht
 · rw [hs,pack_pebs roots D hr hi hb]
   have pos : 0<2^h-1 := by
     have hp := Nat.pow_le_pow_right (n:=2) (by decide) hh
     simp at hp
     omega
   have hc : FamilySync.total (fun _ : Fin k=>CutSpace.pebs (rootGhost (2^h-1)))=k := by
     simp only [rootGhost_pebs pos]
     rw [FamilySync.total_const,Nat.mul_one]
   rw [hc]
   omega
noncomputable def initState (roots : Fin k→Nat) (m : Nat) (q : Config N) :=
 FamilyRound.pack (FamilyRound.locate roots m) q (fun _=>rootGhost m)

noncomputable def initMany (m : Nat) (xs : List (Fin k→Nat)) (q : Config N) : Config N :=
 match xs with |[]=>q |r::rs=>initMany m rs (initState r m q)

theorem free_after_other (a b : Fin k→Nat) (D h : Nat)
 (ha : ∀i,2^D≤a i+1∧a i+1<2^(D+1))
 (hb : ∀i,2^D≤b i+1∧b i+1<2^(D+1))
 (hd : ∀i j,a i≠b j) (q : Config (2^(D+h)-1))
 (hf : BatchedCleanup.Free b (fun i j=>embed_fin_bound (b i) j.val D h (hb i) j.isLt) q) :
 BatchedCleanup.Free b (fun i j=>embed_fin_bound (b i) j.val D h (hb i) j.isLt) (initState a (2^h-1) q) := by
 intro i j
 let v : Fin (2^(D+h)-1) := ⟨embed (b i) j.val,embed_fin_bound (b i) j.val D h (hb i) j.isLt⟩
 have hv : decode (b i) (2^h-1) v=some j := decode_image (b i) (2^h-1) j v rfl
 have hn : FamilyRound.locate a (2^h-1) v=none := by
   cases he : FamilyRound.locate a (2^h-1) v with
   | none => rfl
   | some xy =>
     rcases xy with ⟨x,y⟩
     have hx := FamilyRound.locate_sound a v (x,y) he
     exact False.elim (ParallelMerge.decode_disjoint (a x) (b i) D (ha x) (hb i) (hd x i) v y j hx hv)
 change (initState a (2^h-1) q).peb v=false
 simpa [initState,FamilyRound.pack,hn] using hf i j

theorem init_batches (D h : Nat) (hh : 0<h) (xs : List (Fin k→Nat))
 (q : Config (2^(D+h)-1)) (hq : consistent q)
 (hx : ∀r∈xs,BatchedCleanup.BatchOK D h q r)
 (hd : xs.Pairwise (fun a b=>∀i j,a i≠b j)) :
 ∃t,PaperRuns HeapPath.pred (xs.length*(h+1)) q t ∧ t.state=initMany (2^h-1) xs q ∧
 t.work=xs.length*(k*(2^h-1)) ∧ t.space≤k*(2^h-1)+xs.length*k+CutSpace.pebs q ∧
 CutSpace.pebs t.state≤xs.length*k+CutSpace.pebs q := by
 induction xs generalizing q with
 | nil => exact ⟨⟨q,0,0⟩,by simpa using (PaperRuns.zero (pred:=HeapPath.pred) q),rfl,by simp,by simp,by simp⟩
 | cons a xs ih =>
   have ha := hx a (by simp)
   have pair := List.pairwise_cons.mp hd
   obtain ⟨t,ht,hs,hw,hsp,hpc⟩ := global_init a D h hh ha.level ha.unique q hq ha.free
   have next : ∀b∈xs,BatchedCleanup.BatchOK D h t.state b := by
     intro b hb
     have hz := hx b (by simp [hb])
     refine ⟨hz.level,hz.unique,?_⟩
     rw [hs]
     exact free_after_other a b D h ha.level hz.level (pair.1 b hb) q hz.free
   obtain ⟨u,hu,hus,huw,husp,hup⟩ := ih t.state (BatchedCleanup.consistent_final ht hq) next pair.2
   refine ⟨⟨u.state,t.work+u.work,max t.space u.space⟩,?_,?_,?_,?_,?_⟩
   · have hh := runs_append ht hu
     simpa [List.length_cons,Nat.add_mul,Nat.add_comm] using hh
   · change u.state=initMany _ (a::xs) q
     rw [hus,hs]; rfl
   · change t.work+u.work=(xs.length+1)*(k*(2^h-1))
     rw [hw,huw,Nat.add_mul]; omega
   · change max t.space u.space≤k*(2^h-1)+(xs.length+1)*k+CutSpace.pebs q
     rw [Nat.add_mul]
     apply Nat.max_le.mpr
     constructor <;> omega
   · change CutSpace.pebs u.state≤(xs.length+1)*k+CutSpace.pebs q
     rw [Nat.add_mul]; omega
def groupRoot (D : Nat) (b : Fin B) (i : Fin K) : Nat := 2^D-1+b.val*K+i.val

theorem group_level (D : Nat) (hcap : B*K≤2^D) (b : Fin B) (i : Fin K) :
 2^D≤groupRoot D b i+1 ∧ groupRoot D b i+1<2^(D+1) := by
 have hb := Nat.mul_le_mul_right K (show b.val+1≤B by omega)
 have hp : 0<2^D := Nat.pow_pos (by decide)
 rw [Nat.add_mul] at hb
 unfold groupRoot
 rw [Nat.pow_succ]
 omega

theorem group_distinct (D : Nat) (b c : Fin B) (hn : b≠c) (i j : Fin K) :
 groupRoot D b i≠groupRoot D c j := by
 intro he
 have hne : b.val≠c.val := by intro hh; exact hn (Fin.ext hh)
 by_cases hbc : b.val<c.val
 · have hb := Nat.mul_le_mul_right K (show b.val+1≤c.val by omega)
   rw [Nat.add_mul] at hb
   unfold groupRoot at he
   omega
 · have hb := Nat.mul_le_mul_right K (show c.val+1≤b.val by omega)
   rw [Nat.add_mul] at hb
   unfold groupRoot at he
   omega

theorem group_unique (D : Nat) (b : Fin B) (i j : Fin K)
 (he : groupRoot D b i=groupRoot D b j) : i=j := by
 apply Fin.ext
 unfold groupRoot at he
 omega

/-- Exact factorization partitions the whole depth-D row into B disjoint K-blocks. -/
theorem group_cover (D : Nat) (hk : 0<K) (hsize : B*K=2^D) (r : Nat)
 (hr : 2^D≤r+1∧r+1<2^(D+1)) :
 ∃b : Fin B,∃i : Fin K,groupRoot D b i=r := by
 let x := r-(2^D-1)
 have hp : 0<2^D := Nat.pow_pos (by decide)
 have hx : x<B*K := by rw [hsize]; dsimp [x]; rw [Nat.pow_succ] at hr; omega
 have hb : x/K<B := (Nat.div_lt_iff_lt_mul hk).mpr hx
 refine ⟨⟨x/K,hb⟩,⟨x%K,Nat.mod_lt x hk⟩,?_⟩
 have eq := Nat.mod_add_div x K
 rw [Nat.mul_comm K] at eq
 unfold groupRoot
 dsimp
 dsimp [x] at *
 omega
#print axioms group_cover
#print axioms init_batches
#print axioms global_init
#print axioms pack_pebs
#print axioms fringe_init_fringe
#print axioms init_fringe
end InitialGhost
