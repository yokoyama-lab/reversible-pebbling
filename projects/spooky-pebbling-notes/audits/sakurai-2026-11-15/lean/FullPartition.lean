import InitialGhost
namespace FullPartition
open SpookyRound FringeEmbed

/-- Every vertex below the top D levels has a terminal-fringe address. -/
theorem cover (D h v : Nat) (hv : 2^D-1≤v) (hn : v<2^(D+h)-1) :
 ∃r i,(2^D≤r+1∧r+1<2^(D+1)) ∧ i<2^h-1 ∧ embed r i=v := by
 have posv : 0<v+1 := by omega
 have pd : 0<2^D := Nat.pow_pos (by decide)
 have dl : D≤depth v := (Nat.le_log2 (n:=v+1) (by omega)).mpr (by omega)
 have du : depth v<D+h := (Nat.log2_lt (n:=v+1) (by omega)).mpr (by omega)
 let t := depth v-D
 have dt : depth v=D+t := by dsimp [t]; omega
 have th : t<h := by omega
 let p := 2^t
 let z := (v+1)/p
 let a := (v+1)%p
 have pp : 0<p := Nat.pow_pos (by decide)
 have am : a<p := Nat.mod_lt _ pp
 have eq : a+z*p=v+1 := by
   have he := Nat.mod_add_div (v+1) p
   rw [Nat.mul_comm p] at he
   exact he
 have bd := depth_range v
 have low : 2^D*p≤v+1 := by
   rw [dt,Nat.pow_add] at bd
   exact bd.1
 have high : v+1<2^(D+1)*p := by
   have he : depth v+1=(D+1)+t := by omega
   rw [he,Nat.pow_add] at bd
   exact bd.2
 have zl : 2^D≤z := by
   by_cases hz : 2^D≤z
   · exact hz
   · have hm := Nat.mul_le_mul_right p (show z+1≤2^D by omega)
     rw [Nat.add_mul] at hm
     omega
 have zu : z<2^(D+1) := by
   by_cases hz : z<2^(D+1)
   · exact hz
   · have hm := Nat.mul_le_mul_right p (show 2^(D+1)≤z by omega)
     omega
 let r := z-1
 let i := p+a-1
 have ir : p≤i+1∧i+1<2^(t+1) := by
   rw [Nat.pow_succ]
   dsimp [i,p] at *
   omega
 have di := RetainRoot.depth_eq i t ir.1 ir.2
 have ih : i<2^h-1 := by
   have ph := Nat.pow_le_pow_right (n:=2) (by decide) (show t+1≤h by omega)
   omega
 refine ⟨r,i,by dsimp [r]; omega,ih,?_⟩
 have rz : r+1=z := by dsimp [r]; omega
 have mul : p*r+p=p*z := by rw [←rz,Nat.mul_add,Nat.mul_one]
 unfold embed
 rw [di]
 change p*r+i=v
 dsimp [i]
 rw [Nat.mul_comm z] at eq
 omega
theorem grouped_cover (D h : Nat) (hk : 0<K) (hsize : B*K=2^D)
 (v : Fin (2^(D+h)-1)) (hv : 2^D-1≤v.val) :
 ∃b : Fin B,∃i : Fin K,∃j : Fin (2^h-1),
 FamilyRound.locate (InitialGhost.groupRoot D b) (2^h-1) v=some (i,j) := by
 obtain ⟨r,j,hr,hj,he⟩ := cover D h v.val hv v.isLt
 obtain ⟨b,i,hroot⟩ := InitialGhost.group_cover D hk hsize r hr
 refine ⟨b,i,⟨j,hj⟩,?_⟩
 apply FamilyRound.locate_complete (InitialGhost.groupRoot D b) D
   (InitialGhost.group_level D (Nat.le_of_eq hsize) b) (InitialGhost.group_unique D b)
 apply decode_image
 simpa [hroot] using he

theorem top_none (roots : Fin k→Nat) (D m : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (v : Fin N) (hv : v.val<2^D-1) : FamilyRound.locate roots m v=none := by
 cases hl : FamilyRound.locate roots m v with
 | none => rfl
 | some ij =>
   rcases ij with ⟨i,j⟩
   have he := decode_sound (roots i) m v j (FamilyRound.locate_sound roots v (i,j) hl)
   have hb := root_le_embed (roots i) j.val
   have hh := hr i
   omega

theorem other_none (a b : Fin k→Nat) (D : Nat)
 (ha : ∀i,2^D≤a i+1∧a i+1<2^(D+1)) (hb : ∀i,2^D≤b i+1∧b i+1<2^(D+1))
 (hd : ∀i j,a i≠b j) (v : Fin N) (i : Fin k) (j : Fin m)
 (hv : FamilyRound.locate a m v=some (i,j)) : FamilyRound.locate b m v=none := by
 have h1 := FamilyRound.locate_sound a v (i,j) hv
 cases hl : FamilyRound.locate b m v with
 | none => rfl
 | some xy =>
   rcases xy with ⟨x,y⟩
   have h2 := FamilyRound.locate_sound b v (x,y) hl
   exact False.elim (ParallelMerge.decode_disjoint (a i) (b x) D (ha i) (hb x) (hd i x) v j y h1 h2)

theorem outside (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hv : ∀r∈xs,FamilyRound.locate r m v=none) :
 (InitialGhost.initMany m xs q).peb v=q.peb v ∧ (InitialGhost.initMany m xs q).ghost v=q.ghost v := by
 induction xs generalizing q with
 | nil => exact ⟨rfl,rfl⟩
 | cons a xs ih =>
   have hh := ih (InitialGhost.initState a m q) (fun r hr=>hv r (by simp [hr]))
   simpa [InitialGhost.initMany,InitialGhost.initState,FamilyRound.pack,hv a (by simp)] using hh

theorem selected (D : Nat) (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hl : ∀r∈xs,∀i,2^D≤r i+1∧r i+1<2^(D+1))
 (hd : xs.Pairwise (fun a b=>∀i j,a i≠b j))
 (r : Fin k→Nat) (hr : r∈xs) (i : Fin k) (j : Fin m)
 (hv : FamilyRound.locate r m v=some (i,j)) :
 (InitialGhost.initMany m xs q).peb v=decide (j.val=0) ∧
 (InitialGhost.initMany m xs q).ghost v=decide (j.val≠0) := by
 induction xs generalizing q with
 | nil => simp at hr
 | cons a xs ih =>
   have pair := List.pairwise_cons.mp hd
   have hh : r=a∨r∈xs := by simpa using hr
   rcases hh with rfl|hr
   · have hn : ∀b∈xs,FamilyRound.locate b m v=none := by
       intro b hb
       exact other_none r b D (hl r (by simp)) (hl b (by simp [hb])) (pair.1 b hb) v i j hv
     have ho := outside xs (InitialGhost.initState r m q) v hn
     simpa [InitialGhost.initMany,InitialGhost.initState,FamilyRound.pack,hv,InitialGhost.rootGhost] using ho
   · exact ih (InitialGhost.initState a m q) (fun b hb=>hl b (by simp [hb])) pair.2 hr
def groups (D B K : Nat) : List (Fin K→Nat) := (List.finRange B).map (InitialGhost.groupRoot D)

theorem groups_pairwise : (groups D B K).Pairwise (fun a b=>∀i j,a i≠b j) := by
 apply List.pairwise_map.mpr
 have hn : (List.finRange B).Pairwise (fun a b=>a≠b) := List.nodup_finRange B
 exact hn.imp (fun {a b} hh=>InitialGhost.group_distinct D a b hh)

theorem groups_level (hsize : B*K=2^D) (r : Fin K→Nat) (hr : r∈groups D B K) :
 ∀i,2^D≤r i+1∧r i+1<2^(D+1) := by
 obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
 exact InitialGhost.group_level D (Nat.le_of_eq hsize) b

theorem group_initial (D h B K : Nat) (hh : 0<h) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(h+1)) (FillUpper.empty (2^(D+h)-1)) t ∧
 t.state=InitialGhost.initMany (2^h-1) (groups D B K) (FillUpper.empty (2^(D+h)-1)) ∧
 t.work=B*(K*(2^h-1)) ∧ t.space≤K*(2^h-1)+2^D ∧ CutSpace.pebs t.state≤2^D := by
 have hx : ∀r∈groups D B K,BatchedCleanup.BatchOK D h (FillUpper.empty (2^(D+h)-1)) r := by
   intro r hr
   obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
   refine ⟨InitialGhost.group_level D (Nat.le_of_eq hsize) b,InitialGhost.group_unique D b,?_⟩
   intro i j; rfl
 obtain ⟨t,ht,hs,hw,hsp,hp⟩ := InitialGhost.init_batches D h hh (groups D B K)
   (FillUpper.empty (2^(D+h)-1)) (by simp [FillUpper.consistent,FillUpper.empty]) hx groups_pairwise
 have ln : (groups D B K).length=B := by simp [groups]
 have pc : CutSpace.pebs (FillUpper.empty (2^(D+h)-1))=0 := by
   simp [CutSpace.pebs,FillUpper.empty,List.map_const',List.sum_replicate_nat]
 refine ⟨t,by simpa [ln] using ht,hs,by simpa [ln] using hw,?_,?_⟩
 · simpa [ln,pc,hsize] using hsp
 · simpa [ln,pc,hsize] using hp

theorem local_root_iff (r D m : Nat) (hr : 2^D≤r+1∧r+1<2^(D+1))
 (v : Fin N) (j : Fin m) (hj : decode r m v=some j) :
 j.val=0 ↔ (2^D≤v.val+1∧v.val+1<2^(D+1)) := by
 have he := decode_sound r m v j hj
 have hd := embed_depth r j.val D hr
 rw [he] at hd
 constructor
 · intro hz
   have hz' : depth j.val=0 := by simp [depth,hz]
   rw [hz',Nat.add_zero] at hd
   have bd := depth_range v.val
   simpa [hd] using bd
 · intro hv
   have dd := RetainRoot.depth_eq v.val D hv.1 hv.2
   have dj : depth j.val=0 := by omega
   have bd := depth_range j.val
   rw [dj] at bd
   simp at bd
   omega
def boundary (D n : Nat) : Config n :=
 ⟨fun v=>decide (2^D-1≤v.val ∧ v.val<2^(D+1)-1),fun v=>decide (2^(D+1)-1≤v.val)⟩

theorem initial_boundary (D h B K : Nat) (hk : 0<K) (hsize : B*K=2^D) :
 InitialGhost.initMany (2^h-1) (groups D B K) (FillUpper.empty (2^(D+h)-1))=
 boundary D (2^(D+h)-1) := by
 have pp : 0<2^D := Nat.pow_pos (by decide)
 have pq : 2^D≤2^(D+1) := Nat.pow_le_pow_right (n:=2) (by decide) (by omega)
 have all : ∀v : Fin (2^(D+h)-1),
   (InitialGhost.initMany (2^h-1) (groups D B K) (FillUpper.empty (2^(D+h)-1))).peb v=(boundary D _).peb v ∧
   (InitialGhost.initMany (2^h-1) (groups D B K) (FillUpper.empty (2^(D+h)-1))).ghost v=(boundary D _).ghost v := by
   intro v
   by_cases hv : v.val<2^D-1
   · have hn : ∀r∈groups D B K,FamilyRound.locate r (2^h-1) v=none := by
       intro r hr; exact top_none r D _ (groups_level hsize r hr) v hv
     have hs := outside (groups D B K) (FillUpper.empty (2^(D+h)-1)) v hn
     have h1 : ¬(2^D-1≤v.val∧v.val<2^(D+1)-1) := by omega
     have h2 : ¬2^(D+1)-1≤v.val := by omega
     simpa only [boundary,FillUpper.empty,h1,h2,decide_false] using hs
   · obtain ⟨b,i,j,ha⟩ := grouped_cover D h hk hsize v (by omega)
     have mem : InitialGhost.groupRoot D b∈groups D B K := by simp [groups]
     have hs := selected D (groups D B K) (FillUpper.empty (2^(D+h)-1)) v
       (fun r hr=>groups_level hsize r hr) groups_pairwise _ mem i j ha
     have he := local_root_iff (InitialGhost.groupRoot D b i) D (2^h-1)
       (InitialGhost.group_level D (Nat.le_of_eq hsize) b i) v j
       (FamilyRound.locate_sound _ v (i,j) ha)
     have ep : (j.val=0)↔(2^D-1≤v.val∧v.val<2^(D+1)-1) := by omega
     have eg : (j.val≠0)↔(2^(D+1)-1≤v.val) := by omega
     constructor
     · exact hs.1.trans (by simp only [boundary,ep])
     · exact hs.2.trans (by simp only [boundary,eg])
 apply SpookyReverse.config_ext
 · intro v; exact (all v).1
 · intro v; exact (all v).2

theorem initial_with_boundary (D h B K : Nat) (hh : 0<h) (hk : 0<K) (hsize : B*K=2^D) :
 ∃t,PaperRuns HeapPath.pred (B*(h+1)) (FillUpper.empty (2^(D+h)-1)) t ∧
 t.state=boundary D (2^(D+h)-1) ∧ t.work=B*(K*(2^h-1)) ∧
 t.space≤K*(2^h-1)+2^D ∧ CutSpace.pebs t.state≤2^D := by
 obtain ⟨t,ht,hs,hw,hsp,hp⟩ := group_initial D h B K hh hsize
 exact ⟨t,ht,hs.trans (initial_boundary D h B K hk hsize),hw,hsp,hp⟩
#print axioms initial_with_boundary
#print axioms group_initial
#print axioms selected
#print axioms grouped_cover
#print axioms cover
end FullPartition
