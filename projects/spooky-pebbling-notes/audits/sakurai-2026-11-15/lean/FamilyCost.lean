import FamilyRound
namespace FamilyCost
open SpookyRound FringeEmbed FamilyRound

theorem work (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (hb : ∀i j,embed (roots i) (j : Fin m).val<N)
 (a : Fin k→Action) (hl : ∀i,(a i).first.length=m) :
 roundWork (action (N:=N) (locate roots m) a)=FamilySync.total (fun i=>roundWork (a i)) := by
 rw [WorkBridge.indexed_work (n:=N) _ (by simp [action])]
 have he : (fun v : Fin N=>WorkBridge.cost (firstAt (action (N:=N) (locate roots m) a) v))=
   (fun v=>match locate roots m v with |none=>0 |some (i,j)=>WorkBridge.cost (firstAt (a i) j)) := by
   funext v
   cases hv : locate roots m v with
   | none => simp [hv,WorkBridge.cost]
   | some ij => rcases ij with ⟨i,j⟩; simp [hv]
 rw [he]
 refine Eq.trans ?_ (Eq.trans (family_weight roots D hr hi hb (fun i j=>WorkBridge.cost (firstAt (a i) j))) ?_)
 · congr 1
 ·
   unfold FamilySync.total
   congr 1
   apply List.map_congr_left
   intro i _
   exact (WorkBridge.indexed_work (a i) (hl i)).symm

noncomputable def exterior (roots : Fin k→Nat) (m : Nat) (o : Config N) :=
 ((List.finRange N).map (fun v=>match locate roots m v with |none=>if o.peb v then 1 else 0 |some _=>0)).sum

theorem space (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (hb : ∀i j,embed (roots i) (j : Fin m).val<N)
 (o : Config N) (q : Fin k→Config m) (a : Fin k→Action) :
 roundSpace (pack (locate roots m) o q) (action (N:=N) (locate roots m) a)=
 FamilySync.total (fun i=>roundSpace (q i) (a i))+exterior roots m o := by
 unfold roundSpace
 rw [CutSpace.filter_sum,after_first]
 have he : (fun v : Fin N=>if (pack (locate roots m) o q).peb v ||
   (pack (locate roots m) o (fun i=>afterFirst (q i) (a i))).peb v then 1 else 0)=
   (fun v=>(match locate roots m v with |none=>0 |some (i,j)=>if (q i).peb j || (afterFirst (q i) (a i)).peb j then 1 else 0)+
   (match locate roots m v with |none=>if o.peb v then 1 else 0 |some _=>0)) := by
   funext v
   cases hv : locate roots m v with
   | none => simp [pack,hv]
   | some ij => rcases ij with ⟨i,j⟩; simp [pack,hv]
 rw [he,HeapPath.sum_add]
 apply congrArg (fun x=>x+exterior roots m o)
 refine Eq.trans ?_ (Eq.trans (family_weight roots D hr hi hb (fun i j=>if (q i).peb j || (afterFirst (q i) (a i)).peb j then 1 else 0)) ?_)
 · congr 1
 ·
   unfold FamilySync.total
   congr 1
   apply List.map_congr_left
   intro i _
   exact (CutSpace.filter_sum _ _).symm
noncomputable def product (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (hb : ∀i j,embed (roots i) (j : Fin m).val<N)
 (hc : Closed (N:=N) (locate roots m) p P) (o : Config N) (ho : FillUpper.consistent o) :
 FamilySync.RoundProduct k m N p P where
 pack := pack (locate roots m) o
 exterior := exterior roots m o
 step := by
   intro q e _ he
   classical
   let a := fun i=>Classical.choose (he i)
   have ha := fun i=>Classical.choose_spec (he i)
   have hl : ∀i,Legal p (q i) (a i) := fun i=>(ha i).2.2.1
   have hg := legal (locate roots m) o q a ho hl (locate_injective roots) hc
   refine ⟨edge (pack (locate roots m) o q) (action (N:=N) (locate roots m) a),
     ⟨_,by simp [action],by simp [action],hg,rfl⟩,?_,?_,?_⟩
   · change afterRound _ _=pack _ _ _
     rw [after_round]
     congr 1
     funext i
     exact congrArg (fun x=>x.state) (ha i).2.2.2
   · change roundWork _=FamilySync.total _
     rw [work roots D hr hi hb a (fun i=>(ha i).1)]
     congr 1
     funext i
     exact congrArg (fun x=>x.work) (ha i).2.2.2
   · change roundSpace _ _≤FamilySync.total _+exterior roots m o
     rw [space roots D hr hi hb o q a]
     apply Nat.add_le_add_right
     apply FamilySync.total_mono
     intro i
     have hh := congrArg (fun x=>x.space) (ha i).2.2.2
     exact Nat.le_of_eq hh

noncomputable def fringe_product (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+h)-1)) (ho : FillUpper.consistent o) :
 FamilySync.RoundProduct k (2^h-1) (2^(D+h)-1) HeapPath.pred HeapPath.pred :=
 product roots D hr hi (fun i j=>embed_fin_bound (roots i) j.val D h (hr i) j.isLt)
   (fringe_closed roots D h hr hi) o ho

/-- Concrete arbitrary-K synchronized traces, no abstract RoundProduct premise. -/
theorem fringe_sync (roots : Fin k→Nat) (D h d : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+h)-1)) (ho : FillUpper.consistent o)
 (q : Fin k→Config (2^h-1)) (r : Fin k→SpookyDP.Result (Config (2^h-1)))
 (hq : FamilySync.ConsistentFamily q) (runs : ∀i,PaperRuns HeapPath.pred d (q i) (r i)) :
 ∃t,PaperRuns HeapPath.pred d (pack (locate roots (2^h-1)) o q) t ∧
 t.state=pack (locate roots (2^h-1)) o (fun i=>(r i).state) ∧
 t.work=FamilySync.total (fun i=>(r i).work) ∧
 t.space≤FamilySync.total (fun i=>(r i).space)+exterior roots (2^h-1) o := by
 exact FamilySync.sync (fringe_product roots D h hr hi o ho) q r hq runs

theorem fringe_cleanup (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+h)-1)) (ho : FillUpper.consistent o)
 (q : Fin k→Config (2^h-1)) (hq : FamilySync.ConsistentFamily q) (hp : ∀i v,(q i).peb v=false) :
 ∃t,PaperRuns HeapPath.pred (2*h) (pack (locate roots (2^h-1)) o q) t ∧
 t.state=pack (locate roots (2^h-1)) o (fun _=>FillUpper.empty (2^h-1)) ∧
 t.work=k*(2*(2^h-1)) ∧ t.space≤k*(2^h-1)+exterior roots (2^h-1) o := by
 exact FamilySync.family_cleanup (fringe_product roots D h hr hi o ho) q hq hp
#print axioms fringe_sync
#print axioms fringe_cleanup
#print axioms work
#print axioms space
end FamilyCost
