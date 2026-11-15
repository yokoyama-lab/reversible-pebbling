import FamilySync
namespace FamilyRound
open SpookyRound FringeEmbed

def pack (loc : Fin N→Option (Fin k×Fin m)) (outside : Config N) (q : Fin k→Config m) : Config N :=
 ⟨fun v=>match loc v with |none=>outside.peb v |some (i,j)=>(q i).peb j,
  fun v=>match loc v with |none=>outside.ghost v |some (i,j)=>(q i).ghost j⟩
def action (loc : Fin N→Option (Fin k×Fin m)) (a : Fin k→Action) : Action :=
 ⟨(List.finRange N).map (fun v=>match loc v with |none=>.idle |some (i,j)=>firstAt (a i) j),
 (List.finRange N).map (fun v=>match loc v with |none=>false |some (i,j)=>ghostAt (a i) j)⟩
@[simp] theorem first_action (loc : Fin N→Option (Fin k×Fin m)) (a : Fin k→Action) (v : Fin N) : firstAt (action loc a) v=
 (match loc v with |none=>.idle |some (i,j)=>firstAt (a i) j) := by simp [firstAt,action]
@[simp] theorem ghost_action (loc : Fin N→Option (Fin k×Fin m)) (a : Fin k→Action) (v : Fin N) : ghostAt (action loc a) v=
 (match loc v with |none=>false |some (i,j)=>ghostAt (a i) j) := by simp [ghostAt,action]

theorem after_first (loc : Fin N→Option (Fin k×Fin m)) (o : Config N) (q : Fin k→Config m) (a : Fin k→Action) :
 afterFirst (pack loc o q) (action loc a)=pack loc o (fun i=>afterFirst (q i) (a i)) := by
 apply SpookyReverse.config_ext <;> intro v <;> cases h : loc v with
 | none => simp [afterFirst,pack,h]
 | some ij => rcases ij with ⟨i,j⟩; simp [afterFirst,pack,h]
theorem after_round (loc : Fin N→Option (Fin k×Fin m)) (o : Config N) (q : Fin k→Config m) (a : Fin k→Action) :
 afterRound (pack loc o q) (action loc a)=pack loc o (fun i=>afterRound (q i) (a i)) := by
 apply SpookyReverse.config_ext <;> intro v <;> cases h : loc v with
 | none => simp [afterRound,afterFirst,pack,h]
 | some ij => rcases ij with ⟨i,j⟩; simp [afterRound,afterFirst,pack,h]

def Closed (loc : Fin N→Option (Fin k×Fin m)) (p : Fin m→Fin m→Bool) (P : Fin N→Fin N→Bool) :=
 ∀v i j,loc v=some (i,j)→∀u,P v u=true→∃l,loc u=some (i,l)∧p j l=true

theorem legal (loc : Fin N→Option (Fin k×Fin m)) (o : Config N) (q : Fin k→Config m) (a : Fin k→Action)
 (ho : FillUpper.consistent o) (ha : ∀i,Legal p (q i) (a i))
 (hinj : ∀v w i j,loc v=some (i,j)→loc w=some (i,j)→v=w)
 (hc : Closed loc p P) : Legal P (pack loc o q) (action loc a) := by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro v; cases h : loc v with
   | none => simpa [pack,h] using ho v
   | some ij => rcases ij with ⟨i,j⟩; simpa [pack,h] using (ha i).1 j
 · intro v hv; cases h : loc v with
   | none => simp [h] at hv
   | some ij => rcases ij with ⟨i,j⟩; simpa [pack,h] using (ha i).2.1 j (by simpa [h] using hv)
 · intro v hv; cases h : loc v with
   | none => simp [h] at hv
   | some ij => rcases ij with ⟨i,j⟩; simpa [pack,h] using (ha i).2.2.1 j (by simpa [h] using hv)
 · intro v hv u hu; cases h : loc v with
   | none => simp [h] at hv
   | some ij =>
     rcases ij with ⟨i,j⟩
     obtain ⟨l,hl,hp⟩ := hc v i j h u hu
     simpa [pack,hl] using (ha i).2.2.2.1 j (by simpa [h] using hv) l hp
 · intro v w hvw hv hw u hu hu'
   cases h : loc v with
   | none => simp [h] at hv
   | some ij =>
     rcases ij with ⟨i,j⟩
     cases g : loc w with
     | none => simp [g] at hw
     | some kl =>
       rcases kl with ⟨l,b⟩
       have x : ∃c,loc u=some (i,c)∧(c=j∨p j c=true) := by
         rcases hu with rfl|hu
         · exact ⟨j,h,Or.inl rfl⟩
         · obtain ⟨c,hh,hp⟩ := hc v i j h u hu; exact ⟨c,hh,Or.inr hp⟩
       have y : ∃c,loc u=some (l,c)∧(c=b∨p b c=true) := by
         rcases hu' with rfl|hu'
         · exact ⟨b,g,Or.inl rfl⟩
         · obtain ⟨c,hh,hp⟩ := hc w l b g u hu'; exact ⟨c,hh,Or.inr hp⟩
       obtain ⟨c,hc1,hc2⟩ := x
       obtain ⟨e,he1,he2⟩ := y
       have eq : i=l∧c=e := by simpa using hc1.symm.trans he1
       rcases eq with ⟨rfl,rfl⟩
       have hjb : j≠b := by intro hh; subst b; exact hvw (hinj v w i j h g)
       exact (ha i).2.2.2.2.1 j b hjb (by simpa [h] using hv) (by simpa [g] using hw) c hc2 he2
 · intro v hv; cases h : loc v with
   | none => simp [h] at hv
   | some ij =>
     rcases ij with ⟨i,j⟩
     rw [after_first]
     simpa [pack,h] using (ha i).2.2.2.2.2 j (by simpa [h] using hv)
noncomputable def locate (roots : Fin k→Nat) (m : Nat) (v : Fin N) : Option (Fin k×Fin m) := by
 classical
 exact if hx : ∃ij : Fin k×Fin m,decode (roots ij.1) m v=some ij.2 then some (Classical.choose hx) else none

theorem locate_sound (roots : Fin k→Nat) (v : Fin N) (ij : Fin k×Fin m)
 (h : locate roots m v=some ij) : decode (roots ij.1) m v=some ij.2 := by
 unfold locate at h
 split at h
 · have hh := Classical.choose_spec ‹∃ij : Fin k×Fin m,_›
   cases Option.some.inj h
   exact hh
 · simp at h

theorem pair_unique (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (v : Fin N) (x y : Fin k×Fin m)
 (hx : decode (roots x.1) m v=some x.2) (hy : decode (roots y.1) m v=some y.2) : x=y := by
 have he : roots x.1=roots y.1 := by
   by_cases hh : roots x.1=roots y.1
   · exact hh
   · exact False.elim (ParallelMerge.decode_disjoint _ _ D (hr _) (hr _) hh v x.2 y.2 hx hy)
 have e1 := hi _ _ he
 have e2 : x.2=y.2 := by rw [e1] at hx; exact Option.some.inj (hx.symm.trans hy)
 exact Prod.ext e1 e2

theorem locate_complete (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (v : Fin N) (ij : Fin k×Fin m)
 (h : decode (roots ij.1) m v=some ij.2) : locate roots m v=some ij := by
 unfold locate
 split
 · rename_i hx
   congr 1
   exact pair_unique roots D hr hi v _ ij (Classical.choose_spec hx) h
 · rename_i hx
   exact False.elim (hx ⟨ij,h⟩)

theorem locate_injective (roots : Fin k→Nat) (v w : Fin N) (i : Fin k) (j : Fin m)
 (hv : locate roots m v=some (i,j)) (hw : locate roots m w=some (i,j)) : v=w := by
 exact decode_same (roots i) v w j (locate_sound roots v (i,j) hv) (locate_sound roots w (i,j) hw)

theorem fringe_closed (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) :
 Closed (N:=2^(D+h)-1) (locate roots (2^h-1)) HeapPath.pred HeapPath.pred := by
 intro v i j hv u hu
 have hh := locate_sound roots v (i,j) hv
 obtain ⟨l,hl,hp⟩ := fringe_dep_closed (roots i) D h (hr i) v j hh u hu
 exact ⟨l,locate_complete roots D hr hi u (i,l) hl,hp⟩

/-- No abstract simultaneous-legality assumption remains. Any distinct roots
    at one heap depth, arbitrary K, and arbitrary legal local rounds. -/
theorem fringe_legal (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (o : Config (2^(D+h)-1)) (q : Fin k→Config (2^h-1)) (a : Fin k→Action)
 (ho : FillUpper.consistent o) (ha : ∀i,Legal HeapPath.pred (q i) (a i)) :
 Legal HeapPath.pred (pack (locate roots (2^h-1)) o q) (action (N:=2^(D+h)-1) (locate roots (2^h-1)) a) := by
 exact legal _ o q a ho ha (locate_injective roots) (fringe_closed roots D h hr hi)
theorem locate_weight (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (v : Fin N) (f : Fin k→Fin m→Nat) :
 (match locate roots m v with |none=>0 |some (i,j)=>f i j)=
 ((List.finRange k).map (fun i=>match decode (roots i) m v with |none=>0 |some j=>f i j)).sum := by
 classical
 cases hv : locate roots m v with
 | none =>
   have hz : ∀i,(match decode (roots i) m v with |none=>0 |some j=>f i j)=0 := by
     intro i; cases hd : decode (roots i) m v with
     | none => rfl
     | some j => have hh := locate_complete roots D hr hi v (i,j) hd; simp [hv] at hh
   simp only [hz]
   exact (FamilySync.total_zero (k:=k)).symm
 | some ij =>
   rcases ij with ⟨i,j⟩
   have hz : ∀b,(match decode (roots b) m v with |none=>0 |some c=>f b c)=if b=i then f b j else 0 := by
     intro b
     cases hd : decode (roots b) m v with
     | none =>
       have hn : b≠i := by
         intro he; subst b
         have hh := locate_sound roots v (i,j) hv
         simp [hd] at hh
       simp [hn]
     | some c =>
       have hh := locate_complete roots D hr hi v (b,c) hd
       have he : b=i∧c=j := by simpa using hh.symm.trans hv
       rcases he with ⟨rfl,rfl⟩
       simp
   simp only [hz]
   exact (LiftCost.fin_hit (fun b=>f b j) i).symm

theorem family_weight (roots : Fin k→Nat) (D : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j) (hb : ∀i j,embed (roots i) (j : Fin m).val<N)
 (f : Fin k→Fin m→Nat) :
 ((List.finRange N).map (fun v=>match locate roots m v with
 |none=>0 |some (i,j)=>f i j)).sum=
 FamilySync.total (fun i=>((List.finRange m).map (f i)).sum) := by
 have he : (fun v : Fin N=>match locate roots m v with |none=>0 |some (i,j)=>f i j)=
   (fun v=>((List.finRange k).map (fun i=>match decode (roots i) m v with |none=>0 |some j=>f i j)).sum) := by
   funext v
   exact locate_weight roots D hr hi v f
 rw [he,HeapPath.exchange]
 unfold FamilySync.total
 congr 1
 apply List.map_congr_left
 intro i _
 exact LiftCost.decode_sum (roots i) (hb i) (f i)
#print axioms family_weight
#print axioms fringe_legal
#print axioms legal
end FamilyRound
