import FamilyCost
namespace BatchedCleanup
open SpookyRound FringeEmbed FamilyRound

def restrict (roots : Fin k→Nat) (hb : ∀i j,embed (roots i) (j : Fin m).val<N) (q : Config N) : Fin k→Config m :=
 fun i=>⟨fun j=>q.peb ⟨embed (roots i) j.val,hb i j⟩,fun j=>q.ghost ⟨embed (roots i) j.val,hb i j⟩⟩

theorem reconstruct (roots : Fin k→Nat) (hb : ∀i j,embed (roots i) (j : Fin m).val<N) (q : Config N) :
 pack (locate roots m) q (restrict roots hb q)=q := by
 apply SpookyReverse.config_ext <;> intro v <;> cases hv : locate roots m v with
 | none => simp [pack,hv]
 | some ij =>
   rcases ij with ⟨i,j⟩
   have hh := decode_sound (roots i) m v j (locate_sound roots v (i,j) hv)
   have eq : (⟨embed (roots i) j.val,hb i j⟩ : Fin N)=v := Fin.ext hh
   simp [pack,restrict,hv,eq]

noncomputable def clear (roots : Fin k→Nat) (m : Nat) (q : Config N) :=
 pack (locate roots m) q (fun _=>FillUpper.empty m)

def Free (roots : Fin k→Nat) (hb : ∀i j,embed (roots i) (j : Fin m).val<N) (q : Config N) :=
 ∀i j,q.peb ⟨embed (roots i) j.val,hb i j⟩=false

theorem clear_peb (roots : Fin k→Nat) (hb : ∀i j,embed (roots i) (j : Fin m).val<N) (q : Config N)
 (hf : Free roots hb q) : (clear roots m q).peb=q.peb := by
 funext v
 cases hv : locate roots m v with
 | none => simp [clear,pack,hv]
 | some ij =>
   rcases ij with ⟨i,j⟩
   have hh := decode_sound (roots i) m v j (locate_sound roots v (i,j) hv)
   have eq : (⟨embed (roots i) j.val,hb i j⟩ : Fin N)=v := Fin.ext hh
   have hp := hf i j
   rw [eq] at hp
   simp [clear,pack,FillUpper.empty,hv,hp]

theorem exterior_le (roots : Fin k→Nat) (m : Nat) (q : Config N) :
 FamilyCost.exterior roots m q≤CutSpace.pebs q := by
 apply Exceptions.sum_le
 intro v _
 cases hv : locate roots m v with
 | none => simp [hv]
 | some ij => simp [hv]

theorem consistent_final (hr : PaperRuns p d q r) (hq : FillUpper.consistent q) :
 FillUpper.consistent r.state := by
 induction hr with
 | zero q => exact hq
 | step he ht ih => exact ih (FamilySync.step_consistent he)

theorem global_cleanup (roots : Fin k→Nat) (D h : Nat)
 (hr : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1))
 (hi : ∀i j,roots i=roots j→i=j)
 (q : Config (2^(D+h)-1)) (hq : FillUpper.consistent q)
 (hf : Free roots (fun i j=>embed_fin_bound (roots i) j.val D h (hr i) j.isLt) q) :
 ∃t,PaperRuns HeapPath.pred (2*h) q t ∧ t.state=clear roots (2^h-1) q ∧
 t.state.peb=q.peb ∧ t.work=k*(2*(2^h-1)) ∧ t.space≤k*(2^h-1)+CutSpace.pebs q := by
 let hb := fun i (j : Fin (2^h-1))=>embed_fin_bound (roots i) j.val D h (hr i) j.isLt
 let qs := restrict roots hb q
 have hqs : FamilySync.ConsistentFamily qs := fun i j=>hq _
 obtain ⟨t,ht,hs,hw,hsp⟩ := FamilyCost.fringe_cleanup roots D h hr hi q hq qs hqs hf
 refine ⟨t,?_,hs,?_,hw,?_⟩
 · rw [reconstruct] at ht; exact ht
 · rw [hs]; exact clear_peb roots hb q hf
 · have hh := exterior_le roots (2^h-1) q; omega
structure BatchOK (D h : Nat) (q : Config (2^(D+h)-1)) (roots : Fin k→Nat) : Prop where
 level : ∀i,2^D≤roots i+1∧roots i+1<2^(D+1)
 unique : ∀i j,roots i=roots j→i=j
 free : Free roots (fun i j=>embed_fin_bound (roots i) j.val D h (level i) j.isLt) q

noncomputable def cleaned (m : Nat) (xs : List (Fin k→Nat)) (q : Config N) : Config N :=
 match xs with |[]=>q |r::rs=>cleaned m rs (clear r m q)

theorem batches (D h : Nat) (xs : List (Fin k→Nat)) (q : Config (2^(D+h)-1))
 (hq : FillUpper.consistent q) (hx : ∀roots∈xs,BatchOK D h q roots) :
 ∃t,PaperRuns HeapPath.pred (xs.length*(2*h)) q t ∧ t.state=cleaned (2^h-1) xs q ∧
 t.state.peb=q.peb ∧ t.work=xs.length*(k*(2*(2^h-1))) ∧
 t.space≤k*(2^h-1)+CutSpace.pebs q := by
 induction xs generalizing q with
 | nil => exact ⟨⟨q,0,0⟩,by simpa using (PaperRuns.zero (pred:=HeapPath.pred) q),rfl,rfl,by simp,by simp⟩
 | cons roots xs ih =>
   have hh := hx roots (by simp)
   obtain ⟨t,ht,hs,hp,hw,hsp⟩ := global_cleanup roots D h hh.level hh.unique q hq hh.free
   have hnext : ∀r∈xs,BatchOK D h t.state r := by
     intro r hr
     have hb := hx r (by simp [hr])
     refine ⟨hb.level,hb.unique,?_⟩
     intro i j
     rw [hp]
     exact hb.free i j
   obtain ⟨u,hu,hus,hup,huw,husp⟩ := ih t.state (consistent_final ht hq) hnext
   have hz : CutSpace.pebs t.state=CutSpace.pebs q := by unfold CutSpace.pebs; rw [hp]
   refine ⟨⟨u.state,t.work+u.work,max t.space u.space⟩,?_,?_,?_,?_,?_⟩
   · have run := BatchUpper.runs_append ht hu
     simpa [List.length_cons,Nat.add_mul,Nat.succ_mul,Nat.add_comm] using run
   · change u.state=cleaned _ (roots::xs) q
     rw [hus,hs]; rfl
   · exact hup.trans hp
   · change t.work+u.work=(xs.length+1)*(k*(2*(2^h-1)))
     rw [hw,huw,Nat.add_mul]; omega
   · change max t.space u.space≤_
     rw [hz] at husp
     exact Nat.max_le.mpr ⟨hsp,husp⟩

theorem clear_no_new_ghost (roots : Fin k→Nat) (m : Nat) (q : Config N) (v : Fin N)
 (hv : q.ghost v=false) : (clear roots m q).ghost v=false := by
 cases hl : locate roots m v with
 | none => simpa [clear,pack,hl] using hv
 | some ij => rcases ij with ⟨i,j⟩; simp [clear,pack,hl,FillUpper.empty]

theorem cleaned_no_new_ghost (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (hv : q.ghost v=false) : (cleaned m xs q).ghost v=false := by
 induction xs generalizing q with
 | nil => exact hv
 | cons r rs ih => exact ih (clear r m q) (clear_no_new_ghost r m q v hv)

theorem cleaned_selected (xs : List (Fin k→Nat)) (q : Config N) (v : Fin N)
 (r : Fin k→Nat) (hr : r∈xs) (i : Fin k) (j : Fin m)
 (hv : locate r m v=some (i,j)) : (cleaned m xs q).ghost v=false := by
 induction xs generalizing q with
 | nil => simp at hr
 | cons a xs ih =>
   have hh : r=a∨r∈xs := by simpa using hr
   rcases hh with rfl|hr
   · exact cleaned_no_new_ghost xs (clear r m q) v (by simp [clear,pack,hv,FillUpper.empty])
   · exact ih (clear a m q) hr
#print axioms batches
#print axioms cleaned_selected
#print axioms global_cleanup
end BatchedCleanup
