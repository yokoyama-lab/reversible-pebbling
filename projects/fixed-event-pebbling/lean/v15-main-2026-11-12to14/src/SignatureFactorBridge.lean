import SignatureExact
import ComponentPatterns
import PhysicalCover
namespace SignaturePhysical
open LocalCertificate ErasureCover SlotConcat ChainRecursiveBlockedCover ChainSlotNumbering ChainFinSlotBridge
open ComponentPatterns SwapComponents

def pattern (bs : List Bool) : Fin bs.length → Bool := fun j=>bs.getD j.val false

theorem local_iff (b : Bool) (u : List Nat) : ComponentSlotCover.Local b u ↔ Reach M.Legal (root b) u := by
 cases b
 · exact MComponentCover.large_iff_reach u
 · exact MComponentCover.small_iff_reach u

theorem lift_injective (u v : List Nat) (h : ChainMiddleConverse.liftWord u=ChainMiddleConverse.liftWord v) : u=v := by
 unfold ChainMiddleConverse.liftWord at h
 have h1 := List.append_cancel_left (List.append_cancel_right h)
 have h2 := congrArg (List.map (fun x=>x-3)) h1
 simpa only [List.map_map,Function.comp_def,Nat.add_sub_cancel,List.map_id'] using h2

theorem padded_iff (b : Bool) (u : List Nat) :
 ComponentSlotCover.Padded b (ChainMiddleConverse.liftWord u) ↔ ComponentSlotCover.Local b u := by
 constructor
 · rintro ⟨v,hv,eq⟩
   have e : u=v := lift_injective u v eq
   simpa [e] using hv
 · intro h;exact ⟨u,h,rfl⟩

theorem rest_factors (bs : List Bool) (w : List (Rest bs.length)) (hw : SignatureCover.RestLegal bs w) :
 ∃ (mw : Nat→List (Fin 16)) (tw : List (Fin 8)),
 w=restWord bs.length mw tw ∧ (∀j,j<bs.length→ComponentSlotCover.Slots (bs.getD j false) (mw j)) ∧
 slotLegal 8 ChainTailCover.Legal tw := by
 induction bs with
 | nil => exact ⟨fun _=>[],w,rfl,by intro j hj; simp at hj,hw⟩
 | cons b bs ih =>
   obtain ⟨a,z,rfl,ha,hz⟩ := hw
   obtain ⟨mw,tw,rfl,hm,ht⟩ := ih z hz
   let mw' := fun j=>if j=0 then a else mw (j-1)
   refine ⟨mw',tw,?_,?_,ht⟩
   · simp [restWord,mw']
   · intro j hj
     cases j with
     | zero => simpa [mw'] using ha
     | succ j => simpa [mw'] using hm j (by simpa using hj)

theorem rest_from_factors (bs : List Bool) (mw : Nat→List (Fin 16)) (tw : List (Fin 8))
 (hm : ∀j,j<bs.length→ComponentSlotCover.Slots (bs.getD j false) (mw j))
 (ht : slotLegal 8 ChainTailCover.Legal tw) :
 SignatureCover.RestLegal bs (restWord bs.length mw tw) := by
 induction bs generalizing mw with
 | nil => exact ht
 | cons b bs ih =>
   refine ⟨mw 0,restWord bs.length (fun j=>mw (j+1)) tw,rfl,?_,?_⟩
   · simpa using hm 0 (by simp)
   · exact ih _ (fun j hj=>by simpa using hm (j+1) (by simpa using hj))

theorem rest_subset (bs : List Bool) (w) (hw : SignatureCover.RestLegal bs w) : restLegal bs.length w := by
 induction bs with
 | nil => exact hw
 | cons b bs ih =>
   obtain ⟨a,z,rfl,ha,hz⟩ := hw
   exact ⟨a,z,rfl,⟨ha.1,ComponentSlotCover.padded_subset b _ ha.2⟩,ih _ hz⟩
theorem subset (bs : List Bool) (w) (hw : SignatureCover.Legal bs w) : Legal bs.length w := by
 obtain ⟨a,z,rfl,ha,hz⟩ := hw
 exact ⟨a,z,rfl,ha,rest_subset bs z hz⟩

#print axioms local_iff
#print axioms padded_iff
#print axioms rest_factors
#print axioms rest_from_factors
end SignaturePhysical
