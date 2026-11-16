import SignatureFactorBridge
namespace SignaturePhysical
open LocalCertificate ErasureCover SlotConcat ChainRecursiveBlockedCover ChainSlotNumbering ChainFinSlotBridge
open ComponentPatterns SwapComponents ChainFullSlotAssembly ChainOccurrence

def Component (bs : List Bool) (E : List Nat) :=
 Reach (labelledLegal bs.length E) (ComponentPatterns.representative (pattern bs))
def numbered (bs : List Bool) (w : List (Slots bs.length)) := (w.map (number bs.length)).map Fin.val

theorem assembled_iff (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (iu tw : List Nat) (mu : Nat→List Nat)
 (hi : I.Legal iu) (hm : ∀j,j<bs.length→M.Legal (mu j))
 (ht : tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB) :
 Component bs E (fullSlots bs.length iu mu tw) ↔
 ∀j,j<bs.length→ComponentSlotCover.Local (bs.getD j false) (mu j) := by
 unfold Component ComponentPatterns.representative
 rw [GlobalSwapProduct.physical_reach_iff bs.length E he _ _ _ _ _ _ InitialSwap.legal0 hi
   (fun j _=>mids_legal (pattern bs) j) hm]
 constructor
 · intro h j hj
   apply (local_iff _ _).mpr
   simpa [mids,pattern,hj] using h.2.1 j hj
 · intro h
   refine ⟨(InitialAll.connected iu).mpr hi,?_,?_⟩
   · intro j hj
     simpa [mids,pattern,hj] using (local_iff _ _).mp (h j hj)
   · exact (PaddedSwap.reach_congr (fun v=>ChainTailSegment.legal_iff_two v)).mp
       ((TailSwap.connected tw).mpr ((ChainTailSegment.legal_iff_two tw).mpr ht))

theorem forward (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : List (Slots bs.length)) (hw : SignatureCover.Legal bs w) : Component bs E (numbered bs w) := by
 obtain ⟨iw,rest,rfl,hi,hr⟩ := hw
 obtain ⟨mw,tw,rfl,hm,ht⟩ := rest_factors bs rest hr
 let iu := ChainInitialSegment.middle (iw.map Fin.val)
 let mu := fun j=>ChainMiddleSegment.middle ((mw j).map Fin.val)
 have ig := ChainInitialSegment.all_legal_factor _ hi.2
 have hml (j) (hj : j<bs.length) : slotLegal 16 ML (mw j) :=
   ⟨(hm j hj).1,ComponentSlotCover.padded_subset _ _ (hm j hj).2⟩
 have mg := fun j hj => ChainMiddleSegment.all_legal_factor _ (hml j hj).2
 have ie : iw.map Fin.val=ChainInitialConverse.liftWord iu :=
   ChainFactorRecovery.initial_recovery _ hi.2.1 ig
 have me (j) (hj : j<bs.length) : (mw j).map Fin.val=ChainMiddleConverse.liftWord (mu j) :=
   ChainFactorRecovery.middle_recovery _ (hml j hj).2.1 (mg j hj)
 change Component bs E (numbered bs (word bs.length iw mw tw))
 unfold numbered
 rw [word_eq_fullSlots bs.length iw mw tw iu mu ie me]
 apply (assembled_iff bs E he iu _ mu ig.2.2 (fun j hj=>(mg j hj).2.2)
   ((ChainTailSegment.legal_iff_two _).mp ht.2)).mpr
 intro j hj
 apply (padded_iff _ _).mp
 rw [← me j hj]
 exact (hm j hj).2

theorem reverse (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : List (Slots bs.length)) (hw : Component bs E (numbered bs w)) : SignatureCover.Legal bs w := by
 have legal := SwapGraphBasics.reach_legal hw
 have wl := numbered_legal bs.length E w legal
 obtain ⟨iw,mw,tw,rfl,hi,hm,ht⟩ := legal_factors bs.length w wl
 let iu := ChainInitialSegment.middle (iw.map Fin.val)
 let mu := fun j=>ChainMiddleSegment.middle ((mw j).map Fin.val)
 have ig := ChainInitialSegment.all_legal_factor _ hi.2
 have mg := fun j hj => ChainMiddleSegment.all_legal_factor _ (hm j hj).2
 have ie : iw.map Fin.val=ChainInitialConverse.liftWord iu :=
   ChainFactorRecovery.initial_recovery _ hi.2.1 ig
 have me (j) (hj : j<bs.length) : (mw j).map Fin.val=ChainMiddleConverse.liftWord (mu j) :=
   ChainFactorRecovery.middle_recovery _ (hm j hj).2.1 (mg j hj)
 unfold numbered at hw
 rw [word_eq_fullSlots bs.length iw mw tw iu mu ie me] at hw
 have hc := (assembled_iff bs E he iu _ mu ig.2.2 (fun j hj=>(mg j hj).2.2)
   ((ChainTailSegment.legal_iff_two _).mp ht.2)).mp hw
 refine ⟨iw,restWord bs.length mw tw,rfl,hi,rest_from_factors bs mw tw ?_ ht⟩
 intro j hj
 refine ⟨(hm j hj).1,?_⟩
 rw [me j hj]
 exact (padded_iff _ _).mpr (hc j hj)

theorem component_iff (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : List (Slots bs.length)) : Component bs E (numbered bs w) ↔ SignatureCover.Legal bs w :=
 ⟨reverse bs E he w,forward bs E he w⟩
#print axioms assembled_iff
#print axioms forward
#print axioms reverse
#print axioms component_iff
end SignaturePhysical
