import StateFamilyJoin
import PaddedStateSoundness
import PaddedRelation
namespace ChainConcreteStateFamilies
open ChainStateFamilyJoin ChainPaddedStateSemantics ChainGlobalStateCandidates ChainPrefixStates
open ChainPrefixSetConcat LocalCertificate

def blockL (d n : Nat) (L : Language) : Language := fun w => ∃u,L u ∧ w=pad d n u

theorem pad_permutation (d n : Nat) (u : List Nat) (hu : u.Perm (List.range n)) :
    (pad d n u).Perm (List.range (d+n+1)) := by
  have hp := ChainPaddedRelation.lift_permutation d n u
    ((EnumerationCorrectness.isPermutation_iff_perm_range n u).mpr hu)
  have hp' := (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hp
  simpa [pad,ChainPaddedRelation.liftWord,List.map_append,List.append_assoc,Nat.add_comm] using hp'

theorem padded_half (d n : Nat) (L : Language) (words : List (List Nat))
    (equiv : ∀u,u∈words ↔ L u) (perms : ∀u,L u → u.Perm (List.range n))
    (nonempty : ∃u,L u) : Half (d+n+1) (blockL d n L) (paddedHalf d (states n words)) := by
  constructor
  · rintro w ⟨u,hu,rfl⟩; exact pad_permutation d n u (perms u hu)
  · obtain ⟨u,hu⟩ := nonempty; exact ⟨_,u,hu,rfl⟩
  · intro s hs
    have hn : ∃u,u∈words := by obtain ⟨u,hu⟩ := nonempty; exact ⟨u,(equiv u).mpr hu⟩
    obtain ⟨u,hu,t,ht,he⟩ := candidate_has_padded_prefix d n words hn
      (fun u hu => perms u ((equiv u).mp hu)) s hs
    exact ⟨_,⟨u,(equiv u).mp hu,rfl⟩,t,by omega,he⟩
  · rintro w ⟨u,hu,rfl⟩ t ht
    exact padded_prefix_in_candidates d n words u ((equiv u).mpr hu) (perms u hu) t (by omega)

def IL := blockL 6 10 I.Legal
def ML := blockL 3 12 M.Legal
def TL : Language := fun w => w=ChainTailSegment.wordA ∨ w=ChainTailSegment.wordB

theorem i_half : Half 17 IL iHalf :=
  padded_half 6 10 I.Legal UpperCertificate.I.physicalWords
    (fun w=>EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures w)
    (fun w hw=>(EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1)
    ⟨I.witness 0,I.witnesses_legal 0⟩
theorem m_half : Half 16 ML mHalf :=
  padded_half 3 12 M.Legal UpperCertificate.M.physicalWords
    (fun w=>EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures w)
    (fun w hw=>(EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1)
    ⟨M.witness 0,M.witnesses_legal 0⟩

theorem t_full : Full 8 TL tFull := by
  have perms (w : List Nat) (hw : TL w) : w.Perm (List.range 8) :=
    (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp
      ((ChainTailSegment.legal_iff_two w).mpr hw).1
  constructor
  · exact perms
  · exact ⟨ChainTailSegment.wordA,Or.inl rfl⟩
  · intro s hs
    obtain ⟨w,hw,t,ht,he⟩ := (mem_states_iff 8 _ s).mp hs
    have hl : TL w := by simpa [TL] using hw
    have len : w.length=8 := by simpa using (perms w hl).length_eq
    exact ⟨w,hl,t,by omega,he⟩
  · intro w hw t ht
    apply (mem_states_iff 8 _ _).mpr
    have len : w.length=8 := by simpa using (perms w hw).length_eq
    exact ⟨w,by simpa [TL] using hw,t,by omega,rfl⟩

def restL : Nat → Language
  | 0 => TL
  | r+1 => joined 16 ML (restL r)
def globalL (r : Nat) := joined 17 IL (restL r)

theorem rest_full (r : Nat) : Full (16*r+8) (restL r) (rest r) := by
  induction r with
  | zero => exact t_full
  | succ r ih =>
    have hh := joined_full 16 (16*r+8) ML (restL r) mHalf (rest r) m_half ih
    simpa only [restL,rest,show 16+(16*r+8)=16*(r+1)+8 by omega] using hh

theorem global_full (r : Nat) : Full (25+16*r) (globalL r) (global r) := by
  have hh := joined_full 17 (16*r+8) IL (restL r) iHalf (rest r) i_half (rest_full r)
  simpa only [globalL,global,show 17+(16*r+8)=25+16*r by omega] using hh

#print axioms i_half
#print axioms m_half
#print axioms t_full
#print axioms global_full
end ChainConcreteStateFamilies
