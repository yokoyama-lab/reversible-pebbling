import EdgeFamily
import GlobalStateLanguage
namespace ChainPhysicalEdgeFamily
open ChainLocalEdges ChainGlobalEdgeCandidates ChainEdgeFamily
open ChainConcreteStateFamilies ChainStateFamilyJoin ChainGlobalStateLanguage
open LocalCertificate ChainOccurrence ChainFamilyArithmetic

theorem i_family : Family 17 IL iFull :=
  padded_family 6 10 I.Legal UpperCertificate.I.physicalWords
    (fun w=>EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures w)
    (fun _ hw=>(EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1)
    ⟨I.witness 0,I.witnesses_legal 0⟩
theorem m_family : Family 16 ML mFull :=
  padded_family 3 12 M.Legal UpperCertificate.M.physicalWords
    (fun w=>EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures w)
    (fun _ hw=>(EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1)
    ⟨M.witness 0,M.witnesses_legal 0⟩
theorem t_family : Family 8 TL tFullEdges := by
  have perms := ChainConcreteStateFamilies.t_full.perms
  constructor
  · exact perms
  · exact ⟨ChainTailSegment.wordA,Or.inl rfl⟩
  · intro e he
    obtain ⟨w,hw,t,ht,he⟩ := (mem_edges_iff 8 _ e).mp he
    have hl : TL w := by simpa [TL] using hw
    have len : w.length=8 := by simpa using (perms w hl).length_eq
    exact ⟨w,hl,t,by omega,he⟩
  · intro w hw t ht
    have len : w.length=8 := by simpa using (perms w hw).length_eq
    exact (mem_edges_iff 8 _ _).mpr ⟨w,by simpa [TL] using hw,t,by omega,rfl⟩

theorem rest_family (r : Nat) : Family (16*r+8) (restL r) (ChainGlobalEdgeCandidates.rest r) := by
  induction r with
  | zero => exact t_family
  | succ r ih =>
    have hh := joined_family 16 (16*r+8) ML (restL r) mFull (ChainGlobalEdgeCandidates.rest r) m_family ih
    simpa only [restL,ChainGlobalEdgeCandidates.rest,show 16+(16*r+8)=16*(r+1)+8 by omega] using hh

theorem global_family (r : Nat) : Family (25+16*r) (globalL r) (global r) := by
  have hh := joined_family 17 (16*r+8) IL (restL r) iFull (ChainGlobalEdgeCandidates.rest r) i_family (rest_family r)
  simpa only [globalL,global,show 17+(16*r+8)=25+16*r by omega] using hh

theorem physical_family (r : Nat) (E : List Nat)
    (he : ∀v,v∈E ↔ IsErasure (r+1) v) :
    Family (25+16*r) (labelledLegal r E) (global r) := by
  have hf := global_family r
  have eqv := global_language_iff r E he
  constructor
  · intro w hw; exact hf.perms w ((eqv w).mpr hw)
  · obtain ⟨w,hw⟩ := hf.nonempty; exact ⟨w,(eqv w).mp hw⟩
  · intro e he'; obtain ⟨w,hw,t,ht,eq⟩ := hf.sound e he'
    exact ⟨w,(eqv w).mp hw,t,ht,eq⟩
  · intro w hw t ht; exact hf.complete w ((eqv w).mpr hw) t ht

theorem physical_edges_exact (r : Nat) (E : List Nat)
    (he : ∀v,v∈E ↔ IsErasure (r+1) v) (e : Edge) :
    e∈global r ↔ ∃w,labelledLegal r E w ∧ ∃t,t<w.length ∧ edgeAt (25+16*r) w t=e := by
  have hf := physical_family r E he
  constructor
  · intro h
    obtain ⟨w,hw,t,ht,eq⟩ := hf.sound e h
    have len : w.length=25+16*r := by simpa using (hf.perms w hw).length_eq
    exact ⟨w,hw,t,by omega,eq⟩
  · rintro ⟨w,hw,t,ht,rfl⟩
    have len : w.length=25+16*r := by simpa using (hf.perms w hw).length_eq
    exact hf.complete w hw t (by omega)

theorem physical_edge_count_certificate (r : Nat) (E : List Nat)
    (he : ∀v,v∈E ↔ IsErasure (r+1) v) :
    (global r).length=63*(r+1)+1 ∧ (global r).Nodup ∧
    (∀e,e∈global r ↔ ∃w,labelledLegal r E w ∧ ∃t,t<w.length ∧ edgeAt (25+16*r) w t=e) :=
  ⟨global_length r,global_nodup r,physical_edges_exact r E he⟩
#print axioms physical_edges_exact
#print axioms physical_edge_count_certificate
end ChainPhysicalEdgeFamily
