import StateCertificateBridge
import GlobalStateLanguage
import GlobalStateCanonical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PhysicalStateCertificate
open ChainOccurrence ChainGlobalStateCandidates ChainStateFamilyJoin ChainConcreteStateFamilies
open CompletedSetDFA FiniteDFATransport
theorem physical_full (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 Full (25+16*r) (labelledLegal r E) (global r) := by
 have full := global_full r
 have eq := ChainGlobalStateLanguage.global_language_iff r E he
 constructor
 · intro w hw;exact full.perms w ((eq w).mpr hw)
 · obtain ⟨w,hw⟩ := full.nonempty;exact ⟨w,(eq w).mp hw⟩
 · intro s hs
   obtain ⟨w,hw,t,ht,hts⟩ := full.sound s hs
   exact ⟨w,(eq w).mp hw,t,ht,hts⟩
 · intro w hw t ht;exact full.complete w ((eq w).mpr hw) t ht
theorem certificate (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) : Certificate (labelledLegal r E) (global r) :=
 StateCertificateBridge.certificate_of_full (25+16*r) (labelledLegal r E) (global r)
 (physical_full r E he) (global_nodup r) (fun c hc d hd hs => global_canonical r c d hc hd hs)
theorem complete_state_count (r : Nat) : (global r).length+1=40*(r+1)+6 := by
 rw [global_length]

#print axioms certificate
end PhysicalStateCertificate
