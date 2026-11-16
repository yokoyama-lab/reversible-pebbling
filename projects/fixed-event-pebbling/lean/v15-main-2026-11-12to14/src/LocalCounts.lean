import WholeBijection
import IFinite
import MUpperVerified
import EnumerationCorrectness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ChainWordCounts
theorem enumeration_nodup (events : List LocalCertificate.Event) (erasures final : List Nat)
 (fuel : Nat) (board remaining : List Nat) (hn : remaining.Nodup) :
 (EnumerationCorrectness.enumeratePhysical events erasures final fuel board remaining).Nodup := by
 induction fuel generalizing board remaining with
 | zero => simp only [EnumerationCorrectness.enumeratePhysical]; split <;> simp
 | succ fuel ih =>
  simp only [EnumerationCorrectness.enumeratePhysical,List.Nodup,List.pairwise_flatMap]
  constructor
  · intro e he
    cases hl : events[e]? with
    | none => simp [hl]
    | some ev =>
     cases hs : LocalCertificate.step true erasures board ev with
     | none => simp [hl,hs]
     | some after =>
      simp only [hl,hs,List.pairwise_map]
      exact (ih after (remaining.erase e) (hn.erase e)).imp (by intro a b h eq; exact h (List.cons.inj eq).2)
  · apply hn.imp
    intro a b hab x hx y hy hxy
    cases ha : events[a]? <;> simp [ha] at hx
    rename_i ea
    cases hsa : LocalCertificate.step true erasures board ea <;> simp [hsa] at hx
    rcases hx with ⟨u,hu,rfl⟩
    cases hb : events[b]? <;> simp [hb] at hy
    rename_i eb
    cases hsb : LocalCertificate.step true erasures board eb <;> simp [hsb] at hy
    rcases hy with ⟨v,hv,rfl⟩
    exact hab (List.cons.inj hxy).1
theorem initial_nodup : UpperCertificate.I.physicalWords.Nodup := by
 unfold UpperCertificate.I.physicalWords
 rw [EnumerationCorrectness.same_enumerator]
 exact enumeration_nodup _ _ _ _ _ _ List.nodup_range
theorem middle_nodup : UpperCertificate.M.physicalWords.Nodup := by
 unfold UpperCertificate.M.physicalWords
 rw [EnumerationCorrectness.same_enumerator]
 exact enumeration_nodup _ _ _ _ _ _ List.nodup_range
 theorem initial_iff (w : List Nat) : w ∈ UpperCertificate.I.physicalWords ↔ LocalCertificate.I.Legal w :=
 EnumerationCorrectness.upper_physical_enumeration_legal _ _ _ _ w
 theorem middle_iff (w : List Nat) : w ∈ UpperCertificate.M.physicalWords ↔ LocalCertificate.M.Legal w :=
 EnumerationCorrectness.upper_physical_enumeration_legal _ _ _ _ w
#print axioms initial_nodup
#print axioms middle_nodup
end ChainWordCounts
