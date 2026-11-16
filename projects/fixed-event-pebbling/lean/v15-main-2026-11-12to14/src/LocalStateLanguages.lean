import PrefixStateCorrectness
namespace ChainPrefixStates
open LocalCertificate

theorem i_states_exact (s : List Nat) : s ∈ iStates ↔
    ∃ w, I.Legal w ∧ ∃ t, t ≤ w.length ∧
      (List.range 10).filter (fun e => (w.take t).contains e) = s := by
  rw [iStates,mem_states_iff]
  have h (w : List Nat) : w ∈ UpperCertificate.I.physicalWords ↔ I.Legal w :=
    EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures w
  simp only [h]

theorem m_states_exact (s : List Nat) : s ∈ mStates ↔
    ∃ w, M.Legal w ∧ ∃ t, t ≤ w.length ∧
      (List.range 12).filter (fun e => (w.take t).contains e) = s := by
  rw [mStates,mem_states_iff]
  have h (w : List Nat) : w ∈ UpperCertificate.M.physicalWords ↔ M.Legal w :=
    EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures w
  simp only [h]

#print axioms i_states_exact
#print axioms m_states_exact
end ChainPrefixStates
