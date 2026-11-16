import StateCertificateBridge
import EpsilonLower
namespace StateLower
open CompletedSetDFA FiniteDFATransport
noncomputable def prefixes (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i : Fin sets.length) : List Nat := representative (decode L sets cert i)
theorem prefixes_viable (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i : Fin sets.length) : Viable L (prefixes L sets cert i) := representative_viable _
theorem prefixes_different (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i j : Fin sets.length) (hne : i≠j) : ∃a,(a∈prefixes L sets cert i ∧ a∉prefixes L sets cert j) ∨
 (a∈prefixes L sets cert j ∧ a∉prefixes L sets cert i) := by
 classical
 apply Classical.byContradiction
 intro h
 have same : ∀a,a∈prefixes L sets cert i ↔ a∈prefixes L sets cert j := by
  intro a
  by_cases hi : a∈prefixes L sets cert i <;> by_cases hj : a∈prefixes L sets cert j
  · simp [hi,hj]
  · exact False.elim (h ⟨a,Or.inl ⟨hi,hj⟩⟩)
  · exact False.elim (h ⟨a,Or.inr ⟨hj,hi⟩⟩)
  · simp [hi,hj]
 have heq : decode L sets cert i=decode L sets cert j := by
  apply Subtype.ext;funext a;apply propext
  exact (representative_set _ a).trans ((same a).trans (representative_set _ a).symm)
 exact hne (decode_injective L sets cert i j heq)
theorem physical_nfa_lower (r : Nat) (E : List Nat) (sets : List (List Nat))
 (cert : Certificate (ChainOccurrence.labelledLegal r E) sets) (n : Nat) (M : EpsilonLower.NFA Nat n)
 (rec : ∀w,EpsilonLower.Accept M w ↔ ChainOccurrence.labelledLegal r E w) : sets.length≤n :=
 EpsilonLower.physical_completed_set_lower r E sets.length n M rec
 (prefixes _ sets cert) (prefixes_viable _ sets cert) (prefixes_different _ sets cert)
#print axioms prefixes_different
#print axioms physical_nfa_lower
end StateLower
