import FiniteAlphabetDFA
import PhysicalFiniteDFA
namespace FinitePartialDFA
/-- None denotes failed computation, not an additional state. -/
structure DFA (N n : Nat) where
 step : Fin n → Fin N → Option (Fin n)
 initial : Option (Fin n)
 accept : Fin n → Prop

def next {N n} (M : DFA N n) : Option (Fin n) → Fin N → Option (Fin n)
 | none,_ => none
 | some q,a => M.step q a

def run {N n} (M : DFA N n) : Option (Fin n) → List (Fin N) → Option (Fin n)
 | q,[] => q
 | q,a::w => run M (next M q a) w

def final {N n} (M : DFA N n) : Option (Fin n) → Prop
 | none => False
 | some q => M.accept q

def Accept {N n} (M : DFA N n) (w : List (Fin N)) := final M (run M M.initial w)

def complete {N n} (M : DFA N n) : FiniteAlphabetDFA.DFA N (n+1) where
 step q a := FiniteDFATransport.number (next M (FiniteDFATransport.unnumber q) a)
 initial := FiniteDFATransport.number M.initial
 accept q := final M (FiniteDFATransport.unnumber q)

theorem complete_run {N n} (M : DFA N n) (q) (w : List (Fin N)) :
 FiniteAlphabetDFA.run (complete M) (FiniteDFATransport.number q) w =
 FiniteDFATransport.number (run M q w) := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih =>
  simpa only [FiniteAlphabetDFA.run,complete,FiniteDFATransport.unnumber_number,run] using ih (next M q a)

theorem complete_accept {N n} (M : DFA N n) (w) :
 FiniteAlphabetDFA.Accept (complete M) w ↔ Accept M w := by
 unfold FiniteAlphabetDFA.Accept
 change final M (FiniteDFATransport.unnumber (FiniteAlphabetDFA.run (complete M) (FiniteDFATransport.number M.initial) w)) ↔ _
 rw [complete_run,FiniteDFATransport.unnumber_number]
 rfl

noncomputable def fromCertificate (N : Nat) (L : CompletedSetDFA.Language) (sets : List (List Nat))
 (cert : FiniteDFATransport.Certificate L sets) : DFA N sets.length where
 step q a := FiniteDFATransport.step L sets cert (some q) a.val
 initial := FiniteDFATransport.initial L sets cert
 accept q := FiniteDFATransport.Accept L sets cert (some q)

theorem certificate_next (N L sets cert) (q : Option (Fin sets.length)) (a : Fin N) :
 next (fromCertificate N L sets cert) q a = FiniteDFATransport.step L sets cert q a.val := by
 cases q <;> rfl

theorem certificate_run (N L sets cert) (q : Option (Fin sets.length)) (w : List (Fin N)) :
 run (fromCertificate N L sets cert) q w = FiniteDFATransport.run L sets cert q (w.map Fin.val) := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih =>
  simp only [run,List.map_cons,FiniteDFATransport.run,certificate_next]
  exact ih _

theorem certificate_recognizes (N L sets cert) (respect : CompletedSetDFA.Respects L) (w : List (Fin N)) :
 Accept (fromCertificate N L sets cert) w ↔ L (w.map Fin.val) := by
 unfold Accept
 rw [certificate_run]
 have hf (q : Option (Fin sets.length)) : final (fromCertificate N L sets cert) q ↔ FiniteDFATransport.Accept L sets cert q := by
  cases q <;> rfl
 rw [hf]
 exact FiniteDFATransport.recognizes L sets cert respect _

theorem partial_upper (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃M : DFA (ChainAssembledTrace.fullTable r).length (40*(r+1)+5),
 ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E (w.map Fin.val) := by
 rw [←ChainGlobalStateCandidates.global_length r]
 exact ⟨fromCertificate _ _ _ (PhysicalFiniteDFA.certificate r E he),
  certificate_recognizes _ _ _ _ (ChainCompletedDFA.respects r E)⟩

theorem partial_lower (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (n : Nat)
 (M : DFA (ChainAssembledTrace.fullTable r).length n)
 (rec : ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E (w.map Fin.val)) :
 40*(r+1)+5≤n := by
 have h := FiniteAlphabetDFA.complete_lower r E he (n+1) (complete M)
  (fun w => (complete_accept M w).trans (rec w))
 omega
theorem run_failed {N n} (M : DFA N n) (w : List (Fin N)) : run M none w=none := by
 induction w with
 | nil => rfl
 | cons a w ih => exact ih

theorem accepting_has_initial {N n} (M : DFA N n) (w) (h : Accept M w) :
 ∃q,M.initial=some q := by
 cases hi : M.initial with
 | none =>
  unfold Accept at h
  rw [hi,run_failed] at h
  exact False.elim h
 | some q => exact ⟨q,rfl⟩

theorem partial_upper_with_initial (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃M : DFA (ChainAssembledTrace.fullTable r).length (40*(r+1)+5),
 (∃q,M.initial=some q) ∧
 ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E (w.map Fin.val) := by
 obtain ⟨M,rec⟩ := partial_upper r E he
 obtain ⟨w,hw⟩ := (PhysicalFiniteDFA.physical_full r E he).nonempty
 obtain ⟨v,hv⟩ := FiniteAlphabetDFA.lift_word (ChainAssembledTrace.fullTable r).length w
  (fun a ha => hw.1.2.2 a ha)
 have acc : Accept M v := (rec v).mpr (by simpa only [hv] using hw)
 exact ⟨M,accepting_has_initial M v acc,rec⟩

#print axioms run_failed
#print axioms accepting_has_initial
#print axioms partial_upper_with_initial

#print axioms complete_run
#print axioms complete_accept
#print axioms certificate_next
#print axioms certificate_run
#print axioms certificate_recognizes
#print axioms partial_upper
#print axioms partial_lower
end FinitePartialDFA
