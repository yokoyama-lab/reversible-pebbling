import PhysicalAutomataExact
namespace FiniteAlphabetDFA
structure DFA (N n : Nat) where
 step : Fin n → Fin N → Fin n
 initial : Fin n
 accept : Fin n → Prop
def run {N n : Nat} (M : DFA N n) : Fin n → List (Fin N) → Fin n
 | q,[] => q
 | q,a::w => run M (M.step q a) w
def Accept {N n : Nat} (M : DFA N n) (w : List (Fin N)) := M.accept (run M M.initial w)
def restrict (N : Nat) {n : Nat} (M : CompleteDFALower.DFA n) : DFA N n :=
 ⟨fun q a=>M.step q a.val,M.initial,M.accept⟩
theorem restrict_run {N n : Nat} (M : CompleteDFALower.DFA n) (q : Fin n) (w : List (Fin N)) :
 run (restrict N M) q w=CompleteDFALower.run M q (w.map Fin.val) := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih => exact ih _
def extend {N n : Nat} (M : DFA N n) : CompleteDFALower.DFA n where
 step q a := if h : a<N then M.step q ⟨a,h⟩ else M.initial
 initial := M.initial
 accept := M.accept
theorem extend_run {N n : Nat} (M : DFA N n) (q : Fin n) (w : List (Fin N)) :
 CompleteDFALower.run (extend M) q (w.map Fin.val)=run M q w := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih => simpa [CompleteDFALower.run,run,extend,a.isLt] using ih (M.step q a)
theorem lift_word (N : Nat) (w : List Nat) (h : ∀a∈w,a<N) : ∃v : List (Fin N),v.map Fin.val=w := by
 induction w with
 | nil => exact ⟨[],rfl⟩
 | cons a w ih =>
  obtain ⟨v,hv⟩ := ih (fun a ha=>h a (by simp [ha]))
  exact ⟨⟨a,h a (by simp)⟩::v,by simp [hv]⟩
theorem complete_upper (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃M : DFA (ChainAssembledTrace.fullTable r).length (40*(r+1)+6),
 ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E (w.map Fin.val) := by
 obtain ⟨M,hm⟩ := PhysicalAutomataExact.complete_upper r E he
 refine ⟨restrict _ M,?_⟩
 intro w
 unfold Accept
 rw [restrict_run]
 exact hm _
theorem complete_lower (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (n : Nat)
 (M : DFA (ChainAssembledTrace.fullTable r).length n)
 (rec : ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E (w.map Fin.val)) : 40*(r+1)+6≤n := by
 apply PhysicalAutomataExact.complete_lower_on_alphabet r E he n (extend M)
 intro w hb
 obtain ⟨v,hv⟩ := lift_word _ w hb
 rw [←hv]
 unfold CompleteDFALower.Accept
 rw [extend_run]
 exact rec v
#print axioms complete_upper
#print axioms complete_lower
end FiniteAlphabetDFA
