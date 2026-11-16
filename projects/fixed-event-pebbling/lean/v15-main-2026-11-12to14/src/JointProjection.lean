import UpperProjectionRun
import LowerProjection
namespace JointProjection
open LocalCertificate TerminalProjection LowerProjection UpperProjectionRun UpperProjectionBounds
/-- Disjoint charging, stronger than two separate nonincrease inequalities. -/
theorem split_cost {p b es z c r} (h : Run p b es z c r) (m q : Nat)
 (safe : Safe p q m b es) :
 ∃cl rl cu ru,
 Run p (LowerProjection.low m b) (moves m es) (LowerProjection.low m z) cl rl ∧
 Run q (board m b) (word m es) (board m z) cu ru ∧
 cl+cu≤c ∧ rl+ru≤r := by
 induction h with
 | nil b =>
  exact ⟨0,0,0,0,by simpa [moves] using Run.nil (p:=p) (LowerProjection.low m b),
   by simpa [word] using Run.nil (p:=q) (board m b),by omega,by omega⟩
 | @cons b a z es c r e hs ht ih =>
  have cap := safe [] e es b a 0 0 rfl (Run.nil b) hs
  have safetail : Safe p q m a es := by
   intro pre f post x y cp rp hw hp hf
   exact safe (e::pre) f post x y _ _ (by simp [hw]) (Run.cons hs hp) hf
  obtain ⟨cl,rl,cu,ru,hl,hu,hc,hr⟩ := ih safetail
  by_cases hv : e.vertex≤m
  · have eql := low_step_disappears hs hv
    refine ⟨fee b e+cl,erasure b e+rl,cu,ru,?_,?_,by omega,by omega⟩
    · simpa [moves,hv,fee_low hv,erasure_low hv] using Run.cons (step_low hs hv) hl
    · simpa [word,show ¬m<e.vertex by omega,eql] using hu
  · have hi : m<e.vertex := by omega
    have eql := upper_step_disappears hs hi
    have fc := projected_fee_le (b:=b) hi
    have fr := projected_erasure_le (b:=b) hi
    refine ⟨cl,rl,fee (board m b) (event m e)+cu,erasure (board m b) (event m e)+ru,?_,?_,?_,?_⟩
    · simpa [moves,hv,eql] using hl
    · simpa [word,hi] using Run.cons (high_step hs hi cap) hu
    · rw [fee_shift hi];omega
    · rw [erasure_shift hi];omega
#print axioms split_cost
end JointProjection
