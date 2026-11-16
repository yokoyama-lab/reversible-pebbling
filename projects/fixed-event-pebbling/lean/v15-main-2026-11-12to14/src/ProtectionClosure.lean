import SingletonVisit
import LexMinimum
namespace ProtectionClosure
open LocalCertificate TerminalProjection VisitMeasure SingletonVisit
def Guard (m : Nat) : List Nat → List Event → Prop
 | b,[] => True
 | b,e::es => (e.vertex=m → erasure b e=0) ∧ Guard m (update b e) es
theorem guard_append (m : Nat) (b : List Nat) (xs ys : List Event) :
 Guard m b (xs++ys) ↔ Guard m b xs ∧ Guard m (evolve b xs) ys := by
 induction xs generalizing b with
 | nil => simp [Guard,evolve]
 | cons e xs ih => simp [Guard,evolve,ih,and_assoc]
theorem guard_protected {p m b es} (hg : Guard m b es) : Protected p m b es := by
 intro pre e post x y cp rp hw hp hs
 rw [hw,guard_append] at hg
 have hx := run_evolve hp
 simpa [hx,Guard] using hg.2.1
theorem protected_guard {p m b es z c r} (hr : Run p b es z c r)
 (hp : Protected p m b es) : Guard m b es := by
 induction hr with
 | nil => trivial
 | @cons b a z es c r e hs ht ih =>
  have head := hp [] e es b a 0 0 rfl (Run.nil b) hs
  have tail : Protected p m a es := by
   intro pre f post x y cp rp hw hpre hstep
   exact hp (e::pre) f post x y _ _ (by simp [hw]) (Run.cons hs hpre) hstep
  exact ⟨head,by simpa [step_update hs] using ih tail⟩
theorem update_perm {b a : List Nat} (hp : b.Perm a) (e : Event) : (update b e).Perm (update a e) := by
 cases h : e.place <;> simp only [update,h,Bool.false_eq_true,↓reduceIte]
 · exact hp.erase _
 · exact hp.cons _
theorem guard_perm (m : Nat) (es : List Event) {b a : List Nat} (hp : b.Perm a) :
 Guard m b es ↔ Guard m a es := by
 induction es generalizing b a with
 | nil => rfl
 | cons e es ih =>
  simp only [Guard,ReversibleCleanup.erasure_perm hp,ih (update_perm hp e)]
theorem guard_swap {p m q initial pre post cp rp b cn rn}
 (hq : q<m) (hm : 2≤m) (hpre : Run p initial pre b cp rp)
 (old : Run p b [⟨false,q⟩,⟨true,1⟩] [1,m] 10 1)
 (new : Run p b [⟨true,1⟩,⟨false,q⟩] [1,m] cn rn)
 (hg : Guard m initial (pre++[⟨false,q⟩,⟨true,1⟩]++post)) :
 Guard m initial (pre++[⟨true,1⟩,⟨false,q⟩]++post) := by
 simp only [guard_append,evolve_append,run_evolve hpre,run_evolve old] at hg
 rw [guard_append,guard_append,evolve_append,run_evolve hpre,run_evolve new]
 exact ⟨⟨hg.1.1,by simp [Guard,show q≠m by omega,show 1≠m by omega]⟩,hg.2⟩
theorem guard_delete_q1 {p m initial pre post cp rp b}
 (hb : b.Perm [m,1]) (hpre : Run p initial pre b cp rp)
 (hg : Guard m initial (pre++[⟨false,1⟩,⟨true,1⟩]++post)) (hm : 2≤m) :
 Guard m initial (pre++post) := by
 have he : evolve b [⟨false,1⟩,⟨true,1⟩]=[1,m] := by
  have hp := hb.erase 1
  have hd : b.erase 1=[m] := by simpa [show m≠1 by omega] using hp
  simp [evolve,update,hd]
 simp only [guard_append,evolve_append,run_evolve hpre,he] at hg
 rw [guard_append,run_evolve hpre]
 exact ⟨hg.1.1,(guard_perm m post (hb.trans (List.Perm.swap _ _ []))).mpr hg.2⟩
#print axioms guard_protected
#print axioms protected_guard
#print axioms guard_swap
#print axioms guard_delete_q1
end ProtectionClosure
