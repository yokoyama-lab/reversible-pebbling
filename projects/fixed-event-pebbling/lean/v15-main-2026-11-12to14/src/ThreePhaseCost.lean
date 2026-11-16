import JointProjection
import TerminalExistence
import VisitMeasure
namespace ThreePhaseCost
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure LowerProjection UpperProjectionRun
/-- Capacity changes admissibility, not the board evolution or price. -/
theorem run_deterministic {p q b es z c r z' c' r'}
 (h : Run p b es z c r) (h' : Run q b es z' c' r') :
 z=z' ∧ c=c' ∧ r=r' := by
 induction h generalizing z' c' r' with
 | nil => cases h';exact ⟨rfl,rfl,rfl⟩
 | @cons b a z es c r e hs ht ih =>
  cases h' with
  | @cons b a' z' es c' r' e hs' ht' =>
   have eq : a=a' := (step_update hs).symm.trans (step_update hs')
   subst a'
   obtain ⟨hz,hc,hr⟩ := ih ht'
   exact ⟨hz,by omega,by omega⟩

theorem moves_append (m : Nat) (xs ys : List Event) :
 moves m (xs++ys)=moves m xs++moves m ys := by simp [moves]

/-- Once a reduced-capacity cleanup is supplied, charge the three phases
 jointly. The upper and lower words are concrete projections, not witnesses
 with assumed independent cost bounds. -/
theorem three_phase_cost {p q m n xs ys Q cp rp ct rt cd rd}
 (hp : Run p [] xs Q cp rp) (ht : Run p Q ys [n] ct rt)
 (mn : m<n) (cut : low m Q=[m])
 (safe : Safe p q m [] (xs++ys))
 (cleanup : Run q [m] (moves m ys) [] cd rd) :
 ∃cl rl cu ru,
 Run p [] (moves m xs) [m] cl rl ∧
 Run q [] (word m (xs++ys)) [n-m] cu ru ∧
 cl+cu+cd≤cp+ct ∧ rl+ru+rd≤rp+rt := by
 obtain ⟨cl,rl,cu,ru,hl,hu,hc,hr⟩ := JointProjection.split_cost (run_append hp ht) m q safe
 have loend : low m [n]=[] := by simp [low,show ¬n≤m by omega]
 have hibegin : board m ([] : List Nat)=[] := by simp [board,UpperProjectionBounds.high]
 have hiend : board m [n]=[n-m] := by simp [board,UpperProjectionBounds.high,mn]
 have lobegin : low m ([] : List Nat)=[] := by simp [low]
 rw [moves_append,lobegin,loend] at hl
 obtain ⟨R,c1,r1,c2,r2,h1,h2,ce,re⟩ := run_split hl
 obtain ⟨cx,rx,hx,_,_⟩ := LowerProjection.run_low (m:=m) hp
 rw [lobegin,cut] at hx
 have state := (run_deterministic h1 hx).1
 subst R
 obtain ⟨_,cdEq,rdEq⟩ := run_deterministic h2 cleanup
 refine ⟨c1,r1,cu,ru,h1,?_,?_,?_⟩
 · simpa [hibegin,hiend] using hu
 · omega
 · omega
#print axioms run_deterministic
#print axioms three_phase_cost
end ThreePhaseCost
