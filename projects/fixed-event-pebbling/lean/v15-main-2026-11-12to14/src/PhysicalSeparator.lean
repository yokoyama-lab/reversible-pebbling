import ActualUpperPersistence
import SeparatorSafe
import ThreePhaseCost
namespace PhysicalSeparator
open LocalCertificate TerminalProjection WinningMinimum
/-- Three physical subruns at the correct capacities, whose total price
 is no greater than the arbitrary supplied bounded winning run. -/
theorem decompose {p n es c r}
 (hr : Run p [] es [n] c r) (hb : ∀e∈es,e.vertex≤n) (hn : 2≤n) :
 ∃m wl wu wd cl rl cu ru cd rd,
 1≤m ∧ m<n ∧ 2≤p ∧
 Run p [] wl [m] cl rl ∧ Run (p-1) [] wu [n-m] cu ru ∧
 Run (p-1) [m] wd [] cd rd ∧ cl+cu+cd≤c := by
 obtain ⟨x,hcost,hmin,hclean⟩ := CleanHandoffFinal.clean_handoff_exists hr hb
 obtain ⟨m,pre,post,Q,cp,rp,ct,rt,cd,rd,mp,mn,hw,hpre,hpost,hc,he,low,lower,occupied,hcleanup,dc,dr⟩ :=
  ActualUpperPersistence.actual_cleanup x hmin hn hclean
 have p2 := SeparatorSafe.capacity_two hr hn
 have safe : UpperProjectionRun.Safe p (p-1) m [] x.word := by
  apply SeparatorSafe.safe_of_intermediates x.run p2
  intro P hp
  obtain ⟨v,hv,hpos,hvbound⟩ := lower P hp
  exact ⟨v,hv,hvbound⟩
 rw [hw] at safe
 obtain ⟨cl,rl,cu,ru,hl,hu,total,erasures⟩ :=
  ThreePhaseCost.three_phase_cost hpre hpost mn low safe hcleanup
 exact ⟨m,LowerProjection.moves m pre,UpperProjectionRun.word m (pre++post),
  LowerProjection.moves m post,cl,rl,cu,ru,cd,rd,mp,mn,p2,hl,hu,hcleanup,by omega⟩
#print axioms decompose
end PhysicalSeparator
