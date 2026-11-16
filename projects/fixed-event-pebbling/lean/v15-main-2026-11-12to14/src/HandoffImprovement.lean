import HandoffNontrivial
import GeneralTerminal
import PermMeasure
namespace HandoffImprovement
open LocalCertificate TerminalProjection VisitMeasure CleanHandoffMeasure
/-- Projection and last-bad extraction are explicit inputs, not assumed conclusions. -/
theorem improve_at_cut {p n m pre projected post P c r d s ct rt}
 (old : Run p [] pre P c r)
 (proj : Run p [] projected P d s) (projCost : d≤c)
 (projBound : ∀e∈projected,e.vertex≤m)
 (tail : Run p P post [n] ct rt)
 (tailBound : ∀e∈post,e.vertex≤n)
 (hm : 2≤m) (hmn : m≤n) (member : m∈P)
 (spare : P.length≤p-1) (nontrivial : ¬P.Perm [m])
 (witness : m∈bad n [] (pre++post))
 (suffix : ∀j∈bad n P post,j<m) :
 ∃word cost erased,Run p [] word [n] cost erased ∧ cost≤c+ct ∧
 (∀e∈word,e.vertex≤n) ∧
 rank (bad n [] word)<rank (bad n [] (pre++post)) := by
 obtain ⟨replacement,Q,dc,ds,hr,hperm,hcost,hbound,hprotect,havoid⟩ :=
  GeneralTerminal.bounded_prefix_bypass proj member projBound hm spare nontrivial
 have hb := bypass_bad_bound (n:=n) hbound havoid
 obtain ⟨z,run,hz,le,lt⟩ := PermMeasure.replacement_decreases_perm old hr hperm.symm tail
   (by omega) witness hb suffix
 have zeq : z=[n] := hz.symm.eq_singleton
 subst z
 refine ⟨replacement++post,dc+ct,ds+rt,run,le,?_,lt⟩
 intro e he
 rcases List.mem_append.mp he with he | he
 · exact Nat.le_trans (hbound e he) hmn
 · exact tailBound e he
#print axioms improve_at_cut
end HandoffImprovement
