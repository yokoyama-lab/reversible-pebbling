import LocalCounts
import Std.Tactic
namespace PhysicalCompletionCount
open LocalCertificate EnumerationCorrectness
-- Explicit board and remaining-event state: not a done-mask quotient.
def count (events : List Event) (erasures final : List Nat) :
    Nat → List Nat → List Nat → Nat
  | 0, board, remaining => if remaining.isEmpty && sameBoard board final then 1 else 0
  | fuel+1, board, remaining => (remaining.map fun e =>
      match events[e]? with
      | none => 0
      | some ev => match step true erasures board ev with
        | none => 0
        | some after => count events erasures final fuel after (remaining.erase e)).sum

theorem count_exact (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board remaining : List Nat) :
    count events erasures final fuel board remaining =
      (enumeratePhysical events erasures final fuel board remaining).length := by
  induction fuel generalizing board remaining with
  | zero => simp only [count,enumeratePhysical]; split <;> simp
  | succ fuel ih =>
    simp only [count,enumeratePhysical,List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro e he
    cases hl : events[e]? with
    | none => simp
    | some ev =>
      cases hs : step true erasures board ev with
      | none => simp [hs]
      | some after => simpa [hs] using ih after (remaining.erase e)

theorem zero_iff_no_completion (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board remaining : List Nat) :
    count events erasures final fuel board remaining = 0 ↔
    ∀ t, ¬(t.length = fuel ∧ t.Perm remaining ∧ accepts events erasures final board t) := by
  rw [count_exact,List.length_eq_zero_iff,List.eq_nil_iff_forall_not_mem]
  simp only [physical_enumeration_iff]

-- With distinct remaining event IDs, the list counted above contains no duplicates.
theorem count_distinct (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board remaining : List Nat) (hn : remaining.Nodup) :
    (enumeratePhysical events erasures final fuel board remaining).Nodup ∧
    count events erasures final fuel board remaining =
      (enumeratePhysical events erasures final fuel board remaining).length :=
  ⟨ChainWordCounts.enumeration_nodup _ _ _ _ _ _ hn,count_exact _ _ _ _ _ _⟩
#print axioms count_exact
#print axioms zero_iff_no_completion
#print axioms count_distinct
end PhysicalCompletionCount
