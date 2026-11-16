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
namespace PhysicalCompletionCount
open LocalCertificate EnumerationCorrectness
-- Reordering the remaining-event list does not change the count, even with duplicates.
theorem count_remaining_perm (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board r s : List Nat) (h : r.Perm s) :
    count events erasures final fuel board r = count events erasures final fuel board s := by
  induction fuel generalizing board r s with
  | zero => simp only [count, h.isEmpty_eq]
  | succ fuel ih =>
    simp only [count]
    let f := fun (rs : List Nat) (e : Nat) =>
      match events[e]? with
      | none => 0
      | some ev => match step true erasures board ev with
        | none => 0
        | some after => count events erasures final fuel after (rs.erase e)
    change (r.map (f r)).sum = (s.map (f s)).sum
    have hf : f r = f s := by
      funext e
      dsimp [f]
      cases hl : events[e]? with
      | none => rfl
      | some ev =>
        cases hs : step true erasures board ev with
        | none => simp [hs]
        | some after => simpa [hs] using ih after (r.erase e) (s.erase e) (h.erase e)
    rw [hf]
    exact (h.map (f s)).sum_nat

-- Language equality, not equality of enumeration order.
theorem completions_remaining_perm (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board r s t : List Nat) (h : r.Perm s) :
    t ∈ enumeratePhysical events erasures final fuel board r ↔
      t ∈ enumeratePhysical events erasures final fuel board s := by
  rw [physical_enumeration_iff, physical_enumeration_iff]
  constructor
  · rintro ⟨hl,hp,ha⟩; exact ⟨hl,hp.trans h,ha⟩
  · rintro ⟨hl,hp,ha⟩; exact ⟨hl,hp.trans h.symm,ha⟩
#print axioms count_remaining_perm
#print axioms completions_remaining_perm
end PhysicalCompletionCount
