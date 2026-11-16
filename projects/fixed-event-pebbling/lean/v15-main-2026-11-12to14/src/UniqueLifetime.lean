import TwoLifetime
namespace ChainUniqueLifetime
open LocalCertificate ChainTrace ChainLifetime

def isRemoval (v : Nat) (e : Event) : Bool := !e.place && (e.vertex == v)

theorem absent_no_placement_no_removal (erasures board final : List Nat)
    (es : List Event) (v : Nat) (absent : v ∉ board)
    (noP : ∀ e ∈ es, e.place = true → e.vertex ≠ v)
    (hr : run erasures board es = some final) : es.countP (isRemoval v) = 0 := by
  induction es generalizing board with
  | nil => rfl
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run, hs] at hr
    | some mid =>
      have tail : run erasures mid es = some final := by simpa [run, hs] using hr
      have np : ∀ f ∈ es, f.place = true → f.vertex ≠ v :=
        fun f hf => noP f (List.mem_cons_of_mem e hf)
      have hn : e.vertex ≠ v := by
        intro hv
        cases hp : e.place with
        | false => exact absent (hv ▸ removal_requires_present erasures board mid e hp hs)
        | true => exact noP e (by simp) hp hv
      have am : v ∉ mid := fun hm => absent
        ((step_membership_unchanged erasures board mid e v hn hs).mp hm)
      have ht := ih mid am np tail
      simp [List.countP_cons, isRemoval, hn, ht]

/-- A successful interval with no placement of v has at most one removal of v.
The initial board must be duplicate-free, as removal uses List.erase. -/
theorem no_placement_at_most_one_removal (erasures board final : List Nat)
    (es : List Event) (v : Nat) (nodup : board.Nodup)
    (noP : ∀ e ∈ es, e.place = true → e.vertex ≠ v)
    (hr : run erasures board es = some final) : es.countP (isRemoval v) ≤ 1 := by
  induction es generalizing board with
  | nil => simp
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run, hs] at hr
    | some mid =>
      have tail : run erasures mid es = some final := by simpa [run, hs] using hr
      have np : ∀ f ∈ es, f.place = true → f.vertex ≠ v :=
        fun f hf => noP f (List.mem_cons_of_mem e hf)
      by_cases hv : e.vertex = v
      · have hp : e.place = false := by
          cases he : e.place with
          | false => rfl
          | true => exact False.elim (noP e (by simp) he hv)
        have am : v ∉ mid := hv ▸ removal_absent erasures board mid e nodup hp hs
        have hz := absent_no_placement_no_removal erasures mid final es v am np tail
        simp [List.countP_cons, isRemoval, hp, hv, hz]
      · have ht := ih mid (step_nodup erasures board mid e nodup hs) np tail
        simpa [List.countP_cons, isRemoval, hv] using ht

#print axioms absent_no_placement_no_removal
#print axioms no_placement_at_most_one_removal
end ChainUniqueLifetime
