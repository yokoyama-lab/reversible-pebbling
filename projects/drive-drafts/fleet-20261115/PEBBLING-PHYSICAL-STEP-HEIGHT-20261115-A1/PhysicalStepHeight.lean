import LocalCertificate

/- Uncompiled source candidate importing the ORIGINAL fixed concrete model.
   Do not replace LocalCertificate.step with a reimplemented model.
   Restore finite elaboration limits after importing legacy module options. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace LocalCertificate

 def eventIncrement (e : Event) : Int := if e.place then 1 else -1

 theorem successful_remove_shape (capacity : Bool) (erasures board after : List Nat)
    (e : Event) (hp : e.place = false)
    (hs : step capacity erasures board e = some after) :
    after = board.erase e.vertex ∧ board.contains e.vertex = true := by
  cases hg : (board.contains e.vertex &&
      ((!(e.vertex == 1 || board.contains (e.vertex - 1))) == erasures.contains e.vertex)) with
  | false => simp [step, hp, hg] at hs
  | true =>
      have hc : board.contains e.vertex = true := by
        cases hh : board.contains e.vertex with
        | false => simp [hh] at hg
        | true => rfl
      cases hk : (capacity && decide ((board.erase e.vertex).length > 5)) with
      | false =>
          have heq : board.erase e.vertex = after := by simpa [step, hp, hg, hk] using hs
          exact ⟨heq.symm, hc⟩
      | true => simp [step, hp, hg, hk] at hs

 theorem successful_place_shape (capacity : Bool) (erasures board after : List Nat)
    (e : Event) (hp : e.place = true)
    (hs : step capacity erasures board e = some after) :
    after = e.vertex :: board ∧ board.contains e.vertex = false := by
  cases hg : (!(board.contains e.vertex) &&
      (e.vertex == 1 || board.contains (e.vertex - 1))) with
  | false => simp [step, hp, hg] at hs
  | true =>
      have hc : board.contains e.vertex = false := by
        cases hh : board.contains e.vertex with
        | false => rfl
        | true => simp [hh] at hg
      cases hk : (capacity && decide ((e.vertex :: board).length > 5)) with
      | false =>
          have heq : e.vertex :: board = after := by simpa [step, hp, hg, hk] using hs
          exact ⟨heq.symm, hc⟩
      | true => simp [step, hp, hg, hk] at hs

/-- Exact integer length change of the original successful step.
    Nodup is NOT needed for this length identity: List.erase removes exactly
    one occurrence, and the successful-remove guard proves membership. -/
 theorem successful_step_length_increment (capacity : Bool)
    (erasures board after : List Nat) (e : Event)
    (hs : step capacity erasures board e = some after) :
    (after.length : Int) = (board.length : Int) + eventIncrement e := by
  cases hp : e.place with
  | false =>
      obtain ⟨heq, hc⟩ := successful_remove_shape capacity erasures board after e hp hs
      have hm : e.vertex ∈ board := by simpa using hc
      have hlen : (board.erase e.vertex).length = board.length - 1 :=
        List.length_erase_of_mem hm
      have hpos : 0 < board.length := by
        cases board with
        | nil => simp at hm
        | cons x xs => simp
      rw [heq]
      simp only [eventIncrement, hp, Bool.false_eq_true, if_false]
      omega
  | true =>
      obtain ⟨heq, hc⟩ := successful_place_shape capacity erasures board after e hp hs
      simp [heq, eventIncrement, hp]

/-- These are the original module's initial boards, not copied constants. -/
 theorem I_initial_height : (I.initial.length : Int) = 4 := by decide
 theorem M_initial_height : (M.initial.length : Int) = 4 := by decide
 theorem I_initial_nodup : I.initial.Nodup := by decide
 theorem M_initial_nodup : M.initial.Nodup := by decide

#print axioms successful_remove_shape
#print axioms successful_place_shape
#print axioms successful_step_length_increment
#print axioms I_initial_height
#print axioms M_initial_height
end LocalCertificate
