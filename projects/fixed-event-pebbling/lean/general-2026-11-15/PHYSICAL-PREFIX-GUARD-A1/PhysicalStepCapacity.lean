import PhysicalReplayHeight

/- Finite unit, compiled (green 2026-11-15/16); original LocalCertificate.step only.
   No copy of its predecessor/erasure legality predicate. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate

/-- Capacity=true adds precisely the bound on the resulting board.
    It does not inspect the starting board's length. -/
theorem step_true_iff_false_and_capacity (erasures board after : List Nat)
    (e : Event) :
    step true erasures board e = some after ↔
      step false erasures board e = some after ∧ after.length ≤ 5 := by
  cases hp : e.place <;> simp [step, hp] <;> grind

/-- Capacity trace is defined using ORIGINAL capacity-free transitions;
    every post-step board must satisfy the bound. Empty trace imposes none. -/
inductive CapacityTrace (events : List Event) (erasures : List Nat) :
    List Nat → List Nat → List Nat → Prop
  | nil (board) : CapacityTrace events erasures board [] board
  | cons {board mid after ids i e} :
      events[i]? = some e →
      step false erasures board e = some mid →
      mid.length ≤ 5 →
      CapacityTrace events erasures mid ids after →
      CapacityTrace events erasures board (i :: ids) after

/-- A trace has both real event lookup and real noncapacity transitions. -/
theorem CapacityTrace.replay_false
    (h : CapacityTrace events erasures board ids after) :
    replay false events erasures board ids = some after := by
  induction h with
  | nil board => rfl
  | cons he ht hb htail ih => simp [replay, he, ht, ih]

/-- Exact trace characterization of original capacity-checked replay. -/
theorem replay_true_iff_capacityTrace (events : List Event)
    (erasures board ids after : List Nat) :
    replay true events erasures board ids = some after ↔
      CapacityTrace events erasures board ids after := by
  constructor
  · intro hs
    induction ids generalizing board with
    | nil =>
        have he : board = after := by simpa [replay] using hs
        subst after
        exact CapacityTrace.nil board
    | cons i rest ih =>
        obtain ⟨e, mid, he, ht, hr⟩ :=
          successful_replay_cons_decompose true events erasures board after i rest hs
        have hf := (step_true_iff_false_and_capacity erasures board mid e).mp ht
        exact CapacityTrace.cons he hf.1 hf.2 (ih mid hr)
  · intro h
    induction h with
    | nil board => rfl
    | @cons board mid after ids i e he ht hb htail ih =>
        have hc := (step_true_iff_false_and_capacity erasures board mid e).mpr ⟨ht,hb⟩
        simp [replay, he, hc, ih]

#print axioms step_true_iff_false_and_capacity
#print axioms CapacityTrace.replay_false
#print axioms replay_true_iff_capacityTrace
end LocalCertificate
