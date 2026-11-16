import TraceBridge
namespace EpochPrefix
open SpookyRound TraceBridge CutBound

def initiallyOccupied : State → Nat | .pebble => 1 | _ => 0

theorem occupied_has_epoch (h : Trace s es t) (hp : t = .pebble) :
    1 ≤ initiallyOccupied s + count .compute es := by
  induction h with
  | nil s => simp_all [initiallyOccupied,count]
  | cons hs ht ih =>
    cases hs <;> simp_all [initiallyOccupied,count,List.filter_cons] <;> omega

def before (q : Config n) (u : Fin n) (xs : List Action) : Nat :=
  initiallyOccupied (kind q u) + count .compute (events u xs)

theorem events_append (u : Fin n) (xs ys : List Action) :
    events u (xs ++ ys) = events u xs ++ events u ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [events,ih]

theorem before_append (q : Config n) (u : Fin n) (xs ys : List Action) :
    before q u (xs ++ ys) = before q u xs + count .compute (events u ys) := by
  simp [before,events_append,count,List.filter_append,List.length_append,Nat.add_assoc]

theorem before_mono (q : Config n) (u : Fin n) (xs ys : List Action) :
    before q u xs ≤ before q u (xs ++ ys) := by
  rw [before_append]
  omega

variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
  {xs : List Action} {r : SpookyDP.Result (Config n)} {a : Action}

theorem old_pebble_positive (h : ActionRuns pred q xs r) (u : Fin n)
    (hp : r.state.peb u = true) : 1 ≤ before q u xs := by
  have hh := actionruns_scalar h u
  have hk : kind r.state u = .pebble := by simp [kind,hp]
  exact occupied_has_epoch hh hk

/-- Actual OLD-state child reference is assigned a positive prefix epoch ID. -/
theorem reference_positive (h : ActionRuns pred q xs r)
    (hl : Legal pred r.state a) (v u : Fin n)
    (hv : firstAt a v ≠ .idle) (hu : pred v u = true) :
    1 ≤ before q u xs := by
  exact old_pebble_positive h u (hl.2.2.2.1 v hv u hu)
end EpochPrefix
#print axioms EpochPrefix.occupied_has_epoch
#print axioms EpochPrefix.before_append
#print axioms EpochPrefix.before_mono
#print axioms EpochPrefix.old_pebble_positive
#print axioms EpochPrefix.reference_positive
