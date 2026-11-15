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
namespace EpochContinuity
open SpookyRound TraceBridge CutBound EpochPrefix

theorem no_compute_occupied (h : Trace s es t) (hp : t = .pebble)
    (hz : count .compute es = 0) :
    s = .pebble ∧ ∀ e ∈ es, e = .idle := by
  induction h with
  | nil s => simp_all
  | cons hs ht ih =>
    cases hs <;> simp_all [count,List.filter_cons] <;> exact ih.2

variable {n : Nat} {pred : Fin n → Fin n → Bool} {q p : Config n}
 {xs ys : List Action} {r : SpookyDP.Result (Config n)}

/-- Equal epoch IDs at an OLD-pebbled endpoint force a continuously occupied
scalar interval. Its actions contain neither ghost nor uncompute. -/
theorem same_id_continuous (h : ActionRuns pred p ys r) (u : Fin n)
    (hp : r.state.peb u = true)
    (he : before q u (xs ++ ys) = before q u xs) :
    kind p u = .pebble ∧ ∀ e ∈ events u ys, e = .idle := by
  have hz : count .compute (events u ys) = 0 := by
    rw [before_append] at he
    omega
  exact no_compute_occupied (actionruns_scalar h u) (by simp [kind,hp]) hz

/-- If a removal happened in a segment ending occupied, the epoch counter
strictly increased. This excludes assigning two separated occupied intervals
one ID; it does not yet extract their unique starting indices. -/
theorem removal_forces_new_id (h : ActionRuns pred p ys r) (u : Fin n)
    (hp : r.state.peb u = true)
    (hr : ∃ e ∈ events u ys, e = .ghost ∨ e = .uncompute) :
    before q u xs < before q u (xs ++ ys) := by
  have hm := before_mono q u xs ys
  by_cases he : before q u (xs ++ ys) = before q u xs
  · obtain ⟨_,hi⟩ := same_id_continuous h u hp he
    obtain ⟨e,hem,her⟩ := hr
    have hh := hi e hem
    rcases her with hg | hu <;> simp_all
  · omega
end EpochContinuity
#print axioms EpochContinuity.no_compute_occupied
#print axioms EpochContinuity.same_id_continuous
#print axioms EpochContinuity.removal_forces_new_id
