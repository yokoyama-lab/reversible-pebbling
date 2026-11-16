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

namespace EpochOrigin
open SpookyRound TraceBridge CutBound EpochPrefix

theorem last_witness (P : α → Prop) (xs : List α) (h : ∃ a ∈ xs, P a) :
    ∃ pre a post, xs = pre ++ a :: post ∧ P a ∧ ∀ b ∈ post, ¬ P b := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases ht : ∃ a ∈ xs, P a
    · obtain ⟨pre,a,post,he,hp,hn⟩ := ih ht
      exact ⟨x::pre,a,post,by simp [he],hp,hn⟩
    · have hx : P x := by simpa [ht] using h
      exact ⟨[],x,xs,rfl,hx,by simpa using ht⟩

/-- Uniqueness is about the actual list position, not just a chosen witness. -/
theorem last_position_unique (P : α → Prop) (pre1 pre2 : List α)
    (a b : α) (post1 post2 : List α)
    (he : pre1 ++ a :: post1 = pre2 ++ b :: post2)
    (ha : P a) (hb : P b)
    (h1 : ∀ x ∈ post1, ¬ P x) (h2 : ∀ x ∈ post2, ¬ P x) :
    pre1.length = pre2.length := by
  induction pre1 generalizing pre2 with
  | nil =>
    cases pre2 with
    | nil => rfl
    | cons x xs =>
      have ht : post1 = xs ++ b :: post2 := (List.cons.inj he).2
      have hm : b ∈ post1 := by rw [ht]; simp
      exact False.elim (h1 b hm hb)
  | cons x xs ih =>
    cases pre2 with
    | nil =>
      have ht : xs ++ a :: post1 = post2 := (List.cons.inj he).2
      have hm : a ∈ post2 := by rw [←ht]; simp
      exact False.elim (h2 a hm ha)
    | cons y ys =>
      have hh := ih ys (List.cons.inj he).2
      simpa using congrArg Nat.succ hh

variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {xs : List Action} {r : SpookyDP.Result (Config n)}

/-- For initially nonpebbled vertices ending occupied, extract the unique
last compute ROUND position. Interval continuity is a separate R2 result. -/
theorem actual_unique_last_compute (h : ActionRuns pred q xs r) (u : Fin n)
    (hs : kind q u ≠ .pebble) (hf : kind r.state u = .pebble) :
    ∃ k pre a post, xs = pre ++ a :: post ∧ pre.length = k ∧
      firstAt a u = .pebble ∧ (∀ b ∈ post, firstAt b u ≠ .pebble) ∧
      ∀ pre' a' post', xs = pre' ++ a' :: post' →
        firstAt a' u = .pebble → (∀ b ∈ post', firstAt b u ≠ .pebble) →
        pre'.length = k := by
  obtain ⟨pre,a,post,he,ha,hn⟩ := last_witness (fun a => firstAt a u = .pebble) xs
    (compute_action_exists h u hs hf)
  refine ⟨pre.length,pre,a,post,he,rfl,ha,hn,?_⟩
  intro pre' a' post' he' ha' hn'
  exact last_position_unique (fun a => firstAt a u = .pebble) pre' pre a' a post' post
    (he'.symm.trans he) ha' ha hn' hn
end EpochOrigin
#print axioms EpochOrigin.last_position_unique
#print axioms EpochOrigin.actual_unique_last_compute
