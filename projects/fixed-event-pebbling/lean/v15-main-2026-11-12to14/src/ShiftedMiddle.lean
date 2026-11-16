import MiddleSegment
import MiddleDifference
import ReplayBridge
import FamilyArithmetic
namespace ShiftedMiddle
open LocalCertificate ReplayBridge ChainFamilyArithmetic

theorem step_erasure_congr (capacity : Bool) (erasures erasures' board : List Nat) (e : Event)
    (he : e.place = false → (e.vertex ∈ erasures ↔ e.vertex ∈ erasures')) :
    step capacity erasures board e = step capacity erasures' board e := by
  cases hp : e.place with
  | true => simp [step,hp]
  | false =>
    have hm := he hp
    have hc : erasures.contains e.vertex = erasures'.contains e.vertex := by simp [hm]
    simp [step,hp,hm]

theorem replay_erasure_congr (capacity : Bool) (events : List Event)
    (erasures erasures' board w : List Nat)
    (he : ∀ e ∈ events, e.place = false → (e.vertex ∈ erasures ↔ e.vertex ∈ erasures')) :
    replay capacity events erasures board w = replay capacity events erasures' board w := by
  induction w generalizing board with
  | nil => rfl
  | cons i rest ih =>
    cases hl : events[i]? with
    | none => simp [replay,hl]
    | some e =>
      have hs := step_erasure_congr capacity erasures erasures' board e
        (he e (List.mem_of_getElem? hl))
      simp only [replay,hl]
      change (step capacity erasures board e).bind (fun after => replay capacity events erasures after rest) =
        (step capacity erasures' board e).bind (fun after => replay capacity events erasures' after rest)
      rw [hs]
      cases ht : step capacity erasures' board e with
      | none => rfl
      | some after => exact ih after

theorem legal_erasure_congr (events : List Event) (initial final erasures erasures' w : List Nat)
    (he : ∀ e ∈ events, e.place = false → (e.vertex ∈ erasures ↔ e.vertex ∈ erasures')) :
    legal events initial final erasures w ↔ legal events initial final erasures' w := by
  unfold legal
  rw [replay_erasure_congr true events erasures erasures' initial w he]

theorem middle_away : ∀ e ∈ ChainMiddleSegment.events, 1 < e.vertex := by decide

theorem shifted_middle_factor (offset : Nat) (w : List Nat)
    (h : legal (shiftEvents offset ChainMiddleSegment.events)
      (shiftBoard offset ChainMiddleSegment.initial) (shiftBoard offset ChainMiddleSegment.final)
      (shiftBoard offset [5,11]) w) : ChainMiddleSegment.Good w := by
  have hb := (legal_shift_iff offset ChainMiddleSegment.events ChainMiddleSegment.initial
    ChainMiddleSegment.final [5,11] w middle_away).mp h
  exact ChainMiddleSegment.all_legal_factor w hb

theorem table_shift (j : Nat) :
    MiddleDifference.events (5+6*j) = shiftEvents (6*j) ChainMiddleSegment.events := by
  simp [MiddleDifference.events,shiftEvents,shiftEvent,ChainMiddleSegment.events,M.events,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] <;> omega

/-- Only erasure status of removals matters; an additional final anchor
at s+12 may be an erasure site without affecting its placement event. -/
theorem middle_erasure_sites (k j : Nat) (erasures : List Nat)
    (hj : j+1 < k) (hm : ∀ v, v ∈ erasures ↔ IsErasure k v) :
    ∀ e ∈ MiddleDifference.events (5+6*j), e.place = false →
      (e.vertex ∈ erasures ↔ e.vertex ∈ shiftBoard (6*j) [5,11]) := by
  have hreduce : ∀ v, 5+6*j ≤ v → v < 5+6*j+12 → v ≠ 5+6*j+6 →
      (v ∈ erasures ↔ v ∈ shiftBoard (6*j) [5,11]) := by
    intro v hlo hhi hne
    rw [hm]
    simp only [shiftBoard,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨i,hi,he⟩
      omega
    · intro h
      exact ⟨j,by omega,by omega⟩
  intro e he hp
  simp only [MiddleDifference.events,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst e <;>
    simp only at hp ⊢
  all_goals try { contradiction }
  all_goals apply hreduce <;> omega

#print axioms step_erasure_congr
#print axioms replay_erasure_congr
#print axioms legal_erasure_congr
#print axioms middle_away
#print axioms shifted_middle_factor
#print axioms table_shift
#print axioms middle_erasure_sites
theorem global_erasure_middle_factor (k j : Nat) (erasures w : List Nat)
    (hj : j+1 < k) (hm : ∀ v, v ∈ erasures ↔ IsErasure k v)
    (h : legal (MiddleDifference.events (5+6*j))
      (shiftBoard (6*j) ChainMiddleSegment.initial)
      (shiftBoard (6*j) ChainMiddleSegment.final) erasures w) : ChainMiddleSegment.Good w := by
  have hl := (legal_erasure_congr (MiddleDifference.events (5+6*j))
    (shiftBoard (6*j) ChainMiddleSegment.initial) (shiftBoard (6*j) ChainMiddleSegment.final)
    erasures (shiftBoard (6*j) [5,11]) w (middle_erasure_sites k j erasures hj hm)).mp h
  rw [table_shift j] at hl
  exact shifted_middle_factor (6*j) w hl
#print axioms global_erasure_middle_factor
end ShiftedMiddle
