import LocalCertificate
set_option maxHeartbeats 800000
namespace ReplayBridge
open LocalCertificate

theorem replay_append (capacity : Bool) (events : List Event) (erasures board u v : List Nat) :
    replay capacity events erasures board (u ++ v) =
      (replay capacity events erasures board u).bind (fun after => replay capacity events erasures after v) := by
  induction u generalizing board with
  | nil => simp [replay]
  | cons e rest ih =>
    cases hLookup : events[e]? with
    | none => simp [replay, hLookup]
    | some event =>
      cases hStep : step capacity erasures board event with
      | none => simp [replay, hLookup, hStep]
      | some after => simp [replay, hLookup, hStep, ih]

theorem replay_append_success (capacity : Bool) (events : List Event)
    (erasures initial middle final u v : List Nat)
    (hu : replay capacity events erasures initial u = some middle)
    (hv : replay capacity events erasures middle v = some final) :
    replay capacity events erasures initial (u ++ v) = some final := by
  rw [replay_append, hu]
  exact hv

theorem replay_append_success_iff (capacity : Bool) (events : List Event)
    (erasures initial final u v : List Nat) :
    replay capacity events erasures initial (u ++ v) = some final ↔
    ∃ middle, replay capacity events erasures initial u = some middle ∧
      replay capacity events erasures middle v = some final := by
  rw [replay_append]
  cases hu : replay capacity events erasures initial u <;> simp

def shiftBoard (offset : Nat) (board : List Nat) : List Nat := board.map (· + offset)
def shiftEvent (offset : Nat) (event : Event) : Event := ⟨event.place, event.vertex + offset⟩
def shiftEvents (offset : Nat) (events : List Event) : List Event := events.map (shiftEvent offset)

theorem contains_shift (offset vertex : Nat) (board : List Nat) :
    (shiftBoard offset board).contains (vertex + offset) = board.contains vertex := by
  apply Bool.eq_iff_iff.mpr
  simp [shiftBoard]

theorem erase_shift (offset vertex : Nat) (board : List Nat) :
    (shiftBoard offset board).erase (vertex + offset) = shiftBoard offset (board.erase vertex) := by
  induction board with
  | nil => simp [shiftBoard]
  | cons b bs ih =>
    by_cases h : vertex = b
    · subst b; simp [shiftBoard]
    · have hne : b ≠ vertex := Ne.symm h
      have ih2 := ih
      unfold shiftBoard at ih2
      simp [shiftBoard, hne, ih2]

/-- Translation is valid away from the permanent-input exception vertex 1. -/
theorem step_shift (offset : Nat) (capacity : Bool) (erasures board : List Nat) (event : Event)
    (hAway : 1 < event.vertex) :
    step capacity (shiftBoard offset erasures) (shiftBoard offset board) (shiftEvent offset event) =
      (step capacity erasures board event).map (shiftBoard offset) := by
  have hv : event.vertex ≠ 1 := by omega
  have hvs : event.vertex + offset ≠ 1 := by omega
  have hpred : event.vertex + offset - 1 = (event.vertex - 1) + offset := by omega
  simp only [step, shiftEvent]
  simp only [show (event.vertex + offset == 1) = false by simp [hvs],
    show (event.vertex == 1) = false by simp [hv], Bool.false_or, hpred,
    contains_shift, erase_shift]
  cases event.place <;> simp [shiftBoard, apply_ite]
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals omega

theorem replay_shift (offset : Nat) (capacity : Bool) (events : List Event)
    (erasures board t : List Nat) (hAway : ∀ e ∈ events, 1 < e.vertex) :
    replay capacity (shiftEvents offset events) (shiftBoard offset erasures) (shiftBoard offset board) t =
      (replay capacity events erasures board t).map (shiftBoard offset) := by
  induction t generalizing board with
  | nil => simp [replay]
  | cons i rest ih =>
    cases hLookup : events[i]? with
    | none => simp [replay, shiftEvents, List.getElem?_map, hLookup]
    | some event =>
      have hVertex : 1 < event.vertex := hAway event (List.mem_of_getElem? hLookup)
      simp only [replay, shiftEvents, List.getElem?_map, hLookup, Option.map_some]
      change (step capacity (shiftBoard offset erasures) (shiftBoard offset board)
        (shiftEvent offset event)).bind (fun after =>
          replay capacity (shiftEvents offset events) (shiftBoard offset erasures) after rest) =
        ((step capacity erasures board event).bind (fun after => replay capacity events erasures after rest)).map (shiftBoard offset)
      rw [step_shift offset capacity erasures board event hVertex]
      cases hStep : step capacity erasures board event with
      | none => simp
      | some after => simp [ih]

theorem sameBoard_shift (offset : Nat) (a b : List Nat) :
    sameBoard (shiftBoard offset a) (shiftBoard offset b) = sameBoard a b := by
  unfold sameBoard
  have hla : (shiftBoard offset a).length = a.length := List.length_map _
  have hlb : (shiftBoard offset b).length = b.length := List.length_map _
  rw [hla, hlb]
  have hall : (shiftBoard offset a).all (fun x => (shiftBoard offset b).contains x) =
      a.all (fun x => b.contains x) := by
    change (a.map (· + offset)).all _ = _
    rw [List.all_map]
    congr 1
    funext x
    exact contains_shift offset x b
  rw [hall]

theorem legal_shift_iff (offset : Nat) (events : List Event)
    (initial final erasures t : List Nat) (hAway : ∀ e ∈ events, 1 < e.vertex) :
    legal (shiftEvents offset events) (shiftBoard offset initial) (shiftBoard offset final)
      (shiftBoard offset erasures) t ↔ legal events initial final erasures t := by
  unfold legal
  have hlen : (shiftEvents offset events).length = events.length := List.length_map _
  rw [hlen, replay_shift offset true events erasures initial t hAway]
  cases hReplay : replay true events erasures initial t with
  | none => simp
  | some after => simp [sameBoard_shift]

theorem M_away_from_permanent_input : ∀ e ∈ LocalCertificate.M.events, 1 < e.vertex := by decide

theorem M_legal_translate (offset : Nat) (t : List Nat) :
    legal (shiftEvents offset LocalCertificate.M.events)
      (shiftBoard offset LocalCertificate.M.initial) (shiftBoard offset LocalCertificate.M.final)
      (shiftBoard offset LocalCertificate.M.erasures) t ↔ LocalCertificate.M.Legal t := by
  exact legal_shift_iff offset LocalCertificate.M.events LocalCertificate.M.initial
    LocalCertificate.M.final LocalCertificate.M.erasures t M_away_from_permanent_input

/-- Without the away-from-1 hypothesis, translation need not preserve a step. -/
theorem permanent_input_counterexample :
    step true [] [] ⟨true, 1⟩ = some [1] ∧ step true [] [] ⟨true, 7⟩ = none := by decide

#print axioms replay_append
#print axioms replay_append_success
#print axioms replay_append_success_iff
#print axioms contains_shift
#print axioms erase_shift
#print axioms step_shift
#print axioms replay_shift
#print axioms sameBoard_shift
#print axioms legal_shift_iff
#print axioms M_away_from_permanent_input
#print axioms M_legal_translate
#print axioms permanent_input_counterexample
end ReplayBridge
