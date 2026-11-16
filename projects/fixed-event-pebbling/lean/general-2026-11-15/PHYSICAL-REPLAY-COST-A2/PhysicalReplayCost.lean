import PhysicalReplayHeight
import SignatureSwapStd

/- Uncompiled finite candidate. Instrumentation is NEW; projection below,
   not definitional identification, connects it to the original replay. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate

/-- Sum physical board lengths AFTER successful steps. No initial-board term. -/
def replayWithCost (capacity : Bool) (events : List Event) (erasures : List Nat) :
    List Nat → List Nat → Option (List Nat × Int)
  | board, [] => some (board, 0)
  | board, i :: rest => do
      let event ← events[i]?
      let mid ← step capacity erasures board event
      let result ← replayWithCost capacity events erasures mid rest
      pure (result.1, (mid.length : Int) + result.2)

/-- Actual Option projection equals the original LocalCertificate.replay,
    including failure branches; this is not assumed as an interface axiom. -/
theorem replayWithCost_projection (capacity : Bool) (events : List Event)
    (erasures board ids : List Nat) :
    (replayWithCost capacity events erasures board ids).map Prod.fst =
      replay capacity events erasures board ids := by
  induction ids generalizing board with
  | nil => rfl
  | cons i rest ih =>
      cases he : events[i]? with
      | none => simp [replayWithCost, replay, he]
      | some e =>
          cases ht : step capacity erasures board e with
          | none => simp [replayWithCost, replay, he, ht]
          | some mid =>
              cases hr : replayWithCost capacity events erasures mid rest with
              | none =>
                  simpa [replayWithCost, replay, he, ht, hr] using ih mid
              | some result =>
                  simpa [replayWithCost, replay, he, ht, hr] using ih mid

/-- Each physical after-step length coincides with the mathematical updated
    height. The cost is exactly the existing concrete recursive cost function.
    Nodup and Perm are unnecessary: success supplies each actual step. -/
theorem successful_replayWithCost_cost (capacity : Bool) (events : List Event)
    (erasures board ids after : List Nat) (total : Int)
    (hs : replayWithCost capacity events erasures board ids = some (after, total)) :
    total = PebblingSignature.cost (eventIdIncrement events) (board.length : Int) ids := by
  induction ids generalizing board after total with
  | nil =>
      have hp : (board, (0 : Int)) = (after, total) := by
        simpa [replayWithCost] using hs
      cases hp
      rfl
  | cons i rest ih =>
      cases he : events[i]? with
      | none => simp [replayWithCost, he] at hs
      | some e =>
          cases ht : step capacity erasures board e with
          | none => simp [replayWithCost, he, ht] at hs
          | some mid =>
              cases hr : replayWithCost capacity events erasures mid rest with
              | none => simp [replayWithCost, he, ht, hr] at hs
              | some result =>
                  rcases result with ⟨final, subtotal⟩
                  have hp : (final, (mid.length : Int) + subtotal) = (after, total) := by
                    simpa [replayWithCost, he, ht, hr] using hs
                  have htail := ih mid final subtotal hr
                  cases hp
                  have hstep := successful_step_length_increment capacity erasures board mid e ht
                  have hw : eventIdIncrement events i = eventIncrement e := by
                    simp [eventIdIncrement, he]
                  simp only [PebblingSignature.cost, hw]
                  rw [← hstep]
                  exact congrArg (fun c : Int => (mid.length : Int) + c) htail

/-- Success of the original replay has an instrumented witness with the
    expected cumulative physical height, without postulating successful replay
    of a separate model. -/
theorem successful_replay_has_cost (capacity : Bool) (events : List Event)
    (erasures board ids after : List Nat)
    (hs : replay capacity events erasures board ids = some after) :
    replayWithCost capacity events erasures board ids =
      some (after, PebblingSignature.cost (eventIdIncrement events) (board.length : Int) ids) := by
  have hp := replayWithCost_projection capacity events erasures board ids
  cases hr : replayWithCost capacity events erasures board ids with
  | none => simp [hr, hs] at hp
  | some result =>
      rcases result with ⟨final, total⟩
      have hf : final = after := by simpa [hr, hs] using hp
      subst final
      have hc := successful_replayWithCost_cost capacity events erasures board ids after total hr
      simpa [hc] using hr

#print axioms replayWithCost_projection
#print axioms successful_replayWithCost_cost
#print axioms successful_replay_has_cost
end LocalCertificate
