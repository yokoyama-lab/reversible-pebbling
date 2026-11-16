import ErasurePebbling.Basic

/- UNCOMPILED candidate. Target: Lean 4.31.0, repository commit
6a3bc99b3e84deda8912b59620843c39f5cbdbfe. No compilation or axiom audit
has been performed. Uses the actual IsPlay and MstarLe definitions. -/
namespace ErasurePebbling.NextBoundary
open RevPebbling.PebblingFoundations
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def seed : List Nat :=
  [0,1,2,3,2,4,1,5,4,6,0,7,6,4,5,0,4,1,0,2,3,0,2,1,0]

theorem seed_isPlay : IsPlay 8 4 0 seed := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · decide

theorem seed_length : seed.length = 25 := by decide

theorem seed_upper : MstarLe 8 4 0 25 :=
  ⟨seed, seed_isPlay, by decide⟩

theorem seed_upper_budget (e : Nat) : MstarLe 8 4 e 25 := by
  refine ⟨seed, ?_, by decide⟩
  exact ⟨seed_isPlay.bounds, seed_isPlay.legal, seed_isPlay.peak,
    Nat.le_trans seed_isPlay.budget (Nat.zero_le e), seed_isPlay.final⟩

#print axioms seed_isPlay
#print axioms seed_upper
#print axioms seed_upper_budget
end ErasurePebbling.NextBoundary
