import ErasurePebbling.Additive
import Seed_UNCOMPILED

/- UNCOMPILED. Existing semantic API, no BFS soundness assumption. -/
namespace ErasurePebbling.NextBoundary
open RevPebbling.PebblingFoundations
open ErasurePebbling.Additive

/-- Entire p=4 upper-bound family via the existing additive theorem.
The length is 25+10e and the endpoint is 8+4e. No minimality claim. -/
theorem p4_upper (e : Nat) : MstarLe ((e + 2) * 4) 4 e (25 + e * 10) := by
  exact mstar_reach_le 4 e 25 9 (by decide) seed_upper
    ⟨_, play_4_3, by decide⟩

/-- General concatenation interface, abstracting away the binary endpoints
of mstar_reach_le. Initial and block plays must themselves be supplied. -/
theorem append_blocks (n0 m p e a b : Nat)
    (hn0 : 2 ≤ n0) (hm : 1 ≤ m) (hp : 2 ≤ p)
    (ha : MstarLe n0 p 0 a) (hb : MstarLe m (p - 1) 0 b) :
    MstarLe (n0 + e * m) p e (a + e * (b + 1)) := by
  obtain ⟨sA, hA, hAl⟩ := ha
  obtain ⟨sB, hB, hBl⟩ := hb
  have h0 := first_seg (n0 + e * m) n0 p sA (by omega) (by omega) hA
  have hend : n0 - 1 + e * m = (n0 + e * m) - 1 := by omega
  obtain ⟨t, ht⟩ := phases_seg' (n0 + e * m) p m sB hp hm hB e
    (n0 - 1) (by omega) (by omega)
  rw [hend] at ht
  have h := h0.append ht
  have h' := h.cast (blk_single_eq_target _ (by omega))
  refine ⟨_, ⟨h'.bounds, h'.legal, h'.peak,
    by rw [h'.eras, Nat.zero_add]; exact Nat.le_refl _, h'.exec⟩, ?_⟩
  rw [h'.len]
  exact Nat.add_le_add hAl (Nat.mul_le_mul_left e (Nat.add_le_add_right hBl 1))

#print axioms p4_upper
#print axioms append_blocks
end ErasurePebbling.NextBoundary
