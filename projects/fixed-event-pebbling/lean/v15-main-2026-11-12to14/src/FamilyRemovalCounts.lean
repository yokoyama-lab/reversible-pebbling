import TwoProjection
import FamilyArithmetic
namespace ChainFamilyRemovalCounts
open LocalCertificate ChainTrace ChainTwoLifetimeExact ChainUniqueLifetime ChainTwoProjection ChainFamilyArithmetic

theorem closed_two_placements_two_removals (erasures board final : List Nat)
    (es : List Event) (v : Nat) (nd : board.Nodup)
    (ia : v ∉ board) (fa : v ∉ final)
    (count : es.countP (isPlacement v) = 2)
    (hr : run erasures board es = some final) : es.countP (isRemoval v) = 2 := by
  obtain ⟨a,b,c,p,q,he,hp,hpv,hq,hqv⟩ := two_placements_split v es count
  subst es
  have budget : (a ++ p :: (b ++ q :: c)).countP (isPlacement v) ≤ 2 := by omega
  obtain ⟨ra,rb,rc⟩ := two_lifetimes_exact_gap_counts erasures board final v a b c p q
    nd ia fa hp hpv hq hqv budget hr
  simp [List.countP_append,isRemoval,hp,hq,ra,rb,rc]

theorem placement_count_one_or_two (v : Nat) : placementCount v = 1 ∨ placementCount v = 2 := by
  unfold placementCount
  split <;> simp_all <;> omega

theorem repeated_not_erasure (k v : Nat) (h : placementCount v = 2) : ¬ IsErasure k v := by
  rintro ⟨i,_,he⟩
  have hone := (block_placement_counts i).1
  rw [he] at h
  omega

#print axioms closed_two_placements_two_removals
#print axioms placement_count_one_or_two
#print axioms repeated_not_erasure
end ChainFamilyRemovalCounts
