import SegmentDifference
import FamilyArithmetic
namespace MiddleDifference
open LocalCertificate ChainFamilyArithmetic SegmentDifference

def prefixP (s v : Nat) : Nat := if v < s then placementCount v else if v ≤ s+6 then 1 else 0
def prefixR (s v : Nat) : Nat := if v < s then placementCount v else if v=s+1 ∨ v=s+3 then 1 else 0

def events (s : Nat) : List Event :=
  [⟨false,s+5⟩,⟨true,s+3⟩,⟨false,s+4⟩,
   ⟨false,s⟩,⟨true,s+1⟩,⟨false,s+1⟩,⟨false,s+2⟩,⟨false,s+3⟩,
   ⟨true,s+7⟩,⟨false,s+7⟩,⟨true,s+8⟩,⟨true,s+9⟩,⟨false,s+9⟩,
   ⟨true,s+10⟩,⟨true,s+11⟩,⟨true,s+12⟩]

theorem middle_count_difference (j v : Nat) :
    prefixP (5+6*j+6) v = prefixP (5+6*j) v + (events (5+6*j)).countP (P v) ∧
    prefixR (5+6*j+6) v = prefixR (5+6*j) v + (events (5+6*j)).countP (R v) := by
  let s := 5+6*j
  change prefixP (s+6) v = prefixP s v + (events s).countP (P v) ∧
    prefixR (s+6) v = prefixR s v + (events s).countP (R v)
  by_cases hlo : v < s
  · have hn : ∀ d, d ≤ 12 → s+d ≠ v := by intro d hd; omega
    simp [prefixP,prefixR,hlo,show v<s+6 by omega,events,P,R,
      RemovalOrder.isPlacement,ChainUniqueLifetime.isRemoval,hn,show s≠v by omega]
  · by_cases hhi : s+12 < v
    · have hn : ∀ d, d ≤ 12 → s+d ≠ v := by intro d hd; omega
      simp [prefixP,prefixR,show ¬v<s by omega,show ¬v<s+6 by omega,
        show ¬v≤s+6 by omega,show ¬v≤s+6+6 by omega,
        show v≠s+1 by omega,show v≠s+3 by omega,show v≠s+6+1 by omega,
        show v≠s+6+3 by omega,events,P,R,RemovalOrder.isPlacement,ChainUniqueLifetime.isRemoval,hn,show s≠v by omega]
    · have hcases : v=s ∨ v=s+1 ∨ v=s+2 ∨ v=s+3 ∨ v=s+4 ∨ v=s+5 ∨ v=s+6 ∨
        v=s+7 ∨ v=s+8 ∨ v=s+9 ∨ v=s+10 ∨ v=s+11 ∨ v=s+12 := by omega
      rcases hcases with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst v <;>
        simp [prefixP,prefixR,events,P,R,RemovalOrder.isPlacement,ChainUniqueLifetime.isRemoval,
          s,placementCount,Nat.add_mod] <;> (repeat (first | omega | split))
#print axioms middle_count_difference
theorem events_nodup (s : Nat) : (events s).Nodup := by
  simp [events,List.nodup_cons]

theorem interval_perm_from_cut_differences (j : Nat) (pre interval : List Event)
    (hp : ∀ v, (pre ++ interval).countP (P v) + prefixP (5+6*j) v =
      pre.countP (P v) + prefixP (5+6*j+6) v)
    (hr : ∀ v, (pre ++ interval).countP (R v) + prefixR (5+6*j) v =
      pre.countP (R v) + prefixR (5+6*j+6) v) :
    interval.Perm (events (5+6*j)) := by
  apply segment_perm_of_prefix_differences pre interval (events (5+6*j))
  · intro v
    have h := hp v
    have hd := (middle_count_difference j v).1
    omega
  · intro v
    have h := hr v
    have hd := (middle_count_difference j v).2
    omega
#print axioms events_nodup
#print axioms interval_perm_from_cut_differences
end MiddleDifference
