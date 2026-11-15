import Std
namespace EpochOverlap
/-- Every previously referenced child-epoch precedes every current child-epoch. -/
def Ordered (old fresh : List Nat) : Prop :=
  ∀ x ∈ old, ∀ y ∈ fresh, x ≤ y

theorem shared_unique {old fresh : List Nat} (h : Ordered old fresh)
    {x y : Nat} (xo : x ∈ old) (xf : x ∈ fresh)
    (yo : y ∈ old) (yf : y ∈ fresh) : x = y := by
  have hxy := h x xo y yf
  have hyx := h y yo x xf
  omega

/-- Any duplicate-free list representing the intersection has at most one element.
The chronological ordering assumption remains explicit. -/
theorem overlap_card_le_one {old fresh shared : List Nat}
    (h : Ordered old fresh) (hn : shared.Nodup)
    (ho : shared ⊆ old) (hf : shared ⊆ fresh) : shared.length ≤ 1 := by
  cases shared with
  | nil => simp
  | cons x xs =>
    have hs : (x :: xs) ⊆ [x] := by
      intro y hy
      have he : y = x := shared_unique h (ho hy) (hf hy)
        (ho (by simp)) (hf (by simp))
      simp [he]
    have hl := hn.length_le_of_subset hs
    simpa using hl

/-- Arithmetic accumulation of one charged reuse for every noninitial epoch.
Inputs are per-epoch cardinalities of shared references, not event multiplicities. -/
theorem sum_reuse_le_count (costs : List Nat)
    (h : ∀ c ∈ costs, c ≤ 1) : costs.sum ≤ costs.length := by
  induction costs with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≤ 1 := h c (by simp)
    have ht : ∀ x ∈ cs, x ≤ 1 := by
      intro x hx
      exact h x (by simp [hx])
    have hh := ih ht
    simp only [List.sum_cons, List.length_cons]
    omega

/-- Initial epoch contributes zero reuse; q counts all represented epochs. -/
theorem noninitial_reuse_le (costs : List Nat) (q : Nat)
    (h : ∀ c ∈ costs, c ≤ 1) (hq : costs.length + 1 ≤ q) :
    costs.sum ≤ q - 1 := by
  have hs := sum_reuse_le_count costs h
  omega
end EpochOverlap
#print axioms EpochOverlap.shared_unique
#print axioms EpochOverlap.overlap_card_le_one
#print axioms EpochOverlap.sum_reuse_le_count
#print axioms EpochOverlap.noninitial_reuse_le
