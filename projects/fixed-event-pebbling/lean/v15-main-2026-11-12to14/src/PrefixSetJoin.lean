import PrefixSetConcat
import PaddedStateSemantics
namespace ChainPrefixSetConcat
open ChainGlobalStateCandidates ChainPaddedStateSemantics

theorem prefix_concat_eq (n m : Nat) (u v : List Nat)
    (hp : u.Perm (List.range n)) (t : Nat) :
    setOf (n+m) ((u ++ v.map (fun i=>n+i)).take t)=
      if t<n then setOf n (u.take t) else embed n (setOf m (v.take (t-n))) := by
  have hc := prefix_concat_cases n m u v hp t
  by_cases ht : t<n
  · rw [if_pos ht]
    cases hc with
    | inl h => exact h.2
    | inr h => omega
  · rw [if_neg ht]
    cases hc with
    | inr h => simpa [embed,Nat.add_comm] using h.2
    | inl h =>
      have he : t=n := by omega
      subst t
      rw [h.2]
      have hl : u.length=n := by simpa using hp.length_eq
      rw [List.take_of_length_le (by omega),setOf_full n u hp]
      have hz : setOf m []=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha; simp
      simp [embed,hz]
#print axioms prefix_concat_eq
end ChainPrefixSetConcat
