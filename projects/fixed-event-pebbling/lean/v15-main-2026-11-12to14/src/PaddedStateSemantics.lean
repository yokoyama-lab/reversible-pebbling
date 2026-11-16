import PrefixSetConcat
import GlobalStateCanonical
namespace ChainPaddedStateSemantics
open ChainPrefixSetConcat ChainGlobalStateCandidates ChainPrefixStates

def pad (d n : Nat) (u : List Nat) : List Nat :=
  List.range d ++ (u ++ [n]).map (fun i=>d+i)

theorem setOf_larger (n m : Nat) (u : List Nat) (hu : ∀a∈u,a<n) :
    setOf (n+m) u=setOf n u := by
  have h := setOf_concat n m u [] hu
  have hz : setOf m []=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha; simp
  simpa only [List.map_nil,List.append_nil,hz] using h

theorem setOf_range (n t : Nat) (h : t≤n) : setOf n (List.range t)=List.range t := by
  apply sublist_same_eq List.nodup_range List.filter_sublist (List.range_sublist.mpr h)
  intro x
  simp only [List.mem_filter,List.contains_iff_mem,List.mem_range]
  omega

theorem padded_prefix (d n : Nat) (u : List Nat) (hu : u.Perm (List.range n))
    (t : Nat) (ht : t≤d+n) :
    setOf (d+n+1) ((pad d n u).take t)=
      if t<d then List.range t else embed d (setOf n (u.take (t-d))) := by
  have hl : u.length=n := by simpa using hu.length_eq
  have hb : ∀a∈u,a<n := fun a ha => List.mem_range.mp (hu.mem_iff.mp ha)
  have hc := prefix_concat_cases d (n+1) (List.range d) (u++[n]) (List.Perm.refl _) t
  have he : d+(n+1)=d+n+1 := by omega
  rw [he] at hc
  by_cases htd : t<d
  · simp only [if_pos htd]
    cases hc with
    | inl h =>
      rw [show (pad d n u)=List.range d ++ (u++[n]).map (fun i=>d+i) from rfl,h.2]
      rw [List.take_range,Nat.min_eq_left (by omega)]
      exact setOf_range d t (by omega)
    | inr h => omega
  · simp only [if_neg htd]
    cases hc with
    | inl h =>
      have td : t=d := by omega
      subst t
      rw [show (pad d n u)=List.range d ++ (u++[n]).map (fun i=>d+i) from rfl,h.2]
      simp only [List.take_range,Nat.min_self,Nat.sub_self,List.take_zero]
      have hz : setOf n []=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha; simp
      rw [setOf_range d d (by omega),hz]
      simp [embed]
    | inr h =>
      rw [show (pad d n u)=List.range d ++ (u++[n]).map (fun i=>d+i) from rfl,h.2]
      rw [List.take_append_of_le_length (by omega)]
      rw [setOf_larger n 1 (u.take (t-d)) (fun a ha => hb a (List.mem_of_mem_take ha))]
      simp [embed,Nat.add_comm]

theorem padded_prefix_in_candidates (d n : Nat) (words : List (List Nat))
    (u : List Nat) (hw : u∈words) (hu : u.Perm (List.range n))
    (t : Nat) (ht : t≤d+n) :
    setOf (d+n+1) ((pad d n u).take t) ∈ paddedHalf d (states n words) := by
  rw [padded_prefix d n u hu t ht]
  by_cases htd : t<d
  · simp only [if_pos htd]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨t,List.mem_range.mpr htd,rfl⟩))
  · simp only [if_neg htd]
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨setOf n (u.take (t-d)),?_,rfl⟩
    apply (mem_states_iff n words _).mpr
    refine ⟨u,hw,t-d,?_,rfl⟩
    have hl : u.length=n := by simpa using hu.length_eq
    omega

#print axioms padded_prefix
#print axioms padded_prefix_in_candidates
end ChainPaddedStateSemantics
