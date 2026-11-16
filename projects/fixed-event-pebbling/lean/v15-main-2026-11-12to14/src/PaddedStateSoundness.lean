import PaddedStateSemantics
namespace ChainPaddedStateSemantics
open ChainPrefixSetConcat ChainGlobalStateCandidates ChainPrefixStates

theorem candidate_has_padded_prefix (d n : Nat) (words : List (List Nat))
    (nonempty : ∃u,u∈words) (perms : ∀u∈words,u.Perm (List.range n))
    (s : List Nat) (hs : s∈paddedHalf d (states n words)) :
    ∃u∈words, ∃t, t≤d+n ∧ setOf (d+n+1) ((pad d n u).take t)=s := by
  cases List.mem_append.mp hs with
  | inl h =>
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
    obtain ⟨u,hu⟩ := nonempty
    have htd := List.mem_range.mp ht
    refine ⟨u,hu,t,by omega,?_⟩
    rw [padded_prefix d n u (perms u hu) t (by omega),if_pos htd]
  | inr h =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    obtain ⟨u,hu,t,ht,he⟩ := (mem_states_iff n words a).mp ha
    have hl : u.length=n := by simpa using (perms u hu).length_eq
    refine ⟨u,hu,d+t,by omega,?_⟩
    rw [padded_prefix d n u (perms u hu) (d+t) (by omega),if_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact congrArg (embed d) he

#print axioms candidate_has_padded_prefix
end ChainPaddedStateSemantics
