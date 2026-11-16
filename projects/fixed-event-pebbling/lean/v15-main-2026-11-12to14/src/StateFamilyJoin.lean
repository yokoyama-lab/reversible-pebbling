import PrefixSetJoin
namespace ChainStateFamilyJoin
open ChainPrefixSetConcat ChainGlobalStateCandidates
abbrev Language := List Nat → Prop
structure Half (n : Nat) (L : Language) (ss : List (List Nat)) : Prop where
  perms : ∀w,L w → w.Perm (List.range n)
  nonempty : ∃w,L w
  sound : ∀s∈ss,∃w,L w ∧ ∃t,t<n ∧ setOf n (w.take t)=s
  complete : ∀w,L w → ∀t,t<n → setOf n (w.take t)∈ss
structure Full (n : Nat) (L : Language) (ss : List (List Nat)) : Prop where
  perms : ∀w,L w → w.Perm (List.range n)
  nonempty : ∃w,L w
  sound : ∀s∈ss,∃w,L w ∧ ∃t,t≤n ∧ setOf n (w.take t)=s
  complete : ∀w,L w → ∀t,t≤n → setOf n (w.take t)∈ss

def joined (n : Nat) (L R : Language) : Language :=
  fun w => ∃u v,L u ∧ R v ∧ w=u++v.map (fun i=>n+i)

theorem joined_full (n m : Nat) (L R : Language) (ss tt : List (List Nat))
    (hl : Half n L ss) (hr : Full m R tt) :
    Full (n+m) (joined n L R) (ss ++ tt.map (embed n)) := by
  constructor
  · rintro w ⟨u,v,hu,hv,rfl⟩
    have hp := (hl.perms u hu).append ((hr.perms v hv).map (fun i=>n+i))
    simpa only [List.range_add] using hp
  · obtain ⟨u,hu⟩ := hl.nonempty
    obtain ⟨v,hv⟩ := hr.nonempty
    exact ⟨_,u,v,hu,hv,rfl⟩
  · intro s hs
    cases List.mem_append.mp hs with
    | inl h =>
      obtain ⟨u,hu,t,ht,he⟩ := hl.sound s h
      obtain ⟨v,hv⟩ := hr.nonempty
      refine ⟨_,⟨u,v,hu,hv,rfl⟩,t,by omega,?_⟩
      rw [prefix_concat_eq n m u v (hl.perms u hu) t,if_pos ht,he]
    | inr h =>
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      obtain ⟨v,hv,t,ht,he⟩ := hr.sound a ha
      obtain ⟨u,hu⟩ := hl.nonempty
      refine ⟨_,⟨u,v,hu,hv,rfl⟩,n+t,by omega,?_⟩
      rw [prefix_concat_eq n m u v (hl.perms u hu) (n+t),if_neg (by omega)]
      simpa only [Nat.add_sub_cancel_left,he]
  · rintro w ⟨u,v,hu,hv,rfl⟩ t ht
    rw [prefix_concat_eq n m u v (hl.perms u hu) t]
    by_cases htn : t<n
    · rw [if_pos htn]
      exact List.mem_append.mpr (Or.inl (hl.complete u hu t htn))
    · rw [if_neg htn]
      apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨_,hr.complete v hv (t-n) (by omega),rfl⟩)
#print axioms joined_full
end ChainStateFamilyJoin
