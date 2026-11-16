import GlobalStateCandidates
namespace ChainGlobalStateCandidates
open ChainPrefixStates

theorem sublist_same_eq {α : Type} {u v all : List α}
    (hn : all.Nodup) (hu : u.Sublist all) (hv : v.Sublist all)
    (hm : ∀a,a∈u ↔ a∈v) : u=v := by
  induction hu generalizing v with
  | slnil =>
    cases hv
    rfl
  | @cons u all a hu ih =>
    have hn' := List.nodup_cons.mp hn
    cases hv with
    | cons _ hv => exact ih hn'.2 hv hm
    | cons_cons _ hv =>
      have ha : a∈u := (hm a).mpr (by simp)
      exact False.elim (hn'.1 (hu.subset ha))
  | @cons_cons u all a hu ih =>
    have hn' := List.nodup_cons.mp hn
    cases hv with
    | cons _ hv =>
      have ha : a∈_ := (hm a).mp (by simp)
      exact False.elim (hn'.1 (hv.subset ha))
    | @cons_cons v _ _ hv =>
      congr 1
      apply ih hn'.2 hv
      intro x
      have hna : a∉u := fun h => hn'.1 (hu.subset h)
      have hnb : a∉v := fun h => hn'.1 (hv.subset h)
      by_cases he : x=a
      · subst x; simp [hna,hnb]
      · simpa [List.mem_cons,he] using hm x

theorem state_sublist (n : Nat) (words : List (List Nat)) (s : List Nat)
    (hs : s∈states n words) : s.Sublist (List.range n) := by
  obtain ⟨w,hw,t,ht,rfl⟩ := (mem_states_iff n words s).mp hs
  exact List.filter_sublist

theorem embed_sublist (o n : Nat) (s : List Nat) (hs : s.Sublist (List.range n)) :
    (embed o s).Sublist (List.range (o+n)) := by
  rw [List.range_add]
  have hh := (List.Sublist.refl (List.range o)).append (hs.map (fun i=>o+i))
  simpa [embed,Nat.add_comm] using hh

theorem paddedHalf_sublist (d n : Nat) (ss : List (List Nat))
    (hs : ∀s∈ss,s.Sublist (List.range n)) (s : List Nat) (h : s∈paddedHalf d ss) :
    s.Sublist (List.range (d+n+1)) := by
  cases List.mem_append.mp h with
  | inl h =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    apply List.range_sublist.mpr
    have := List.mem_range.mp hi
    omega
  | inr h =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact (embed_sublist d n a (hs a ha)).trans (List.range_sublist.mpr (by omega))

theorem rest_sublist (r : Nat) (s : List Nat) (h : s∈rest r) :
    s.Sublist (List.range (16*r+8)) := by
  induction r generalizing s with
  | zero => exact state_sublist 8 _ s h
  | succ r ih =>
    cases List.mem_append.mp h with
    | inl h =>
      exact (paddedHalf_sublist 3 12 mStates (state_sublist 12 _) s h).trans
        (List.range_sublist.mpr (by omega))
    | inr h =>
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      have hh := embed_sublist 16 (16*r+8) a (ih a ha)
      simpa only [show 16 + (16*r+8)=16*(r+1)+8 by omega] using hh

theorem global_sublist (r : Nat) (s : List Nat) (h : s∈global r) :
    s.Sublist (List.range (25+16*r)) := by
  cases List.mem_append.mp h with
  | inl h =>
    exact (paddedHalf_sublist 6 10 iStates (state_sublist 10 _) s h).trans
      (List.range_sublist.mpr (by omega))
  | inr h =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have hh := embed_sublist 17 (16*r+8) a (rest_sublist r a ha)
    simpa only [show 17 + (16*r+8)=25+16*r by omega] using hh

theorem global_canonical (r : Nat) (s t : List Nat)
    (hs : s∈global r) (ht : t∈global r) (hm : ∀i,i∈s ↔ i∈t) : s=t :=
  sublist_same_eq List.nodup_range (global_sublist r s hs) (global_sublist r t ht) hm

#print axioms global_sublist
#print axioms global_canonical
end ChainGlobalStateCandidates
