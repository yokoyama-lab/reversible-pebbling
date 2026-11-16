import PaddedEdges
import ConcreteStateFamilies
namespace ChainEdgeFamily
open ChainLocalEdges ChainGlobalEdgeCandidates ChainEdgeConcat ChainPaddedEdges
open ChainStateFamilyJoin ChainConcreteStateFamilies ChainPaddedStateSemantics

structure Family (n : Nat) (L : Language) (es : List Edge) : Prop where
  perms : ∀w,L w → w.Perm (List.range n)
  nonempty : ∃w,L w
  sound : ∀e∈es,∃w,L w ∧ ∃t,t<n ∧ edgeAt n w t=e
  complete : ∀w,L w → ∀t,t<n → edgeAt n w t∈es

theorem joined_family (n m : Nat) (L R : Language) (es fs : List Edge)
    (hl : Family n L es) (hr : Family m R fs) :
    Family (n+m) (joined n L R) (es ++ fs.map (embedEdge n)) := by
  constructor
  · rintro w ⟨u,v,hu,hv,rfl⟩
    have hp := (hl.perms u hu).append ((hr.perms v hv).map (fun i=>n+i))
    simpa only [List.range_add] using hp
  · obtain ⟨u,hu⟩ := hl.nonempty; obtain ⟨v,hv⟩ := hr.nonempty
    exact ⟨_,u,v,hu,hv,rfl⟩
  · intro e he
    cases List.mem_append.mp he with
    | inl h =>
      obtain ⟨u,hu,t,ht,he⟩ := hl.sound e h
      obtain ⟨v,hv⟩ := hr.nonempty
      have hvl : v.length=m := by simpa using (hr.perms v hv).length_eq
      refine ⟨_,⟨u,v,hu,hv,rfl⟩,t,by omega,?_⟩
      rw [edgeAt_concat n m u v (hl.perms u hu) hvl t (by omega),if_pos ht,he]
    | inr h =>
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      obtain ⟨v,hv,t,ht,he⟩ := hr.sound a ha
      obtain ⟨u,hu⟩ := hl.nonempty
      have hvl : v.length=m := by simpa using (hr.perms v hv).length_eq
      refine ⟨_,⟨u,v,hu,hv,rfl⟩,n+t,by omega,?_⟩
      rw [edgeAt_concat n m u v (hl.perms u hu) hvl (n+t) (by omega),if_neg (by omega)]
      simp only [Nat.add_sub_cancel_left,he]
  · rintro w ⟨u,v,hu,hv,rfl⟩ t ht
    have hvl : v.length=m := by simpa using (hr.perms v hv).length_eq
    rw [edgeAt_concat n m u v (hl.perms u hu) hvl t ht]
    by_cases htn : t<n
    · rw [if_pos htn]; exact List.mem_append.mpr (Or.inl (hl.complete u hu t htn))
    · rw [if_neg htn]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_,hr.complete v hv (t-n) (by omega),rfl⟩))

theorem padded_family (d n : Nat) (L : Language) (words : List (List Nat))
    (equiv : ∀w,w∈words ↔ L w) (perms : ∀w,L w → w.Perm (List.range n))
    (nonempty : ∃w,L w) :
    Family (d+n+1) (blockL d n L) (paddingEdges d n (edges n words)) := by
  constructor
  · rintro w ⟨u,hu,rfl⟩; exact pad_permutation d n u (perms u hu)
  · obtain ⟨u,hu⟩ := nonempty; exact ⟨_,u,hu,rfl⟩
  · intro e he
    simp only [paddingEdges,List.mem_append,List.mem_singleton] at he
    rcases he with (h|h)|h
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      obtain ⟨u,hu⟩ := nonempty
      have htd := List.mem_range.mp ht
      refine ⟨_,⟨u,hu,rfl⟩,t,by omega,?_⟩
      rw [padded_edge d n u (perms u hu) t (by omega),if_pos htd]
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      obtain ⟨u,hu,t,ht,he⟩ := (mem_edges_iff n words a).mp ha
      have hul := (equiv u).mp hu
      have hlen : u.length=n := by simpa using (perms u hul).length_eq
      refine ⟨_,⟨u,hul,rfl⟩,d+t,by omega,?_⟩
      rw [padded_edge d n u (perms u hul) (d+t) (by omega),if_neg (by omega),if_pos (by omega)]
      simp only [Nat.add_sub_cancel_left,he]
    · subst e
      obtain ⟨u,hu⟩ := nonempty
      refine ⟨_,⟨u,hu,rfl⟩,d+n,by omega,?_⟩
      rw [padded_edge d n u (perms u hu) (d+n) (by omega),if_neg (by omega),if_neg (by omega)]
  · rintro w ⟨u,hu,rfl⟩ t ht
    rw [padded_edge d n u (perms u hu) t ht]
    by_cases hd : t<d
    · rw [if_pos hd]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨t,List.mem_range.mpr hd,rfl⟩))))
    · rw [if_neg hd]
      by_cases hn : t<d+n
      · rw [if_pos hn]
        apply List.mem_append.mpr; apply Or.inl; apply List.mem_append.mpr; apply Or.inr
        apply List.mem_map.mpr
        refine ⟨edgeAt n u (t-d),?_,rfl⟩
        have hlen : u.length=n := by simpa using (perms u hu).length_eq
        exact (mem_edges_iff n words _).mpr ⟨u,(equiv u).mpr hu,t-d,by omega,rfl⟩
      · rw [if_neg hn]
        exact List.mem_append.mpr (Or.inr (by simp))
#print axioms joined_family
#print axioms padded_family
end ChainEdgeFamily
