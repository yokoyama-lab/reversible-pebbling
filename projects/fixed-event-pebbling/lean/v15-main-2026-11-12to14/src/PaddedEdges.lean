import EdgeConcat
import PaddedStateSemantics
namespace ChainPaddedEdges
open ChainLocalEdges ChainGlobalEdgeCandidates ChainGlobalStateCandidates
open ChainPaddedStateSemantics ChainPrefixSetConcat ChainEdgeConcat

theorem range_edge (d t : Nat) (ht : t<d) : edgeAt d (List.range d) t=(List.range t,t) := by
  apply Prod.ext
  · change setOf d ((List.range d).take t)=List.range t
    rw [List.take_range,Nat.min_eq_left (by omega)]
    exact setOf_range d t (by omega)
  · simp [edgeAt,List.getD_eq_getElem?_getD,ht]

theorem embed_final (d n : Nat) : embedEdge d (List.range n,n)=(List.range (d+n),d+n) := by
  simp [embedEdge,embed,List.range_add,Nat.add_comm]

theorem padded_edge (d n : Nat) (u : List Nat) (hu : u.Perm (List.range n))
    (t : Nat) (ht : t<d+n+1) : edgeAt (d+n+1) (pad d n u) t=
      if t<d then (List.range t,t)
      else if t<d+n then embedEdge d (edgeAt n u (t-d))
      else (List.range (d+n),d+n) := by
  have hl : u.length=n := by simpa using hu.length_eq
  have hv : (u++[n]).length=n+1 := by simp [hl]
  have ho := edgeAt_concat d (n+1) (List.range d) (u++[n]) (List.Perm.refl _) hv t (by omega)
  have hlen : d+(n+1)=d+n+1 := by omega
  rw [hlen] at ho
  change edgeAt (d+n+1) (pad d n u) t=_ at ho
  rw [ho]
  by_cases hd : t<d
  · rw [if_pos hd,if_pos hd,range_edge d t hd]
  · rw [if_neg hd,if_neg hd]
    have hi := edgeAt_concat n 1 u [0] hu (by rfl) (t-d) (by omega)
    simp only [List.map_cons,List.map_nil,Nat.add_zero] at hi
    rw [hi]
    by_cases hn : t<d+n
    · rw [if_pos hn,if_pos (by omega)]
    · rw [if_neg hn,if_neg (by omega)]
      have he : t-d=n := by omega
      rw [he,Nat.sub_self]
      have hz : edgeAt 1 [0] 0=([],0) := by rfl
      rw [hz]
      have hz' : embedEdge n ([],0)=(List.range n,n) := by simp [embedEdge,embed]
      rw [hz',embed_final]
#print axioms padded_edge
end ChainPaddedEdges
