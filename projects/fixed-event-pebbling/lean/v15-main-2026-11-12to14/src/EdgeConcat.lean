import GlobalEdgeCandidates
import PrefixSetJoin
namespace ChainEdgeConcat
open ChainLocalEdges ChainGlobalEdgeCandidates ChainPrefixSetConcat

theorem edgeAt_concat (n m : Nat) (u v : List Nat)
    (hu : u.Perm (List.range n)) (hv : v.length=m) (t : Nat) (ht : t<n+m) :
    edgeAt (n+m) (u++v.map (fun i=>n+i)) t=
      if t<n then edgeAt n u t else embedEdge n (edgeAt m v (t-n)) := by
  have hl : u.length=n := by simpa using hu.length_eq
  by_cases htn : t<n
  · rw [if_pos htn]
    apply Prod.ext
    · exact (prefix_concat_eq n m u v hu t).trans (if_pos htn)
    · change (u++v.map (fun i=>n+i)).getD t 0=u.getD t 0
      have htu : t<u.length := by omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left htu]
  · rw [if_neg htn]
    apply Prod.ext
    · exact (prefix_concat_eq n m u v hu t).trans (if_neg htn)
    · change (u++v.map (fun i=>n+i)).getD t 0=v.getD (t-n) 0+n
      have htv : t-n<v.length := by omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right (show u.length≤t by omega),
        hl,htv,Nat.add_comm]
#print axioms edgeAt_concat
end ChainEdgeConcat
