import RawSwapGraph
namespace RawSwapGraph
open LocalCertificate ChainTrace

theorem decode_cons {table i xs a tail}
 (h : decodeTrace table (i::xs)=some (a::tail)) : table[i]?=some a ∧ decodeTrace table xs=some tail := by
 cases hi : table[i]? with
 | none => simp [decodeTrace,hi] at h
 | some b =>
  cases ht : decodeTrace table xs with
  | none => simp [decodeTrace,hi,ht] at h
  | some t =>
   have eq : b::t=a::tail := by simpa [decodeTrace,hi,ht] using h
   exact ⟨congrArg some (List.cons.inj eq).1,congrArg some (List.cons.inj eq).2⟩
theorem decode_swap_split (table : List Event) (u : List Nat) (pre : List Event) (a b : Event) (post : List Event)
 (h : decodeTrace table u=some (pre++a::b::post)) :
 ∃p i j s,u=p++i::j::s ∧ decodeTrace table p=some pre ∧ table[i]?=some a ∧ table[j]?=some b ∧ decodeTrace table s=some post := by
 induction pre generalizing u with
 | nil =>
  cases u with
  | nil => simp [decodeTrace] at h
  | cons i xs =>
   have hi := decode_cons h
   cases xs with
   | nil => simp [decodeTrace] at hi
   | cons j s =>
    have hj := decode_cons hi.2
    exact ⟨[],i,j,s,rfl,rfl,hi.1,hj.1,hj.2⟩
 | cons a' pre ih =>
  cases u with
  | nil => simp [decodeTrace] at h
  | cons i xs =>
   have hi := decode_cons h
   obtain ⟨p,j,k,s,eq,dp,dj,dk,ds⟩ := ih xs hi.2
   refine ⟨i::p,j,k,s,by simp [eq],?_,dj,dk,ds⟩
   simp [decodeTrace,hi.1,dp]

theorem decode_append {table u v ru rv} (du : decodeTrace table u=some ru) (dv : decodeTrace table v=some rv) :
 decodeTrace table (u++v)=some (ru++rv) := by
 induction u generalizing ru with
 | nil => have eq : []=ru := by simpa [decodeTrace] using du
          subst ru;simpa using dv
 | cons i xs ih =>
  cases hi : table[i]? with
  | none => simp [decodeTrace,hi] at du
  | some a =>
   cases hx : decodeTrace table xs with
   | none => simp [decodeTrace,hi,hx] at du
   | some tail =>
    have eq : a::tail=ru := by simpa [decodeTrace,hi,hx] using du
    subst ru
    simp [decodeTrace,hi,ih hx]

theorem decode_swapped {table p i j s pre a b post}
 (dp : decodeTrace table p=some pre) (di : table[i]?=some a) (dj : table[j]?=some b) (ds : decodeTrace table s=some post) :
 decodeTrace table (p++j::i::s)=some (pre++b::a::post) := by
 apply decode_append dp
 simp [decodeTrace,di,dj,ds]
#print axioms decode_swap_split
#print axioms decode_swapped
end RawSwapGraph
