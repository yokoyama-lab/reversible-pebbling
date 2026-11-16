import CanonicalDecode
namespace CanonicalSwap
open LocalCertificate ChainOccurrence

theorem order_swap (pre post : List Nat) (a b i j : Nat)
 (h : (pre++a::b::post).idxOf i < (pre++a::b::post).idxOf j)
 (hij : ¬(i=a ∧ j=b)) :
 (pre++b::a::post).idxOf i < (pre++b::a::post).idxOf j := by
 have hip : ∀x, x∈pre → pre.idxOf x<pre.length := fun _=>List.idxOf_lt_length_of_mem
 by_cases ip : i∈pre <;> by_cases jp : j∈pre <;>
 by_cases ia : a=i <;> by_cases ib : b=i <;>
 by_cases ja : a=j <;> by_cases jb : b=j <;>
 have hi := hip i <;> have hj := hip j <;>
 simp_all [List.idxOf_append,List.idxOf_cons,beq_iff_eq,cond_eq_ite] <;> try omega
 all_goals first | have hb := hip i ip; omega | have hb := hip j jp; omega

theorem canonical_swap (table : List Event) (pre post : List Nat) (a b : Fin table.length)
 (different : (table[a.val]).vertex ≠ (table[b.val]).vertex)
 (h : canonical table (pre++a.val::b.val::post)) :
 canonical table (pre++b.val::a.val::post) := by
 intro i j ij same
 apply order_swap pre post a.val b.val i.val j.val (h i j ij same)
 rintro ⟨ia,jb⟩
 apply different
 simpa [ia,jb] using same
#print axioms order_swap
#print axioms canonical_swap
end CanonicalSwap
