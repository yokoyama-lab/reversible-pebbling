import EventEncoding
import EnumerationCorrectness
namespace ChainDecodedPerm
open LocalCertificate ChainTrace
 def lookup (table : List Event) (i : Nat) : Event := (table[i]?).getD ⟨false,0⟩
 theorem decode_map (table : List Event) (w : List Nat) (es : List Event)
   (h : decodeTrace table w = some es) : es = w.map (lookup table) := by
   induction w generalizing es with
   | nil => simpa [decodeTrace] using h.symm
   | cons i w ih =>
     cases he : table[i]? with
     | none => simp [decodeTrace,he] at h
     | some e =>
       cases ht : decodeTrace table w with
       | none => simp [decodeTrace,he,ht] at h
       | some tail =>
         have hs : es=e::tail := by simpa [decodeTrace,he,ht] using h.symm
         rw [hs,ih tail ht]
         simp [lookup,he]
 theorem range_lookup (table : List Event) : (List.range table.length).map (lookup table) = table := by
   apply List.ext_getElem
   · simp
   · intro i h1 h2
     simp [lookup,List.getElem?_eq_getElem h2]
 theorem decode_perm (table : List Event) (w : List Nat) (es : List Event)
   (hp : isPermutation table.length w) (hd : decodeTrace table w = some es) : es.Perm table := by
   rw [decode_map table w es hd]
   have h := ((EnumerationCorrectness.isPermutation_iff_perm_range table.length w).mp hp).map (lookup table)
   rw [range_lookup] at h
   exact h
 theorem decode_legal_perm (table : List Event) (initial final erasures w : List Nat) (es : List Event)
   (hl : legal table initial final erasures w) (hd : decodeTrace table w = some es) : es.Perm table :=
   decode_perm table w es hl.1 hd
#print axioms decode_map
#print axioms range_lookup
#print axioms decode_perm
#print axioms decode_legal_perm
end ChainDecodedPerm
