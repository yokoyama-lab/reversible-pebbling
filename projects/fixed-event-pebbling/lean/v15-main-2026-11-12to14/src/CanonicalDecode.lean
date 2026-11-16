import OccurrenceOrder
namespace ChainOccurrence
open LocalCertificate ChainTrace

def orderedPresent (table : List Event) (w : List Nat) : Prop :=
  ∀ i∈w, ∀ j∈w, i<j → ∀ a b,
    table[i]?=some a → table[j]?=some b → a.vertex=b.vertex →
    w.idxOf i < w.idxOf j

theorem canonical_ordered (table : List Event) (w : List Nat)
    (h : canonical table w) : orderedPresent table w := by
  intro i hi j hj hij a b ha hb he
  obtain ⟨ib,ia⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨jb,ja⟩ := List.getElem?_eq_some_iff.mp hb
  exact h ⟨i,ib⟩ ⟨j,jb⟩ hij (by simpa [ia,ja] using he)

theorem ordered_tail (table : List Event) (i : Nat) (xs : List Nat)
    (nd : (i::xs).Nodup) (h : orderedPresent table (i::xs)) :
    orderedPresent table xs := by
  intro a ha b hb hab ea eb hea heb hev
  have hn := (List.nodup_cons.mp nd).1
  have na : i≠a := by intro he; subst a; exact hn ha
  have nb : i≠b := by intro he; subst b; exact hn hb
  have hh := h a (by simp [ha]) b (by simp [hb]) hab ea eb hea heb hev
  simp only [List.idxOf_cons,beq_false_of_ne na,beq_false_of_ne nb,Bool.false_eq_true,
    cond_false] at hh
  omega

theorem ordered_decode_injective (table : List Event) (xs ys : List Nat) (raw : List Event)
    (perm : xs.Perm ys) (nd : xs.Nodup)
    (ox : orderedPresent table xs) (oy : orderedPresent table ys)
    (dx : decodeTrace table xs=some raw) (dy : decodeTrace table ys=some raw) :
    xs=ys := by
  induction xs generalizing ys raw with
  | nil =>
    have he : ys=[] := List.eq_nil_of_length_eq_zero (by have := perm.length_eq; simpa using this.symm)
    exact he.symm
  | cons i xs ih =>
    cases ys with
    | nil => have := perm.length_eq; simp at this
    | cons j ys =>
      have ndy : (j::ys).Nodup := perm.nodup_iff.mp nd
      cases hix : table[i]? with
      | none => simp [decodeTrace,hix] at dx
      | some ei =>
        cases hiy : table[j]? with
        | none => simp [decodeTrace,hiy] at dy
        | some ej =>
          cases htx : decodeTrace table xs with
          | none => simp [decodeTrace,hix,htx] at dx
          | some rx =>
            cases hty : decodeTrace table ys with
            | none => simp [decodeTrace,hiy,hty] at dy
            | some ry =>
              have ex : ei::rx=raw := by simpa [decodeTrace,hix,htx] using dx
              have ey : ej::ry=raw := by simpa [decodeTrace,hiy,hty] using dy
              have eqs := List.cons.inj (ex.trans ey.symm)
              have ij : i=j := by
                have imy : i∈j::ys := perm.mem_iff.mp (by simp)
                have jmx : j∈i::xs := perm.mem_iff.mpr (by simp)
                by_cases hlt : i<j
                · have h := oy i imy j (by simp) hlt ei ej hix hiy (by rw [eqs.1])
                  simp at h
                · by_cases hgt : j<i
                  · have h := ox j jmx i (by simp) hgt ej ei hiy hix (by rw [eqs.1])
                    simp at h
                  · omega
              subst j
              have pp := perm.cons_inv
              have rr : rx=ry := eqs.2
              have tails := ih ys rx pp (List.nodup_cons.mp nd).2
                (ordered_tail table i xs nd ox) (ordered_tail table i ys ndy oy)
                htx (by rw [rr]; exact hty)
              exact congrArg (List.cons i) tails

theorem canonical_decode_injective (table : List Event) (xs ys : List Nat)
    (px : isPermutation table.length xs) (py : isPermutation table.length ys)
    (cx : canonical table xs) (cy : canonical table ys)
    (raw : List Event) (dx : decodeTrace table xs=some raw) (dy : decodeTrace table ys=some raw) :
    xs=ys := by
  have xp := (EnumerationCorrectness.isPermutation_iff_perm_range table.length xs).mp px
  have yp := (EnumerationCorrectness.isPermutation_iff_perm_range table.length ys).mp py
  exact ordered_decode_injective table xs ys raw (xp.trans yp.symm) px.2.1
    (canonical_ordered table xs cx) (canonical_ordered table ys cy) dx dy

theorem labelled_decode_injective (r : Nat) (E xs ys : List Nat)
    (hx : labelledLegal r E xs) (hy : labelledLegal r E ys)
    (he : decodeTrace (ChainAssembledTrace.fullTable r) xs =
      decodeTrace (ChainAssembledTrace.fullTable r) ys) : xs=ys := by
  obtain ⟨raw,dx,hr⟩ := hx.2.2
  exact canonical_decode_injective _ xs ys hx.1 hy.1 hx.2.1 hy.2.1 raw dx
    (he.symm.trans dx)

#print axioms labelled_decode_injective
#print axioms canonical_ordered
#print axioms ordered_tail
#print axioms ordered_decode_injective
#print axioms canonical_decode_injective
end ChainOccurrence
