import EnumerationCorrectness
namespace ExtensionCompleteness
open UpperCertificate LocalCertificate

def RespectsFrom (preds : List (List Nat)) (remaining t : List Nat) : Prop :=
  ∀ e ∈ t, ∀ p ∈ preds.getD e [], p ∈ remaining → t.idxOf p < t.idxOf e

theorem extensions_complete (preds : List (List Nat)) (fuel : Nat)
    (remaining t : List Nat) (hn : remaining.Nodup)
    (hp : t.Perm remaining) (hl : t.length = fuel)
    (hr : RespectsFrom preds remaining t) :
    t ∈ enumerateExtensions preds fuel remaining := by
  induction fuel generalizing remaining t with
  | zero =>
    have ht : t = [] := List.length_eq_zero_iff.mp hl
    subst t
    have he := hp.nil_eq
    subst remaining
    simp [enumerateExtensions]
  | succ fuel ih =>
    cases t with
    | nil => simp at hl
    | cons e t =>
      have hp' := List.cons_perm_iff_perm_erase.mp hp
      have htn := List.nodup_cons.mp (hp.symm.nodup hn)
      have enabled : (preds.getD e []).all (fun p => !(remaining.contains p)) = true := by
        apply List.all_eq_true.mpr
        intro p hpred
        have hnot : p ∉ remaining := by
          intro hmem
          have h := hr e (by simp) p hpred hmem
          simp at h
        simpa using hnot
      have hrt : RespectsFrom preds (remaining.erase e) t := by
        intro a ha p hpred hmem
        have hpa := (hn.mem_erase_iff.mp hmem).1
        have hae : a ≠ e := by
          intro h; subst a; exact htn.1 ha
        have h := hr a (by simp [ha]) p hpred (List.mem_of_mem_erase hmem)
        simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq] at h
        split at h <;> split at h <;> omega
      have ht := ih (remaining.erase e) t (hn.erase e) hp'.2 (by simpa using hl) hrt
      simp only [enumerateExtensions, List.mem_flatMap]
      refine ⟨e, hp'.1, ?_⟩
      rw [if_pos enabled]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩

theorem satisfies_enumerated (preds : List (List Nat)) (t : List Nat)
    (hp : isPermutation preds.length t)
    (hs : satisfiesPredecessors preds t = true) :
    t ∈ enumerateExtensions preds preds.length (List.range preds.length) := by
  apply extensions_complete preds preds.length (List.range preds.length) t List.nodup_range
    ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hp) hp.1
  intro e he p hpred hmem
  have hae := hp.2.2 e he
  have h1 := List.all_eq_true.mp hs e (List.mem_range.mpr hae)
  have h2 := List.all_eq_true.mp h1 p hpred
  simpa using h2

#print axioms extensions_complete
#print axioms satisfies_enumerated


def predecessorRelation (preds : List (List Nat)) (a b : Fin preds.length) : Prop :=
  a.val ∈ preds.getD b.val []

theorem extends_enumerated (preds : List (List Nat)) (t : List Nat)
    (valid : ∀ e, e < preds.length → ∀ p ∈ preds.getD e [], p < preds.length)
    (h : ErasureCover.Extends (semantics preds.length) (predecessorRelation preds) t) :
    t ∈ enumerateExtensions preds preds.length (List.range preds.length) := by
  apply satisfies_enumerated preds t h.1
  apply List.all_eq_true.mpr
  intro e he
  apply List.all_eq_true.mpr
  intro p hp
  have he' := List.mem_range.mp he
  have hp' := valid e he' p hp
  have ord := h.2 (⟨p,hp'⟩ : Fin preds.length) (⟨e,he'⟩ : Fin preds.length) hp
  simpa [semantics] using ord

theorem strict_poset_predecessors_valid (preds : List (List Nat))
    (h : strictPoset preds.length preds = true) :
    ∀ e, e < preds.length → ∀ p ∈ preds.getD e [], p < preds.length := by
  simp only [strictPoset, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  intro e he p hp
  exact ((h.2 e (List.mem_range.mpr he)).2 p hp).1

theorem strict_poset_extends_enumerated (preds : List (List Nat)) (t : List Nat)
    (hp : strictPoset preds.length preds = true)
    (ht : ErasureCover.Extends (semantics preds.length) (predecessorRelation preds) t) :
    t ∈ enumerateExtensions preds preds.length (List.range preds.length) :=
  extends_enumerated preds t (strict_poset_predecessors_valid preds hp) ht

#print axioms extends_enumerated
#print axioms strict_poset_predecessors_valid
#print axioms strict_poset_extends_enumerated
end ExtensionCompleteness
