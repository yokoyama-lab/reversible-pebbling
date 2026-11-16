import BeforeTrace

/- Uncompiled source candidate, ordinary finite-order infrastructure.
   No novelty claim. No assumed orientation/Before bridge. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

/-- For two distinct IDs that occur in a concrete list, at least one ordering
    is witnessed by the original prefix/middle/suffix Before definition.
    This stronger disjunction does not itself need Nodup. -/
 theorem before_total_of_mem (w : List E) (a b : E)
    (ha : a ∈ w) (hb : b ∈ w) (hab : a ≠ b) :
    Before w a b ∨ Before w b a := by
  revert ha hb
  induction w with
  | nil => simp
  | cons x w ih =>
      intro ha hb
      rcases List.mem_cons.mp ha with hax | ha'
      · rcases List.mem_cons.mp hb with hbx | hb'
        · exact False.elim (hab (hax.trans hbx.symm))
        · exact Or.inl ((before_cons_iff x a b w).mpr (Or.inl ⟨hax.symm, hb'⟩))
      · rcases List.mem_cons.mp hb with hbx | hb'
        · exact Or.inr ((before_cons_iff x b a w).mpr (Or.inl ⟨hbx.symm, ha'⟩))
        · rcases ih ha' hb' with h | h
          · exact Or.inl ((before_cons_iff x a b w).mpr (Or.inr h))
          · exact Or.inr ((before_cons_iff x b a w).mpr (Or.inr h))

 theorem before_total_of_nodup (w : List E) (_hd : w.Nodup) (a b : E)
    (ha : a ∈ w) (hb : b ∈ w) (hab : a ≠ b) :
    Before w a b ∨ Before w b a := before_total_of_mem w a b ha hb hab

/-- Actual list Pairwise facts apply to every Before witness. -/
 theorem pairwise_rel_of_before (S : E → E → Prop) (w : List E)
    (hw : w.Pairwise S) {a b : E} (h : Before w a b) : S a b := by
  obtain ⟨p, m, t, rfl⟩ := h
  have ht := (List.pairwise_append.mp hw).2.1
  exact (List.pairwise_cons.mp ht).1 b (by simp)

/-- Derives base-edge respect, rather than assuming it. A global R may mention
    absent labels, so support is explicitly needed for every edge being used. -/
 theorem pairwise_base_edge_before (R : E → E → Prop) (w : List E)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x) {a b : E}
    (ha : a ∈ w) (hb : b ∈ w) (hR : R a b) : Before w a b := by
  have hab : a ≠ b := by
    intro he
    subst b
    exact hirr a hR
  rcases before_total_of_mem w a b ha hb hab with h | h
  · exact h
  · exact False.elim ((pairwise_rel_of_before (fun x y => ¬ R y x) w hw h) hR)

 theorem pairwise_respects_supported_base (R : E → E → Prop) (w : List E)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ w ∧ y ∈ w) :
    ∀ x y, R x y → Before w x y := by
  intro x y h
  have hm := hsupport x y h
  exact pairwise_base_edge_before R w hw hirr hm.1 hm.2 h

/-- Fixed-ID universe formulation: support is checked against U and explicitly
    transported to the realizing word by its actual permutation witness. -/
 theorem permutation_pairwise_respects_base (R : E → E → Prop) (U w : List E)
    (hp : w.Perm U) (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U) :
    ∀ x y, R x y → Before w x y := by
  apply pairwise_respects_supported_base R w hw hirr
  intro x y h
  have hm := hsupport x y h
  exact ⟨hp.mem_iff.mpr hm.1, hp.mem_iff.mpr hm.2⟩

#print axioms before_total_of_mem
#print axioms pairwise_base_edge_before
#print axioms permutation_pairwise_respects_base
end PebblingSignature
