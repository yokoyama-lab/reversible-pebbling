import BeforeTrace

/- SOURCE CANDIDATE ONLY. No compilation by this worker.
   Proves concrete closure order laws; not yet completion-language exactness. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

 theorem before_irrefl_of_nodup (w : List E) (hd : w.Nodup) (a : E) :
    ¬ Before w a a := by
  revert hd
  induction w with
  | nil => simp [Before]
  | cons x w ih =>
      intro hd hb
      obtain ⟨hx, ht⟩ := List.nodup_cons.mp hd
      rcases (before_cons_iff x a a w).mp hb with ⟨he, hm⟩ | hb'
      · exact hx (by simpa [he] using hm)
      · exact ih ht hb'

 theorem before_trans_of_nodup (w : List E) (hd : w.Nodup)
    (a b c : E) (hab : Before w a b) (hbc : Before w b c) : Before w a c := by
  revert hd hab hbc
  induction w with
  | nil => simp [Before]
  | cons x w ih =>
      intro hd hab hbc
      obtain ⟨hx, ht⟩ := List.nodup_cons.mp hd
      rcases (before_cons_iff x a b w).mp hab with ⟨hxa, hb⟩ | hab'
      · rcases (before_cons_iff x b c w).mp hbc with ⟨hxb, hc⟩ | hbc'
        · exact False.elim (hx (by simpa [hxb] using hb))
        · exact (before_cons_iff x a c w).mpr
            (Or.inl ⟨hxa, before_right_mem hbc'⟩)
      · rcases (before_cons_iff x b c w).mp hbc with ⟨hxb, hc⟩ | hbc'
        · exact False.elim (hx (by simpa [hxb] using before_right_mem hab'))
        · exact (before_cons_iff x a c w).mpr (Or.inr (ih ht hab' hbc'))

/-- Explicit nonempty finite path: the actual transitive closure. -/
inductive NonemptyReach (B : E → E → Prop) : E → E → Prop
  | edge {x y} : B x y → NonemptyReach B x y
  | tail {x y z} : NonemptyReach B x y → B y z → NonemptyReach B x z

 theorem NonemptyReach.trans {B : E → E → Prop} {x y z : E}
    (p : NonemptyReach B x y) (q : NonemptyReach B y z) : NonemptyReach B x z := by
  induction q with
  | edge h => exact .tail p h
  | tail q h ih => exact .tail ih h

/-- Universal property: this is the least transitive relation containing B. -/
 theorem NonemptyReach.lift {B T : E → E → Prop}
    (hBT : ∀ x y, B x y → T x y)
    (hT : ∀ x y z, T x y → T y z → T x z)
    {x y : E} (p : NonemptyReach B x y) : T x y := by
  induction p with
  | edge h => exact hBT _ _ h
  | tail p h ih => exact hT _ _ _ ih (hBT _ _ h)

 def signatureGenerators (s : E → Int) (R : E → E → Prop) (w : List E)
    (x y : E) : Prop := R x y ∨ (s x ≠ s y ∧ Before w x y)

 def Completion (s : E → Int) (R : E → E → Prop) (w : List E) : E → E → Prop :=
    NonemptyReach (signatureGenerators s R w)

/-- hR means exactly that the realizing word respects each actual base edge.
    This is NOT an assumption about closure or its order properties. -/
 theorem completion_before (s : E → Int) (R : E → E → Prop) (w : List E)
    (hd : w.Nodup) (hR : ∀ x y, R x y → Before w x y)
    {x y : E} (p : Completion s R w x y) : Before w x y := by
  apply NonemptyReach.lift (T := Before w) ?_ ?_ p
  · intro a b h
    rcases h with h | h
    · exact hR a b h
    · exact h.2
  · exact before_trans_of_nodup w hd

 theorem completion_irrefl (s : E → Int) (R : E → E → Prop) (w : List E)
    (hd : w.Nodup) (hR : ∀ x y, R x y → Before w x y) (x : E) :
    ¬ Completion s R w x x := by
  intro p
  exact before_irrefl_of_nodup w hd x (completion_before s R w hd hR p)

 theorem completion_trans (s : E → Int) (R : E → E → Prop) (w : List E)
    {x y z : E} (p : Completion s R w x y) (q : Completion s R w y z) :
    Completion s R w x z := NonemptyReach.trans p q

/-- Concrete non-strict order for the ordinary poset bridge. -/
 def CompletionLE (s : E → Int) (R : E → E → Prop) (w : List E) (x y : E) : Prop :=
    x = y ∨ Completion s R w x y

 theorem completionLE_refl (s : E → Int) (R : E → E → Prop) (w : List E) (x : E) :
    CompletionLE s R w x x := Or.inl rfl

 theorem completionLE_trans (s : E → Int) (R : E → E → Prop) (w : List E)
    {x y z : E} (p : CompletionLE s R w x y) (q : CompletionLE s R w y z) :
    CompletionLE s R w x z := by
  rcases p with rfl | p
  · exact q
  · rcases q with rfl | q
    · exact Or.inr p
    · exact Or.inr (completion_trans s R w p q)

 theorem completionLE_antisymm (s : E → Int) (R : E → E → Prop) (w : List E)
    (hd : w.Nodup) (hR : ∀ x y, R x y → Before w x y)
    {x y : E} (p : CompletionLE s R w x y) (q : CompletionLE s R w y x) : x = y := by
  rcases p with h | p
  · exact h
  · rcases q with h | q
    · exact h.symm
    · exact False.elim (completion_irrefl s R w hd hR x (completion_trans s R w p q))

 theorem completion_strict_part (s : E → Int) (R : E → E → Prop) (w : List E)
    (hd : w.Nodup) (hR : ∀ x y, R x y → Before w x y) (x y : E) :
    Completion s R w x y ↔ CompletionLE s R w x y ∧ x ≠ y := by
  constructor
  · intro p
    refine ⟨Or.inr p, ?_⟩
    intro he
    subst y
    exact completion_irrefl s R w hd hR x p
  · rintro ⟨h, hn⟩
    rcases h with he | p
    · exact False.elim (hn he)
    · exact p

#print axioms before_trans_of_nodup
#print axioms completion_before
#print axioms completion_irrefl
#print axioms completionLE_antisymm
#print axioms completion_strict_part
end PebblingSignature
