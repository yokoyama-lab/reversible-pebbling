import ExtensionBefore
import CompletionOrder

/- SOURCE ONLY, not compiled. Concrete ordinary-extension exactness unit.
   Dependencies must be the fixed compiler-verified versions. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

/-- Reverse bridge from original Before witnesses to actual List.Pairwise. -/
 theorem pairwise_of_forall_before (S : E → E → Prop) (w : List E)
    (hw : ∀ a b, Before w a b → S a b) : w.Pairwise S := by
  induction w with
  | nil => exact .nil
  | cons x w ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        exact hw x y ((before_cons_iff x x y w).mpr (Or.inl ⟨rfl, hy⟩))
      · apply ih
        intro a b hab
        exact hw a b ((before_cons_iff x a b w).mpr (Or.inr hab))

 theorem pairwise_no_reverse_iff_respects (R : E → E → Prop) (w : List E)
    (hd : w.Nodup) (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ w ∧ y ∈ w) :
    w.Pairwise (fun x y => ¬ R y x) ↔ (∀ x y, R x y → Before w x y) := by
  constructor
  · intro hw
    exact pairwise_respects_supported_base R w hw hirr hsupport
  · intro hw
    apply pairwise_of_forall_before
    intro x y hxy hyx
    have hback : Before w y x := hw y x hyx
    exact before_irrefl_of_nodup w hd x
      (before_trans_of_nodup w hd x y x hxy hback)

/-- Ordinary extension language exactness for the actual transitive closure.
    Both w and v use the same fixed ID universe U. No guards or projection are
    silently added to the component language. Signature uses original Before. -/
 theorem completion_extensions_iff (s : E → Int) (R : E → E → Prop)
    (U w v : List E) (hU : U.Nodup) (hpw : w.Perm U) (hpv : v.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U) :
    v.Pairwise (fun x y => ¬ Completion s R w y x) ↔
      v.Pairwise (fun x y => ¬ R y x) ∧
        (∀ x y, s x ≠ s y → (Before w x y ↔ Before v x y)) := by
  have hdw : w.Nodup := hpw.nodup_iff.mpr hU
  have hdv : v.Nodup := hpv.nodup_iff.mpr hU
  have hwR : ∀ x y, R x y → Before w x y :=
    permutation_pairwise_respects_base R U w hpw hw hirr hsupport
  have hsuppV : ∀ x y, R x y → x ∈ v ∧ y ∈ v := by
    intro x y h
    have hm := hsupport x y h
    exact ⟨hpv.mem_iff.mpr hm.1, hpv.mem_iff.mpr hm.2⟩
  have hcIrr : ∀ x, ¬ Completion s R w x x :=
    completion_irrefl s R w hdw hwR
  have hcSupp : ∀ x y, Completion s R w x y → x ∈ v ∧ y ∈ v := by
    intro x y h
    have hb := completion_before s R w hdw hwR h
    exact ⟨hpv.mem_iff.mpr (hpw.mem_iff.mp (before_left_mem hb)),
      hpv.mem_iff.mpr (hpw.mem_iff.mp (before_right_mem hb))⟩
  have hbridge := pairwise_no_reverse_iff_respects (Completion s R w) v hdv hcIrr hcSupp
  constructor
  · intro hvC
    have hvRespect := hbridge.mp hvC
    have hvR : v.Pairwise (fun x y => ¬ R y x) := by
      apply (pairwise_no_reverse_iff_respects R v hdv hirr hsuppV).mpr
      intro x y h
      exact hvRespect x y (NonemptyReach.edge (Or.inl h))
    refine ⟨hvR, ?_⟩
    intro x y hsign
    constructor
    · intro hxy
      exact hvRespect x y (NonemptyReach.edge (Or.inr ⟨hsign, hxy⟩))
    · intro hvxy
      have hne : x ≠ y := by intro he; exact hsign (congrArg s he)
      have hxw : x ∈ w := hpw.mem_iff.mpr (hpv.mem_iff.mp (before_left_mem hvxy))
      have hyw : y ∈ w := hpw.mem_iff.mpr (hpv.mem_iff.mp (before_right_mem hvxy))
      rcases before_total_of_mem w x y hxw hyw hne with hwxy | hwyx
      · exact hwxy
      · have hvyx : Before v y x := hvRespect y x
          (NonemptyReach.edge (Or.inr ⟨Ne.symm hsign, hwyx⟩))
        exact False.elim (before_irrefl_of_nodup v hdv x
          (before_trans_of_nodup v hdv x y x hvxy hvyx))
  · rintro ⟨hvR, hsig⟩
    have hvRespectR := pairwise_respects_supported_base R v hvR hirr hsuppV
    apply hbridge.mpr
    intro x y hp
    apply NonemptyReach.lift (T := Before v) ?_ ?_ hp
    · intro a b hgen
      rcases hgen with hR | ⟨hs, hb⟩
      · exact hvRespectR a b hR
      · exact (hsig a b hs).mp hb
    · exact before_trans_of_nodup v hdv

#print axioms pairwise_of_forall_before
#print axioms pairwise_no_reverse_iff_respects
#print axioms completion_extensions_iff
end PebblingSignature
