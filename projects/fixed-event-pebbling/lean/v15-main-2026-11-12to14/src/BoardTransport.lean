import ChainTrace
namespace BoardTransport
open LocalCertificate ChainTrace

theorem step_perm_transport (erasures board board' after : List Nat) (e : Event)
    (hb : board.Perm board') (hs : step true erasures board e = some after) :
    ∃ after', step true erasures board' e = some after' ∧ after.Perm after' := by
  cases hp : e.place with
  | true =>
    obtain ⟨ha,hpred,hcap,he⟩ := (placement_step erasures board after e hp).mp hs
    refine ⟨e.vertex::board',?_,?_⟩
    · apply (placement_step erasures board' (e.vertex::board') e hp).mpr
      refine ⟨?_,?_,?_,rfl⟩
      · intro hm; exact ha (hb.mem_iff.mpr hm)
      · rcases hpred with h1 | hm
        · exact Or.inl h1
        · exact Or.inr (hb.mem_iff.mp hm)
      · simpa only [List.length_cons,hb.length_eq] using hcap
    · rw [he]
      exact List.Perm.cons e.vertex hb
  | false =>
    have he := removal_step_after erasures board after e hp hs
    subst after
    refine ⟨board'.erase e.vertex,?_,hb.erase e.vertex⟩
    have hcontains : ∀ v, board.contains v = board'.contains v := fun _ => hb.contains_eq
    have hlen := (hb.erase e.vertex).length_eq
    simp [step,hp] at hs ⊢
    simpa only [hcontains,hlen,hb.mem_iff] using hs

/-- Concrete board ordering is irrelevant to the successful physical word. -/
theorem run_perm_transport (erasures board board' after : List Nat) (es : List Event)
    (hb : board.Perm board') (hr : run erasures board es = some after) :
    ∃ after', run erasures board' es = some after' ∧ after.Perm after' := by
  induction es generalizing board board' with
  | nil =>
    simp [run] at hr
    subst after
    exact ⟨board',rfl,hb⟩
  | cons e es ih =>
    cases hs : step true erasures board e with
    | none => simp [run,hs] at hr
    | some mid =>
      have ht : run erasures mid es = some after := by simpa [run,hs] using hr
      obtain ⟨mid',hs',hm⟩ := step_perm_transport erasures board board' mid e hb hs
      obtain ⟨after',ht',ha⟩ := ih mid mid' hm ht
      exact ⟨after',by simpa [run,hs'] using ht',ha⟩

/-- Safe concatenation through a checkpoint known only up to board permutation. -/
theorem concatenate_through_perm (erasures initial actual expected final : List Nat)
    (xs ys : List Event)
    (hx : run erasures initial xs = some actual) (hb : expected.Perm actual)
    (hy : run erasures expected ys = some final) :
    ∃ final', run erasures initial (xs ++ ys) = some final' ∧ final.Perm final' := by
  obtain ⟨final',hy',hf⟩ := run_perm_transport erasures expected actual final ys hb hy
  refine ⟨final',?_,hf⟩
  rw [run_append,hx]
  exact hy'
#print axioms step_perm_transport
#print axioms run_perm_transport
#print axioms concatenate_through_perm
theorem nodup_membership_perm (xs ys : List Nat)
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ v, v ∈ xs ↔ v ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y rest =>
        have hh := (hm y).mpr (by simp)
        simp at hh
    subst ys
    exact List.Perm.nil
  | cons a xs ih =>
    have hx' := List.nodup_cons.mp hx
    have ha : a ∈ ys := (hm a).mp (by simp)
    have hmem : ∀ v, v ∈ xs ↔ v ∈ ys.erase a := by
      intro v
      rw [hy.mem_erase_iff]
      constructor
      · intro hv
        refine ⟨?_,(hm v).mp (List.mem_cons_of_mem a hv)⟩
        intro heq; subst v; exact hx'.1 hv
      · rintro ⟨hne,hv⟩
        rcases List.mem_cons.mp ((hm v).mpr hv) with h | h
        · exact False.elim (hne h)
        · exact h
    have hi := ih (ys.erase a) hx'.2 (hy.erase a) hmem
    exact (List.Perm.cons a hi).trans (List.perm_cons_erase ha).symm
#print axioms nodup_membership_perm
end BoardTransport
