import SignatureInvariant

/- SOURCE CANDIDATE: no compilation performed by this worker. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

/-- The original positional/existential Before, not a replacement definition. -/
def Before (w : List E) (a b : E) : Prop :=
  ∃ p m t, w = p ++ a :: (m ++ b :: t)

private theorem split_member {x : E} {w : List E} (h : x ∈ w) :
    ∃ p t, w = p ++ x :: t := by
  induction w with
  | nil => simp at h
  | cons y w ih =>
      rcases List.mem_cons.mp h with he | ht
      · subst y
        exact ⟨[], w, rfl⟩
      · obtain ⟨p, t, hp⟩ := ih ht
        exact ⟨y :: p, t, by simp [hp]⟩

 theorem before_right_mem {w : List E} {a b : E} (h : Before w a b) : b ∈ w := by
  obtain ⟨p, m, t, rfl⟩ := h
  simp

 theorem before_cons_iff (x a b : E) (w : List E) :
    Before (x :: w) a b ↔ (x = a ∧ b ∈ w) ∨ Before w a b := by
  constructor
  · rintro ⟨p, m, t, h⟩
    cases p with
    | nil =>
        change x :: w = a :: (m ++ b :: t) at h
        have he := List.cons.inj h
        exact Or.inl ⟨he.1, by simp [he.2]⟩
    | cons y p =>
        change x :: w = y :: (p ++ a :: (m ++ b :: t)) at h
        exact Or.inr ⟨p, m, t, (List.cons.inj h).2⟩
  · intro h
    rcases h with ⟨rfl, hb⟩ | ⟨p, m, t, ht⟩
    · obtain ⟨m, t, ht⟩ := split_member hb
      exact ⟨[], m, t, by simp [ht]⟩
    · exact ⟨x :: p, m, t, by simp [ht]⟩

 theorem before_left_mem {w : List E} {a b : E} (h : Before w a b) : a ∈ w := by
  obtain ⟨p, m, t, rfl⟩ := h
  simp

 theorem trace_cons (x a b : E) (w : List E) :
    pairTrace a b (x :: w) =
      if x = a ∨ x = b then x :: pairTrace a b w else pairTrace a b w := by
  by_cases h : x = a ∨ x = b <;> simp [pairTrace, h]

 theorem trace_nil_of_absent (a b : E) (w : List E)
    (ha : a ∉ w) (hb : b ∉ w) : pairTrace a b w = [] := by
  revert ha hb
  induction w with
  | nil => intro _ _; rfl
  | cons x w ih =>
      intro ha hb
      have hxa : x ≠ a := by intro he; subst x; exact ha (by simp)
      have hxb : x ≠ b := by intro he; subst x; exact hb (by simp)
      have ha' : a ∉ w := by intro h; exact ha (by simp [h])
      have hb' : b ∉ w := by intro h; exact hb (by simp [h])
      simpa [trace_cons, hxa, hxb] using ih ha' hb'

/-- With a absent and no repeats, retaining a or b yields exactly [b]
    iff b is present. -/
 theorem trace_singleton_of_left_absent (a b : E) (w : List E)
    (hd : w.Nodup) (ha : a ∉ w) :
    pairTrace a b w = [b] ↔ b ∈ w := by
  revert hd ha
  induction w with
  | nil => intro _ _; simp [pairTrace]
  | cons x w ih =>
      intro hd ha
      obtain ⟨hx, hd'⟩ := List.nodup_cons.mp hd
      have hxa : x ≠ a := by intro he; subst x; exact ha (by simp)
      have ha' : a ∉ w := by intro h; exact ha (by simp [h])
      by_cases hxb : x = b
      · subst x
        have ht := trace_nil_of_absent a b w ha' hx
        simp [trace_cons, ht]
      · simpa [trace_cons, hxa, hxb, Ne.symm hxb] using ih hd' ha'

/-- Stronger than the requested statement: explicit membership assumptions
    are unnecessary, since either side implies both memberships. -/
 theorem pairTrace_eq_pair_iff_before (a b : E) (w : List E)
    (hab : a ≠ b) (hd : w.Nodup) :
    pairTrace a b w = [a, b] ↔ Before w a b := by
  revert hd
  induction w with
  | nil => intro _; simp [pairTrace, Before]
  | cons x w ih =>
      intro hd
      obtain ⟨hx, hd'⟩ := List.nodup_cons.mp hd
      by_cases hxa : x = a
      · subst x
        have hnb : ¬ Before w a b := fun h => hx (before_left_mem h)
        simpa [trace_cons, before_cons_iff, hnb] using
          trace_singleton_of_left_absent a b w hd' hx
      · by_cases hxb : x = b
        · subst x
          have hnb : ¬ Before w a b := fun h => hx (before_right_mem h)
          simp [trace_cons, before_cons_iff, hxa, Ne.symm hab, hnb]
        · simpa [trace_cons, before_cons_iff, hxa, hxb] using ih hd'

 theorem pairTrace_eq_pair_iff_before_of_mem (a b : E) (w : List E)
    (hd : w.Nodup) (hab : a ≠ b) (_ha : a ∈ w) (_hb : b ∈ w) :
    pairTrace a b w = [a, b] ↔ Before w a b :=
  pairTrace_eq_pair_iff_before a b w hab hd

theorem sameSignature_before_iff (s : E → Int) (u v : List E)
    (hu : u.Nodup) (hv : v.Nodup) (hs : SameSignature s u v)
    (a b : E) (hsab : s a ≠ s b) :
    Before u a b ↔ Before v a b := by
  have hab : a ≠ b := by intro he; exact hsab (congrArg s he)
  constructor
  · intro h
    apply (pairTrace_eq_pair_iff_before a b v hab hv).mp
    rw [← hs a b hsab]
    exact (pairTrace_eq_pair_iff_before a b u hab hu).mpr h
  · intro h
    apply (pairTrace_eq_pair_iff_before a b u hab hu).mp
    rw [hs a b hsab]
    exact (pairTrace_eq_pair_iff_before a b v hab hv).mpr h

#print axioms pairTrace_eq_pair_iff_before
#print axioms sameSignature_before_iff
#print axioms pairTrace_eq_pair_iff_before_of_mem
end PebblingSignature
