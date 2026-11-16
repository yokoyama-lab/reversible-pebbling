import LocalCertificate
import UpperCore
namespace EnumerationCorrectness
open LocalCertificate

def enumeratePhysical (events : List Event) (erasures final : List Nat) :
    Nat → List Nat → List Nat → List (List Nat)
  | 0, board, remaining => if remaining.isEmpty && sameBoard board final then [[]] else []
  | fuel + 1, board, remaining => remaining.flatMap fun e =>
      match events[e]? with
      | none => []
      | some event => match step true erasures board event with
        | none => []
        | some after => (enumeratePhysical events erasures final fuel after (remaining.erase e)).map (e :: ·)

def accepts (events : List Event) (erasures final board t : List Nat) : Prop :=
  (match replay true events erasures board t with
   | none => false
   | some after => sameBoard after final) = true

theorem mem_succ (events : List Event) (erasures final board remaining : List Nat)
    (fuel e : Nat) (t : List Nat) :
    e :: t ∈ enumeratePhysical events erasures final (fuel+1) board remaining ↔
    e ∈ remaining ∧ ∃ ev, events[e]? = some ev ∧ ∃ after,
      step true erasures board ev = some after ∧
      t ∈ enumeratePhysical events erasures final fuel after (remaining.erase e) := by
  simp only [enumeratePhysical, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases he : events[a]? with
    | none => simp [he] at h
    | some ev =>
      cases hs : step true erasures board ev with
      | none => simp [he, hs] at h
      | some after =>
        simp only [he, hs, List.mem_map] at h
        obtain ⟨w, hw, eq⟩ := h
        have eq' := List.cons.inj eq
        rcases eq' with ⟨rfl, rfl⟩
        exact ⟨ha, ev, he, after, hs, hw⟩
  · rintro ⟨he, ev, hlookup, after, hs, ht⟩
    exact ⟨e, he, by simpa [hlookup, hs] using ht⟩

theorem nil_not_mem_succ (events : List Event) (erasures final board remaining : List Nat)
    (fuel : Nat) : [] ∉ enumeratePhysical events erasures final (fuel+1) board remaining := by
  simp only [enumeratePhysical, List.mem_flatMap]
  rintro ⟨e, he, h⟩
  cases hl : events[e]? with
  | none => simp [hl] at h
  | some ev =>
    cases hs : step true erasures board ev with
    | none => simp [hl, hs] at h
    | some after => simp [hl, hs] at h

theorem physical_enumeration_iff (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board remaining t : List Nat) :
    t ∈ enumeratePhysical events erasures final fuel board remaining ↔
    t.length = fuel ∧ t.Perm remaining ∧ accepts events erasures final board t := by
  induction fuel generalizing board remaining t with
  | zero =>
    cases t <;> cases remaining <;> simp [enumeratePhysical, accepts, replay]
  | succ fuel ih =>
    cases t with
    | nil => simp [nil_not_mem_succ]
    | cons e t =>
      rw [mem_succ]
      cases hl : events[e]? with
      | none => simp [hl, accepts, replay]
      | some ev =>
        cases hs : step true erasures board ev with
        | none => simp [hl, hs, accepts, replay]
        | some after =>
          simp [hl, hs, ih, accepts, replay, List.cons_perm_iff_perm_erase, and_assoc, and_left_comm, and_comm]

#print axioms physical_enumeration_iff


theorem perm_of_nodup_subset_length (xs ys : List Nat) (hn : xs.Nodup)
    (hs : xs ⊆ ys) (hl : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst ys; exact List.Perm.refl []
  | cons a xs ih =>
    have hn' := List.nodup_cons.mp hn
    have ha : a ∈ ys := hs (by simp)
    apply List.cons_perm_iff_perm_erase.mpr
    refine ⟨ha, ih (ys.erase a) hn'.2 ?_ ?_⟩
    · intro x hx
      have hxa : x ≠ a := by
        intro eq
        subst x
        exact hn'.1 hx
      apply (List.mem_erase_of_ne hxa).mpr
      exact hs (by simp [hx])
    · have he := List.length_erase_of_mem ha
      simp only [List.length_cons] at hl
      omega

theorem isPermutation_iff_perm_range (n : Nat) (t : List Nat) :
    isPermutation n t ↔ t.Perm (List.range n) := by
  constructor
  · intro h
    apply perm_of_nodup_subset_length t (List.range n) h.2.1
    · intro e he; exact List.mem_range.mpr (h.2.2 e he)
    · simpa using h.1
  · intro h
    refine ⟨?_, h.symm.nodup List.nodup_range, ?_⟩
    · simpa using h.length_eq
    · intro e he; exact List.mem_range.mp (h.subset he)

theorem physical_enumeration_legal (events : List Event) (initial final erasures t : List Nat) :
    t ∈ enumeratePhysical events erasures final events.length initial (List.range events.length) ↔
    legal events initial final erasures t := by
  rw [physical_enumeration_iff]
  simp only [legal, isPermutation_iff_perm_range, accepts]
  constructor
  · intro h; exact ⟨h.2.1, h.2.2⟩
  · intro h; exact ⟨by simpa using h.1.length_eq, h.1, h.2⟩

#print axioms perm_of_nodup_subset_length
#print axioms isPermutation_iff_perm_range
#print axioms physical_enumeration_legal


theorem same_enumerator (events : List Event) (erasures final : List Nat)
    (fuel : Nat) (board remaining : List Nat) :
    UpperCertificate.enumeratePhysical events erasures final fuel board remaining =
    enumeratePhysical events erasures final fuel board remaining := by
  induction fuel generalizing board remaining with
  | zero => rfl
  | succ fuel ih =>
    simp only [UpperCertificate.enumeratePhysical, enumeratePhysical]
    apply congrArg (fun f => remaining.flatMap f)
    funext e
    cases hl : events[e]? with
    | none => simp
    | some ev =>
      cases hs : step true erasures board ev with
      | none => simp [hs]
      | some after => simp [hs, ih]

theorem upper_physical_enumeration_legal (events : List Event)
    (initial final erasures t : List Nat) :
    t ∈ UpperCertificate.enumeratePhysical events erasures final events.length initial
      (List.range events.length) ↔ legal events initial final erasures t := by
  rw [same_enumerator, physical_enumeration_legal]

#print axioms same_enumerator
#print axioms upper_physical_enumeration_legal
#print axioms mem_succ
#print axioms nil_not_mem_succ
end EnumerationCorrectness
