import OccurrenceOrder
namespace SlotConcat
open ErasureCover
variable {A B : Type} [DecidableEq A] [DecidableEq B]
local instance : BEq (Sum A B) := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq (Sum A B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def semantics (all : List A) : Semantics A (List A) where
  admissible w := w.Perm all
  before w a b := w.idxOf a < w.idxOf b

def join (xs : List A) (ys : List B) : List (Sum A B) :=
  xs.map Sum.inl ++ ys.map Sum.inr

theorem idx_map_inl (xs : List A) (a : A) :
    (xs.map (Sum.inl : A → Sum A B)).idxOf (.inl a)=xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x=a
    · subst x; simp
    · have hs : (Sum.inl x : Sum A B) ≠ Sum.inl a := by simpa using h
      simp [List.idxOf_cons,beq_false_of_ne h,beq_false_of_ne hs,ih]

theorem idx_map_inr (ys : List B) (b : B) :
    (ys.map (Sum.inr : B → Sum A B)).idxOf (.inr b)=ys.idxOf b := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y=b
    · subst y; simp
    · have hs : (Sum.inr y : Sum A B) ≠ Sum.inr b := by simpa using h
      simp [List.idxOf_cons,beq_false_of_ne h,beq_false_of_ne hs,ih]

theorem idx_left (xs : List A) (ys : List B) (a : A) (ha : a∈xs) :
    (join xs ys).idxOf (.inl a)=xs.idxOf a := by
  unfold join
  rw [List.idxOf_append,if_pos (by simpa using ha)]
  exact idx_map_inl xs a

theorem idx_right (xs : List A) (ys : List B) (b : B) :
    (join xs ys).idxOf (.inr b)=xs.length+ys.idxOf b := by
  unfold join
  rw [List.idxOf_append,if_neg (by simp)]
  simp [idx_map_inr,Nat.add_comm]

theorem preserves_left (xs : List A) (ys : List B) (a b : A)
    (ha : a∈xs) (hb : b∈xs) :
    (join xs ys).idxOf (.inl a)<(join xs ys).idxOf (.inl b) ↔ xs.idxOf a<xs.idxOf b := by
  rw [idx_left xs ys a ha,idx_left xs ys b hb]

theorem preserves_right (xs : List A) (ys : List B) (a b : B) :
    (join xs ys).idxOf (.inr a)<(join xs ys).idxOf (.inr b) ↔ ys.idxOf a<ys.idxOf b := by
  rw [idx_right,idx_right]
  omega

theorem all_left_before_right (xs : List A) (ys : List B) (a : A) (b : B)
    (ha : a∈xs) :
    (join xs ys).idxOf (.inl a)<(join xs ys).idxOf (.inr b) := by
  rw [idx_left xs ys a ha,idx_right]
  have := List.idxOf_lt_length_of_mem ha
  omega

theorem no_right_before_left (xs : List A) (ys : List B) (a : B) (b : A)
    (hb : b∈xs) :
    ¬(join xs ys).idxOf (.inr a)<(join xs ys).idxOf (.inl b) := by
  have := all_left_before_right xs ys b a hb
  omega

theorem common_extension_join
    (allA : List A) (allB : List B) (completeA : ∀ a, a∈allA)
    (sx tx zx : List A) (sy ty zy : List B)
    (hs : sx.Perm allA) (ht : tx.Perm allA)
    (hx : Extends (semantics allA) (Common (semantics allA) sx tx) zx)
    (hy : Extends (semantics allB) (Common (semantics allB) sy ty) zy) :
    Extends (semantics (join allA allB))
      (Common (semantics (join allA allB)) (join sx sy) (join tx ty)) (join zx zy) := by
  constructor
  · exact (hx.1.map Sum.inl).append (hy.1.map Sum.inr)
  · intro a b hab
    have zs : ∀ a, a∈zx := fun a => hx.1.mem_iff.mpr (completeA a)
    have ss : ∀ a, a∈sx := fun a => hs.mem_iff.mpr (completeA a)
    have ts : ∀ a, a∈tx := fun a => ht.mem_iff.mpr (completeA a)
    change (join zx zy).idxOf a < (join zx zy).idxOf b
    change ((join sx sy).idxOf a < (join sx sy).idxOf b) ∧
      ((join tx ty).idxOf a < (join tx ty).idxOf b) at hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply (preserves_left zx zy a b (zs a) (zs b)).mpr
        exact hx.2 a b ⟨(preserves_left sx sy a b (ss a) (ss b)).mp hab.1,
          (preserves_left tx ty a b (ts a) (ts b)).mp hab.2⟩
      | inr b => exact all_left_before_right zx zy a b (zs a)
    | inr a =>
      cases b with
      | inl b => exact False.elim (no_right_before_left sx sy a b (ss b) hab.1)
      | inr b =>
        apply (preserves_right zx zy a b).mpr
        exact hy.2 a b ⟨(preserves_right sx sy a b).mp hab.1,
          (preserves_right tx ty a b).mp hab.2⟩

def lefts (w : List (Sum A B)) : List A :=
  w.filterMap (fun e => match e with | .inl a => some a | .inr _ => none)

theorem left_join (xs : List A) (ys : List B) : lefts (join xs ys)=xs := by
  simp [lefts,join,List.filterMap_map,Function.comp_def]

def blockedLegal (LA : List A → Prop) (LB : List B → Prop) (w : List (Sum A B)) :=
  ∃ xs ys, w=join xs ys ∧ LA xs ∧ LB ys

theorem bad_left_stays_bad (LA : List A → Prop) (LB : List B → Prop)
    (zx : List A) (zy : List B) (bad : ¬LA zx) :
    ¬blockedLegal LA LB (join zx zy) := by
  rintro ⟨xs,ys,he,hx,hy⟩
  have h := congrArg lefts he
  simp only [left_join] at h
  exact bad (h.symm ▸ hx)

/-- A genuine bad common-order extension in the ordinary sum-slot word semantics.
Legality is explicitly the exact blocked product language, not physical replay. -/
theorem blocked_bad_common_extension
    (allA : List A) (allB : List B) (completeA : ∀ a, a∈allA)
    (LA : List A → Prop) (LB : List B → Prop)
    (sx tx zx : List A) (sy ty zy : List B)
    (hs : sx.Perm allA) (ht : tx.Perm allA)
    (hx : Extends (semantics allA) (Common (semantics allA) sx tx) zx)
    (hy : Extends (semantics allB) (Common (semantics allB) sy ty) zy)
    (bad : ¬LA zx) :
    Extends (semantics (join allA allB))
      (Common (semantics (join allA allB)) (join sx sy) (join tx ty)) (join zx zy) ∧
      ¬blockedLegal LA LB (join zx zy) :=
  ⟨common_extension_join allA allB completeA sx tx zx sy ty zy hs ht hx hy,
    bad_left_stays_bad LA LB zx zy bad⟩

#print axioms left_join
#print axioms bad_left_stays_bad
#print axioms blocked_bad_common_extension
#print axioms idx_left
#print axioms idx_right
#print axioms preserves_left
#print axioms preserves_right
#print axioms all_left_before_right
#print axioms no_right_before_left
#print axioms common_extension_join
end SlotConcat
