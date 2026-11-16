import SlotConcat
import ProductUpper
namespace ChainBlockedOrder
open ErasureCover SlotConcat
variable {A B : Type} [DecidableEq A] [DecidableEq B]
local instance : BEq (Sum A B) := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq (Sum A B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

theorem filter_none (xs : List A) : xs.filterMap (fun _ => (none : Option B)) = [] :=
  List.filterMap_eq_nil_iff.mpr (by simp)

def rights (w : List (Sum A B)) : List B := w.filterMap (fun x => match x with | .inl _ => none | .inr b => some b)
theorem right_join (xs : List A) (ys : List B) : rights (join xs ys)=ys := by
  simp [rights,join,List.filterMap_map,Function.comp_def]

theorem cross_forces_join (w : List (Sum A B)) (nd : w.Nodup)
    (cross : ∀ a b, Sum.inl a ∈ w → Sum.inr b ∈ w → w.idxOf (.inl a)<w.idxOf (.inr b)) :
    ∃ xs ys, w=join xs ys := by
  induction w with
  | nil => exact ⟨[],[],rfl⟩
  | cons e w ih =>
    have hn := List.nodup_cons.mp nd
    have ct : ∀ a b, Sum.inl a ∈ w → Sum.inr b ∈ w → w.idxOf (.inl a)<w.idxOf (.inr b) := by
      intro a b ha hb
      have ea : e ≠ Sum.inl a := fun he => hn.1 (he ▸ ha)
      have eb : e ≠ Sum.inr b := fun he => hn.1 (he ▸ hb)
      have h := cross a b (by simp [ha]) (by simp [hb])
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq,ea,eb,if_false] at h
      omega
    obtain ⟨xs,ys,he⟩ := ih hn.2 ct
    cases e with
    | inl a => exact ⟨a::xs,ys,by simp [he,join]⟩
    | inr b =>
      have noleft : xs=[] := by
        cases xs with
        | nil => rfl
        | cons a xs =>
          have ha : Sum.inl a ∈ w := by simp [he,join]
          have h := cross a b (by simp [ha]) (by simp)
          simp at h
      exact ⟨[],b::ys,by simp [he,noleft,join]⟩

def ordinal (QA : A → A → Prop) (QB : B → B → Prop) : Sum A B → Sum A B → Prop
  | .inl a, .inl b => QA a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr a, .inr b => QB a b

theorem ordinal_strict (QA : A → A → Prop) (QB : B → B → Prop)
    (ha : StrictOrder QA) (hb : StrictOrder QB) : StrictOrder (ordinal QA QB) := by
  constructor
  · intro a h; cases a <;> exact (by first | exact ha.1 _ h | exact hb.1 _ h)
  · intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [ordinal]
    · exact ha.2 _ _ _ hab hbc
    · exact hb.2 _ _ _ hab hbc

theorem join_extends_iff (allA : List A) (allB : List B)
    (completeA : ∀ a, a∈allA) (completeB : ∀ b, b∈allB)
    (QA : A → A → Prop) (QB : B → B → Prop) (xs : List A) (ys : List B) :
    Extends (semantics (join allA allB)) (ordinal QA QB) (join xs ys) ↔
      Extends (semantics allA) QA xs ∧ Extends (semantics allB) QB ys := by
  constructor
  · intro h
    have hx : xs.Perm allA := by
      have hh := h.1.filterMap (fun x => match x with | .inl a => some a | .inr _ => none)
      simpa [join,List.filterMap_map,Function.comp_def,filter_none] using hh
    have hy : ys.Perm allB := by
      have hh := h.1.filterMap (fun x => match x with | .inl _ => none | .inr b => some b)
      simpa [join,List.filterMap_map,Function.comp_def,filter_none] using hh
    refine ⟨⟨hx,?_⟩,⟨hy,?_⟩⟩
    · intro a b hab
      exact (preserves_left xs ys a b (hx.mem_iff.mpr (completeA a))
        (hx.mem_iff.mpr (completeA b))).mp (h.2 (.inl a) (.inl b) hab)
    · intro a b hab
      exact (preserves_right xs ys a b).mp (h.2 (.inr a) (.inr b) hab)
  · rintro ⟨hx,hy⟩
    refine ⟨(hx.1.map Sum.inl).append (hy.1.map Sum.inr),?_⟩
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact (preserves_left xs ys a b (hx.1.mem_iff.mpr (completeA a))
          (hx.1.mem_iff.mpr (completeA b))).mpr (hx.2 a b hab)
      | inr b => exact all_left_before_right xs ys a b (hx.1.mem_iff.mpr (completeA a))
    | inr a =>
      cases b with
      | inl b => exact False.elim hab
      | inr b => exact (preserves_right xs ys a b).mpr (hy.2 a b hab)

theorem ordinal_extends_iff (allA : List A) (allB : List B)
    (nd : (join allA allB).Nodup)
    (completeA : ∀ a, a∈allA) (completeB : ∀ b, b∈allB)
    (QA : A → A → Prop) (QB : B → B → Prop) (w : List (Sum A B)) :
    Extends (semantics (join allA allB)) (ordinal QA QB) w ↔
      ∃ xs ys, w=join xs ys ∧ Extends (semantics allA) QA xs ∧ Extends (semantics allB) QB ys := by
  constructor
  · intro h
    obtain ⟨xs,ys,he⟩ := cross_forces_join w (h.1.nodup_iff.mpr nd)
      (fun a b _ _ => h.2 (.inl a) (.inr b) True.intro)
    exact ⟨xs,ys,he,(join_extends_iff allA allB completeA completeB QA QB xs ys).mp (he ▸ h)⟩
  · rintro ⟨xs,ys,he,hx,hy⟩
    rw [he]
    exact (join_extends_iff allA allB completeA completeB QA QB xs ys).mpr ⟨hx,hy⟩

theorem ordinal_sound (allA : List A) (allB : List B)
    (nd : (join allA allB).Nodup) (completeA : ∀ a, a∈allA) (completeB : ∀ b, b∈allB)
    (LA : List A → Prop) (LB : List B → Prop) (QA : A → A → Prop) (QB : B → B → Prop)
    (ha : Sound (semantics allA) LA QA) (hb : Sound (semantics allB) LB QB) :
    Sound (semantics (join allA allB)) (blockedLegal LA LB) (ordinal QA QB) := by
  intro w hw
  obtain ⟨xs,ys,he,hx,hy⟩ := (ordinal_extends_iff allA allB nd completeA completeB QA QB w).mp hw
  exact ⟨xs,ys,he,ha xs hx,hb ys hy⟩

#print axioms cross_forces_join
#print axioms ordinal_strict
#print axioms join_extends_iff
#print axioms ordinal_extends_iff
#print axioms ordinal_sound
theorem paired_cover_upper {CA CB : Type} (allA : List A) (allB : List B)
    (nd : (join allA allB).Nodup) (completeA : ∀ a, a∈allA) (completeB : ∀ b, b∈allB)
    (LA : List A → Prop) (LB : List B → Prop)
    (QA : CA → A → A → Prop) (QB : CB → B → B → Prop)
    (sa : ∀ c, StrictOrder (QA c)) (sb : ∀ c, StrictOrder (QB c))
    (ha : ∀ c, Sound (semantics allA) LA (QA c)) (hb : ∀ c, Sound (semantics allB) LB (QB c))
    (coverA : ∀ xs, LA xs → ∃ c, Extends (semantics allA) (QA c) xs)
    (coverB : ∀ ys, LB ys → ∃ c, Extends (semantics allB) (QB c) ys) :
    (∀ c : CA × CB, StrictOrder (ordinal (QA c.1) (QB c.2)) ∧
      Sound (semantics (join allA allB)) (blockedLegal LA LB) (ordinal (QA c.1) (QB c.2))) ∧
    (∀ w, blockedLegal LA LB w → ∃ c : CA × CB,
      Extends (semantics (join allA allB)) (ordinal (QA c.1) (QB c.2)) w) := by
  constructor
  · intro c
    exact ⟨ordinal_strict _ _ (sa c.1) (sb c.2),
      ordinal_sound allA allB nd completeA completeB LA LB _ _ (ha c.1) (hb c.2)⟩
  · rintro w ⟨xs,ys,he,hx,hy⟩
    obtain ⟨a,ha⟩ := coverA xs hx
    obtain ⟨b,hb⟩ := coverB ys hy
    refine ⟨(a,b),?_⟩
    rw [he]
    exact (join_extends_iff allA allB completeA completeB _ _ xs ys).mpr ⟨ha,hb⟩

theorem bad_right_stays_bad (LA : List A → Prop) (LB : List B → Prop)
    (zx : List A) (zy : List B) (bad : ¬LB zy) : ¬blockedLegal LA LB (join zx zy) := by
  rintro ⟨xs,ys,he,hx,hy⟩
  have h := congrArg rights he
  simp only [right_join] at h
  exact bad (h.symm ▸ hy)

theorem blocked_bad_common_extension_right
    (allA : List A) (allB : List B) (completeA : ∀ a, a∈allA)
    (LA : List A → Prop) (LB : List B → Prop)
    (sx tx zx : List A) (sy ty zy : List B)
    (hs : sx.Perm allA) (ht : tx.Perm allA)
    (hx : Extends (semantics allA) (Common (semantics allA) sx tx) zx)
    (hy : Extends (semantics allB) (Common (semantics allB) sy ty) zy)
    (bad : ¬LB zy) :
    Extends (semantics (join allA allB))
      (Common (semantics (join allA allB)) (join sx sy) (join tx ty)) (join zx zy) ∧
      ¬blockedLegal LA LB (join zx zy) :=
  ⟨common_extension_join allA allB completeA sx tx zx sy ty zy hs ht hx hy,
    bad_right_stays_bad LA LB zx zy bad⟩

#print axioms paired_cover_upper
#print axioms bad_right_stays_bad
#print axioms blocked_bad_common_extension_right
end ChainBlockedOrder
