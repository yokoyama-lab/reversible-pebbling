import SlotConcat
import ProductUpper
namespace ChainWordRenaming
open ErasureCover
variable {A B : Type} [DecidableEq A] [DecidableEq B]
 theorem map_inverse (f : A → B) (g : B → A) (gf : ∀ a,g (f a)=a) (w : List A) :
   (w.map f).map g=w := by simpa only [List.map_map,Function.comp_def,gf] using List.map_id' w
 theorem idx_map_injective (f : A → B) (hf : ∀ a b,f a=f b→a=b) (w : List A) (a : A) :
   (w.map f).idxOf (f a)=w.idxOf a := by
   induction w with
   | nil => rfl
   | cons b w ih =>
     by_cases h : b=a
     · subst b; simp
     · have hn : f b ≠ f a := fun he => h (hf b a he)
       simp [List.idxOf_cons,beq_false_of_ne h,beq_false_of_ne hn,ih]
 def rename (g : B → A) (R : A → A → Prop) : B → B → Prop := fun b c => R (g b) (g c)
 theorem rename_strict (g : B → A) (R : A → A → Prop) (hs : StrictOrder R) :
   StrictOrder (rename g R) := ⟨fun b => hs.1 (g b),fun a b c => hs.2 (g a) (g b) (g c)⟩
 theorem extends_map_iff (f : A → B) (g : B → A)
   (gf : ∀ a,g (f a)=a) (fg : ∀ b,f (g b)=b) (all : List A) (R : A → A → Prop) (w : List A) :
   Extends (SlotConcat.semantics (all.map f)) (rename g R) (w.map f) ↔
     Extends (SlotConcat.semantics all) R w := by
   have fi : ∀ a b,f a=f b→a=b := by intro a b he; have := congrArg g he; simpa [gf] using this
   constructor
   · intro h
     have hp := h.1.map g
     rw [map_inverse f g gf w,map_inverse f g gf all] at hp
     refine ⟨hp,?_⟩
     intro a b hab
     have hh := h.2 (f a) (f b) (by simpa [rename,gf] using hab)
     simpa only [SlotConcat.semantics,idx_map_injective f fi] using hh
   · intro h
     refine ⟨h.1.map f,?_⟩
     intro b c hbc
     have hh := h.2 (g b) (g c) hbc
     change (w.map f).idxOf b < (w.map f).idxOf c
     rw [← fg b,← fg c,idx_map_injective f fi,idx_map_injective f fi]
     exact hh
 theorem renamed_sound (f : A → B) (g : B → A)
   (gf : ∀ a,g (f a)=a) (fg : ∀ b,f (g b)=b) (all : List A)
   (LA : List A → Prop) (LB : List B → Prop)
   (legal : ∀ w,LB (w.map f) ↔ LA w) (R : A → A → Prop)
   (hs : Sound (SlotConcat.semantics all) LA R) :
   Sound (SlotConcat.semantics (all.map f)) LB (rename g R) := by
   intro w hw
   have hi := map_inverse g f fg w
   have he : Extends (SlotConcat.semantics (all.map f)) (rename g R) ((w.map g).map f) := by simpa [hi] using hw
   have ha := (extends_map_iff f g gf fg all R (w.map g)).mp he
   have hl := (legal (w.map g)).mpr (hs _ ha)
   simpa [hi] using hl
#print axioms map_inverse
#print axioms idx_map_injective
#print axioms rename_strict
#print axioms extends_map_iff
#print axioms renamed_sound
 theorem cover_family_transfer {C : Type} (f : A → B) (g : B → A)
   (gf : ∀ a,g (f a)=a) (fg : ∀ b,f (g b)=b) (all : List A)
   (LA : List A → Prop) (LB : List B → Prop)
   (legal : ∀ w,LB (w.map f) ↔ LA w) (R : C → A → A → Prop)
   (strict : ∀c,StrictOrder (R c))
   (sound : ∀c,Sound (SlotConcat.semantics all) LA (R c))
   (covers : ∀w,LA w → ∃c,Extends (SlotConcat.semantics all) (R c) w) :
   (∀c,StrictOrder (rename g (R c))) ∧
   (∀c,Sound (SlotConcat.semantics (all.map f)) LB (rename g (R c))) ∧
   (∀w,LB w → ∃c,Extends (SlotConcat.semantics (all.map f)) (rename g (R c)) w) := by
   refine ⟨fun c => rename_strict g (R c) (strict c),
     fun c => renamed_sound f g gf fg all LA LB legal (R c) (sound c),?_⟩
   intro w hw
   have hi := map_inverse g f fg w
   have hl : LA (w.map g) := (legal (w.map g)).mp (by simpa [hi] using hw)
   obtain ⟨c,hc⟩ := covers (w.map g) hl
   refine ⟨c,?_⟩
   have he := (extends_map_iff f g gf fg all (R c) (w.map g)).mpr hc
   simpa [hi] using he
#print axioms cover_family_transfer
 theorem cover_lower_transfer (N : Nat) (f : A → B) (g : B → A)
   (gf : ∀ a,g (f a)=a) (fg : ∀ b,f (g b)=b) (all : List A)
   (LA : List A → Prop) (LB : List B → Prop)
   (legal : ∀ w,LB (w.map f) ↔ LA w)
   (lower : ∀ n (R : Fin n → A → A → Prop),
     (∀c,Sound (SlotConcat.semantics all) LA (R c)) →
     (∀w,LA w → ∃c,Extends (SlotConcat.semantics all) (R c) w) → N≤n)
   (n : Nat) (Q : Fin n → B → B → Prop)
   (hs : ∀c,Sound (SlotConcat.semantics (all.map f)) LB (Q c))
   (hc : ∀w,LB w → ∃c,Extends (SlotConcat.semantics (all.map f)) (Q c) w) : N≤n := by
   let R := fun c a b => Q c (f a) (f b)
   have eqrel (c : Fin n) : rename g (R c)=Q c := by
     funext a b
     simp [rename,R,fg]
   apply lower n R
   · intro c w hw
     have he := (extends_map_iff f g gf fg all (R c) w).mpr hw
     rw [eqrel] at he
     exact (legal w).mp (hs c (w.map f) he)
   · intro w hw
     obtain ⟨c,he⟩ := hc (w.map f) ((legal w).mpr hw)
     refine ⟨c,(extends_map_iff f g gf fg all (R c) w).mp ?_⟩
     simpa [eqrel] using he
#print axioms cover_lower_transfer
end ChainWordRenaming
