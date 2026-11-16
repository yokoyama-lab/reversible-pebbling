import PhysicalCover
namespace PrecedenceGuard
open ErasureCover
universe u
variable {α : Type u} [DecidableEq α]
/-- The edge appending b is retained precisely when all Q-predecessors have already occurred. -/
def Guard (Q : α→α→Prop) (pre : List α) (b : α) : Prop := ∀a,Q a b→a∈pre
def Online (Q : α→α→Prop) (w : List α) : Prop :=
 ∀pre b post,w=pre++b::post→Guard Q pre b

theorem idx_at_split (pre : List α) (b : α) (post : List α)
 (h : (pre++b::post).Nodup) : (pre++b::post).idxOf b=pre.length := by
 have hb : b∉pre := by
  intro hb
  have nd := List.nodup_append.mp h
  exact nd.2.2 b hb b (by simp) rfl
 simp [List.idxOf_append,hb]

theorem before_split_iff (pre : List α) (b a : α) (post : List α)
 (h : (pre++b::post).Nodup) :
 (pre++b::post).idxOf a < (pre++b::post).idxOf b ↔ a∈pre := by
 rw [idx_at_split pre b post h,List.idxOf_append]
 by_cases ha : a∈pre
 · simp [ha,List.idxOf_lt_length_of_mem ha]
 · simp [ha]

theorem online_iff_order (w : List α) (Q : α→α→Prop) (h : w.Nodup)
 (ht : ∀a b,Q a b→b∈w) :
 Online Q w ↔ ∀a b,Q a b→w.idxOf a<w.idxOf b := by
 constructor
 · intro hg a b hab
   obtain ⟨pre,post,eq⟩ := List.mem_iff_append.mp (ht a b hab)
   subst w
   exact (before_split_iff pre b a post h).mpr (hg pre b post rfl a hab)
 · intro ho pre b post eq a hab
   subst w
   exact (before_split_iff pre b a post h).mp (ho a b hab)
#print axioms online_iff_order
end PrecedenceGuard
namespace PrecedenceGuard
open ErasureCover LocalCertificate
/-- Numeric occurrence labels carry Q only inside the fixed finite event alphabet. -/
def liftQ {n : Nat} (Q : Fin n→Fin n→Prop) (a b : Nat) : Prop :=
 ∃i j : Fin n,a=i.val ∧ b=j.val ∧ Q i j

theorem online_iff_extends (n : Nat) (Q : Fin n→Fin n→Prop) (w : List Nat)
 (hw : isPermutation n w) :
 Online (liftQ Q) w ↔ Extends (semantics n) Q w := by
 have ht : ∀a b,liftQ Q a b→b∈w := by
  rintro a b ⟨i,j,rfl,rfl,_⟩
  exact ((EnumerationCorrectness.isPermutation_iff_perm_range n w).mp hw).mem_iff.mpr
   (List.mem_range.mpr j.isLt)
 rw [online_iff_order w (liftQ Q) hw.2.1 ht]
 constructor
 · intro h;exact ⟨hw,fun a b hab=>h a.val b.val ⟨a,b,rfl,rfl,hab⟩⟩
 · intro h a b hab
   obtain ⟨i,j,rfl,rfl,hij⟩ := hab
   exact h.2 i j hij

/-- Filtering paths of any existing permutation language by online guards recognizes exactly its Q-restriction. -/
theorem filter_language (n : Nat) (L : List Nat→Prop)
 (hL : ∀w,L w→isPermutation n w) (Q : Fin n→Fin n→Prop) (w : List Nat) :
 (L w ∧ Online (liftQ Q) w) ↔ (L w ∧ Extends (semantics n) Q w) := by
 constructor
 · rintro ⟨hw,hg⟩;exact ⟨hw,(online_iff_extends n Q w (hL w hw)).mp hg⟩
 · rintro ⟨hw,hg⟩;exact ⟨hw,(online_iff_extends n Q w (hL w hw)).mpr hg⟩

theorem physical_filter_language (r : Nat) (E : List Nat)
 (Q : Fin (25+16*r)→Fin (25+16*r)→Prop) (w : List Nat) :
 (ChainOccurrence.labelledLegal r E w ∧ Online (liftQ Q) w) ↔
 (ChainOccurrence.labelledLegal r E w ∧ Extends (semantics (25+16*r)) Q w) := by
 apply filter_language (25+16*r) (ChainOccurrence.labelledLegal r E)
 intro u hu
 have hp := hu.1
 simpa only [ChainOccurrence.table_length] using hp
#print axioms online_iff_extends
#print axioms filter_language
#print axioms physical_filter_language
end PrecedenceGuard
namespace PrecedenceGuard
universe u
variable {α : Type u} [DecidableEq α]
/-- Executable-shape prefix traversal: the event b is appended only when its guard passes. -/
def Runs (Q : α→α→Prop) : List α→List α→Prop
 | _,[] => True
 | done,b::bs => Guard Q done b ∧ Runs Q (done++[b]) bs

theorem runs_iff_splits (Q : α→α→Prop) (done w : List α) :
 Runs Q done w ↔ ∀pre b post,w=pre++b::post→Guard Q (done++pre) b := by
 induction w generalizing done with
 | nil => simp [Runs]
 | cons x xs ih =>
  rw [Runs,ih]
  constructor
  · rintro ⟨hx,hs⟩ pre b post eq
    cases pre with
    | nil => simp only [List.nil_append,List.cons.injEq] at eq
             obtain ⟨rfl,rfl⟩ := eq
             simpa using hx
    | cons y pre =>
      simp only [List.cons_append,List.cons.injEq] at eq
      obtain ⟨rfl,eq⟩ := eq
      simpa [List.append_assoc] using hs pre b post eq
  · intro h
    constructor
    · simpa using h [] x xs rfl
    · intro pre b post eq
      have hh := h (x::pre) b post (by simp [eq])
      simpa [List.append_assoc] using hh

theorem runs_empty_iff_online (Q : α→α→Prop) (w : List α) : Runs Q [] w ↔ Online Q w := by
 simpa [Online] using runs_iff_splits Q [] w

theorem physical_run_filter (r : Nat) (E : List Nat)
 (Q : Fin (25+16*r)→Fin (25+16*r)→Prop) (w : List Nat) :
 (ChainOccurrence.labelledLegal r E w ∧ Runs (liftQ Q) [] w) ↔
 (ChainOccurrence.labelledLegal r E w ∧ ErasureCover.Extends (LocalCertificate.semantics (25+16*r)) Q w) := by
 rw [runs_empty_iff_online]
 exact physical_filter_language r E Q w
#print axioms runs_empty_iff_online
#print axioms physical_run_filter
end PrecedenceGuard
