import FactorRecovery
import ProductUpper
namespace ChainPaddingTransport
open LocalCertificate

theorem forced_head (a : Nat) (rest w : List Nat) (hp : w.Perm (a::rest))
    (before : ∀ b ∈ rest, w.idxOf a < w.idxOf b) :
    ∃ tail, w=a::tail ∧ tail.Perm rest := by
  cases w with
  | nil => have h := hp.length_eq; simp at h
  | cons b bs =>
    by_cases he : b=a
    · subst b
      exact ⟨bs,rfl,List.Perm.cons_inv hp⟩
    · have bm : b ∈ a::rest := hp.mem_iff.mp (by simp)
      have br : b ∈ rest := (List.mem_cons.mp bm).resolve_left he
      have h := before b br
      simp at h

theorem forced_prefix (pre rest w : List Nat) (nd : (pre++rest).Nodup)
    (hp : w.Perm (pre++rest))
    (before : ∀ a ∈ pre, ∀ b ∈ pre++rest,
      (pre++rest).idxOf a < (pre++rest).idxOf b → w.idxOf a < w.idxOf b) :
    ∃ mid, w=pre++mid ∧ mid.Perm rest := by
  induction pre generalizing w with
  | nil => exact ⟨w,rfl,by simpa using hp⟩
  | cons a pre ih =>
    have nds := List.nodup_cons.mp nd
    have head : ∀ b ∈ pre++rest, w.idxOf a < w.idxOf b := by
      intro b hb
      have ne : a ≠ b := by intro he; subst b; exact nds.1 hb
      apply before a (by simp) b (by simp [hb])
      simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,ne]
    obtain ⟨tail,he,ht⟩ := forced_head a (pre++rest) w hp head
    subst w
    have bt : ∀ b ∈ pre, ∀ c ∈ pre++rest,
        (pre++rest).idxOf b < (pre++rest).idxOf c → tail.idxOf b < tail.idxOf c := by
      intro b hb c hc hbc
      have ab : a ≠ b := by intro he; subst b; exact nds.1 (by simp [hb])
      have ac : a ≠ c := by intro he; subst c; exact nds.1 hc
      have hh := before b (by simp [hb]) c (by simp [hc])
      simp only [List.cons_append,List.idxOf_cons,cond_eq_ite,beq_iff_eq,ab,ac,if_false] at hh
      exact Nat.lt_of_succ_lt_succ (hh (by omega))
    obtain ⟨mid,hm,hperm⟩ := ih tail nds.2 ht bt
    exact ⟨mid,by simp [hm],hperm⟩

#print axioms forced_head
#print axioms forced_prefix
theorem forced_last (w : List Nat) (a : Nat) (nd : w.Nodup) (ha : a ∈ w)
    (before : ∀ b ∈ w, b ≠ a → w.idxOf b < w.idxOf a) :
    ∃ mid, w=mid++[a] := by
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp ha
  subst w
  cases post with
  | nil => exact ⟨pre,rfl⟩
  | cons b bs =>
    have hn := List.nodup_append.mp nd
    have ab : a ≠ b := by
      have h := (List.nodup_cons.mp hn.2.1).1
      exact fun he => h (by simp [he])
    have ap : a ∉ pre := by
      intro hm
      exact hn.2.2 a hm a (by simp) rfl
    have bp : b ∉ pre := by
      intro hm
      exact hn.2.2 b hm b (by simp) rfl
    have hh := before b (by simp) (Ne.symm ab)
    simp [List.idxOf_append,ap,bp,List.idxOf_cons,cond_eq_ite,beq_iff_eq,ab] at hh
    omega

#print axioms forced_last
theorem boundary_factor (pre core : List Nat) (last : Nat) (w : List Nat)
    (nd : (pre ++ (core ++ [last])).Nodup) (hp : w.Perm (pre ++ (core ++ [last])))
    (first : ∀ a ∈ pre, ∀ b ∈ pre ++ (core ++ [last]),
      (pre ++ (core ++ [last])).idxOf a < (pre ++ (core ++ [last])).idxOf b → w.idxOf a < w.idxOf b)
    (lastBefore : ∀ b ∈ w, b ≠ last → w.idxOf b < w.idxOf last) :
    ∃ mid, w=pre ++ mid ++ [last] ∧ mid.Perm core := by
  obtain ⟨tail,he,ht⟩ := forced_prefix pre (core++[last]) w nd hp first
  subst w
  have wn := hp.nodup_iff.mpr nd
  have split := List.nodup_append.mp wn
  have lm : last ∈ tail := ht.mem_iff.mpr (by simp)
  have lp : last ∉ pre := fun h => split.2.2 last h last lm rfl
  have beforeTail : ∀ b ∈ tail, b ≠ last → tail.idxOf b < tail.idxOf last := by
    intro b hb hne
    have bp : b ∉ pre := fun h => split.2.2 b h b hb rfl
    have h := lastBefore b (by simp [hb]) hne
    simp only [List.idxOf_append,if_neg bp,if_neg lp] at h
    omega
  obtain ⟨mid,hm⟩ := forced_last tail last split.2.1 lm beforeTail
  refine ⟨mid,by simp [hm,List.append_assoc],?_⟩
  rw [hm] at ht
  exact (List.perm_append_right_iff [last]).mp ht

theorem inner_before_iff (pre mid post : List Nat) (a b : Nat)
    (nd : (pre ++ (mid ++ post)).Nodup) (ha : a ∈ mid) (hb : b ∈ mid) :
    (pre ++ (mid ++ post)).idxOf a < (pre ++ (mid ++ post)).idxOf b ↔ mid.idxOf a < mid.idxOf b := by
  have hn := List.nodup_append.mp nd
  have ap : a ∉ pre := fun h => hn.2.2 a h a (by simp [ha]) rfl
  have bp : b ∉ pre := fun h => hn.2.2 b h b (by simp [hb]) rfl
  simp [List.idxOf_append,ap,bp,ha,hb]

#print axioms boundary_factor
#print axioms inner_before_iff
end ChainPaddingTransport
