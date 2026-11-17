import ErasurePebbling.NextPointLower

/-!
# Rigidity on the triangular frontier

At `n = T(p) + e·T(p−1)` the shortest clean plans have `L₀ = 2n − 1 + 2(n − A)` moves
(`Triangular.mstar_exact`).  Every such plan places each cell the same number of times, and
erases the same cells: reading the chain from the bottom, a fixed automaton `pst` decides
for each cell whether it is placed once or twice and whether its last removal is an erasure
(`rigidity`).  So the placement-count vector and the set of erased cells do not depend on
the plan (`counts_unique`); for `p = 4, e = 1` the once-placed cells below the target are
`3, 5, 6, 7, 9, 10` (nodes, 1-based) and node `7` is erased (`example_p4_e1`).

The automaton keeps `(k, g)`: the rank `k` of the last single in the current run and the
number `g` of doubles since then.  A run is full at `k = p − 1`; the next cell starts a new run
and is erased.  Otherwise the next single comes exactly after `p − 2 − k` doubles.  The proof
reads this off the tight form of the frontier bound (`NextPointLower.Tr.frontier_eq`): at the
frontier every gap meets its capacity `p − 1 − k` (`tight_gap`), and a double always leaves
room for at least one more (`double_room`).
-/

namespace ErasurePebbling.FrontierRigidity

open RevPebbling.PebblingFoundations
open ErasurePebbling.NextPointLower
open ErasurePebbling.NextPointLower.Tr

/-- The frontier automaton: state `(k, g)` before cell `i`. -/
def pst (p : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | i + 1 =>
      let x := pst p i
      if x.1 + 1 = p then (1, 0) else if x.2 + x.1 + 2 = p then (x.1 + 1, 0) else (x.1, x.2 + 1)

/-- Cell `i` (0-based) is placed once. -/
def psingle (p i : Nat) : Bool := decide ((pst p i).1 + 1 = p ∨ (pst p i).2 + (pst p i).1 + 2 = p)

/-- Cell `i` starts a new run; its last removal is the erasure. -/
def pasc (p i : Nat) : Bool := decide ((pst p i).1 + 1 = p)

/-- The example of the 2026-11-11 note: `p = 4, e = 1, n = 11`. -/
theorem example_p4_e1 :
    (List.range 10).filter (psingle 4 ·) = [2, 4, 5, 6, 8, 9] ∧
    (List.range 10).filter (pasc 4 ·) = [6] := by decide

namespace Tr

variable {T : Tr}

theorem kr_mono_run (x : Nat) : ∀ d, (∀ w, x < w → w ≤ x + d → ¬ T.asc w) →
    T.kr x + (if T.single (x + d) ∧ 0 < d then 1 else 0) ≤ T.kr (x + d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
      intro h
      have := ih (fun w a b => h w a (by omega))
      have hk := T.kr_succ (x + d)
      rw [show x + d + 1 = x + (d + 1) by omega, if_neg (h (x + (d + 1)) (by omega) (Nat.le_refl _))] at hk
      rw [hk]
      have : T.kr x ≤ T.kr (x + d) := by split at this <;> omega
      by_cases hs : T.single (x + (d + 1))
      · rw [if_pos ⟨hs, by omega⟩, if_pos hs]; omega
      · rw [if_neg (fun h => hs h.1), if_neg hs]; omega

theorem kr_flat (y : Nat) : ∀ d, (∀ z, y < z → z ≤ y + d → ¬ T.single z ∧ ¬ T.asc z) →
    T.kr (y + d) = T.kr y := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro h
      have hz := h (y + (d + 1)) (by omega) (Nat.le_refl _)
      have hk := T.kr_succ (y + d)
      rw [show y + d + 1 = y + (d + 1) by omega, if_neg hz.2, if_neg hz.1] at hk
      rw [hk, ih (fun z a b => h z a (by omega))]; omega

theorem gap_add (y : Nat) : ∀ d, (∀ z, y ≤ z → z < y + d → ¬ T.single z) → T.gap (y + d) = T.gap y + d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro h
      rw [show y + (d + 1) = (y + d) + 1 by omega]
      simp only [Tr.gap]
      rw [if_neg (h (y + d) (by omega) (by omega)), ih (fun z a b => h z a (by omega))]; omega

section rig
variable {e : Nat} (F : T.Forced e) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
  (hfr : T.n = Triangular.tri T.p + e * Triangular.tri (T.p - 1))
include F hp hn

/-- At the frontier every gap meets its capacity. -/
theorem tight_gap (hfr : T.n = Triangular.tri T.p + e * Triangular.tri (T.p - 1))
    {s : Nat} (hs : T.single s) (hsn : s < T.n - 1) (hna : ¬ T.asc s) :
    T.gap s + T.kr s + 1 = T.p := by
  obtain ⟨h, hpt⟩ := frontier_eq F hp hn
  have heq : rsum (T.n - 1) (fun i => if T.single i then T.gap i else 0) =
      rsum (T.n - 1) (fun i => if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0) := by omega
  have := rsum_eq_of_le _ _ _ hpt heq s hsn
  simp only [if_pos hs, if_pos (And.intro hs hna)] at this
  have hk := T.kr_le (c := s + 1) (by omega) (by omega) (by omega)
  rw [show s + 1 - 1 = s by omega] at hk
  omega

/-- A cell whose rank is full starts a new run. -/
theorem full_is_asc {i : Nat} (hi1 : 1 ≤ i) (hi : i < T.n - 1) (hk : T.kr (i - 1) + 1 = T.p) :
    T.asc i := by
  apply Classical.byContradiction; intro hna
  obtain ⟨c, h1, h2, h3, h4⟩ := T.next_bnd hn (T.n - 1 - (i - 1)) (i - 1) (by omega) (by omega)
  have hci : c ≠ i := by
    intro hc; subst hc
    rcases h3 with h | h
    · omega
    · exact hna h
  obtain ⟨hc1, _⟩ := bnd_le F hp hn h3
  have hkc := bnd_kr F hp hn h3 hc1
  have hsc := end_single F hp hn h3
  have := kr_mono_run (T := T) (i - 1) (c - 1 - (i - 1)) (fun w a b => h4 w a (by omega))
  rw [show i - 1 + (c - 1 - (i - 1)) = c - 1 by omega, if_pos ⟨hsc, by omega⟩] at this
  omega

theorem next_single : ∀ d y, y + d = T.n - 2 → ¬ T.single y →
    ∃ s, y < s ∧ s < T.n - 1 ∧ T.single s ∧ ∀ z, y < z → z < s → ¬ T.single z := by
  have hlast : T.single (T.n - 2) := by
    have := end_single F hp hn (c := T.n - 1) (Or.inl rfl)
    rwa [show T.n - 1 - 1 = T.n - 2 by omega] at this
  intro d
  induction d with
  | zero => intro y hy hs; exact absurd (by rw [show y = T.n - 2 by omega]; exact hlast) hs
  | succ d ih =>
      intro y hy hs
      by_cases h1 : T.single (y + 1)
      · exact ⟨y + 1, by omega, by omega, h1, fun z a b => by omega⟩
      · obtain ⟨s, a, b, c, d'⟩ := ih (y + 1) (by omega) h1
        refine ⟨s, by omega, b, c, fun z za zb => ?_⟩
        by_cases hz : z = y + 1
        · subst hz; exact h1
        · exact d' z (by omega) zb

/-- A double leaves room for at least one more cell before the next single. -/
theorem double_room {i : Nat} (hi : i < T.n - 1) (hs : ¬ T.single i) (hna : ¬ T.asc i) :
    T.gap i + T.kr i + 3 ≤ T.p := by
  obtain ⟨s, h1, h2, h3, h4⟩ := next_single F hp hn (T.n - 2 - i) i (by omega) hs
  have hnas : ¬ T.asc s := by
    intro ha
    have := end_single F hp hn (Or.inr ha)
    by_cases hsi : s - 1 = i
    · rw [hsi] at this; exact hs this
    · exact h4 (s - 1) (by omega) (by omega) this
  have hg := gap_add (T := T) i (s - i) (fun z a b => by
    by_cases hz : z = i
    · subst hz; exact hs
    · exact h4 z (by omega) (by omega))
  rw [show i + (s - i) = s by omega] at hg
  have hkf := kr_flat (T := T) i (s - 1 - i) (fun z a b =>
    ⟨h4 z a (by omega), fun ha => h4 z a (by omega) (asc_single F hp hn ha)⟩)
  rw [show i + (s - 1 - i) = s - 1 by omega] at hkf
  have hks := T.kr_succ (s - 1)
  rw [show s - 1 + 1 = s by omega, if_pos h3, if_neg hnas] at hks
  have := gap_bound F hp hn h3 h2 hnas
  omega

/-- Rank of the last single before cell `i` in its run. -/
def krm (T : Tr) (i : Nat) : Nat := if i = 0 then 0 else T.kr (i - 1)

/-- One step of the automaton. -/
theorem step (hfr : T.n = Triangular.tri T.p + e * Triangular.tri (T.p - 1))
    {i : Nat} (hi : i < T.n - 1) (h : pst T.p i = (krm T i, T.gap i)) :
    (T.single i ↔ psingle T.p i = true) ∧ (T.asc i ↔ pasc T.p i = true) ∧
      pst T.p (i + 1) = (krm T (i + 1), T.gap (i + 1)) := by
  have hst : pst T.p (i + 1) = (let x := pst T.p i
      if x.1 + 1 = T.p then (1, 0) else if x.2 + x.1 + 2 = T.p then (x.1 + 1, 0) else (x.1, x.2 + 1)) := rfl
  have hg1 : T.gap (i + 1) = if T.single i then 0 else T.gap i + 1 := rfl
  have hk1 : krm T (i + 1) = T.kr i := by simp [krm]
  rw [hst, h, hk1, hg1]
  unfold psingle pasc
  rw [h]
  simp only
  by_cases hfull : krm T i + 1 = T.p
  · -- a new run starts at `i`
    have hi1 : 1 ≤ i := by
      apply Classical.byContradiction; intro h0
      have : i = 0 := by omega
      subst this
      have : krm T 0 = 0 := rfl
      omega
    have hkm : krm T i = T.kr (i - 1) := by simp [krm]; omega
    have ha := full_is_asc F hp hn hi1 hi (by rw [← hkm]; exact hfull)
    have hs := asc_single F hp hn ha
    have hk := kr_of_asc F hp hn ha
    rw [if_pos hfull, if_pos hs, hk]
    simp [hfull, ha, hs]
  · have hna : ¬ T.asc i := by
      intro ha
      have := F.kr_asc (i - 1) (by have := ha.2.1; have := ha.1; omega) (by rw [show i - 1 + 1 = i by have := ha.1; omega]; exact ha)
      have hkm : krm T i = T.kr (i - 1) := by simp [krm]; have := ha.1; omega
      omega
    have hki : T.kr i = (if T.single i then 1 else 0) + krm T i := by
      by_cases h0 : i = 0
      · subst h0; rw [T.kr_zero]; simp [krm]
      · have := T.kr_succ (i - 1)
        rw [show i - 1 + 1 = i by omega, if_neg hna] at this
        rw [this]; simp [krm, h0]
    rw [if_neg hfull]
    by_cases hs : T.single i
    · have ht := tight_gap F hp hn hfr hs hi hna
      rw [if_pos hs] at hki
      have hgk : T.gap i + krm T i + 2 = T.p := by omega
      rw [if_pos hgk, if_pos hs, hki]
      simp [hs, hna, hfull, hgk]; omega
    · have hr := double_room F hp hn hi hs hna
      rw [if_neg hs] at hki
      have hgk : ¬ T.gap i + krm T i + 2 = T.p := by omega
      rw [if_neg hgk, if_neg hs, hki]
      simp [hs, hna, hfull, hgk]

theorem invariant (hfr : T.n = Triangular.tri T.p + e * Triangular.tri (T.p - 1)) :
    ∀ i, i ≤ T.n - 1 → pst T.p i = (krm T i, T.gap i) := by
  intro i
  induction i with
  | zero => intro _; simp [pst, krm, Tr.gap]
  | succ i ih => intro hi; exact (step F hp hn hfr (by omega) (ih (by omega))).2.2

theorem pattern (hfr : T.n = Triangular.tri T.p + e * Triangular.tri (T.p - 1))
    {i : Nat} (hi : i < T.n - 1) :
    (T.single i ↔ psingle T.p i = true) ∧ (T.asc i ↔ pasc T.p i = true) :=
  let h := step F hp hn hfr hi (invariant F hp hn hfr i (by omega))
  ⟨h.1, h.2.1⟩

end rig
end Tr

/-! ## Statement on clean plans -/

theorem count_eq_c (n p e : Nat) (s : List Nat) (hn : 1 ≤ n) (h : IsPlay n p e s) (i : Nat) :
    (ofPlay n p e s hn h).c i = s.count i := by
  show (s.take s.length).count i = s.count i
  rw [List.take_length]

theorem isE_iff (n p e : Nat) (s : List Nat) (hn : 1 ≤ n) (h : IsPlay n p e s) {k : Nat}
    (hk : k < s.length) :
    isErase (execB (empty n) (s.take k)) (s.getD k 0) = true ↔ (ofPlay n p e s hn h).isE k := by
  have hmv := h.bounds _ (getD_mem hk)
  show _ ↔ ((s.take k).count (s.getD k 0) % 2 = 1 ∧ 0 < s.getD k 0 ∧
    (s.take k).count (s.getD k 0 - 1) % 2 = 0)
  unfold isErase okMove
  rw [nth_state n s k _ hmv, nth_state n s k _ (by omega)]
  generalize (s.take k).count (s.getD k 0) = A
  generalize (s.take k).count (s.getD k 0 - 1) = B
  generalize s.getD k 0 = x
  by_cases h1 : A % 2 = 1 <;> by_cases h2 : x = 0 <;> by_cases h3 : B % 2 = 1 <;>
    simp [h1, h2, h3] <;> omega

/-- **Rigidity at the frontier.**  Every clean plan with peak `p`, at most `e` erasures and
at most `L₀` moves at `n = T(p) + e·T(p−1)`: cell `i < n − 1` is placed once if
`psingle p i` and twice otherwise, the target once; it uses exactly `e` erasures, and a move
is an erasure exactly when it is the last move on a cell with `pasc p`. -/
theorem rigidity (n p e : Nat) (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hfr : n = Triangular.tri p + e * Triangular.tri (p - 1)) (s : List Nat) (h : IsPlay n p e s)
    (hlen : s.length + 2 * ((p - 1) * (e + 1) + 1) + 1 ≤ 4 * n) :
    (∀ i, i < n - 1 → s.count i = if psingle p i then 2 else 4) ∧
    s.count (n - 1) = 1 ∧
    erasures (empty n) s = e ∧
    (∀ k, k < s.length →
      (isErase (execB (empty n) (s.take k)) (s.getD k 0) = true ↔
        (s.getD k 0 < n - 1 ∧ pasc p (s.getD k 0) = true ∧ (s.drop (k + 1)).count (s.getD k 0) = 0))) := by
  let T := ofPlay n p e s (by omega) h
  have hT : T.n = n := rfl
  have hTp : T.p = p := rfl
  have F := T.forced e hp hn hlen (by rw [eras_ofPlay]; exact h.budget)
  have hpat : ∀ {i}, i < n - 1 → (T.single i ↔ psingle p i = true) ∧ (T.asc i ↔ pasc p i = true) :=
    fun {i} hi => Tr.pattern F hp hn hfr (i := i) hi
  have hc := count_eq_c n p e s (by omega) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [← hc i]
    by_cases hs : T.single i
    · rw [if_pos ((hpat hi).1.mp hs)]; exact hs
    · rw [if_neg (fun h' => hs ((hpat hi).1.mpr h'))]
      exact F.c_double i hi hs
  · rw [← hc]; exact F.c_last1
  · rw [← eras_ofPlay n p e s (by omega) h]; exact F.eras_eq
  · intro k hk
    have hmv := h.bounds _ (getD_mem hk)
    have hsplit : (s.take (k + 1)).count (s.getD k 0) + (s.drop (k + 1)).count (s.getD k 0) =
        s.count (s.getD k 0) := by
      rw [← List.count_append, List.take_append_drop]
    have hNk : T.N (s.getD k 0) (k + 1) = (s.take (k + 1)).count (s.getD k 0) := rfl
    have hmvk : T.mv k = s.getD k 0 := rfl
    rw [isE_iff n p e s (by omega) h hk]
    constructor
    · intro hE
      obtain ⟨y, hy, hty⟩ := T.isE_asc (by rw [F.numAsc_eq, F.eras_eq]) hk hE
      have hcy : 0 < T.c y := by have := T.c_ge_two (i := y) hy.2.1; omega
      obtain ⟨_, tm, _⟩ := T.tau_spec hcy
      rw [hty, hmvk] at tm
      subst tm
      have hdone := (T.N_eq_c_iff hcy (show k + 1 ≤ T.L by exact hk)).mpr (by omega)
      rw [hNk, hc] at hdone
      exact ⟨hy.2.1, (hpat hy.2.1).2.mp hy, by omega⟩
    · rintro ⟨hlt, ha, hd⟩
      have hy := (hpat hlt).2.mpr ha
      have hcy : 0 < T.c (s.getD k 0) := by have := T.c_ge_two (i := s.getD k 0) hlt; omega
      have hdone : T.N (s.getD k 0) (k + 1) = T.c (s.getD k 0) := by rw [hNk, hc]; omega
      have h1 := (T.N_eq_c_iff hcy (show k + 1 ≤ T.L by exact hk)).mp hdone
      have h2 := T.N_lt_of_mv (i := s.getD k 0) hmvk (show k < k + 1 by omega) (show k + 1 ≤ T.L by exact hk)
      have h3 : ¬ T.tau (s.getD k 0) < k := fun hl => by
        have q1 := (T.N_eq_c_iff hcy (show k ≤ T.L from Nat.le_of_lt hk)).mpr hl
        have q2 := T.N_le_c (s.getD k 0) (show k + 1 ≤ T.L by exact hk)
        omega
      have htk : T.tau (s.getD k 0) = k := by omega
      have := T.asc_isE hy
      rwa [htk] at this

/-- The placement counts of a plan meeting the bound at the frontier do not depend on the plan. -/
theorem counts_unique (n p e : Nat) (hp : 2 ≤ p) (hn : 2 ≤ n)
    (hfr : n = Triangular.tri p + e * Triangular.tri (p - 1)) (s t : List Nat)
    (hs : IsPlay n p e s) (ht : IsPlay n p e t)
    (hls : s.length + 2 * ((p - 1) * (e + 1) + 1) + 1 ≤ 4 * n)
    (hlt : t.length + 2 * ((p - 1) * (e + 1) + 1) + 1 ≤ 4 * n) :
    ∀ i, s.count i = t.count i := by
  intro i
  have a := rigidity n p e hp hn hfr s hs hls
  have b := rigidity n p e hp hn hfr t ht hlt
  by_cases hi : i < n - 1
  · rw [a.1 i hi, b.1 i hi]
  · by_cases he : i = n - 1
    · subst he; rw [a.2.1, b.2.1]
    · have h1 : i ∉ s := fun hm => by have := hs.bounds i hm; omega
      have h2 : i ∉ t := fun hm => by have := ht.bounds i hm; omega
      rw [List.count_eq_zero_of_not_mem h1, List.count_eq_zero_of_not_mem h2]

/-- At the frontier `M* = L₀`, so every shortest plan meets the length bound of `rigidity`. -/
theorem optimal_meets_bound (p e : Nat) (hp : 3 ≤ p) (s : List Nat)
    (h : IsPlay (Triangular.tri p + e * Triangular.tri (p - 1)) p e s)
    (hopt : ∀ t, IsPlay (Triangular.tri p + e * Triangular.tri (p - 1)) p e t → s.length ≤ t.length) :
    s.length + 2 * ((p - 1) * (e + 1) + 1) + 1 ≤ 4 * (Triangular.tri p + e * Triangular.tri (p - 1)) := by
  have hu := Triangular.tri_ge (p - 1)
  have hv := Triangular.tri_ge p
  have hle : (p - 1) * e ≤ e * Triangular.tri (p - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
  have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
  obtain ⟨⟨t, ht, htl⟩, _⟩ := Triangular.mstar_exact p e (Triangular.tri p + e * Triangular.tri (p - 1))
    hp (by omega) (Nat.le_refl _)
  have := hopt t ht
  omega

end ErasurePebbling.FrontierRigidity
