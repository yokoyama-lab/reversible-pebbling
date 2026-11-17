import ErasurePebbling.NextPoint

/-!
# One past the triangular frontier: the lower bound

`NextPoint` built a plan of `L₀ + 2` moves at `n = T(p) + e·T(p−1) + 1` and left two
candidates.  Here the smaller one is excluded, so `M*(n, p, e) = L₀ + 2` (`next_exact`) and
`M*(4e+8, 4, e) = 25 + 10e` (`p4_exact`).

The main statement is `frontier_lower`: a clean plan with peak `p` and at most `e`
erasures whose length is at most `L₀ = 2n − 1 + 2(n − A)`, `A = (p−1)(e+1)+1`, only exists for
`n ≤ T(p) + e·T(p−1)`.  The proof works on the plan directly (no contraction):

* `Tr` records a plan by its toggle counts `N i k`; `ofPlay` builds it from `IsPlay`.
* A cell `y` is an *ascent* when its last move comes after the last move of `y − 1`; its last
  move is then an erasure, so there are at most `e` ascents (`numAsc_le_eras`).  Between
  ascents the last-move times decrease (`tau_run`): these are the runs.
* Right after the cell `c` right of a run is first placed, all singles (cells placed once) of
  the run are on the board, so a run holds at most `p − 1` singles (`kr_le`).
* The length bound gives at least `A − 1` singles, so every bound is tight (`forced`): exactly
  `e` ascents, `p − 1` singles per run, every other cell placed exactly twice.
* Then run ends and ascents are singles (`end_single`, `asc_single`), the cell right of a run
  stays until the run's singles are gone (`bnd_on`), and below the `k`-th single of a run that
  is not a run start lie at most `p − 1 − k` doubles, all on the board at its last removal
  (`gap_bound`).  Summing over the runs gives the frontier (`frontier`).
-/

namespace ErasurePebbling.NextPointLower

open RevPebbling.PebblingFoundations

/-- A clean plan seen through its toggle counts: `N i k` is the number of moves on
cell `i` among the first `k` moves, `mv k` the cell moved at time `k`. -/
structure Tr where
  n : Nat
  L : Nat
  p : Nat
  mv : Nat → Nat
  N : Nat → Nat → Nat
  N_zero : ∀ i, N i 0 = 0
  N_succ : ∀ i k, k < L → N i (k + 1) = N i k + (if mv k = i then 1 else 0)
  mv_lt : ∀ k, k < L → mv k < n
  place : ∀ k, k < L → N (mv k) k % 2 = 0 → 0 < mv k → N (mv k - 1) k % 2 = 1
  peak : ∀ k, k ≤ L → rsum n (fun i => if N i k % 2 = 1 then 1 else 0) ≤ p
  final : ∀ i, i < n → (N i L % 2 = 1 ↔ i = n - 1)

namespace Tr

variable (T : Tr)

/-- Irreversible removal at time `k`. -/
def isE (k : Nat) : Prop :=
  T.N (T.mv k) k % 2 = 1 ∧ 0 < T.mv k ∧ T.N (T.mv k - 1) k % 2 = 0

instance (k : Nat) : Decidable (T.isE k) := by unfold isE; infer_instance

def eras : Nat := rsum T.L (fun k => if T.isE k then 1 else 0)

theorem N_step_le (i k : Nat) (hk : k < T.L) : T.N i (k + 1) ≤ T.N i k + 1 := by
  rw [T.N_succ i k hk]; split <;> omega

theorem N_mono_add (i : Nat) : ∀ k d, k + d ≤ T.L → T.N i k ≤ T.N i (k + d) := by
  intro k d
  induction d with
  | zero => intro _; exact Nat.le_refl _
  | succ d ih =>
      intro h
      have := ih (by omega)
      rw [show k + (d + 1) = (k + d) + 1 by omega, T.N_succ i (k + d) (by omega)]
      omega

theorem N_mono {i k k' : Nat} (h : k ≤ k') (h' : k' ≤ T.L) : T.N i k ≤ T.N i k' := by
  have := T.N_mono_add i k (k' - k) (by omega)
  rwa [show k + (k' - k) = k' by omega] at this

/-- After a move on `i` the count has strictly grown. -/
theorem N_lt_of_mv {i j k : Nat} (hm : T.mv j = i) (hj : j < k) (hk : k ≤ T.L) :
    T.N i j < T.N i k := by
  have h1 := T.N_succ i j (by omega)
  rw [if_pos hm] at h1
  have := T.N_mono (i := i) (show j + 1 ≤ k by omega) hk
  omega

/-- Discrete intermediate values: every value between two counts is taken at a move on `i`. -/
theorem ivt (i : Nat) : ∀ k', k' ≤ T.L → ∀ k m, k ≤ k' → T.N i k ≤ m → m < T.N i k' →
    ∃ j, k ≤ j ∧ j < k' ∧ T.mv j = i ∧ T.N i j = m := by
  intro k'
  induction k' with
  | zero =>
      intro _ k m hk h1 h2
      have : k = 0 := by omega
      subst this; rw [T.N_zero] at h2; omega
  | succ k' ih =>
      intro hL k m hk h1 h2
      by_cases hc : m < T.N i k' ∧ k ≤ k'
      · obtain ⟨j, a, b, c, d⟩ := ih (by omega) k m hc.2 h1 hc.1
        exact ⟨j, a, by omega, c, d⟩
      · have hs := T.N_succ i k' (by omega)
        by_cases hkk : k = k' + 1
        · subst hkk; omega
        · have hm : m = T.N i k' := by
            have := T.N_mono (i := i) (show k ≤ k' by omega) (by omega)
            split at hs <;> omega
          have hmv : T.mv k' = i := by
            apply Classical.byContradiction; intro hne; rw [if_neg hne] at hs; omega
          exact ⟨k', by omega, by omega, hmv, hm.symm⟩

theorem mv_inj {i j j' : Nat} (hj : j < T.L) (hj' : j' < T.L) (h1 : T.mv j = i) (h2 : T.mv j' = i)
    (h : T.N i j = T.N i j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | he | hg
  · have := T.N_lt_of_mv h1 hl (by omega); omega
  · exact he
  · have := T.N_lt_of_mv h2 hg (by omega); omega

/-- Occupied cell `i` at time `k`: every cell below has been placed before. -/
theorem below_placed : ∀ i k, k ≤ T.L → T.N i k % 2 = 1 → ∀ j, j < i → 0 < T.N j k := by
  intro i
  induction i with
  | zero => intro _ _ _ j hj; omega
  | succ i ih =>
      intro k hk hodd j hj
      obtain ⟨j0, -, hj0, hm, hN⟩ := T.ivt (i + 1) k hk 0 0 (Nat.zero_le _)
        (by rw [T.N_zero]; omega) (by omega)
      have hpl := T.place j0 (by omega) (by rw [hm, hN]) (by rw [hm]; omega)
      rw [hm, show i + 1 - 1 = i by omega] at hpl
      by_cases hji : j = i
      · subst hji
        have := T.N_mono (i := j) (show j0 ≤ k by omega) hk
        omega
      · have := ih j0 (by omega) hpl j (by omega)
        have := T.N_mono (i := j) (show j0 ≤ k by omega) hk
        omega

/-! ### Final counts -/

def c (i : Nat) : Nat := T.N i T.L

theorem c_last (hn : 1 ≤ T.n) : T.c (T.n - 1) % 2 = 1 := (T.final _ (by omega)).mpr rfl

theorem c_even {i : Nat} (hi : i < T.n - 1) : T.c i % 2 = 0 := by
  have := T.final i (by omega)
  unfold c; omega

theorem c_pos {i : Nat} (hi : i < T.n) (hn : 1 ≤ T.n) : 0 < T.c i := by
  by_cases h : i = T.n - 1
  · have := T.c_last hn; rw [← h] at this; omega
  · exact T.below_placed (T.n - 1) T.L (Nat.le_refl _) (T.c_last hn) i (by omega)

theorem c_ge_two {i : Nat} (hi : i < T.n - 1) : 2 ≤ T.c i := by
  have := T.c_even hi; have := T.c_pos (i := i) (by omega) (by omega); omega

theorem N_le_c (i : Nat) {k : Nat} (hk : k ≤ T.L) : T.N i k ≤ T.c i := T.N_mono hk (Nat.le_refl _)

/-! ### Last move on a cell -/

def lastT (i : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if T.mv k = i then k else lastT i k

theorem lastT_spec (i : Nat) : ∀ k, k ≤ T.L → 0 < T.N i k →
    T.lastT i k < k ∧ T.mv (T.lastT i k) = i ∧ T.N i (T.lastT i k) + 1 = T.N i k := by
  intro k
  induction k with
  | zero => intro _ h; rw [T.N_zero] at h; omega
  | succ k ih =>
      intro hk hpos
      have hs := T.N_succ i k (by omega)
      simp only [lastT]
      by_cases hm : T.mv k = i
      · rw [if_pos hm]; rw [if_pos hm] at hs; exact ⟨by omega, hm, by omega⟩
      · rw [if_neg hm]; rw [if_neg hm] at hs
        obtain ⟨a, b, d⟩ := ih (by omega) (by omega)
        exact ⟨by omega, b, by omega⟩

/-- Time of the last move on cell `i`. -/
def tau (i : Nat) : Nat := T.lastT i T.L

theorem tau_spec {i : Nat} (h : 0 < T.c i) :
    T.tau i < T.L ∧ T.mv (T.tau i) = i ∧ T.N i (T.tau i) + 1 = T.c i :=
  T.lastT_spec i T.L (Nat.le_refl _) h

/-- `N i k = c i` exactly after the last move. -/
theorem N_eq_c_iff {i k : Nat} (h : 0 < T.c i) (hk : k ≤ T.L) : T.N i k = T.c i ↔ T.tau i < k := by
  obtain ⟨h1, _, h3⟩ := T.tau_spec h
  constructor
  · intro he
    apply Classical.byContradiction; intro hn
    have := T.N_mono (i := i) (show k ≤ T.tau i by omega) (by omega)
    omega
  · intro hlt
    have hs := T.N_succ i (T.tau i) h1
    rw [if_pos (T.tau_spec h).2.1] at hs
    have := T.N_mono (i := i) (show T.tau i + 1 ≤ k by omega) hk
    have := T.N_le_c i hk
    omega

theorem tau_ne {i j : Nat} (hi : 0 < T.c i) (hj : 0 < T.c j) (h : i ≠ j) : T.tau i ≠ T.tau j := by
  intro he
  have a := (T.tau_spec hi).2.1
  have b := (T.tau_spec hj).2.1
  rw [he] at a; exact h (a.symm.trans b)


/-! ### Sums -/

theorem rsum_eq_zero (f : Nat → Nat) : ∀ m, (∀ j, j < m → f j = 0) → rsum m f = 0 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih => intro h; simp only [rsum]; rw [ih (fun j hj => h j (by omega)), h m (by omega)]

theorem rsum_shift (f : Nat → Nat) : ∀ m, rsum (m + 1) f = f 0 + rsum m (fun i => f (i + 1)) := by
  intro m
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum] at *; rw [ih]; omega

theorem rsum_swap (f : Nat → Nat → Nat) (b : Nat) : ∀ a,
    rsum a (fun i => rsum b (fun k => f i k)) = rsum b (fun k => rsum a (fun i => f i k)) := by
  intro a
  induction a with
  | zero => simp [rsum, rsum_zero_fun]
  | succ a ih =>
      simp only [rsum]
      rw [ih, ← rsum_add]

theorem rsum_mul_ind (P : Nat → Prop) [DecidablePred P] (x : Nat) : ∀ m,
    rsum m (fun i => if P i then x else 0) = x * rsum m (fun i => if P i then 1 else 0) := by
  intro m
  induction m with
  | zero => simp [rsum]
  | succ m ih => simp only [rsum]; rw [ih, Nat.mul_add]; split <;> simp

theorem rsum_pos {f : Nat → Nat} : ∀ m, 0 < rsum m f → ∃ i, i < m ∧ 0 < f i := by
  intro m
  induction m with
  | zero => simp [rsum]
  | succ m ih =>
      intro h
      simp only [rsum] at h
      by_cases hf : 0 < f m
      · exact ⟨m, by omega, hf⟩
      · obtain ⟨i, hi, hp⟩ := ih (by omega); exact ⟨i, by omega, hp⟩

theorem rsum_ind_le (a : Nat) : ∀ m, rsum m (fun y => if y = a then 1 else 0) ≤ 1 := by
  intro m
  induction m with
  | zero => simp [rsum]
  | succ m ih =>
      simp only [rsum]
      by_cases h : m = a
      · subst h
        have : rsum m (fun y => if y = m then 1 else 0) = 0 := by
          exact rsum_eq_zero _ m (fun j hj => if_neg (by omega))
        rw [this]; simp
      · rw [if_neg h]; omega

theorem rsum_ind_eq (a : Nat) : ∀ m, a < m → rsum m (fun y => if y = a then 1 else 0) = 1 := by
  intro m hm
  refine Eq.trans (rsum_congr _ _ m (fun j _ => ?_)) (rsum_indicator a m hm)
  by_cases hj : j = a
  · subst hj; simp
  · rw [if_neg hj, if_neg (Ne.symm hj)]

theorem rsum_interval : ∀ m hi lo, hi ≤ m → lo ≤ hi →
    rsum m (fun i => if lo ≤ i ∧ i < hi then 1 else 0) = hi - lo := by
  intro m
  induction m with
  | zero => intro hi lo h1 h2; simp [rsum]; omega
  | succ m ih =>
      intro hi lo h1 h2
      simp only [rsum]
      by_cases hm : hi ≤ m
      · rw [ih hi lo hm h2, if_neg (by omega)]; simp
      · have hh : hi = m + 1 := by omega
        subst hh
        have e1 : rsum m (fun i => if lo ≤ i ∧ i < m + 1 then 1 else 0)
            = rsum m (fun i => if lo ≤ i ∧ i < m then 1 else 0) := by
          apply rsum_congr; intro j hj
          by_cases a : lo ≤ j
          · rw [if_pos ⟨a, by omega⟩, if_pos ⟨a, hj⟩]
          · rw [if_neg (fun h => a h.1), if_neg (fun h => a h.1)]
        rw [e1]
        by_cases hlo : lo ≤ m
        · rw [ih m lo (Nat.le_refl _) hlo, if_pos ⟨hlo, by omega⟩]; omega
        · have z : rsum m (fun i => if lo ≤ i ∧ i < m then 1 else 0) = 0 := by
            exact rsum_eq_zero _ m (fun j hj => if_neg (by omega))
          rw [z, if_neg (by omega)]; omega

theorem rsum_restrict (f : Nat → Nat) (m : Nat) : ∀ n, m ≤ n →
    rsum n (fun i => if i < m then f i else 0) = rsum m f := by
  intro n
  induction n with
  | zero => intro h; have : m = 0 := by omega
            subst this; rfl
  | succ n ih =>
      intro h
      by_cases hm : m ≤ n
      · simp only [rsum]; rw [ih hm, if_neg (by omega)]; omega
      · have : m = n + 1 := by omega
        subst this
        simp only [rsum]
        rw [if_pos (by omega)]
        congr 1
        apply rsum_congr; intro j hj; rw [if_pos (by omega)]

/-! ### Ascents and runs -/

/-- Cell `y` is an ascent: its last move comes after the last move of the cell below. -/
def asc (y : Nat) : Prop := 1 ≤ y ∧ y < T.n - 1 ∧ T.tau (y - 1) < T.tau y

instance (y : Nat) : Decidable (T.asc y) := by unfold asc; infer_instance

/-- Run index: number of ascents in `[1, i]`. -/
def rho (i : Nat) : Nat := rsum (i + 1) (fun y => if T.asc y then 1 else 0)

theorem rho_succ (i : Nat) : T.rho (i + 1) = T.rho i + (if T.asc (i + 1) then 1 else 0) := rfl

theorem rho_mono {x y : Nat} (h : x ≤ y) : T.rho x ≤ T.rho y := by
  induction y with
  | zero => have : x = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ y ih =>
      by_cases hx : x = y + 1
      · subst hx; exact Nat.le_refl _
      · have := ih (by omega); rw [T.rho_succ]; omega

theorem rho_noasc {x y : Nat} (hxy : x ≤ y) (h : T.rho x = T.rho y) :
    ∀ w, x < w → w ≤ y → ¬ T.asc w := by
  intro w h1 h2 ha
  have a := T.rho_mono (show x ≤ w - 1 by omega)
  have b := T.rho_mono h2
  have c := T.rho_succ (w - 1)
  rw [show w - 1 + 1 = w by omega, if_pos ha] at c
  omega

theorem rho_eq_of_noasc {x : Nat} : ∀ y, x ≤ y → (∀ w, x < w → w ≤ y → ¬ T.asc w) →
    T.rho x = T.rho y := by
  intro y
  induction y with
  | zero => intro h _; have : x = 0 := by omega
            subst this; rfl
  | succ y ih =>
      intro h hw
      by_cases hx : x = y + 1
      · subst hx; rfl
      · rw [T.rho_succ, if_neg (hw (y + 1) (by omega) (Nat.le_refl _)),
          ih (by omega) (fun w a b => hw w a (by omega))]
        omega

/-- Last moves decrease inside a run. -/
theorem tau_run {x : Nat} : ∀ y, x ≤ y → y < T.n - 1 → T.rho x = T.rho y → T.tau y ≤ T.tau x := by
  intro y
  induction y with
  | zero => intro h _ _; have : x = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ y ih =>
      intro h hy hr
      by_cases hx : x = y + 1
      · subst hx; exact Nat.le_refl _
      · have hna := T.rho_noasc (show x ≤ y + 1 by omega) hr (y + 1) (by omega) (Nat.le_refl _)
        have hr' : T.rho x = T.rho y := by
          have := T.rho_mono (show x ≤ y by omega); have := T.rho_mono (show y ≤ y + 1 by omega)
          omega
        have := ih (by omega) (by omega) hr'
        have : ¬ T.tau y < T.tau (y + 1) := fun hl => hna ⟨by omega, hy, by simpa using hl⟩
        omega

/-! ### Ascents are erasures -/

def numAsc : Nat := rsum (T.n - 1) (fun y => if T.asc y then 1 else 0)

theorem asc_isE {y : Nat} (h : T.asc y) : T.isE (T.tau y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hc := T.c_ge_two (i := y) h2
  have hc' := T.c_ge_two (i := y - 1) (by omega)
  have he := T.c_even (i := y) h2
  have he' := T.c_even (i := y - 1) (by omega)
  obtain ⟨t1, t2, t3⟩ := T.tau_spec (i := y) (by omega)
  have hd := (T.N_eq_c_iff (i := y - 1) (k := T.tau y) (by omega) (by omega)).mpr h3
  refine ⟨?_, ?_, ?_⟩
  · rw [t2]; omega
  · rw [t2]; omega
  · rw [t2, hd]; exact he'

theorem asc_inner_le (k : Nat) (hk : k < T.L) :
    rsum (T.n - 1) (fun y => if T.asc y ∧ T.tau y = k then 1 else 0) ≤ (if T.isE k then 1 else 0) := by
  by_cases hE : T.isE k
  · rw [if_pos hE]
    have := rsum_le (fun y => if T.asc y ∧ T.tau y = k then 1 else 0)
      (fun y => if y = T.mv k then 1 else 0) (T.n - 1) (by
        intro y _
        by_cases ha : T.asc y ∧ T.tau y = k
        · have hy : y = T.mv k := by
            have := (T.tau_spec (i := y) (by have := T.c_ge_two (i := y) ha.1.2.1; omega)).2.1
            rw [ha.2] at this; exact this.symm
          rw [if_pos ha, if_pos hy]; exact Nat.le_refl _
        · rw [if_neg ha]; exact Nat.zero_le _)
    exact Nat.le_trans this (rsum_ind_le _ _)
  · rw [if_neg hE]
    have : rsum (T.n - 1) (fun y => if T.asc y ∧ T.tau y = k then 1 else 0) = rsum (T.n - 1) (fun _ => 0) := by
      apply rsum_congr; intro y _
      by_cases ha : T.asc y ∧ T.tau y = k
      · exact absurd (ha.2 ▸ T.asc_isE ha.1) hE
      · rw [if_neg ha]
    rw [this, rsum_zero_fun]; exact Nat.le_refl _

theorem numAsc_eq_swap :
    T.numAsc = rsum T.L (fun k => rsum (T.n - 1) (fun y => if T.asc y ∧ T.tau y = k then 1 else 0)) := by
  unfold numAsc
  rw [← rsum_swap]
  apply rsum_congr; intro y hy
  by_cases ha : T.asc y
  · rw [if_pos ha]
    have ht := (T.tau_spec (i := y) (by have := T.c_ge_two (i := y) ha.2.1; omega)).1
    refine (rsum_ind_eq (T.tau y) T.L ht).symm.trans (rsum_congr _ _ T.L (fun k _ => ?_))
    by_cases hk : k = T.tau y
    · subst hk; simp [ha]
    · rw [if_neg hk, if_neg]; intro h; exact hk h.2.symm
  · rw [if_neg ha]
    exact (rsum_eq_zero _ T.L (fun k _ => if_neg (fun h => ha h.1))).symm

theorem numAsc_le_eras : T.numAsc ≤ T.eras := by
  rw [numAsc_eq_swap]
  exact rsum_le _ _ _ (fun k hk => T.asc_inner_le k hk)

/-- If there are as many ascents as erasures, every erasure is the last move of an ascent. -/
theorem isE_asc (heq : T.numAsc = T.eras) {k : Nat} (hk : k < T.L) (hE : T.isE k) :
    ∃ y, T.asc y ∧ T.tau y = k := by
  rw [numAsc_eq_swap] at heq
  have hpt := rsum_eq_of_le _ _ T.L (fun k hk => T.asc_inner_le k hk) heq k hk
  rw [if_pos hE] at hpt
  obtain ⟨y, _, hy⟩ := rsum_pos (T.n - 1) (by omega : 0 < rsum (T.n - 1)
    (fun y => if T.asc y ∧ T.tau y = k then 1 else 0))
  by_cases ha : T.asc y ∧ T.tau y = k
  · exact ⟨y, ha⟩
  · rw [if_neg ha] at hy; omega

/-! ### Singles, ranks and the local capacity bound -/

/-- Cell placed exactly once (for cells below the target). -/
def single (i : Nat) : Prop := T.c i = 2

instance (i : Nat) : Decidable (T.single i) := by unfold single; infer_instance

/-- Rank of `i` among the singles of its run: singles `x ≤ i` with the same run index. -/
def kr (i : Nat) : Nat := rsum (i + 1) (fun x => if T.rho x = T.rho i ∧ T.single x then 1 else 0)

theorem kr_zero : T.kr 0 = (if T.single 0 then 1 else 0) := by
  simp [kr, rsum]

theorem rsum_succ_eq (f : Nat → Nat) (m : Nat) : rsum (m + 1) f = rsum m f + f m := rfl

theorem kr_succ (i : Nat) :
    T.kr (i + 1) = (if T.single (i + 1) then 1 else 0) + (if T.asc (i + 1) then 0 else T.kr i) := by
  have e : T.kr (i + 1) = rsum (i + 1) (fun x => if T.rho x = T.rho (i + 1) ∧ T.single x then 1 else 0)
      + (if T.single (i + 1) then 1 else 0) := by
    unfold kr; rw [rsum_succ_eq]
    by_cases hs : T.single (i + 1)
    · rw [if_pos ⟨rfl, hs⟩, if_pos hs]
    · rw [if_neg (fun h => hs h.2), if_neg hs]
  rw [e]
  by_cases ha : T.asc (i + 1)
  · rw [if_pos ha]
    have : rsum (i + 1) (fun x => if T.rho x = T.rho (i + 1) ∧ T.single x then 1 else 0) = 0 := by
      apply rsum_eq_zero; intro j hj
      rw [if_neg]; intro h
      have a := T.rho_mono (show j ≤ i by omega)
      have b := T.rho_succ i
      rw [if_pos ha] at b; omega
    rw [this]; omega
  · rw [if_neg ha]
    have hr : T.rho (i + 1) = T.rho i := by rw [T.rho_succ, if_neg ha]; omega
    rw [hr]; unfold kr; omega

theorem telescope (f V : Nat → Nat) (b : Nat → Prop) [DecidablePred b] (h0 : V 0 = f 0)
    (hs : ∀ i, V (i + 1) = f (i + 1) + (if b (i + 1) then 0 else V i)) :
    ∀ m, rsum (m + 1) f = rsum m (fun i => if b (i + 1) then V i else 0) + V m := by
  intro m
  induction m with
  | zero => simp [rsum, h0]
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl]
      simp only [rsum] at *
      rw [ih, hs m]
      split <;> omega

theorem first_place {i : Nat} (hi : i < T.n) (hn : 1 ≤ T.n) :
    ∃ f, f < T.L ∧ T.mv f = i ∧ T.N i f = 0 := by
  obtain ⟨j, -, hj, hm, hN⟩ := T.ivt i T.L (Nat.le_refl _) 0 0 (Nat.zero_le _)
    (by simp [T.N_zero]) (T.c_pos hi hn)
  exact ⟨j, hj, hm, hN⟩

/-- The cell below a freshly placed cell `c` is removed for the last time later. -/
theorem tau_pred_gt {c f : Nat} (hc1 : 1 ≤ c) (hc : c ≤ T.n - 1) (hf : f < T.L) (hm : T.mv f = c)
    (hN : T.N c f = 0) : f < T.tau (c - 1) := by
  have hpl := T.place f hf (by rw [hm, hN]) (by rw [hm]; omega)
  rw [hm] at hpl
  have h2 := T.c_ge_two (i := c - 1) (by omega)
  have he := T.c_even (i := c - 1) (by omega)
  have hne : T.N (c - 1) f ≠ T.c (c - 1) := by intro h; rw [h] at hpl; omega
  have h1 : ¬ T.tau (c - 1) < f := fun h => hne ((T.N_eq_c_iff (by omega) (by omega)).mpr h)
  have h3 : f ≠ T.tau (c - 1) := by
    intro h; have := (T.tau_spec (i := c - 1) (by omega)).2.1; rw [← h, hm] at this; omega
  omega

theorem N_succ_self {i f : Nat} (hf : f < T.L) (hm : T.mv f = i) : T.N i (f + 1) = T.N i f + 1 := by
  rw [T.N_succ i f hf, if_pos hm]

/-- Right after `c` is placed, every single of the run ending at `c − 1` is on the board. -/
theorem single_on {c f : Nat} (hc1 : 1 ≤ c) (hc : c ≤ T.n - 1) (hf : f < T.L) (hm : T.mv f = c)
    (hN : T.N c f = 0) {x : Nat} (hx : x ≤ c - 1) (hr : T.rho x = T.rho (c - 1)) (hs : T.single x) :
    T.N x (f + 1) = 1 := by
  have ht := T.tau_pred_gt hc1 hc hf hm hN
  have hrun := T.tau_run (x := x) (c - 1) hx (by omega) hr
  have hc1' := T.N_succ_self hf hm
  have hpos := T.below_placed c (f + 1) (by omega) (by rw [hc1', hN]) x (by omega)
  have hlt : ¬ T.tau x < f + 1 := by omega
  have hne : T.N x (f + 1) ≠ T.c x := fun h => hlt ((T.N_eq_c_iff (by unfold single at hs; omega) (by omega)).mp h)
  have := T.N_le_c x (show f + 1 ≤ T.L by omega)
  unfold single at hs
  omega

/-- Indicator of "single of the run ending at `c − 1`, or `c` itself". -/
def runSet (c : Nat) (i : Nat) : Prop :=
  (i ≤ c - 1 ∧ T.rho i = T.rho (c - 1) ∧ T.single i) ∨ i = c

instance (c i : Nat) : Decidable (T.runSet c i) := by unfold runSet; infer_instance

theorem runSet_count {c : Nat} (hc1 : 1 ≤ c) (hc : c < T.n) :
    rsum T.n (fun i => if T.runSet c i then 1 else 0) = T.kr (c - 1) + 1 := by
  have h1 : rsum T.n (fun i => if T.runSet c i then 1 else 0) =
      rsum T.n (fun i => (if i < c then (if T.rho i = T.rho (c - 1) ∧ T.single i then 1 else 0) else 0)
        + (if i = c then 1 else 0)) := by
    apply rsum_congr; intro i _
    unfold runSet
    by_cases hic : i = c
    · subst hic; simp
    · by_cases hlt : i < c
      · rw [if_pos hlt, if_neg hic]
        by_cases hq : T.rho i = T.rho (c - 1) ∧ T.single i
        · rw [if_pos (Or.inl ⟨by omega, hq⟩), if_pos hq]
        · rw [if_neg (by intro h; rcases h with h | h; exact hq ⟨h.2.1, h.2.2⟩; exact hic h), if_neg hq]
      · rw [if_neg hlt, if_neg hic, if_neg (by intro h; rcases h with h | h <;> omega)]
  rw [h1, rsum_add, rsum_restrict _ c T.n (by omega), rsum_ind_eq c T.n hc]
  unfold kr; rw [show c - 1 + 1 = c by omega]

theorem runSet_on {c f : Nat} (hc1 : 1 ≤ c) (hc : c ≤ T.n - 1) (hf : f < T.L) (hm : T.mv f = c)
    (hN : T.N c f = 0) {i : Nat} (h : T.runSet c i) : T.N i (f + 1) % 2 = 1 := by
  rcases h with ⟨a, b, d⟩ | h
  · rw [T.single_on hc1 hc hf hm hN a b d]
  · subst h; rw [T.N_succ_self hf hm, hN]

/-- **Local capacity.**  A run holds at most `p − 1` singles. -/
theorem kr_le {c : Nat} (hc1 : 1 ≤ c) (hc : c ≤ T.n - 1) (hn : 1 ≤ T.n) : T.kr (c - 1) + 1 ≤ T.p := by
  obtain ⟨f, hf, hm, hN⟩ := T.first_place (i := c) (by omega) hn
  rw [← T.runSet_count hc1 (by omega)]
  refine Nat.le_trans (rsum_le _ (fun i => if T.N i (f + 1) % 2 = 1 then 1 else 0) T.n ?_)
    (T.peak (f + 1) (by omega))
  intro i _
  by_cases h : T.runSet c i
  · rw [if_pos h, if_pos (T.runSet_on hc1 hc hf hm hN h)]; exact Nat.le_refl _
  · rw [if_neg h]; exact Nat.zero_le _

/-- **Full board.**  If the run is full, nothing else is on the board right after `c` is placed. -/
theorem full {c f : Nat} (hc1 : 1 ≤ c) (hc : c ≤ T.n - 1) (hf : f < T.L) (hm : T.mv f = c)
    (hN : T.N c f = 0) (hk : T.kr (c - 1) + 1 = T.p) {x : Nat} (hx : x < T.n)
    (hon : T.N x (f + 1) % 2 = 1) : T.runSet c x := by
  apply Classical.byContradiction; intro hnot
  have h1 : rsum T.n (fun i => if T.runSet c i ∨ i = x then 1 else 0) =
      rsum T.n (fun i => (if T.runSet c i then 1 else 0) + (if i = x then 1 else 0)) := by
    apply rsum_congr; intro i _
    by_cases hix : i = x
    · subst hix; rw [if_pos (Or.inr rfl), if_neg hnot, if_pos rfl]
    · by_cases hr : T.runSet c i
      · rw [if_pos (Or.inl hr), if_pos hr, if_neg hix]
      · rw [if_neg (by intro h; rcases h with h | h; exact hr h; exact hix h), if_neg hr, if_neg hix]
  have h2 := rsum_le (fun i => if T.runSet c i ∨ i = x then 1 else 0)
    (fun i => if T.N i (f + 1) % 2 = 1 then 1 else 0) T.n (by
      intro i _
      by_cases h : T.runSet c i ∨ i = x
      · have hon' : T.N i (f + 1) % 2 = 1 := by
          rcases h with h | h
          · exact T.runSet_on hc1 hc hf hm hN h
          · subst h; exact hon
        rw [if_pos h, if_pos hon']; exact Nat.le_refl _
      · rw [if_neg h]; exact Nat.zero_le _)
  rw [h1, rsum_add, T.runSet_count hc1 (by omega), rsum_ind_eq x T.n hx] at h2
  have := T.peak (f + 1) (by omega)
  omega

/-! ### Forcing equality -/

theorem rsum_N (k : Nat) (hk : k ≤ T.L) : rsum T.n (fun i => T.N i k) = k := by
  induction k with
  | zero => exact rsum_eq_zero _ _ (fun j _ => T.N_zero j)
  | succ k ih =>
      have h1 : rsum T.n (fun i => T.N i (k + 1)) =
          rsum T.n (fun i => T.N i k + (if T.mv k = i then 1 else 0)) :=
        rsum_congr _ _ _ (fun i _ => T.N_succ i k (by omega))
      rw [h1, rsum_add, ih (by omega), rsum_indicator (T.mv k) T.n (T.mv_lt k (by omega))]

def S : Nat := rsum (T.n - 1) (fun i => if T.single i then 1 else 0)

theorem numAsc_shift (hn : 2 ≤ T.n) :
    T.numAsc = rsum (T.n - 2) (fun i => if T.asc (i + 1) then 1 else 0) := by
  unfold numAsc
  rw [show T.n - 1 = (T.n - 2) + 1 by omega, rsum_shift]
  have : ¬ T.asc 0 := fun h => by have := h.1; omega
  rw [if_neg this]; omega

theorem S_telescope (hn : 2 ≤ T.n) :
    T.S = rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.kr i else 0) + T.kr (T.n - 2) := by
  unfold S
  rw [show T.n - 1 = (T.n - 2) + 1 by omega]
  exact telescope (fun i => if T.single i then 1 else 0) T.kr T.asc T.kr_zero T.kr_succ (T.n - 2)

/-- The length counted by the classes of cells. -/
def g (i : Nat) : Nat := if i = T.n - 1 then 1 else if T.single i then 2 else 4

theorem g_le_c {i : Nat} (hi : i < T.n) (hn : 1 ≤ T.n) : T.g i ≤ T.c i := by
  unfold g
  by_cases h : i = T.n - 1
  · rw [if_pos h]; exact T.c_pos hi hn
  · rw [if_neg h]
    have := T.c_ge_two (i := i) (by omega)
    have := T.c_even (i := i) (by omega)
    unfold single
    split <;> omega

theorem rsum_g (hn : 1 ≤ T.n) : rsum T.n T.g + 2 * T.S = 4 * (T.n - 1) + 1 := by
  have h1 : rsum T.n T.g = rsum (T.n - 1) (fun i => if T.single i then 2 else 4) + 1 := by
    rw [show T.n = (T.n - 1) + 1 by omega]
    simp only [rsum]
    rw [show T.n - 1 + 1 - 1 = T.n - 1 by omega]
    congr 1
    · apply rsum_congr; intro j hj; unfold g; rw [if_neg (by omega)]
    · simp [g]
  have h2 : ∀ m, rsum m (fun i => if T.single i then 2 else 4) + 2 * rsum m (fun i => if T.single i then 1 else 0)
      = 4 * m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [rsum]; split <;> omega
  unfold S
  have := h2 (T.n - 1)
  omega

/-- What the length bound forces. -/
structure Forced (e : Nat) : Prop where
  numAsc_eq : T.numAsc = e
  eras_eq : T.eras = e
  kr_last : T.kr (T.n - 2) + 1 = T.p
  kr_asc : ∀ i, i + 2 < T.n → T.asc (i + 1) → T.kr i + 1 = T.p
  c_double : ∀ i, i < T.n - 1 → ¬ T.single i → T.c i = 4
  c_last1 : T.c (T.n - 1) = 1
  S_eq : T.S = (T.p - 1) * (e + 1)

theorem forced (e : Nat) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
    (hlen : T.L + 2 * ((T.p - 1) * (e + 1) + 1) + 1 ≤ 4 * T.n) (he : T.eras ≤ e) : T.Forced e := by
  have hkl : ∀ i, i + 2 ≤ T.n → T.kr i + 1 ≤ T.p := by
    intro i hi
    have := T.kr_le (c := i + 1) (by omega) (by omega) (by omega)
    rwa [show i + 1 - 1 = i by omega] at this
  have hA := T.numAsc_le_eras
  -- upper bound on S
  have hsum : rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.kr i else 0) ≤
      rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.p - 1 else 0) :=
    rsum_le _ _ _ (fun i hi => by
      have := hkl i (by omega)
      split <;> omega)
  rw [rsum_mul_ind (fun i => T.asc (i + 1)), ← T.numAsc_shift hn] at hsum
  have hS := T.S_telescope hn
  have hlast := hkl (T.n - 2) (by omega)
  -- lower bound on S from the length
  have hL := T.rsum_N T.L (Nat.le_refl _)
  have hgc := rsum_le T.g (fun i => T.N i T.L) T.n (fun i hi => T.g_le_c hi (by omega))
  have hg := T.rsum_g (by omega)
  -- arithmetic with q = p − 1
  have hq : 1 ≤ T.p - 1 := by omega
  have hmul : (T.p - 1) * (e + 1) = (T.p - 1) * e + (T.p - 1) := Nat.mul_succ _ _
  have hmulA : (T.p - 1) * (T.numAsc + 1) = (T.p - 1) * T.numAsc + (T.p - 1) := Nat.mul_succ _ _
  have hSlo : (T.p - 1) * (e + 1) ≤ T.S := by omega
  have hAe : T.numAsc = e := by
    apply Classical.byContradiction; intro hne
    have : (T.p - 1) * (T.numAsc + 1) ≤ (T.p - 1) * e := Nat.mul_le_mul_left _ (by omega)
    omega
  subst hAe
  have hSeq : T.S = (T.p - 1) * (T.numAsc + 1) := by omega
  have hsumeq : rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.kr i else 0) =
      rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.p - 1 else 0) := by
    rw [rsum_mul_ind (fun i => T.asc (i + 1)), ← T.numAsc_shift hn]; omega
  have hgeq : rsum T.n T.g = rsum T.n (fun i => T.N i T.L) := by omega
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_, hSeq⟩
  · intro i hi ha
    have := rsum_eq_of_le _ _ _ (fun i hi => by
      have := hkl i (by omega)
      show (if T.asc (i + 1) then T.kr i else 0) ≤ (if T.asc (i + 1) then T.p - 1 else 0)
      split <;> omega) hsumeq i (by omega)
    simp only [if_pos ha] at this
    omega
  · intro i hi hs
    have := rsum_eq_of_le _ _ _ (fun i hi => T.g_le_c hi (by omega)) hgeq i (by omega)
    unfold g at this
    rw [if_neg (by omega), if_neg hs] at this
    exact this.symm
  · have := rsum_eq_of_le _ _ _ (fun i hi => T.g_le_c hi (by omega)) hgeq (T.n - 1) (by omega)
    unfold g at this
    rw [if_pos rfl] at this
    exact this.symm

/-! ### Structure of a plan that meets the bound -/

/-- Run boundary: the cell right of a run (an ascent, or the target cell). -/
def bnd (c : Nat) : Prop := c = T.n - 1 ∨ T.asc c

theorem next_bnd (hn : 2 ≤ T.n) : ∀ d x, x + d = T.n - 1 → 1 ≤ d →
    ∃ c, x < c ∧ c ≤ T.n - 1 ∧ T.bnd c ∧ ∀ w, x < w → w < c → ¬ T.asc w := by
  intro d
  induction d with
  | zero => intro x _ h; omega
  | succ d ih =>
      intro x hx _
      by_cases hd : d = 0
      · subst hd; exact ⟨x + 1, by omega, by omega, Or.inl (by omega), fun w a b => by omega⟩
      · by_cases ha : T.asc (x + 1)
        · exact ⟨x + 1, by omega, by omega, Or.inr ha, fun w a b => by omega⟩
        · obtain ⟨c, h1, h2, h3, h4⟩ := ih (x + 1) (by omega) (by omega)
          refine ⟨c, by omega, h2, h3, fun w a b => ?_⟩
          by_cases hw : w = x + 1
          · subst hw; exact ha
          · exact h4 w (by omega) b

theorem rho_of_next {x c : Nat} (h1 : x < c) (h4 : ∀ w, x < w → w < c → ¬ T.asc w) :
    T.rho x = T.rho (c - 1) :=
  T.rho_eq_of_noasc (c - 1) (by omega) (fun w a b => h4 w a (by omega))

variable {T}

section forced
variable {e : Nat} (F : T.Forced e) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
include F hp hn

theorem bnd_kr {c : Nat} (hb : T.bnd c) (hc1 : 1 ≤ c) : T.kr (c - 1) + 1 = T.p := by
  rcases hb with h | h
  · subst h; exact F.kr_last
  · have := F.kr_asc (c - 1) (by have := h.2.1; omega) (by rw [show c - 1 + 1 = c by omega]; exact h)
    exact this

theorem bnd_le {c : Nat} (hb : T.bnd c) : 1 ≤ c ∧ c ≤ T.n - 1 := by
  rcases hb with h | h
  · omega
  · exact ⟨h.1, by have := h.2.1; omega⟩

/-- The last cell of a run is a single. -/
theorem end_single {c : Nat} (hb : T.bnd c) : T.single (c - 1) := by
  obtain ⟨hc1, hc⟩ := bnd_le F hp hn hb
  obtain ⟨f, hf, hm, hN⟩ := T.first_place (i := c) (by omega) (by omega)
  have hpl := T.place f hf (by rw [hm, hN]) (by rw [hm]; omega)
  rw [hm] at hpl
  have hs : T.N (c - 1) (f + 1) = T.N (c - 1) f := by
    rw [T.N_succ _ f hf, if_neg (by rw [hm]; omega)]; omega
  have := T.full hc1 hc hf hm hN (bnd_kr F hp hn hb hc1) (x := c - 1) (by omega) (by rw [hs]; exact hpl)
  rcases this with h | h
  · exact h.2.2
  · omega

/-- Ascents (run starts after the first run) are singles. -/
theorem asc_single {c : Nat} (ha : T.asc c) : T.single c := by
  have hc := ha.2.1
  have hc0 := ha.1
  obtain ⟨c', h1, h2, h3, h4⟩ := T.next_bnd hn (T.n - 1 - c) c (by omega) (by omega)
  obtain ⟨hc1', _⟩ := bnd_le F hp hn h3
  obtain ⟨f, hf, hm, hN⟩ := T.first_place (i := c') (by omega) (by omega)
  have hfull := fun {x} hx hon => T.full hc1' (by omega) hf hm hN (bnd_kr F hp hn h3 hc1') (x := x) hx hon
  have hrc : T.rho c = T.rho (c' - 1) := T.rho_of_next h1 h4
  have hrp : T.rho c = T.rho (c - 1) + 1 := by
    have := T.rho_succ (c - 1); rw [show c - 1 + 1 = c by omega, if_pos ha] at this; exact this
  have hsp := end_single F hp hn (Or.inr ha)
  have hon' : T.N c' (f + 1) % 2 = 1 := by rw [T.N_succ_self hf hm, hN]
  -- the cell below `c` is gone for good by time `f + 1`
  have hpd : T.N (c - 1) (f + 1) = 2 := by
    have hpos := T.below_placed c' (f + 1) (by omega) hon' (c - 1) (by omega)
    have hle := T.N_le_c (c - 1) (show f + 1 ≤ T.L by omega)
    unfold single at hsp
    have : T.N (c - 1) (f + 1) % 2 = 0 := by
      apply Classical.byContradiction; intro hne
      rcases hfull (x := c - 1) (by omega) (by omega) with h | h
      · omega
      · omega
    omega
  apply Classical.byContradiction; intro hns
  have hc2 := T.c_ge_two (i := c) hc
  have hce := T.c_even (i := c) hc
  have hoff : T.N c (f + 1) % 2 = 0 := by
    apply Classical.byContradiction; intro hne
    rcases hfull (x := c) (by omega) (by omega) with h | h
    · exact hns h.2.2
    · omega
  have ht1 := T.tau_run (x := c) (c' - 1) (by omega) (by omega) hrc
  have ht2 := T.tau_pred_gt hc1' (by omega) hf hm hN
  obtain ⟨tl, tm, tN⟩ := T.tau_spec (i := c) (by omega)
  have hmono := T.N_mono (i := c) (show f + 1 ≤ T.tau c by omega) (by omega)
  obtain ⟨j, hj1, hj2, hjm, hjN⟩ := T.ivt c (T.tau c) (by omega) (f + 1) (T.N c (f + 1))
    (by omega) (Nat.le_refl _) (by omega)
  have hpl := T.place j (by omega) (by rw [hjm, hjN]; exact hoff) (by rw [hjm]; omega)
  rw [hjm] at hpl
  have a := T.N_mono (i := c - 1) hj1 (by omega)
  have b := T.N_le_c (c - 1) (show j ≤ T.L by omega)
  unfold single at hsp
  omega

/-- The cell right of a run stays on the board until every single of the run is gone. -/
theorem bnd_on {c s : Nat} (hb : T.bnd c) (hs : T.single s) (hsc : s ≤ c - 1)
    (hr : T.rho s = T.rho (c - 1)) : T.N c (T.tau s) % 2 = 1 := by
  obtain ⟨hc1, hc⟩ := bnd_le F hp hn hb
  obtain ⟨f, hf, hm, hN⟩ := T.first_place (i := c) (by omega) (by omega)
  have ht1 := T.tau_run (x := s) (c - 1) hsc (by omega) hr
  have ht2 := T.tau_pred_gt hc1 hc hf hm hN
  have hss : 0 < T.c s := by unfold single at hs; omega
  obtain ⟨tl, _, _⟩ := T.tau_spec hss
  have hlo : 1 ≤ T.N c (T.tau s) := by
    have := T.N_mono (i := c) (show f + 1 ≤ T.tau s by omega) (by omega)
    rw [T.N_succ_self hf hm, hN] at this; omega
  rcases hb with h | ha
  · -- the target cell is placed once and never removed
    have hc1' : T.c c = 1 := by
      subst h
      exact F.c_last1
    have := T.N_le_c c (show T.tau s ≤ T.L by omega)
    omega
  · have hsc' := asc_single F hp hn ha
    unfold single at hsc'
    have hcc := ha.2.1
    obtain ⟨c', h1, h2, h3, h4⟩ := T.next_bnd hn (T.n - 1 - c) c (by omega) (by omega)
    obtain ⟨hc1', _⟩ := bnd_le F hp hn h3
    obtain ⟨f', hf', hm', hN'⟩ := T.first_place (i := c') (by omega) (by omega)
    have hrc : T.rho c = T.rho (c' - 1) := T.rho_of_next h1 h4
    have hrp : T.rho c = T.rho (c - 1) + 1 := by
      have := T.rho_succ (c - 1); rw [show c - 1 + 1 = c by omega, if_pos ha] at this; exact this
    have hon' : T.N c' (f' + 1) % 2 = 1 := by rw [T.N_succ_self hf' hm', hN']
    have hoff : T.N s (f' + 1) % 2 = 0 := by
      apply Classical.byContradiction; intro hne
      rcases T.full hc1' (by omega) hf' hm' hN' (bnd_kr F hp hn h3 hc1') (x := s) (by omega)
        (by omega) with h | h
      · omega
      · omega
    have hpos := T.below_placed c' (f' + 1) (by omega) hon' s (by omega)
    have hle := T.N_le_c s (show f' + 1 ≤ T.L by omega)
    unfold single at hs
    have hdone : T.tau s < f' + 1 := (T.N_eq_c_iff hss (by omega)).mp (by omega)
    have ht3 := T.tau_run (x := c) (c' - 1) (by omega) (by omega) hrc
    have ht4 := T.tau_pred_gt hc1' (by omega) hf' hm' hN'
    have hnd : ¬ T.tau c < T.tau s := by omega
    have hne : T.N c (T.tau s) ≠ T.c c := fun h => hnd ((T.N_eq_c_iff (by omega) (by omega)).mp h)
    have := T.N_le_c c (show T.tau s ≤ T.L by omega)
    omega

end forced

/-! ### Gaps of doubles below a single -/

/-- Number of consecutive non-singles directly below cell `i`. -/
def gap (T : Tr) : Nat → Nat
  | 0 => 0
  | i + 1 => if T.single i then 0 else gap T i + 1

theorem gap_spec (T : Tr) : ∀ i, T.gap i ≤ i ∧ ∀ x, i - T.gap i ≤ x → x < i → ¬ T.single x := by
  intro i
  induction i with
  | zero => exact ⟨Nat.le_refl _, fun x _ h => by omega⟩
  | succ i ih =>
      simp only [gap]
      by_cases hs : T.single i
      · rw [if_pos hs]; exact ⟨by omega, fun x a b => by omega⟩
      · rw [if_neg hs]
        refine ⟨by omega, fun x a b => ?_⟩
        by_cases hx : x = i
        · subst hx; exact hs
        · exact ih.2 x (by omega) (by omega)

section forced2
variable {T : Tr} {e : Nat} (F : T.Forced e) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
include F hp hn

/-- The last removal of a single that is not a run start is reversible. -/
theorem rev_at_tau {s : Nat} (hs : T.single s) (hsn : s < T.n - 1) (hna : ¬ T.asc s) (h1 : 1 ≤ s) :
    T.N (s - 1) (T.tau s) % 2 = 1 := by
  apply Classical.byContradiction; intro hne
  have hss : 0 < T.c s := by unfold single at hs; omega
  obtain ⟨tl, tm, tN⟩ := T.tau_spec hss
  have hE : T.isE (T.tau s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [tm]; unfold single at hs; omega
    · rw [tm]; omega
    · rw [tm]; omega
  obtain ⟨y, hy, hty⟩ := T.isE_asc (by rw [F.numAsc_eq, F.eras_eq]) tl hE
  have hy2 := (T.tau_spec (i := y) (by have := T.c_ge_two (i := y) hy.2.1; omega)).2.1
  rw [hty, tm] at hy2
  subst hy2; exact hna hy

/-- **Gap bound.**  Below the `k`-th single of a run (not a run start) lie at most `p − 1 − k`
consecutive doubles. -/
theorem gap_bound {s : Nat} (hs : T.single s) (hsn : s < T.n - 1) (hna : ¬ T.asc s) :
    T.gap s + T.kr s + 1 ≤ T.p := by
  obtain ⟨hgle, hgap⟩ := T.gap_spec s
  obtain ⟨c, h1, h2, h3, h4⟩ := T.next_bnd hn (T.n - 1 - s) s (by omega) (by omega)
  obtain ⟨hc1, hc⟩ := bnd_le F hp hn h3
  have hrs : T.rho s = T.rho (c - 1) := T.rho_of_next h1 h4
  obtain ⟨f, hf, hm, hN⟩ := T.first_place (i := c) (by omega) (by omega)
  have hfull := fun {x} hx hon => T.full hc1 hc hf hm hN (bnd_kr F hp hn h3 hc1) (x := x) hx hon
  have hss : T.c s = 2 := hs
  obtain ⟨tl, tm, tN⟩ := T.tau_spec (i := s) (by omega)
  have ht1 := T.tau_run (x := s) (c - 1) (by omega) (by omega) hrs
  have ht2 := T.tau_pred_gt hc1 hc hf hm hN
  have hon_c : T.N c (f + 1) % 2 = 1 := by rw [T.N_succ_self hf hm, hN]
  -- facts about each gap cell
  have hgcell : ∀ x, s - T.gap s ≤ x → x < s →
      T.c x = 4 ∧ T.rho x = T.rho s ∧ T.tau s < T.tau x ∧ T.N x (f + 1) = 2 := by
    intro x a b
    have hnx := hgap x a b
    have hc4 := F.c_double x (by omega) hnx
    have hrx : T.rho x = T.rho s := T.rho_eq_of_noasc s (by omega) (by
      intro w wa wb hw
      by_cases hws : w = s
      · subst hws; exact hna hw
      · exact hgap w (by omega) (by omega) (asc_single F hp hn hw))
    have htx := T.tau_run (x := x) s (by omega) (by omega) hrx
    have htne := T.tau_ne (i := x) (j := s) (by omega) (by omega) (by omega)
    have hoff : T.N x (f + 1) % 2 = 0 := by
      apply Classical.byContradiction; intro hne
      rcases hfull (x := x) (by omega) (by omega) with h | h
      · exact hnx h.2.2
      · omega
    have hpos := T.below_placed c (f + 1) (by omega) hon_c x (by omega)
    have hnd : T.N x (f + 1) ≠ T.c x := fun h =>
      (show ¬ T.tau x < f + 1 by omega) ((T.N_eq_c_iff (by omega) (by omega)).mp h)
    have hle := T.N_le_c x (show f + 1 ≤ T.L by omega)
    exact ⟨hc4, hrx, by omega, by omega⟩
  -- every gap cell is on the board at the last removal of `s`
  have hgon : ∀ d, 1 ≤ d → d ≤ T.gap s → T.N (s - d) (T.tau s) = 3 := by
    intro d
    induction d with
    | zero => intro h; omega
    | succ d ih =>
        intro _ hd
        obtain ⟨hc4, -, hlt, hN2⟩ := hgcell (s - (d + 1)) (by omega) (by omega)
        have hup : T.N (s - (d + 1)) (T.tau s) ≤ 3 := by
          have hnd : T.N (s - (d + 1)) (T.tau s) ≠ T.c (s - (d + 1)) := fun h =>
            (show ¬ T.tau (s - (d + 1)) < T.tau s by omega) ((T.N_eq_c_iff (by omega) (by omega)).mp h)
          have := T.N_le_c (s - (d + 1)) (show T.tau s ≤ T.L by omega)
          omega
        have hlo := T.N_mono (i := s - (d + 1)) (show f + 1 ≤ T.tau s by omega) (by omega)
        by_cases hd0 : d = 0
        · subst hd0
          have hrev := rev_at_tau F hp hn hs hsn hna (by omega)
          rw [show s - (0 + 1) = s - 1 by omega] at *
          omega
        · have hprev := ih (by omega) (by omega)
          obtain ⟨-, -, -, hN2'⟩ := hgcell (s - d) (by omega) (by omega)
          obtain ⟨j, hj1, hj2, hjm, hjN⟩ := T.ivt (s - d) (T.tau s) (by omega) (f + 1) 2
            (by omega) (by omega) (by omega)
          have hpl := T.place j (by omega) (by rw [hjm, hjN]) (by rw [hjm]; omega)
          rw [hjm, show s - d - 1 = s - (d + 1) by omega] at hpl
          have a := T.N_mono (i := s - (d + 1)) hj1 (by omega)
          have b := T.N_mono (i := s - (d + 1)) (show j ≤ T.tau s by omega) (by omega)
          omega
  -- count what is on the board at the last removal of `s`
  let Q : Nat → Prop := fun i =>
    (i < s + 1 ∧ T.rho i = T.rho s ∧ T.single i) ∨ (s - T.gap s ≤ i ∧ i < s) ∨ i = c
  have hQon : ∀ i, Q i → T.N i (T.tau s) % 2 = 1 := by
    intro i hi
    rcases hi with ⟨a, b, d⟩ | ⟨a, b⟩ | h
    · have hti := T.tau_run (x := i) s (by omega) (by omega) b
      have hd : T.c i = 2 := d
      have hpos : 1 ≤ T.N i (T.tau s) := by
        by_cases his : i = s
        · subst his; omega
        · exact T.below_placed s (T.tau s) (by omega) (by omega) i (by omega)
      have hnd : T.N i (T.tau s) ≠ T.c i := fun h =>
        (show ¬ T.tau i < T.tau s by omega) ((T.N_eq_c_iff (by omega) (by omega)).mp h)
      have := T.N_le_c i (show T.tau s ≤ T.L by omega)
      omega
    · have := hgon (s - i) (by omega) (by omega)
      rw [show s - (s - i) = i by omega] at this; omega
    · subst h; exact bnd_on F hp hn h3 hs (by omega) hrs
  have hcount : rsum T.n (fun i => if Q i then 1 else 0) = T.kr s + T.gap s + 1 := by
    have e1 : rsum T.n (fun i => if Q i then 1 else 0) =
        rsum T.n (fun i => ((if i < s + 1 then (if T.rho i = T.rho s ∧ T.single i then 1 else 0) else 0)
          + (if s - T.gap s ≤ i ∧ i < s then 1 else 0)) + (if i = c then 1 else 0)) := by
      apply rsum_congr; intro i _
      by_cases hic : i = c
      · subst hic
        rw [if_pos (Or.inr (Or.inr rfl)), if_neg (by omega), if_neg (by omega), if_pos rfl]
      · rw [if_neg hic]
        by_cases hg : s - T.gap s ≤ i ∧ i < s
        · have hns := hgap i hg.1 hg.2
          rw [if_pos (Or.inr (Or.inl hg)), if_pos hg, if_pos (by omega), if_neg (fun h => hns h.2)]
        · rw [if_neg hg]
          by_cases hq : i < s + 1 ∧ T.rho i = T.rho s ∧ T.single i
          · rw [if_pos (Or.inl hq), if_pos hq.1, if_pos hq.2]
          · rw [if_neg (by intro h; rcases h with h | h | h; exact hq h; exact hg h; exact hic h)]
            by_cases hlt : i < s + 1
            · rw [if_pos hlt, if_neg (fun h => hq ⟨hlt, h⟩)]
            · rw [if_neg hlt]
    rw [e1, rsum_add, rsum_add, rsum_restrict _ (s + 1) T.n (by omega),
      rsum_interval T.n s (s - T.gap s) (by omega) (by omega), rsum_ind_eq c T.n (by omega)]
    unfold kr; omega
  have hpk := T.peak (T.tau s) (by omega)
  have := rsum_le (fun i => if Q i then 1 else 0) (fun i => if T.N i (T.tau s) % 2 = 1 then 1 else 0)
    T.n (fun i _ => by
      by_cases h : Q i
      · rw [if_pos h, if_pos (hQon i h)]; exact Nat.le_refl _
      · rw [if_neg h]; exact Nat.zero_le _)
  omega

end forced2

/-! ### Summing the gaps -/

theorem rsum_one : ∀ m, rsum m (fun _ => 1) = m := by
  intro m; induction m with
  | zero => rfl
  | succ m ih => simp only [rsum, ih]

theorem gap_tele (T : Tr) : ∀ m, rsum m (fun i => if T.single i then 0 else 1) =
    rsum m (fun i => if T.single i then T.gap i else 0) + T.gap m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [rsum, gap]
      rw [ih]
      by_cases hs : T.single m
      · simp [hs]
      · simp [hs]; omega

/-- `Σ_{j<k} (p − 2 − j)`: the gap capacity of a run holding `k` singles. -/
def hcap (T : Tr) (k : Nat) : Nat := rsum k (fun j => T.p - 2 - j)

theorem tri_hcap : ∀ q, rsum q (fun j => q - 1 - j) + 1 = Triangular.tri q := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih =>
      have h1 : rsum (q + 1) (fun j => q + 1 - 1 - j) = rsum q (fun j => q - 1 - j) + q := by
        simp only [rsum]
        have : rsum q (fun j => q + 1 - 1 - j) = rsum q (fun j => (q - 1 - j) + 1) :=
          rsum_congr _ _ q (fun j hj => by omega)
        rw [this, rsum_add (fun j => q - 1 - j) (fun _ => 1) q, rsum_one]; omega
      rw [h1]; simp only [Triangular.tri]; omega

section forced3
variable {T : Tr} {e : Nat} (F : T.Forced e) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
include F hp hn

theorem kr_of_asc {i : Nat} (ha : T.asc i) : T.kr i = 1 := by
  have h1 := ha.1
  have hs := asc_single F hp hn ha
  have := T.kr_succ (i - 1)
  rw [show i - 1 + 1 = i by omega, if_pos hs, if_pos ha] at this
  exact this

theorem gap_of_asc {i : Nat} (ha : T.asc i) : T.gap i = 0 := by
  have h1 := ha.1
  have hs := end_single F hp hn (Or.inr ha)
  rw [show i = (i - 1) + 1 by omega]
  simp only [gap]; rw [if_pos hs]

/-- **The bound, with its slack.**  The gaps below the singles fall short of their
capacities by exactly `T(p) + e·T(p−1) − n`. -/
theorem frontier_eq :
    T.n + rsum (T.n - 1) (fun i => if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0) =
      Triangular.tri T.p + e * Triangular.tri (T.p - 1) +
        rsum (T.n - 1) (fun i => if T.single i then T.gap i else 0) ∧
    (∀ i, i < T.n - 1 → (if T.single i then T.gap i else 0) ≤
      (if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0)) := by
  -- the doubles
  have hD := T.gap_tele (T.n - 1)
  have hlast : T.gap (T.n - 1) = 0 := by
    have hs := end_single F hp hn (c := T.n - 1) (Or.inl rfl)
    rw [show T.n - 1 = (T.n - 2) + 1 by omega]
    simp only [gap]; rw [if_pos (by rwa [show T.n - 2 = T.n - 1 - 1 by omega])]
  rw [hlast] at hD
  have hSD : T.S + rsum (T.n - 1) (fun i => if T.single i then 0 else 1) = T.n - 1 := by
    unfold S; rw [← rsum_add]
    rw [rsum_congr _ (fun _ => 1) _ (fun i _ => by split <;> rfl), rsum_one]
  -- gap ≤ capacity, pointwise
  have h1pt : ∀ i, i < T.n - 1 → (if T.single i then T.gap i else 0) ≤
      (if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0) := by
      intro i hi
      by_cases hs : T.single i
      · rw [if_pos hs]
        by_cases ha : T.asc i
        · rw [gap_of_asc F hp hn ha]; exact Nat.zero_le _
        · rw [if_pos ⟨hs, ha⟩]
          have := gap_bound F hp hn hs hi ha
          omega
      · rw [if_neg hs]; exact Nat.zero_le _
  have h1 := rsum_le (fun i => if T.single i then T.gap i else 0)
    (fun i => if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0) (T.n - 1) h1pt
  -- split off the run starts
  have h2 : rsum (T.n - 1) (fun i => if T.single i then T.p - 1 - T.kr i else 0) =
      rsum (T.n - 1) (fun i => if T.single i ∧ ¬ T.asc i then T.p - 1 - T.kr i else 0) +
      rsum (T.n - 1) (fun i => if T.asc i then T.p - 2 else 0) := by
    rw [← rsum_add]
    apply rsum_congr; intro i _
    by_cases ha : T.asc i
    · rw [if_pos (asc_single F hp hn ha), if_neg (fun h => h.2 ha), if_pos ha, kr_of_asc F hp hn ha]
      omega
    · rw [if_neg ha]
      by_cases hs : T.single i
      · rw [if_pos hs, if_pos ⟨hs, ha⟩]; omega
      · rw [if_neg hs, if_neg (fun h => hs h.1)]
  have h3 : rsum (T.n - 1) (fun i => if T.asc i then T.p - 2 else 0) = (T.p - 2) * e := by
    rw [rsum_mul_ind]; unfold numAsc at *; rw [← F.numAsc_eq]; rfl
  -- telescoping the capacities over runs
  have h4 : rsum (T.n - 1) (fun i => if T.single i then T.p - 1 - T.kr i else 0) =
      rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.hcap (T.kr i) else 0) + T.hcap (T.kr (T.n - 2)) := by
    rw [show T.n - 1 = (T.n - 2) + 1 by omega]
    apply telescope (fun i => if T.single i then T.p - 1 - T.kr i else 0) (fun i => T.hcap (T.kr i)) T.asc
    · rw [T.kr_zero]
      by_cases hs : T.single 0
      · simp only [if_pos hs, hcap, rsum]; omega
      · simp only [if_neg hs, hcap, rsum]
    · intro i
      rw [T.kr_succ i]
      by_cases ha : T.asc (i + 1)
      · rw [if_pos ha, if_pos ha]
        by_cases hs : T.single (i + 1)
        · simp only [if_pos hs, hcap, rsum]; omega
        · simp only [if_neg hs, hcap, rsum]
      · rw [if_neg ha, if_neg ha]
        by_cases hs : T.single (i + 1)
        · simp only [if_pos hs]
          rw [Nat.add_comm 1 (T.kr i)]
          simp only [hcap, rsum]; omega
        · simp only [if_neg hs, Nat.zero_add]
  have hH : T.hcap (T.p - 1) + 1 = Triangular.tri (T.p - 1) := by
    have e1 : T.hcap (T.p - 1) = rsum (T.p - 1) (fun j => T.p - 1 - 1 - j) :=
      rsum_congr _ _ _ (fun j _ => by omega)
    rw [e1]; exact tri_hcap (T.p - 1)
  have h5 : rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.hcap (T.kr i) else 0) =
      T.hcap (T.p - 1) * e := by
    have : rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.hcap (T.kr i) else 0) =
        rsum (T.n - 2) (fun i => if T.asc (i + 1) then T.hcap (T.p - 1) else 0) := by
      apply rsum_congr; intro i hi
      by_cases ha : T.asc (i + 1)
      · rw [if_pos ha, if_pos ha, show T.kr i = T.p - 1 by have := F.kr_asc i (by omega) ha; omega]
      · rw [if_neg ha, if_neg ha]
    rw [this, rsum_mul_ind (fun i => T.asc (i + 1)), ← T.numAsc_shift hn, F.numAsc_eq]
  have h6 : T.kr (T.n - 2) = T.p - 1 := by have := F.kr_last; omega
  rw [h6] at h4
  have hS := F.S_eq
  have htp : Triangular.tri T.p = Triangular.tri (T.p - 1) + (T.p - 1) := by
    have key : Triangular.tri (T.p - 1 + 1) = Triangular.tri (T.p - 1) + (T.p - 1) := rfl
    rw [show T.p - 1 + 1 = T.p by omega] at key; exact key
  -- arithmetic
  have m1 : (T.p - 1) * (e + 1) = (T.p - 2) * e + e + (T.p - 1) := by
    have a : (T.p - 1) * (e + 1) = (T.p - 1) * e + (T.p - 1) := Nat.mul_succ _ _
    have b := Nat.succ_mul (T.p - 2) e
    rw [show (T.p - 2).succ = T.p - 1 by omega] at b
    omega
  have m2 : e * Triangular.tri (T.p - 1) = T.hcap (T.p - 1) * e + e := by
    rw [← hH, Nat.mul_succ, Nat.mul_comm]
  exact ⟨by omega, h1pt⟩

/-- **The bound.**  A plan meeting the length bound lives below the triangular frontier. -/
theorem frontier : T.n ≤ Triangular.tri T.p + e * Triangular.tri (T.p - 1) := by
  obtain ⟨h, hpt⟩ := frontier_eq F hp hn
  have := rsum_le _ _ _ hpt
  omega

end forced3

theorem frontier_of_length (T : Tr) (e : Nat) (hp : 2 ≤ T.p) (hn : 2 ≤ T.n)
    (hlen : T.L + 2 * ((T.p - 1) * (e + 1) + 1) + 1 ≤ 4 * T.n) (he : T.eras ≤ e) :
    T.n ≤ Triangular.tri T.p + e * Triangular.tri (T.p - 1) :=
  frontier (T.forced e hp hn hlen he) hp hn

end Tr

/-! ## From clean plans to traces -/

theorem ones_eq_rsum : ∀ b : Board, ones b = rsum b.length (fun i => if nth b i then 1 else 0) := by
  intro b
  induction b with
  | nil => rfl
  | cons x b ih =>
      rw [List.length_cons, Tr.rsum_shift]
      have h1 : ones (x :: b) = (if x then 1 else 0) + ones b := by
        cases x <;> simp [ones, List.count_cons] <;> omega
      have h2 : nth (x :: b) 0 = x := rfl
      have h3 : ∀ i, nth (x :: b) (i + 1) = nth b i := fun i => rfl
      rw [h1, ih, h2]
      simp only [h3]

theorem ones_take_le (b : Board) (s : List Nat) (k : Nat) :
    ones (execB b (s.take k)) ≤ maxOnes b s := by
  have h := maxOnes_append b (s.take k) (s.drop k)
  rw [List.take_append_drop] at h
  have := ones_le_maxOnes (execB b (s.take k)) (s.drop k)
  rw [h]; omega

theorem take_succ_of_lt {s : List Nat} {k : Nat} (hk : k < s.length) :
    s.take (k + 1) = s.take k ++ [s.getD k 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  rfl

theorem nth_state (n : Nat) (s : List Nat) (k j : Nat) (hj : j < n) :
    nth (execB (empty n) (s.take k)) j = decide ((s.take k).count j % 2 = 1) := by
  have := nth_execB_parity (s.take k) (empty n) j (by rw [length_empty]; exact hj)
  rw [this, nth_empty]; simp

theorem getD_mem {s : List Nat} {k : Nat} (hk : k < s.length) : s.getD k 0 ∈ s := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

/-- The trace of a clean plan. -/
def ofPlay (n p e : Nat) (s : List Nat) (hn : 1 ≤ n) (h : IsPlay n p e s) : Tr where
  n := n
  L := s.length
  p := p
  mv := fun k => s.getD k 0
  N := fun i k => (s.take k).count i
  N_zero := by intro i; simp
  N_succ := by
    intro i k hk
    rw [take_succ_of_lt hk, List.count_append, List.count_singleton]
    by_cases h : s.getD k 0 = i
    · simp [h]
    · simp [h]
  mv_lt := fun k hk => h.bounds _ (getD_mem hk)
  place := by
    intro k hk hev hpos
    have hmv := h.bounds _ (getD_mem hk)
    have hleg := h.legal
    rw [← List.take_append_drop k s, legalE_append, List.drop_eq_getElem_cons hk] at hleg
    have hok : okE (execB (empty n) (s.take k)) s[k] = true := by
      simp only [Bool.and_eq_true, legalE_cons] at hleg; exact hleg.2.1
    have hsk : s[k] = s.getD k 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    rw [hsk] at hok
    unfold okE okMove at hok
    rw [nth_state n s k _ hmv] at hok
    rw [nth_state n s k _ (by omega)] at hok
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    omega
  peak := by
    intro k _
    have h1 := ones_take_le (empty n) s k
    rw [ones_eq_rsum, length_execB, length_empty] at h1
    have h2 : rsum n (fun i => if nth (execB (empty n) (s.take k)) i then 1 else 0) =
        rsum n (fun i => if (s.take k).count i % 2 = 1 then 1 else 0) := by
      apply rsum_congr; intro i hi; rw [nth_state n s k i hi]; simp
    rw [h2] at h1
    exact Nat.le_trans h1 h.peak
  final := by
    intro i hi
    have := nth_state n s s.length i hi
    rw [List.take_length, h.final, nth_target n i hn] at this
    simp only [decide_eq_decide] at this
    show (s.take s.length).count i % 2 = 1 ↔ i = n - 1
    rw [List.take_length]
    exact this.symm

theorem eras_ofPlay (n p e : Nat) (s : List Nat) (hn : 1 ≤ n) (h : IsPlay n p e s) :
    (ofPlay n p e s hn h).eras = erasures (empty n) s := by
  have key : ∀ k, k ≤ s.length → erasures (empty n) (s.take k) =
      rsum k (fun j => if (ofPlay n p e s hn h).isE j then 1 else 0) := by
    intro k
    induction k with
    | zero => simp [rsum]
    | succ k ih =>
        intro hk
        rw [take_succ_of_lt (by omega), erasures_append, ih (by omega)]
        simp only [rsum]
        congr 1
        have hmv := h.bounds _ (getD_mem (show k < s.length by omega))
        simp only [erasures_cons, erasures_nil, Nat.add_zero]
        have hiff : isErase (execB (empty n) (s.take k)) (s.getD k 0) = true ↔
            (ofPlay n p e s hn h).isE k := by
          show _ ↔ ((s.take k).count (s.getD k 0) % 2 = 1 ∧ 0 < s.getD k 0 ∧
            (s.take k).count (s.getD k 0 - 1) % 2 = 0)
          unfold isErase okMove
          rw [nth_state n s k _ hmv, nth_state n s k _ (by omega)]
          generalize (s.take k).count (s.getD k 0) = A
          generalize (s.take k).count (s.getD k 0 - 1) = B
          generalize s.getD k 0 = x
          by_cases h1 : A % 2 = 1 <;> by_cases h2 : x = 0 <;> by_cases h3 : B % 2 = 1 <;>
            simp [h1, h2, h3] <;> omega
        by_cases hx : (ofPlay n p e s hn h).isE k
        · rw [if_pos (hiff.mpr hx), if_pos hx]
        · rw [if_neg (fun h' => hx (hiff.mp h')), if_neg hx]
  unfold Tr.eras
  have := key s.length (Nat.le_refl _)
  rw [List.take_length] at this
  exact this.symm

/-- **Lower bound below the frontier.**  A clean plan with at most
`2n − 1 + 2(n − A)` moves, `A = (p−1)(e+1)+1`, only exists for `n ≤ T(p) + e·T(p−1)`. -/
theorem frontier_lower (n p e : Nat) (hp : 2 ≤ p) (hn : 2 ≤ n) (s : List Nat) (h : IsPlay n p e s)
    (hlen : s.length + 2 * ((p - 1) * (e + 1) + 1) + 1 ≤ 4 * n) :
    n ≤ Triangular.tri p + e * Triangular.tri (p - 1) := by
  have := Tr.frontier_of_length (ofPlay n p e s (by omega) h) e hp hn hlen
    (by rw [eras_ofPlay]; exact h.budget)
  exact this

/-- **One past the frontier: exact.**  For `p ≥ 4`, `n = T(p) + e·T(p−1) + 1`,
`M*(n, p, e) = L₀ + 2` with `L₀ = 2n − 1 + 2(n − A)`. -/
theorem next_exact (p e : Nat) (hp : 4 ≤ p) :
    MstarIs (Triangular.tri p + e * Triangular.tri (p - 1) + 1) p e
      (2 * (Triangular.tri p + e * Triangular.tri (p - 1) + 1) - 1 +
        2 * (Triangular.tri p + e * Triangular.tri (p - 1) + 1 - ((p - 1) * (e + 1) + 1)) + 2) := by
  obtain ⟨⟨s, hs, hl⟩, h2⟩ := NextPoint.next_point p e hp
  have hu := Triangular.tri_ge (p - 1)
  have hv := Triangular.tri_ge p
  have hle : (p - 1) * e ≤ e * Triangular.tri (p - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
  have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
  have low : ∀ t, IsPlay (Triangular.tri p + e * Triangular.tri (p - 1) + 1) p e t →
      2 * (Triangular.tri p + e * Triangular.tri (p - 1) + 1) - 1 +
        2 * (Triangular.tri p + e * Triangular.tri (p - 1) + 1 - ((p - 1) * (e + 1) + 1)) + 2
        ≤ t.length := by
    intro t ht
    rcases h2 t ht with he | he
    · have := frontier_lower _ p e (by omega) (by omega) t ht (by omega)
      omega
    · exact he
  exact ⟨⟨s, hs, Nat.le_antisymm hl (low s hs)⟩, low⟩

/-- **p = 4 endpoint.**  `M*(4e+8, 4, e) = 25 + 10e`. -/
theorem p4_exact (e : Nat) : MstarIs (4 * e + 8) 4 e (25 + 10 * e) := by
  have h := next_exact 4 e (Nat.le_refl _)
  have en : Triangular.tri 4 + e * Triangular.tri (4 - 1) + 1 = 4 * e + 8 := by
    simp [Triangular.tri]; omega
  rw [en] at h
  have el : 2 * (4 * e + 8) - 1 + 2 * (4 * e + 8 - ((4 - 1) * (e + 1) + 1)) + 2 = 25 + 10 * e := by
    omega
  rw [el] at h
  exact h

end ErasurePebbling.NextPointLower
