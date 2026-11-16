import ErasurePebbling.FirstDrop

/-!
# The contraction lower bound

For `p ≥ 2` and every clean plan `s` on a chain of length `n ≥ 1` with peak
`p` and at most `e` erasures, with `A = (p−1)(e+1) + 1`:

  `|s| ≥ 2n − 1 + 2·max(0, n − A)`          (`contraction_bound`).

Theorem A says that a plan placing every cell exactly once (`|s| = 2n − 1`)
needs `n ≤ A`.  A longer plan places some cell twice; *contracting* the
lowest such cell gives a clean plan on a chain one shorter, with no larger
peak and no more erasures, that is at least four moves shorter.  Induction
on `n` then gives the bound.

The contraction is a projection along a board map:

* `x = 0` (0-indexed): delete cell `0` (`dropB`); the old cell `1` becomes
  the new entrance cell and is always available.
* `x ≥ 1`: cell `x − 1` is toggled exactly twice, so its pebble lives on one
  interval, and every placement of `x` falls inside it.  Merge cells
  `x − 1` and `x` into one cell carrying their OR (`mergeB`); moves that do
  not change the merged board are dropped.  The merged cell then changes at
  most twice (`count_merge_le_two`).

Every kept move is legal, is an erasure only if the original move was, and
the pebble count never grows (`proj_isPlay`).

(Paper proof: the 2026-11-11 note `消去ペブリング_再配置縮約一般下界`; this
file is its machine-checked version.  The note also derives the finer form
`n ≤ (p−1)(r+1) + 1 + D` with `D` the number of re-placed cells; only the
length bound is formalized here.)
-/

namespace ErasurePebbling
namespace Contraction

/-- Case split every `if` in the goal and close the arithmetic leftovers. -/
macro "ifs_close" : tactic =>
  `(tactic| ((repeat' split) <;> (try subst_vars) <;> (try rfl) <;> (try omega) <;> (try simp [*])))

open RevPebbling.PebblingFoundations

/-! ## Projection of a play along a board map -/

section Proj

variable (f : Board → Board) (g : Nat → Nat)

/-- Replay `s` on the image board `f b`, keeping a move (renamed by `g`) only
when it changes the image. -/
def proj : Board → List Nat → List Nat
  | _, [] => []
  | b, i :: rest =>
      if f (toggle b i) = f b then proj (toggle b i) rest
      else g i :: proj (toggle b i) rest

theorem proj_cons_eq {b : Board} {i : Nat} {rest : List Nat} (h : f (toggle b i) = f b) :
    proj f g b (i :: rest) = proj f g (toggle b i) rest := by
  simp [proj, h]

theorem proj_cons_ne {b : Board} {i : Nat} {rest : List Nat} (h : f (toggle b i) ≠ f b) :
    proj f g b (i :: rest) = g i :: proj f g (toggle b i) rest := by
  simp [proj, h]

variable (N : Nat)
variable (H : ∀ b i, b.length = N → f (toggle b i) ≠ f b → toggle (f b) (g i) = f (toggle b i))

include H in
theorem execB_proj : ∀ s b, b.length = N → execB (f b) (proj f g b s) = f (execB b s) := by
  intro s
  induction s with
  | nil => intro b _; rfl
  | cons i rest ih =>
      intro b hb
      by_cases h : f (toggle b i) = f b
      · rw [proj_cons_eq f g h, ← h, ih _ (by rw [length_toggle]; exact hb)]; rfl
      · rw [proj_cons_ne f g h]
        show execB (toggle (f b) (g i)) _ = _
        rw [H b i hb h, ih _ (by rw [length_toggle]; exact hb)]; rfl

variable (H2 : ∀ b i, b.length = N → okE b i = true → f (toggle b i) ≠ f b →
    okE (f b) (g i) = true ∧ (isErase (f b) (g i) = true → isErase b i = true))

include H H2 in
theorem legalE_proj : ∀ s b, b.length = N → legalE b s = true →
    legalE (f b) (proj f g b s) = true ∧ erasures (f b) (proj f g b s) ≤ erasures b s := by
  intro s
  induction s with
  | nil => intro b _ _; simp [proj]
  | cons i rest ih =>
      intro b hb hl
      simp only [legalE_cons, Bool.and_eq_true] at hl
      have hb' : (toggle b i).length = N := by rw [length_toggle]; exact hb
      obtain ⟨ih1, ih2⟩ := ih _ hb' hl.2
      by_cases h : f (toggle b i) = f b
      · rw [proj_cons_eq f g h, ← h]
        refine ⟨ih1, ?_⟩
        rw [erasures_cons]; omega
      · rw [proj_cons_ne f g h]
        obtain ⟨hok, her⟩ := H2 b i hb hl.1 h
        rw [legalE_cons, erasures_cons, erasures_cons, H b i hb h]
        refine ⟨by simp [hok, ih1], ?_⟩
        by_cases he : isErase (f b) (g i) = true
        · rw [if_pos he, if_pos (her he)]; omega
        · rw [if_neg he]; omega

variable (H4 : ∀ b, b.length = N → ones (f b) ≤ ones b)

include H H4 in
theorem maxOnes_proj : ∀ s b, b.length = N → maxOnes (f b) (proj f g b s) ≤ maxOnes b s := by
  intro s
  induction s with
  | nil => intro b hb; exact H4 b hb
  | cons i rest ih =>
      intro b hb
      have hb' : (toggle b i).length = N := by rw [length_toggle]; exact hb
      have ih' := ih _ hb'
      by_cases h : f (toggle b i) = f b
      · rw [proj_cons_eq f g h, ← h]
        show _ ≤ max _ _
        omega
      · rw [proj_cons_ne f g h]
        show max _ _ ≤ max _ _
        rw [H b i hb h]
        have := H4 b hb
        omega

end Proj

theorem proj_mem (f : Board → Board) (g : Nat → Nat) :
    ∀ s b k, k ∈ proj f g b s → ∃ j ∈ s, k = g j := by
  intro s
  induction s with
  | nil => intro b k hk; simp [proj] at hk
  | cons i rest ih =>
      intro b k hk
      by_cases h : f (toggle b i) = f b
      · rw [proj_cons_eq f g h] at hk
        obtain ⟨j, hj, rfl⟩ := ih _ _ hk
        exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · rw [proj_cons_ne f g h] at hk
        rcases List.mem_cons.mp hk with rfl | hk'
        · exact ⟨i, List.mem_cons_self, rfl⟩
        · obtain ⟨j, hj, rfl⟩ := ih _ _ hk'
          exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩

/-- A projection satisfying the step conditions turns a clean plan on `n`
cells into a clean plan on `n − 1` cells. -/
theorem proj_isPlay (f : Board → Board) (g : Nat → Nat) (n p e : Nat) (s : List Nat)
    (H : ∀ b i, b.length = n → f (toggle b i) ≠ f b → toggle (f b) (g i) = f (toggle b i))
    (H2 : ∀ b i, b.length = n → okE b i = true → f (toggle b i) ≠ f b →
      okE (f b) (g i) = true ∧ (isErase (f b) (g i) = true → isErase b i = true))
    (H4 : ∀ b, b.length = n → ones (f b) ≤ ones b)
    (hg : ∀ j, j < n → g j < n - 1)
    (he : f (empty n) = empty (n - 1)) (ht : f (target n) = target (n - 1))
    (h : IsPlay n p e s) : IsPlay (n - 1) p e (proj f g (empty n) s) := by
  have hl := legalE_proj f g n H H2 s (empty n) (length_empty n) h.legal
  rw [he] at hl
  refine ⟨?_, hl.1, ?_, Nat.le_trans hl.2 h.budget, ?_⟩
  · intro k hk
    obtain ⟨j, hj, rfl⟩ := proj_mem f g s _ k hk
    exact hg j (h.bounds j hj)
  · have := maxOnes_proj f g n H H4 s (empty n) (length_empty n)
    rw [he] at this
    exact Nat.le_trans this h.peak
  · have := execB_proj f g n H s (empty n) (length_empty n)
    rw [he, h.final, ht] at this
    exact this

/-! ## Board helpers -/

theorem toggle_ge (b : Board) {i : Nat} (h : b.length ≤ i) : toggle b i = b :=
  set_ge_length b i _ h

theorem nth_toggle_eq (b : Board) {i : Nat} (hi : i < b.length) (j : Nat) :
    nth (toggle b i) j = if j = i then !nth b i else nth b j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl, nth_toggle_self b hi]
  · rw [if_neg h, nth_toggle_ne b (Ne.symm h)]

/-- Deleting index `k` from a `mk` board. -/
theorem ones_mk_del : ∀ (N : Nat) (f : Nat → Bool) (k : Nat), k ≤ N →
    ones (mk (N + 1) f) = ones (mk N (fun j => if j < k then f j else f (j + 1))) +
      (if f k then 1 else 0) := by
  intro N
  induction N with
  | zero =>
      intro f k hk
      have : k = 0 := by omega
      subst this
      rw [ones_mk_succ]; simp
  | succ N ih =>
      intro f k hk
      by_cases hkN : k = N + 1
      · subst hkN
        rw [ones_mk_succ (N + 1)]
        congr 2
        apply mk_congr
        intro j hj
        rw [if_pos hj]
      · rw [ones_mk_succ (N + 1), ih f k (by omega), ones_mk_succ N]
        have : (if N < k then f N else f (N + 1)) = f (N + 1) := by rw [if_neg (by omega)]
        rw [this]
        omega

/-! ## Deleting the bottom cell -/

def dropB (b : Board) : Board := mk (b.length - 1) (fun j => nth b (j + 1))

theorem length_dropB (b : Board) : (dropB b).length = b.length - 1 := by simp [dropB]

theorem nth_dropB (b : Board) {j : Nat} (h : j < b.length - 1) :
    nth (dropB b) j = nth b (j + 1) := nth_mk_of_lt h

theorem dropB_toggle_zero (b : Board) : dropB (toggle b 0) = dropB b := by
  unfold dropB
  rw [length_toggle]
  apply mk_congr
  intro j _
  exact nth_toggle_ne b (by omega)

theorem toggle_dropB (b : Board) {i : Nat} (h1 : 1 ≤ i) (hi : i < b.length) :
    toggle (dropB b) (i - 1) = dropB (toggle b i) := by
  unfold dropB
  rw [length_toggle, toggle_mk _ (by omega)]
  apply mk_congr
  intro j _
  rw [nth_toggle_eq b hi]
  by_cases hj : j = i - 1
  · have : j + 1 = i := by omega
    rw [if_pos hj, if_pos this, Nat.sub_add_cancel h1]
  · rw [if_neg hj, if_neg (by omega)]

theorem changed_dropB {b : Board} {i : Nat} (h : dropB (toggle b i) ≠ dropB b) :
    1 ≤ i ∧ i < b.length := by
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; exact absurd (dropB_toggle_zero b) h
    · exact h0
  · apply Classical.byContradiction
    intro hi
    rw [toggle_ge b (by omega)] at h
    exact h rfl

theorem ones_dropB (b : Board) : ones (dropB b) ≤ ones b := by
  rcases b.length.eq_zero_or_pos with h0 | h0
  · simp [dropB, h0]
  · have hb := mk_nth b
    have := ones_mk_del (b.length - 1) (nth b) 0 (Nat.zero_le _)
    rw [Nat.sub_add_cancel h0, hb] at this
    have e : mk (b.length - 1) (fun j => if j < 0 then nth b j else nth b (j + 1)) = dropB b := by
      unfold dropB; apply mk_congr; intro j _; simp
    rw [e] at this
    omega

theorem dropB_empty (n : Nat) : dropB (empty n) = empty (n - 1) := by
  unfold dropB
  rw [length_empty, empty_eq_mk (n - 1)]
  apply mk_congr
  intro j _
  exact nth_empty n _

theorem dropB_target (n : Nat) (hn : 2 ≤ n) : dropB (target n) = target (n - 1) := by
  unfold dropB
  rw [length_target, target_eq_mk (n - 1) (by omega)]
  apply mk_congr
  intro j _
  rw [nth_target n _ (by omega)]
  simp only [decide_eq_decide]
  omega

theorem step_dropB (b : Board) (i : Nat) (hok : okE b i = true)
    (h : dropB (toggle b i) ≠ dropB b) :
    okE (dropB b) (i - 1) = true ∧
      (isErase (dropB b) (i - 1) = true → isErase b i = true) := by
  obtain ⟨h1, hi⟩ := changed_dropB h
  have hnth : nth (dropB b) (i - 1) = nth b i := by
    rw [nth_dropB b (by omega), Nat.sub_add_cancel h1]
  have hmv : okMove b i = true → okMove (dropB b) (i - 1) = true := by
    intro hm
    by_cases hi1 : i = 1
    · subst hi1; simp [okMove]
    · have hm' : nth b (i - 1) = true := by
        simpa [okMove, show i ≠ 0 by omega] using hm
      have : nth (dropB b) (i - 1 - 1) = nth b (i - 1) := by
        rw [nth_dropB b (by omega)]; congr 1; omega
      simp [okMove, this, hm']
  unfold okE isErase at *
  rw [hnth]
  cases hm : okMove b i
  · rw [hm] at hok
    simp at hok
    simp [hok]
  · rw [hmv hm]
    simp

/-! ## Merging cells `x − 1` and `x` -/

section Merge

variable (x : Nat)

def mval (b : Board) (j : Nat) : Bool :=
  if j < x - 1 then nth b j else if j = x - 1 then (nth b (x - 1) || nth b x) else nth b (j + 1)

def mergeB (b : Board) : Board := mk (b.length - 1) (mval x b)

def gM (i : Nat) : Nat := if i < x then i else i - 1

variable {x}

theorem length_mergeB (b : Board) : (mergeB x b).length = b.length - 1 := by simp [mergeB]

theorem nth_mergeB (b : Board) {j : Nat} (h : j < b.length - 1) :
    nth (mergeB x b) j = mval x b j := nth_mk_of_lt h

theorem toggle_mergeB_other (b : Board) (hx : 1 ≤ x) (hxn : x < b.length) {i : Nat}
    (hi : i < b.length) (h1 : i ≠ x - 1) (h2 : i ≠ x) :
    toggle (mergeB x b) (gM x i) = mergeB x (toggle b i) := by
  have hg : gM x i < b.length - 1 := by unfold gM; split <;> omega
  unfold mergeB
  rw [length_toggle, toggle_mk (n := b.length - 1) (mval x b) hg]
  apply mk_congr
  intro j _
  simp only [mval, nth_toggle_eq b hi, gM]
  ifs_close

theorem toggle_mergeB_low (b : Board) (hx : 1 ≤ x) (hxn : x < b.length)
    (hb : nth b x = false) :
    toggle (mergeB x b) (gM x (x - 1)) = mergeB x (toggle b (x - 1)) := by
  have hg : gM x (x - 1) = x - 1 := by unfold gM; rw [if_pos (by omega)]
  rw [hg]
  unfold mergeB
  rw [length_toggle, toggle_mk (n := b.length - 1) (mval x b) (show x - 1 < b.length - 1 by omega)]
  apply mk_congr
  intro j _
  simp only [mval, nth_toggle_eq b (show x - 1 < b.length by omega)]
  ifs_close
  all_goals (first | exact absurd trivial ‹¬True› | (simp only [Nat.sub_add_cancel hx]; simp [*]))

theorem toggle_mergeB_high (b : Board) (hx : 1 ≤ x) (hxn : x < b.length)
    (hb : nth b (x - 1) = false) :
    toggle (mergeB x b) (gM x x) = mergeB x (toggle b x) := by
  have hg : gM x x = x - 1 := by unfold gM; rw [if_neg (by omega)]
  rw [hg]
  unfold mergeB
  rw [length_toggle, toggle_mk (n := b.length - 1) (mval x b) (show x - 1 < b.length - 1 by omega)]
  apply mk_congr
  intro j _
  simp only [mval, nth_toggle_eq b hxn]
  ifs_close
  all_goals (first | exact absurd trivial ‹¬True› | (simp only [Nat.sub_add_cancel hx]; simp [*]))

theorem mergeB_toggle_low_eq (b : Board) (hx : 1 ≤ x) (hxn : x < b.length)
    (hb : nth b x = true) : mergeB x (toggle b (x - 1)) = mergeB x b := by
  unfold mergeB
  rw [length_toggle]
  apply mk_congr
  intro j _
  simp only [mval, nth_toggle_eq b (show x - 1 < b.length by omega)]
  ifs_close

theorem mergeB_toggle_high_eq (b : Board) (hx : 1 ≤ x) (hxn : x < b.length)
    (hb : nth b (x - 1) = true) : mergeB x (toggle b x) = mergeB x b := by
  unfold mergeB
  rw [length_toggle]
  apply mk_congr
  intro j _
  simp only [mval, nth_toggle_eq b hxn]
  ifs_close

theorem toggle_mergeB (b : Board) (hx : 1 ≤ x) (hxn : x < b.length) (i : Nat)
    (h : mergeB x (toggle b i) ≠ mergeB x b) :
    toggle (mergeB x b) (gM x i) = mergeB x (toggle b i) := by
  by_cases hi : i < b.length
  · by_cases h1 : i = x - 1
    · subst h1
      cases hb : nth b x
      · exact toggle_mergeB_low b hx hxn hb
      · exact absurd (mergeB_toggle_low_eq b hx hxn hb) h
    · by_cases h2 : i = x
      · subst h2
        cases hb : nth b (i - 1)
        · exact toggle_mergeB_high b hx hxn hb
        · exact absurd (mergeB_toggle_high_eq b hx hxn hb) h
      · exact toggle_mergeB_other b hx hxn hi h1 h2
  · rw [toggle_ge b (by omega)] at h
    exact absurd rfl h

theorem step_mergeB (b : Board) (hx : 1 ≤ x) (hxn : x < b.length) (i : Nat)
    (hok : okE b i = true) (h : mergeB x (toggle b i) ≠ mergeB x b) :
    okE (mergeB x b) (gM x i) = true ∧
      (isErase (mergeB x b) (gM x i) = true → isErase b i = true) := by
  have hi : i < b.length := by
    apply Classical.byContradiction
    intro hi
    rw [toggle_ge b (by omega)] at h
    exact h rfl
  -- reduce both claims to: same pebble, and availability can only grow
  suffices hs : nth (mergeB x b) (gM x i) = nth b i ∧
      (okMove b i = true → okMove (mergeB x b) (gM x i) = true) by
    obtain ⟨hn, hm⟩ := hs
    unfold okE isErase at *
    rw [hn]
    cases hmb : okMove b i
    · rw [hmb] at hok; simp at hok; simp [hok]
    · rw [hm hmb]; simp
  by_cases h1 : i = x - 1
  · subst h1
    have hb : nth b x = false := by
      cases hb : nth b x
      · rfl
      · exact absurd (mergeB_toggle_low_eq b hx hxn hb) h
    have hg : gM x (x - 1) = x - 1 := by unfold gM; rw [if_pos (by omega)]
    rw [hg, nth_mergeB b (by omega)]
    refine ⟨by simp [mval, hb], ?_⟩
    intro hm
    by_cases hx1 : x - 1 = 0
    · simp [okMove, hx1]
    · have hm' : nth b (x - 1 - 1) = true := by simpa [okMove, hx1] using hm
      have : nth (mergeB x b) (x - 1 - 1) = nth b (x - 1 - 1) := by
        rw [nth_mergeB b (by omega)]; simp only [mval]; rw [if_pos (by omega)]
      simp [okMove, this, hm']
  by_cases h2 : i = x
  · subst h2
    have hb : nth b (i - 1) = false := by
      cases hb : nth b (i - 1)
      · rfl
      · exact absurd (mergeB_toggle_high_eq b hx hxn hb) h
    have hpeb : nth b i = true := by
      unfold okE okMove at hok
      simpa [show i ≠ 0 by omega, hb] using hok
    have hg : gM i i = i - 1 := by unfold gM; rw [if_neg (by omega)]
    rw [hg, nth_mergeB b (by omega)]
    refine ⟨by simp [mval, hpeb], ?_⟩
    intro hm
    simp [okMove, show i ≠ 0 by omega, hb] at hm
  -- a move away from the merged pair
  by_cases hix : i < x
  · have hg : gM x i = i := by unfold gM; rw [if_pos hix]
    rw [hg, nth_mergeB b (by omega)]
    refine ⟨by simp only [mval]; rw [if_pos (by omega)], ?_⟩
    intro hm
    by_cases hi0 : i = 0
    · simp [okMove, hi0]
    · have hm' : nth b (i - 1) = true := by simpa [okMove, hi0] using hm
      have : nth (mergeB x b) (i - 1) = nth b (i - 1) := by
        rw [nth_mergeB b (by omega)]; simp only [mval]; rw [if_pos (by omega)]
      simp [okMove, this, hm']
  · have hg : gM x i = i - 1 := by unfold gM; rw [if_neg hix]
    rw [hg, nth_mergeB b (by omega)]
    refine ⟨by
      simp only [mval]; rw [if_neg (by omega), if_neg (by omega), Nat.sub_add_cancel (by omega)], ?_⟩
    intro hm
    have hm' : nth b (i - 1) = true := by simpa [okMove, show i ≠ 0 by omega] using hm
    have hne : (i - 1 == 0) = false := by simp; omega
    simp only [okMove, hne, Bool.false_or]
    rw [nth_mergeB b (by omega)]
    simp only [mval]
    rw [if_neg (by omega)]
    by_cases hxx : i - 1 - 1 = x - 1
    · rw [if_pos hxx]
      have : i - 1 = x := by omega
      rw [this] at hm'
      simp [hm']
    · rw [if_neg hxx, show i - 1 - 1 + 1 = i - 1 by omega, hm']

theorem ones_mergeB (b : Board) (hx : 1 ≤ x) (hxn : x < b.length) :
    ones (mergeB x b) ≤ ones b := by
  -- `b` with cell `x − 1` replaced by the OR
  let f' : Nat → Bool := fun j => if j = x - 1 then (nth b (x - 1) || nth b x) else nth b j
  have hlen : b.length - 1 + 1 = b.length := by omega
  have h1 := ones_mk_del (b.length - 1) f' x (by omega)
  have h2 := ones_mk_del (b.length - 1) (nth b) (x - 1) (by omega)
  rw [hlen] at h1 h2
  rw [mk_nth] at h2
  have e1 : mk (b.length - 1) (fun j => if j < x then f' j else f' (j + 1)) = mergeB x b := by
    unfold mergeB; apply mk_congr; intro j _
    simp only [f', mval]
    ifs_close
  have e2 : mk (b.length - 1) (fun j => if j < x - 1 then f' j else f' (j + 1)) =
      mk (b.length - 1) (fun j => if j < x - 1 then nth b j else nth b (j + 1)) := by
    apply mk_congr; intro j _
    simp only [f']
    ifs_close
  have h3 := ones_mk_del (b.length - 1) f' (x - 1) (by omega)
  rw [hlen, e2] at h3
  rw [e1] at h1
  have hfx : f' x = nth b x := by simp only [f']; rw [if_neg (by omega)]
  have hfx1 : f' (x - 1) = (nth b (x - 1) || nth b x) := by simp [f']
  rw [hfx] at h1
  rw [hfx1] at h3
  cases ha : nth b (x - 1) <;> cases hc : nth b x <;> simp [ha, hc] at h1 h2 h3 <;> omega

theorem mergeB_empty (n : Nat) : mergeB x (empty n) = empty (n - 1) := by
  unfold mergeB
  rw [length_empty, empty_eq_mk (n - 1)]
  apply mk_congr
  intro j _
  simp [mval, nth_empty]

theorem mergeB_target (n : Nat) (hx : 1 ≤ x) (hxn : x < n) :
    mergeB x (target n) = target (n - 1) := by
  unfold mergeB
  rw [length_target, target_eq_mk (n - 1) (by omega)]
  apply mk_congr
  intro j _
  simp only [mval, nth_target n _ (by omega)]
  ifs_close
  all_goals (first | omega | (simp only [← Bool.decide_or, decide_eq_decide]; omega))

end Merge

/-! ## Counting the kept moves -/

theorem toggle_ne_self (c : Board) {k : Nat} (hk : k < c.length) : toggle c k ≠ c := by
  intro h
  have := nth_toggle_self c hk
  rw [h] at this
  cases hc : nth c k <;> rw [hc] at this <;> cases this

theorem dropB_changed (b : Board) {i : Nat} (h1 : 1 ≤ i) (hi : i < b.length) :
    dropB (toggle b i) ≠ dropB b := by
  rw [← toggle_dropB b h1 hi]
  exact toggle_ne_self _ (by rw [length_dropB]; omega)

/-- Deleting cell `0` drops exactly its moves. -/
theorem length_proj_dropB : ∀ (s : List Nat) (b : Board), (∀ i ∈ s, i < b.length) →
    (proj dropB (· - 1) b s).length + s.count 0 = s.length := by
  intro s
  induction s with
  | nil => intro b _; simp [proj]
  | cons i rest ih =>
      intro b hb
      have hb' : ∀ k ∈ rest, k < (toggle b i).length := by
        intro k hk; rw [length_toggle]; exact hb k (List.mem_cons_of_mem _ hk)
      have hi : i < b.length := hb i List.mem_cons_self
      have := ih (toggle b i) hb'
      by_cases h0 : i = 0
      · subst h0
        rw [proj_cons_eq _ _ (dropB_toggle_zero b), List.count_cons_self, List.length_cons]
        omega
      · rw [proj_cons_ne _ _ (dropB_changed b (by omega) hi), List.count_cons_of_ne h0,
          List.length_cons, List.length_cons]
        omega

section MergeCount

variable {x : Nat}

theorem mergeB_changed_other (b : Board) (hx : 1 ≤ x) (hxn : x < b.length) {i : Nat}
    (hi : i < b.length) (h1 : i ≠ x - 1) (h2 : i ≠ x) :
    mergeB x (toggle b i) ≠ mergeB x b := by
  rw [← toggle_mergeB_other b hx hxn hi h1 h2]
  apply toggle_ne_self
  rw [length_mergeB]; unfold gM; split <;> omega

/-- Moves of the merged pair become moves at `x − 1`; all other moves are kept. -/
theorem length_proj_mergeB (hx : 1 ≤ x) : ∀ (s : List Nat) (b : Board), x < b.length →
    (∀ i ∈ s, i < b.length) →
    (proj (mergeB x) (gM x) b s).length + (s.count (x - 1) + s.count x) =
      s.length + (proj (mergeB x) (gM x) b s).count (x - 1) := by
  intro s
  induction s with
  | nil => intro b _ _; simp [proj]
  | cons i rest ih =>
      intro b hxn hb
      have hxn' : x < (toggle b i).length := by rw [length_toggle]; exact hxn
      have hb' : ∀ k ∈ rest, k < (toggle b i).length := by
        intro k hk; rw [length_toggle]; exact hb k (List.mem_cons_of_mem _ hk)
      have hi : i < b.length := hb i List.mem_cons_self
      have := ih (toggle b i) hxn' hb'
      by_cases hp : i = x - 1 ∨ i = x
      · have hg : gM x i = x - 1 := by unfold gM; split <;> omega
        have hc : (i :: rest).count (x - 1) + (i :: rest).count x =
            rest.count (x - 1) + rest.count x + 1 := by
          rcases hp with rfl | rfl
          · rw [List.count_cons_self, List.count_cons_of_ne (by omega)]; omega
          · rw [List.count_cons_self, List.count_cons_of_ne (by omega)]; omega
        rw [hc]
        by_cases h : mergeB x (toggle b i) = mergeB x b
        · rw [proj_cons_eq _ _ h, List.length_cons]; omega
        · rw [proj_cons_ne _ _ h, hg, List.count_cons_self, List.length_cons, List.length_cons]
          omega
      · have h1 : i ≠ x - 1 := fun e => hp (Or.inl e)
        have h2 : i ≠ x := fun e => hp (Or.inr e)
        have hg : gM x i ≠ x - 1 := by unfold gM; split <;> omega
        rw [proj_cons_ne _ _ (mergeB_changed_other b hx hxn hi h1 h2),
          List.count_cons_of_ne h1, List.count_cons_of_ne h2,
          List.count_cons_of_ne hg, List.length_cons, List.length_cons]
        omega

/-- Number of kept moves at the merged cell. -/
abbrev mc (x : Nat) (b : Board) (s : List Nat) : Nat := (proj (mergeB x) (gM x) b s).count (x - 1)

theorem mc_other (hx : 1 ≤ x) (b : Board) (hxn : x < b.length) {i : Nat} (rest : List Nat)
    (hi : i < b.length) (h1 : i ≠ x - 1) (h2 : i ≠ x) :
    mc x b (i :: rest) = mc x (toggle b i) rest := by
  have hg : gM x i ≠ x - 1 := by unfold gM; split <;> omega
  unfold mc
  rw [proj_cons_ne _ _ (mergeB_changed_other b hx hxn hi h1 h2), List.count_cons_of_ne hg]

theorem mc_pair (b : Board) {i : Nat} (rest : List Nat) (hp : i = x - 1 ∨ i = x) :
    mc x b (i :: rest) ≤ mc x (toggle b i) rest + 1 := by
  have hg : gM x i = x - 1 := by unfold gM; split <;> omega
  unfold mc
  by_cases h : mergeB x (toggle b i) = mergeB x b
  · rw [proj_cons_eq _ _ h]; omega
  · rw [proj_cons_ne _ _ h, hg, List.count_cons_self]
    exact Nat.le_refl _

theorem mc_same (b : Board) {i : Nat} (rest : List Nat) (h : mergeB x (toggle b i) = mergeB x b) :
    mc x b (i :: rest) = mc x (toggle b i) rest := by
  unfold mc; rw [proj_cons_eq _ _ h]

/-- Phase 3: cell `x − 1` is gone for good. -/
theorem mc_phase_after (hx : 1 ≤ x) : ∀ (s : List Nat) (b : Board), x < b.length →
    (∀ i ∈ s, i < b.length) → legalE b s = true →
    nth b (x - 1) = false → s.count (x - 1) = 0 →
    mc x b s ≤ (if nth b x then 1 else 0) := by
  intro s
  induction s with
  | nil => intro b _ _ _ _ _; simp [mc, proj]
  | cons i rest ih =>
      intro b hxn hb hl hlo hc
      simp only [legalE_cons, Bool.and_eq_true] at hl
      have hxn' : x < (toggle b i).length := by rw [length_toggle]; exact hxn
      have hb' : ∀ k ∈ rest, k < (toggle b i).length := by
        intro k hk; rw [length_toggle]; exact hb k (List.mem_cons_of_mem _ hk)
      have hi : i < b.length := hb i List.mem_cons_self
      have h1 : i ≠ x - 1 := by
        intro e; subst e; rw [List.count_cons_self] at hc; omega
      have hc' : rest.count (x - 1) = 0 := by rwa [List.count_cons_of_ne h1] at hc
      have hlo' : nth (toggle b i) (x - 1) = false := by rw [nth_toggle_ne b h1]; exact hlo
      by_cases h2 : i = x
      · subst h2
        have hpeb : nth b i = true := by
          have := hl.1
          unfold okE okMove at this
          simpa [show i ≠ 0 by omega, hlo] using this
        have hoff : nth (toggle b i) i = false := by rw [nth_toggle_self b hi, hpeb]; rfl
        have hih := ih (toggle b i) hxn' hb' hl.2 hlo' hc'
        rw [hoff] at hih
        simp only [Bool.false_eq_true, if_false] at hih
        have hpair := mc_pair (x := i) b rest (Or.inr rfl)
        rw [hpeb]; simp only [if_true]; omega
      · rw [mc_other hx b hxn rest hi h1 h2]
        have := ih (toggle b i) hxn' hb' hl.2 hlo' hc'
        rwa [nth_toggle_ne b h2] at this

/-- Phase 2: cell `x − 1` is pebbled and will be removed once. -/
theorem mc_phase_on (hx : 1 ≤ x) : ∀ (s : List Nat) (b : Board), x < b.length →
    (∀ i ∈ s, i < b.length) → legalE b s = true →
    nth b (x - 1) = true → s.count (x - 1) = 1 → mc x b s ≤ 1 := by
  intro s
  induction s with
  | nil => intro b _ _ _ _ _; simp [mc, proj]
  | cons i rest ih =>
      intro b hxn hb hl hon hc
      simp only [legalE_cons, Bool.and_eq_true] at hl
      have hxn' : x < (toggle b i).length := by rw [length_toggle]; exact hxn
      have hb' : ∀ k ∈ rest, k < (toggle b i).length := by
        intro k hk; rw [length_toggle]; exact hb k (List.mem_cons_of_mem _ hk)
      have hi : i < b.length := hb i List.mem_cons_self
      by_cases h1 : i = x - 1
      · subst h1
        have hc' : rest.count (x - 1) = 0 := by rw [List.count_cons_self] at hc; omega
        have hoff : nth (toggle b (x - 1)) (x - 1) = false := by
          rw [nth_toggle_self b hi, hon]; rfl
        have hph := mc_phase_after hx rest (toggle b (x - 1)) hxn' hb' hl.2 hoff hc'
        rw [nth_toggle_ne b (show x - 1 ≠ x by omega)] at hph
        cases hbx : nth b x
        · rw [hbx] at hph
          have := mc_pair (x := x) b rest (Or.inl rfl)
          simp at hph; omega
        · rw [mc_same b rest (mergeB_toggle_low_eq b hx hxn hbx)]
          rw [hbx] at hph; simpa using hph
      · have hc' : rest.count (x - 1) = 1 := by rwa [List.count_cons_of_ne h1] at hc
        have hon' : nth (toggle b i) (x - 1) = true := by rw [nth_toggle_ne b h1]; exact hon
        by_cases h2 : i = x
        · subst h2
          rw [mc_same b rest (mergeB_toggle_high_eq b hx hxn hon)]
          exact ih _ hxn' hb' hl.2 hon' hc'
        · rw [mc_other hx b hxn rest hi h1 h2]
          exact ih _ hxn' hb' hl.2 hon' hc'

/-- Phase 1: cells `x − 1` and `x` empty, `x − 1` toggled twice in all.
The merged cell then changes at most twice. -/
theorem mc_phase_before (hx : 1 ≤ x) : ∀ (s : List Nat) (b : Board), x < b.length →
    (∀ i ∈ s, i < b.length) → legalE b s = true →
    nth b (x - 1) = false → nth b x = false → s.count (x - 1) = 2 → mc x b s ≤ 2 := by
  intro s
  induction s with
  | nil => intro b _ _ _ _ _ _; simp [mc, proj]
  | cons i rest ih =>
      intro b hxn hb hl hlo hhi hc
      simp only [legalE_cons, Bool.and_eq_true] at hl
      have hxn' : x < (toggle b i).length := by rw [length_toggle]; exact hxn
      have hb' : ∀ k ∈ rest, k < (toggle b i).length := by
        intro k hk; rw [length_toggle]; exact hb k (List.mem_cons_of_mem _ hk)
      have hi : i < b.length := hb i List.mem_cons_self
      by_cases h1 : i = x - 1
      · subst h1
        have hc' : rest.count (x - 1) = 1 := by rw [List.count_cons_self] at hc; omega
        have hon : nth (toggle b (x - 1)) (x - 1) = true := by
          rw [nth_toggle_self b hi, hlo]; rfl
        have := mc_phase_on hx rest (toggle b (x - 1)) hxn' hb' hl.2 hon hc'
        have := mc_pair (x := x) b rest (Or.inl rfl)
        omega
      · have hc' : rest.count (x - 1) = 2 := by rwa [List.count_cons_of_ne h1] at hc
        by_cases h2 : i = x
        · subst h2
          exfalso
          have := hl.1
          unfold okE okMove at this
          simp [show i ≠ 0 by omega, hlo, hhi] at this
        · rw [mc_other hx b hxn rest hi h1 h2]
          exact ih _ hxn' hb' hl.2 (by rw [nth_toggle_ne b h1]; exact hlo)
            (by rw [nth_toggle_ne b h2]; exact hhi) hc'

end MergeCount

/-! ## The two contractions -/

theorem contract_drop (n p e : Nat) (s : List Nat) (hn : 2 ≤ n) (h : IsPlay n p e s) :
    ∃ s', IsPlay (n - 1) p e s' ∧ s'.length + s.count 0 = s.length := by
  refine ⟨proj dropB (· - 1) (empty n) s, ?_, ?_⟩
  · apply proj_isPlay dropB (· - 1) n p e s
    · intro b i _ hch
      obtain ⟨h1, hi⟩ := changed_dropB hch
      exact toggle_dropB b h1 hi
    · intro b i _ hok hch
      exact step_dropB b i hok hch
    · intro b _; exact ones_dropB b
    · intro j hj; show j - 1 < n - 1; omega
    · exact dropB_empty n
    · exact dropB_target n hn
    · exact h
  · exact length_proj_dropB s (empty n) (fun i hi => by rw [length_empty]; exact h.bounds i hi)

theorem contract_merge (n p e x : Nat) (s : List Nat) (hx : 1 ≤ x) (hxn : x < n)
    (h : IsPlay n p e s) (hc : s.count (x - 1) = 2) :
    ∃ s', IsPlay (n - 1) p e s' ∧ s'.length + s.count x ≤ s.length := by
  refine ⟨proj (mergeB x) (gM x) (empty n) s, ?_, ?_⟩
  · apply proj_isPlay (mergeB x) (gM x) n p e s
    · intro b i hb hch
      exact toggle_mergeB b hx (by omega) i hch
    · intro b i hb hok hch
      exact step_mergeB b hx (by omega) i hok hch
    · intro b hb; exact ones_mergeB b hx (by omega)
    · intro j hj; unfold gM; split <;> omega
    · exact mergeB_empty n
    · exact mergeB_target n hx hxn
    · exact h
  · have hb : ∀ i ∈ s, i < (empty n).length := fun i hi => by
      rw [length_empty]; exact h.bounds i hi
    have hxn' : x < (empty n).length := by rw [length_empty]; exact hxn
    have hlen := length_proj_mergeB hx s (empty n) hxn' hb
    have hmc := mc_phase_before hx s (empty n) hxn' hb h.legal (nth_empty n _) (nth_empty n _) hc
    unfold mc at hmc
    omega

/-! ## The bound -/

theorem count_parity (n p e : Nat) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s)
    (j : Nat) (hj : j < n) : (s.count j % 2 = 1 ↔ j = n - 1) := by
  have := nth_execB_parity s (empty n) j (by rw [length_empty]; exact hj)
  rw [h.final, nth_target n j hn, nth_empty] at this
  have h' : decide (j = n - 1) = decide (s.count j % 2 = 1) := by simpa using this
  simpa using h'.symm

theorem exists_min (P : Nat → Prop) [DecidablePred P] :
    ∀ m, (∃ j, j < m ∧ P j) → ∃ j, P j ∧ ∀ i, i < j → ¬ P i := by
  intro m
  induction m with
  | zero => intro ⟨j, hj, _⟩; omega
  | succ m ih =>
      intro ⟨j, hj, hp⟩
      by_cases hlow : ∃ j, j < m ∧ P j
      · exact ih hlow
      · refine ⟨m, ?_, fun i hi hpi => hlow ⟨i, hi, hpi⟩⟩
        by_cases hjm : j = m
        · exact hjm ▸ hp
        · exact absurd ⟨j, by omega, hp⟩ hlow

/-- Theorem A, read as a cell bound: a plan placing every cell once has
`n ≤ (p−1)(e+1) + 1`. -/
theorem le_of_tight (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s)
    (hlen : s.length = 2 * n - 1) : n ≤ (p - 1) * (e + 1) + 1 := by
  have he := theoremA_lower n p e hp hn s h hlen
  unfold estar at he
  have hq : (n - 1 + (p - 1) - 1) / (p - 1) < e + 2 := by omega
  have h2 := (Nat.div_lt_iff_lt_mul (show 0 < p - 1 by omega)).mp hq
  have e1 : (e + 2) * (p - 1) = (p - 1) * (e + 1) + (p - 1) := by
    rw [Nat.mul_comm, show e + 2 = (e + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
  rw [e1] at h2
  omega

/-- **Contraction lower bound.**  For `p ≥ 2`, every clean plan on `n ≥ 1`
cells with peak `p` and at most `e` erasures satisfies
`4n ≤ |s| + 1 + 2A` with `A = (p−1)(e+1) + 1`, i.e.
`|s| ≥ 2n − 1 + 2(n − A)`. -/
theorem contraction_bound (p e : Nat) (hp : 2 ≤ p) :
    ∀ n s, 1 ≤ n → IsPlay n p e s → 4 * n ≤ s.length + 1 + 2 * ((p - 1) * (e + 1) + 1) := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ k ih =>
      intro s _ h
      have hfl := floor_length (k + 1) p e (by omega) s h
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; omega
      have hn : 2 ≤ k + 1 := by omega
      by_cases htight : s.length = 2 * (k + 1) - 1
      · have := le_of_tight (k + 1) p e hp (by omega) s h htight
        omega
      -- some cell is toggled more often than forced
      have hforced := forced_le_count (k + 1) (by omega) s h.bounds h.legal h.final
      have hex : ∃ j, j < k + 1 ∧ (j < k + 1 ∧ forced (k + 1) j < s.count j) := by
        apply Classical.byContradiction
        intro hno
        have hle : ∀ j, j < k + 1 → s.count j ≤ forced (k + 1) j := by
          intro j hj
          apply Classical.byContradiction
          intro hlt
          exact hno ⟨j, hj, hj, by omega⟩
        have := rsum_le (fun j => s.count j) (forced (k + 1)) (k + 1) hle
        rw [rsum_count (k + 1) s h.bounds, rsum_forced (k + 1) (by omega)] at this
        omega
      obtain ⟨x, ⟨hxn, hxc⟩, hmin⟩ := exists_min _ (k + 1) hex
      have hpar := count_parity (k + 1) p e (by omega) s h
      have hoddS := length_odd (k + 1) p e (by omega) s h
      by_cases hx0 : x = 0
      · subst hx0
        obtain ⟨s', hs', hl⟩ := contract_drop (k + 1) p e s hn h
        have hf : forced (k + 1) 0 = 2 := by simp [forced]; omega
        have hp0 := hpar 0 (by omega)
        have : 4 ≤ s.count 0 := by
          have : ¬ (s.count 0 % 2 = 1) := fun e => by have := hp0.mp e; omega
          omega
        have := ih s' (by omega) (by simpa using hs')
        omega
      · have hlow : s.count (x - 1) = 2 := by
          have h1 := hforced (x - 1) (by omega)
          have h2 : ¬ (x - 1 < k + 1 ∧ forced (k + 1) (x - 1) < s.count (x - 1)) :=
            hmin (x - 1) (by omega)
          have hf : forced (k + 1) (x - 1) = 2 := by simp [forced]; omega
          omega
        obtain ⟨s', hs', hl⟩ := contract_merge (k + 1) p e x s (by omega) hxn h hlow
        have hs'' : IsPlay k p e s' := by simpa using hs'
        have ih' := ih s' (by omega) hs''
        have hoddS' := length_odd k p e (by omega) s' hs''
        have hpx := hpar x hxn
        by_cases hlast : x = k
        · have hf : forced (k + 1) x = 1 := by simp [forced]; omega
          have : 3 ≤ s.count x := by
            have : s.count x % 2 = 1 := hpx.mpr (by omega)
            omega
          omega
        · have hf : forced (k + 1) x = 2 := by simp [forced]; omega
          have : 4 ≤ s.count x := by
            have : ¬ (s.count x % 2 = 1) := fun e => by have := hpx.mp e; omega
            omega
          omega

/-- The bound in `M*` form: `|s| ≥ 2n − 1 + 2·max(0, n − A)`. -/
theorem length_ge (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (s : List Nat) (h : IsPlay n p e s) :
    2 * n - 1 + 2 * (n - ((p - 1) * (e + 1) + 1)) ≤ s.length := by
  have h1 := contraction_bound p e hp n s hn h
  have h2 := floor_length n p e hn s h
  omega

/-- Near the saturation threshold: at `n = (p−1)(e+1) + 1 + j` every clean plan
has at least `2n − 1 + 2j` moves. -/
theorem near_band_lower (p e j : Nat) (hp : 2 ≤ p) (s : List Nat)
    (h : IsPlay ((p - 1) * (e + 1) + 1 + j) p e s) :
    2 * ((p - 1) * (e + 1) + 1 + j) - 1 + 2 * j ≤ s.length := by
  have := length_ge _ p e hp (by omega) s h
  have e1 : (p - 1) * (e + 1) + 1 + j - ((p - 1) * (e + 1) + 1) = j := by omega
  rw [e1] at this
  exact this

/-- `p = 4`: `M*(n, 4, e) ≥ 4n − 6e − 9` for `n ≥ 3e + 4`. -/
theorem p4_lower (n e : Nat) (hn : 3 * e + 4 ≤ n) (s : List Nat) (h : IsPlay n 4 e s) :
    4 * n - 6 * e - 9 ≤ s.length := by
  have := length_ge n 4 e (by omega) (by omega) s h
  have e1 : (4 - 1) * (e + 1) + 1 = 3 * e + 4 := by omega
  rw [e1] at this
  omega

/-- Consistency with `first_drop` (the case `j = 1`): the lower bound is attained. -/
theorem first_drop_tight (p e : Nat) (hp : 3 ≤ p) :
    MstarIs ((p - 1) * (e + 1) + 2) p e (2 * ((p - 1) * (e + 1) + 2) - 1 + 2 * 1) := by
  have h := (first_drop p e hp).1
  have e1 : 2 * ((p - 1) * (e + 1) + 2) - 1 + 2 * 1 = 2 * ((p - 1) * (e + 1) + 2) + 1 := by omega
  rw [e1]
  exact h

end Contraction
end ErasurePebbling
