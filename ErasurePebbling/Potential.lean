import ErasurePebbling.Sweep

/-!
# The saturation potential (Theorem A, lower bound, part 1)

RC-02 proves the lower bound of Theorem A by a counting argument on the
permutation `τ` of removal times: in a `2n − 1`-move plan every cell is
placed once and removed at most once, an irreversible removal of cell
`i` is exactly an *ascent* `τ(i) > τ(i−1)`, and each descending run of
`τ` has at most `p − 1` cells.

The formalisation replaces the permutation by a **potential on boards**
that is non-decreasing along a tight play except that it may drop by
one at each irreversible removal.  For a board `b` of length `n` with
peak `p` let

* `dCount n b` = number of pebbled cells whose lower neighbour is empty
  (cells whose removal would be irreversible; cell `0` never counts);
* `fb n b`     = the largest *rising edge* (a pebbled cell whose lower
  neighbour is empty, or cell `0` if pebbled), `0` if there is none:
  the bottom of the run of pebbles that contains the highest pebble;
* `pot n p b`  = `⌈(n − 1 − fb n b)/(p − 1)⌉ + dCount n b − 1`.

`pot` of the empty board is `e*(n, p)`, `pot` of the target `{n}` is
`0`, a placement above all pebbles leaves `pot` unchanged
(`pot_place`), and a removal that is not the highest pebble lowers
`pot` by at most the erasure indicator (`pot_remove`).  The lower bound
follows in `ErasurePebbling.Saturation`.

The reading: the frontier run `[fb, top]` has at most `p` pebbles; the
cells above `fb` (there are `n − 1 − fb`) have to be covered by future
descending runs of at most `p − 1` cells, each of which but the one
containing `fb` costs an erasure, and each pebbled cell with an empty
lower neighbour costs one more.
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-! ## Definitions -/

/-- Number of cells `k < m` whose pebble can only be removed irreversibly. -/
def dCount : Nat → Board → Nat
  | 0, _ => 0
  | m + 1, b => dCount m b + (if isErase b m then 1 else 0)

/-- A rising edge: pebbled, and the lower neighbour empty (cell `0`: pebbled). -/
def edge (b : Board) (k : Nat) : Bool := nth b k && (k == 0 || !nth b (k - 1))

/-- The largest rising edge below `m` (`0` if none). -/
def fb : Nat → Board → Nat
  | 0, _ => 0
  | m + 1, b => if edge b m then m else fb m b

/-- The saturation potential. -/
def pot (n p : Nat) (b : Board) : Nat :=
  (n - 1 - fb n b + (p - 1) - 1) / (p - 1) + dCount n b - 1

@[simp] theorem dCount_zero (b : Board) : dCount 0 b = 0 := rfl
@[simp] theorem dCount_succ (m : Nat) (b : Board) :
    dCount (m + 1) b = dCount m b + (if isErase b m then 1 else 0) := rfl
@[simp] theorem fb_zero (b : Board) : fb 0 b = 0 := rfl
@[simp] theorem fb_succ (m : Nat) (b : Board) : fb (m + 1) b = if edge b m then m else fb m b := rfl

/-! ## Toggle lemmas on `nth` -/

theorem nth_toggle_self (b : Board) {i : Nat} (hi : i < b.length) :
    nth (toggle b i) i = !nth b i := nth_set_eq b i _ hi

theorem nth_toggle_ne (b : Board) {i j : Nat} (h : i ≠ j) :
    nth (toggle b i) j = nth b j := nth_set_ne b i j _ h

theorem length_toggle (b : Board) (i : Nat) : (toggle b i).length = b.length := by
  simp [toggle]

/-- Cells other than `i`, `i+1` do not change their erasability. -/
theorem isErase_toggle_far (b : Board) {i j : Nat} (h1 : j ≠ i) (h2 : j ≠ i + 1) :
    isErase (toggle b i) j = isErase b j := by
  unfold isErase okMove
  rw [nth_toggle_ne b h1.symm, nth_toggle_ne b (by omega)]

theorem edge_toggle_far (b : Board) {i j : Nat} (h1 : j ≠ i) (h2 : j ≠ i + 1) :
    edge (toggle b i) j = edge b j := by
  unfold edge
  rw [nth_toggle_ne b h1.symm, nth_toggle_ne b (by omega)]

/-! ## Structural lemmas on `dCount` and `fb` -/

theorem dCount_agree (b b' : Board) (m : Nat) :
    ∀ k, m ≤ k → (∀ j, m ≤ j → j < k → isErase b j = isErase b' j) →
      dCount k b + dCount m b' = dCount k b' + dCount m b := by
  intro k
  induction k with
  | zero => intro hm _; have : m = 0 := by omega
            subst this; simp
  | succ k ih =>
      intro hm h
      rcases Nat.lt_or_ge k m with hk | hk
      · have : m = k + 1 := by omega
        subst this; omega
      · have := ih hk (fun j hj1 hj2 => h j hj1 (by omega))
        rw [dCount_succ, dCount_succ, h k hk (by omega)]
        omega

theorem dCount_congr (b b' : Board) : ∀ k, (∀ j, j < k → isErase b j = isErase b' j) →
    dCount k b = dCount k b' := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [dCount_succ, dCount_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

theorem fb_lt (b : Board) : ∀ m, 0 < m → fb m b < m := by
  intro m hm
  cases m with
  | zero => omega
  | succ m =>
      rw [fb_succ]
      split
      · omega
      · cases m with
        | zero => simp
        | succ m => have := fb_lt b (m + 1) (by omega); omega

theorem fb_le (b : Board) (m : Nat) : fb m b ≤ m := by
  cases m with
  | zero => simp
  | succ m => exact Nat.le_of_lt (fb_lt b (m + 1) (by omega))

/-- Above `fb m b` (and below `m`) there is no rising edge. -/
theorem fb_max (b : Board) : ∀ m j, fb m b < j → j < m → edge b j = false := by
  intro m
  induction m with
  | zero => intro j _ h; omega
  | succ m ih =>
      intro j h1 h2
      rw [fb_succ] at h1
      split at h1
      · omega
      · rcases Nat.lt_or_ge j m with hj | hj
        · exact ih j h1 hj
        · have : j = m := by omega
          subst this; simpa using ‹¬ edge b j = true›

/-- If some edge exists below `m`, `fb m b` is an edge. -/
theorem fb_edge (b : Board) : ∀ m, (∃ j, j < m ∧ edge b j = true) → edge b (fb m b) = true := by
  intro m
  induction m with
  | zero => intro ⟨j, hj, _⟩; omega
  | succ m ih =>
      intro ⟨j, hj, he⟩
      rw [fb_succ]
      split
      · assumption
      · apply ih
        refine ⟨j, ?_, he⟩
        rcases Nat.lt_or_ge j m with h | h
        · exact h
        · have : j = m := by omega
          subst this; simp_all

theorem fb_of_no_edge (b : Board) : ∀ m, (∀ j, j < m → edge b j = false) → fb m b = 0 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      rw [fb_succ, if_neg (by simp [h m (by omega)])]
      exact ih (fun j hj => h j (by omega))

/-- Two boards whose edges agree on `[m, k)` either have the same `fb k`, or
both `fb k` are determined below `m`. -/
theorem fb_agree (b b' : Board) (m : Nat) :
    ∀ d, (∀ j, m ≤ j → j < m + d → edge b j = edge b' j) →
      fb (m + d) b = fb (m + d) b' ∨ (fb (m + d) b = fb m b ∧ fb (m + d) b' = fb m b') := by
  intro d
  induction d with
  | zero => intro _; right; exact ⟨rfl, rfl⟩
  | succ d ih =>
      intro h
      have e : m + (d + 1) = (m + d) + 1 := rfl
      rw [e, fb_succ, fb_succ, h (m + d) (by omega) (by omega)]
      split
      · left; rfl
      · exact ih (fun j hj1 hj2 => h j hj1 (by omega))

theorem fb_congr (b b' : Board) (m : Nat) (h : ∀ j, j < m → edge b j = edge b' j) :
    fb m b = fb m b' := by
  have := fb_agree b b' 0 m (fun j _ hj => h j (by omega))
  simp only [Nat.zero_add, fb_zero] at this
  rcases this with h | ⟨h1, h2⟩
  · exact h
  · rw [h1, h2]

/-- Below `fb`... : cells `j` with `fb n b < j`, `j < n` that are pebbled have
a pebbled lower neighbour (no edge above `fb`). -/
theorem pebbled_pred_of_gt_fb (b : Board) (n j : Nat) (h1 : fb n b < j) (h2 : j < n)
    (hj : nth b j = true) : nth b (j - 1) = true := by
  have he := fb_max b n j h1 h2
  unfold edge at he
  rw [hj] at he
  simp at he
  exact he.2

/-- Contiguity: from a pebbled cell `t` down to `fb n b` everything is pebbled. -/
theorem run_below (b : Board) (n t : Nat) (ht : t < n) (hpeb : nth b t = true) (hfb : fb n b ≤ t) :
    ∀ d, d ≤ t - fb n b → nth b (t - d) = true := by
  intro d
  induction d with
  | zero => simpa using hpeb
  | succ d ih =>
      intro hd
      have h := ih (by omega)
      have := pebbled_pred_of_gt_fb b n (t - d) (by omega) (by omega) h
      have e : t - (d + 1) = t - d - 1 := by omega
      rw [e]; exact this

/-! ## Boards as `mk` -/

theorem mk_nth (b : Board) : mk b.length (nth b) = b := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_mk]
  split
  · simp [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ‹_›]
  · rw [List.getElem?_eq_none]; omega

/-- A pebbled run `[u, v]` forces at least `v + 1 − u` pebbles. -/
theorem ones_ge_run (b : Board) (u v : Nat) (hv : v < b.length)
    (h : ∀ j, u ≤ j → j ≤ v → nth b j = true) : v + 1 - u ≤ ones b := by
  have hb : ones b = ones (mk b.length (nth b)) := by rw [mk_nth]
  rw [hb]
  have := ones_mk_le_of_imp (n := b.length)
    (f := fun i => decide (u ≤ i ∧ i < u + (v + 1 - u))) (g := nth b)
    (fun i _ hi => by
      simp at hi
      exact h i hi.1 (by omega))
  rw [ones_run] at this
  omega

/-! ## Values of the potential at the two ends -/

theorem isErase_empty (n j : Nat) : isErase (empty n) j = false := by
  simp [isErase, nth_empty]

theorem edge_empty (n j : Nat) : edge (empty n) j = false := by
  simp [edge, nth_empty]

theorem dCount_empty (n : Nat) : ∀ m, dCount m (empty n) = 0 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp [ih, isErase_empty]

theorem pot_empty (n p : Nat) : pot n p (empty n) = estar n p := by
  unfold pot estar
  rw [dCount_empty, fb_of_no_edge _ _ (fun j _ => edge_empty n j)]
  simp

theorem nth_target (n j : Nat) (hn : 1 ≤ n) : nth (target n) j = decide (j = n - 1) := by
  rw [target_eq_mk n hn, nth_mk]
  split
  · rfl
  · simp; omega

theorem edge_target (n j : Nat) (hn : 1 ≤ n) : edge (target n) j = decide (j = n - 1) := by
  unfold edge
  rw [nth_target n j hn, nth_target n (j - 1) hn]
  by_cases h : j = n - 1
  · subst h
    by_cases h1 : n - 1 = 0
    · simp [h1]
    · have h2 : ¬ (n - 1 - 1 = n - 1) := by omega
      simp [h1, h2]
  · simp [h]

theorem fb_target (n : Nat) (hn : 1 ≤ n) : fb n (target n) = n - 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [fb_succ, edge_target _ _ hn]
      simp

theorem isErase_target_low (n k : Nat) (hn : 1 ≤ n) (hk : k < n - 1) :
    isErase (target n) k = false := by
  simp [isErase, nth_target n k hn]
  omega

theorem dCount_target_low (n : Nat) (hn : 1 ≤ n) : ∀ m, m ≤ n - 1 → dCount m (target n) = 0 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      rw [dCount_succ, ih (by omega), isErase_target_low n m hn (by omega)]
      rfl

theorem dCount_target (n : Nat) (hn : 1 ≤ n) : dCount n (target n) ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [dCount_succ, dCount_target_low (n + 1) hn n (by omega)]
      split <;> omega

theorem pot_target (n p : Nat) (hn : 1 ≤ n) (hp : 2 ≤ p) : pot n p (target n) = 0 := by
  unfold pot
  rw [fb_target n hn]
  have hd := dCount_target n hn
  have h0 : (n - 1 - (n - 1) + (p - 1) - 1) / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [h0]
  omega

/-! ## Characterising `fb` -/

theorem fb_eq_of (b : Board) (n u : Nat) (hu : u < n) (hedge : edge b u = true)
    (hmax : ∀ j, u < j → j < n → edge b j = false) : fb n b = u := by
  have h1 := fb_edge b n ⟨u, hu, hedge⟩
  rcases Nat.lt_trichotomy (fb n b) u with h | h | h
  · have := fb_max b n u h hu
    rw [this] at hedge; cases hedge
  · exact h
  · have := hmax (fb n b) h (fb_lt b n (by omega))
    rw [this] at h1; cases h1

/-! ## The two step lemmas -/

/-- Placing a pebble above all pebbles leaves the potential unchanged. -/
theorem pot_place (n p : Nat) (b : Board) (hb : b.length = n) (i : Nat) (hi : i < n)
    (hempty : nth b i = false) (hok : okMove b i = true)
    (habove : ∀ j, i ≤ j → j < n → nth b j = false) :
    pot n p (toggle b i) = pot n p b := by
  have hib : i < b.length := by omega
  have hself : nth (toggle b i) i = true := by rw [nth_toggle_self b hib, hempty]; rfl
  -- erasability is unchanged everywhere
  have hd : dCount n (toggle b i) = dCount n b := by
    apply dCount_congr
    intro j hj
    by_cases h1 : j = i
    · subst h1
      have : isErase b j = false := by simp [isErase, hempty]
      rw [this]
      unfold isErase okMove
      rw [hself]
      by_cases h0 : j = 0
      · subst h0; simp
      · have h0' : (j == 0) = false := by simpa using h0
        rw [nth_toggle_ne b (by omega)]
        unfold okMove at hok
        rw [h0'] at hok
        simp at hok
        simp [hok, h0']
    · by_cases h2 : j = i + 1
      · subst h2
        have e1 : isErase b (i + 1) = false := by
          simp [isErase, habove (i + 1) (by omega) hj]
        have e2 : isErase (toggle b i) (i + 1) = false := by
          simp [isErase, nth_toggle_ne b (show i ≠ i + 1 by omega), habove (i + 1) (by omega) hj]
        rw [e1, e2]
      · exact isErase_toggle_far b h1 h2
  -- the frontier bottom is unchanged
  have hf : fb n (toggle b i) = fb n b := by
    by_cases h0 : i = 0
    · subst h0
      have hnone : ∀ j, j < n → edge b j = false := by
        intro j hj; simp [edge, habove j (Nat.zero_le _) hj]
      rw [fb_of_no_edge b n hnone]
      apply fb_eq_of _ _ _ hi
      · simp [edge, hself]
      · intro j hj1 hj2
        by_cases h1 : j = 1
        · subst h1
          simp [edge, nth_toggle_ne b (show 0 ≠ 1 by omega), habove 1 (by omega) hj2]
        · rw [edge_toggle_far b (by omega) (by omega)]
          exact hnone j hj2
    · apply fb_congr
      intro j hj
      by_cases h1 : j = i
      · subst h1
        have hpred : nth b (j - 1) = true := by
          unfold okMove at hok
          have h0' : (j == 0) = false := by simpa using h0
          rw [h0'] at hok; simpa using hok
        have e1 : edge b j = false := by simp [edge, hempty]
        have e2 : edge (toggle b j) j = false := by
          simp [edge, hself, nth_toggle_ne b (show j ≠ j - 1 by omega), hpred, h0]
        rw [e1, e2]
      · by_cases h2 : j = i + 1
        · subst h2
          have e1 : edge b (i + 1) = false := by simp [edge, habove (i + 1) (by omega) hj]
          have e2 : edge (toggle b i) (i + 1) = false := by
            simp [edge, nth_toggle_ne b (show i ≠ i + 1 by omega), habove (i + 1) (by omega) hj]
          rw [e1, e2]
        · exact edge_toggle_far b h1 h2
  unfold pot
  rw [hd, hf]

/-- Removing a pebble that is not the highest one lowers the potential by at
most the erasure indicator. -/
theorem pot_remove (n p : Nat) (hp : 2 ≤ p) (b : Board) (hb : b.length = n) (i : Nat) (hi : i < n)
    (hpeb : nth b i = true) (hnot_top : ∃ j', i < j' ∧ j' < n ∧ nth b j' = true)
    (hones : ones b ≤ p) :
    pot n p b ≤ (if isErase b i then 1 else 0) + pot n p (toggle b i) := by
  obtain ⟨j', hij', hj'n, hj'peb⟩ := hnot_top
  have hib : i < b.length := by omega
  have hi1 : i + 1 < n := by omega
  have hself : nth (toggle b i) i = false := by rw [nth_toggle_self b hib, hpeb]; rfl
  have hnext : nth (toggle b i) (i + 1) = nth b (i + 1) := nth_toggle_ne b (by omega)
  -- (F1) erasability: dCount n b + [b(i+1)] = dCount n b' + er
  have hF1 : dCount n b + (if nth b (i + 1) then 1 else 0) =
      dCount n (toggle b i) + (if isErase b i then 1 else 0) := by
    have hag := dCount_agree b (toggle b i) (i + 2) n (by omega)
      (fun j hj1 hj2 => (isErase_toggle_far b (by omega) (by omega)).symm)
    have hlow : dCount i b = dCount i (toggle b i) :=
      dCount_congr b _ i (fun j hj => (isErase_toggle_far b (by omega) (by omega)).symm)
    have e1 : dCount (i + 2) b = dCount i b + (if isErase b i then 1 else 0)
        + (if isErase b (i + 1) then 1 else 0) := rfl
    have e2 : dCount (i + 2) (toggle b i) = dCount i (toggle b i)
        + (if isErase (toggle b i) i then 1 else 0)
        + (if isErase (toggle b i) (i + 1) then 1 else 0) := rfl
    have v1 : isErase b (i + 1) = false := by
      simp [isErase, okMove, hpeb]
    have v2 : isErase (toggle b i) i = false := by simp [isErase, hself]
    have v3 : isErase (toggle b i) (i + 1) = nth b (i + 1) := by
      simp [isErase, okMove, hnext, hself]
    rw [e1, e2, v1, v2, v3, hlow] at hag
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hag
    omega
  -- edges of b and b' agree above i + 1
  have hfar : ∀ j, i + 2 ≤ j → j < n → edge (toggle b i) j = edge b j :=
    fun j hj1 _ => edge_toggle_far b (by omega) (by omega)
  have hu_le := fb_le b n
  by_cases hF : fb n b ≤ i ∧ nth b (i + 1) = true
  · -- frontier case: the run splits at i, the new frontier bottom is i + 1
    obtain ⟨hu, hnxt⟩ := hF
    have hrun : ∀ j, fb n b ≤ j → j ≤ i + 1 → nth b j = true := by
      intro j hj1 hj2
      have := run_below b n (i + 1) hi1 hnxt (by omega) (i + 1 - j) (by omega)
      have e : i + 1 - (i + 1 - j) = j := by omega
      rw [e] at this; exact this
    have hcnt : i + 1 + 1 - fb n b ≤ ones b := ones_ge_run b (fb n b) (i + 1) (by omega) hrun
    have hfb' : fb n (toggle b i) = i + 1 := by
      apply fb_eq_of _ _ _ hi1
      · simp [edge, hnext, hnxt, hself]
      · intro j hj1 hj2
        rw [hfar j (by omega) hj2]
        exact fb_max b n j (by omega) hj2
    unfold pot
    rw [hfb']
    -- arithmetic
    have hg : n - 1 - fb n b + (p - 1) - 1 ≤ (n - 1 - (i + 1) + (p - 1) - 1) + (p - 1) := by omega
    have hdiv := Nat.div_le_div_right (c := p - 1) hg
    rw [Nat.add_div_right _ (by omega)] at hdiv
    rw [if_pos hnxt] at hF1
    generalize (n - 1 - fb n b + (p - 1) - 1) / (p - 1) = C1 at hdiv ⊢
    generalize (n - 1 - (i + 1) + (p - 1) - 1) / (p - 1) = C at hdiv ⊢
    generalize (if isErase b i = true then 1 else 0 : Nat) = er at hF1 ⊢
    omega
  · -- i lies below the frontier run (the case `fb ≤ i` is impossible)
    have hlt : i < fb n b := by
      rcases Nat.lt_or_ge i (fb n b) with h | hu
      · exact h
      · exfalso
        apply hF
        refine ⟨hu, ?_⟩
        have := run_below b n j' hj'n hj'peb (by omega) (j' - (i + 1)) (by omega)
        have e : j' - (j' - (i + 1)) = i + 1 := by omega
        rw [e] at this; exact this
    have hex : ∃ j, j < n ∧ edge b j = true := by
      apply Classical.byContradiction
      intro hno
      have : ∀ j, j < n → edge b j = false := by
        intro j hj
        cases h : edge b j
        · rfl
        · exact absurd ⟨j, hj, h⟩ hno
      have := fb_of_no_edge b n this
      omega
    have hedge : edge b (fb n b) = true := fb_edge b n hex
    have hne : fb n b ≠ i + 1 := by
      intro h
      rw [h] at hedge
      simp [edge, hpeb] at hedge
    have hu2 : i + 2 ≤ fb n b := by omega
    have hfb' : fb n (toggle b i) = fb n b := by
      apply fb_eq_of _ _ _ (fb_lt b n (by omega))
      · rw [hfar _ hu2 (fb_lt b n (by omega))]; exact hedge
      · intro j hj1 hj2
        rw [hfar j (by omega) hj2]
        exact fb_max b n j hj1 hj2
    unfold pot
    rw [hfb']
    generalize (n - 1 - fb n b + (p - 1) - 1) / (p - 1) = C1
    generalize (if isErase b i = true then 1 else 0 : Nat) = er at hF1 ⊢
    generalize (if nth b (i + 1) = true then 1 else 0 : Nat) = t at hF1 ⊢
    omega

end ErasurePebbling
