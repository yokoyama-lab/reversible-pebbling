import ErasurePebbling.Contraction

/-!
# The contraction bound is attained up to the triangular frontier

Write `A = (p−1)(e+1)+1` and `T(p) = p(p−1)/2 + 1` (`tri`, with
`T(p+1) = T(p) + p`).  `Contraction.length_ge` gives
`|s| ≥ 2n − 1 + 2·max(0, n − A)` for every clean plan.  Here the matching
plans are built for every `p ≥ 3`, `e` and `n ≤ T(p) + e·T(p−1)`:

* `window_seg`: a play on a short chain, shifted to the cells
  `[x, x+m)` of a longer one whose cell `x−1` carries a stone (or `x = 0`),
  is still a play; it keeps its legality and its erasures, and its peak
  grows by the stones held outside the window;
* `Seg.reverse`: a play without erasure may be run backwards;
* `tri_spec`: for `p ≥ 2` and `p ≤ n ≤ T(p)` there is a plan with peak
  `p`, no erasure and `4n − 2p − 1` moves.  Split `n = a + b` with
  `1 ≤ a ≤ p−1` and `p−1 ≤ b ≤ T(p−1)`; sweep to a stone on cell `a−1`,
  run the `(p−1)`-plan on the next `b` cells while that stone is held,
  then undo the first sweep under the final stone;
* `blocks_spec`: `e` further blocks of length `b ∈ [p−1, T(p−1)]`, each
  run on a held stone that is then erased (one irreversible removal);
* `mstar_exact`: `M*(n, p, e) = 2n − 1 + 2·max(0, n − A)` for
  `1 ≤ n ≤ T(p) + e·T(p−1)`; `near_band_exact` (`n = A + j`,
  `j ≤ p − 2`) and `mstar_p4_interior` (`M*(n,4,e) = 4n − 6e − 9` for
  `3e+4 ≤ n ≤ 4e+7`) are special cases.

(Paper proof: the 2026-11-11 note `消去ペブリング_三角数厳密領域`;
this file is its machine-checked version.)
-/

namespace ErasurePebbling
namespace Triangular

open RevPebbling.PebblingFoundations

/-! ## Boards -/

theorem board_ext {b1 b2 : Board} (hl : b1.length = b2.length)
    (h : ∀ j, j < b1.length → nth b1 j = nth b2 j) : b1 = b2 := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  simpa [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] using this

theorem ones_toggle_eq (b : Board) {i : Nat} (hi : i < b.length) :
    ones (toggle b i) + (if nth b i then 1 else 0) = ones b + (if nth b i then 0 else 1) := by
  cases h : nth b i
  · have := UpperBound.ones_toggle_of_false h hi; simp; omega
  · have := UpperBound.ones_toggle_of_true h hi; simp; omega

/-! ## Running a play inside a window -/

/-- `B` shows the board `c` on the cells `[x, x + c.length)`, and the cell
below the window is pebbled (or the window starts at the entrance). -/
structure Win (x : Nat) (c B : Board) : Prop where
  len : x + c.length ≤ B.length
  agree : ∀ i, i < c.length → nth B (x + i) = nth c i
  anchor : x = 0 ∨ nth B (x - 1) = true

theorem win_step {x : Nat} {c B : Board} (w : Win x c B) {i : Nat} (hi : i < c.length) :
    okMove B (x + i) = okMove c i ∧ nth B (x + i) = nth c i ∧
    Win x (toggle c i) (toggle B (x + i)) ∧
    ones (toggle B (x + i)) + ones c = ones B + ones (toggle c i) ∧
    ∀ j, (j < x ∨ x + c.length ≤ j) → nth (toggle B (x + i)) j = nth B j := by
  have hB : x + i < B.length := by have := w.len; omega
  have hn := w.agree i hi
  refine ⟨?_, hn, ?_, ?_, ?_⟩
  · simp only [okMove]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rcases w.anchor with hx | hx
      · subst hx; simp
      · simp [hx]
    · have e : x + i - 1 = x + (i - 1) := by omega
      rw [e, w.agree (i - 1) (by omega)]
      have h1 : (x + i == 0) = false := by simp; omega
      have h2 : (i == 0) = false := by simp; omega
      rw [h1, h2]
  · refine ⟨?_, ?_, ?_⟩
    · rw [length_toggle, length_toggle]; exact w.len
    · intro j hj
      rw [length_toggle] at hj
      rw [Contraction.nth_toggle_eq B hB, Contraction.nth_toggle_eq c hi]
      by_cases hji : j = i
      · subst hji; simp [hn]
      · rw [if_neg (by omega), if_neg hji]; exact w.agree j hj
    · rcases w.anchor with hx | hx
      · exact Or.inl hx
      · by_cases hx0 : x = 0
        · exact Or.inl hx0
        · right; rw [nth_toggle_ne B (show x + i ≠ x - 1 by omega)]; exact hx
  · have h1 := ones_toggle_eq B hB
    have h2 := ones_toggle_eq c hi
    rw [hn] at h1
    cases hc : nth c i <;> simp [hc] at h1 h2 <;> omega
  · intro j hj
    exact nth_toggle_ne B (by omega)

theorem execB_cons (b : Board) (i : Nat) (s : List Nat) :
    execB b (i :: s) = execB (toggle b i) s := rfl

theorem win_run (x : Nat) : ∀ (t : List Nat) (c B : Board) (K : Nat),
    (∀ i ∈ t, i < c.length) → Win x c B → ones B ≤ K + ones c →
    legalE B (t.map (x + ·)) = legalE c t ∧
    erasures B (t.map (x + ·)) = erasures c t ∧
    maxOnes B (t.map (x + ·)) ≤ K + maxOnes c t ∧
    Win x (execB c t) (execB B (t.map (x + ·))) ∧
    (∀ j, (j < x ∨ x + c.length ≤ j) → nth (execB B (t.map (x + ·))) j = nth B j) := by
  intro t
  induction t with
  | nil =>
    intro c B K _ w hK
    exact ⟨rfl, rfl, by simpa [maxOnes] using hK, w, fun j _ => rfl⟩
  | cons i rest ih =>
    intro c B K hb w hK
    have hi := hb i (by simp)
    obtain ⟨hok, hn, w', hones, hout⟩ := win_step w hi
    have hb' : ∀ j ∈ rest, j < (toggle c i).length := by
      intro j hj; rw [length_toggle]; exact hb j (by simp [hj])
    obtain ⟨r1, r2, r3, r4, r5⟩ := ih (toggle c i) (toggle B (x + i)) K hb' w' (by omega)
    simp only [List.map_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [legalE_cons, okE, hok, hn, r1]
    · rw [erasures_cons, erasures_cons, r2]
      have : isErase B (x + i) = isErase c i := by simp only [isErase, hok, hn]
      rw [this]
    · simp only [maxOnes]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans hK (Nat.add_le_add_left (Nat.le_max_left _ _) _),
         Nat.le_trans r3 (Nat.add_le_add_left (Nat.le_max_right _ _) _)⟩
    · rw [execB_cons, execB_cons]; exact r4
    · intro j hj
      rw [execB_cons, r5 j (by rw [length_toggle]; exact hj), hout j hj]

/-- **Window embedding.**  A play on `m` cells, shifted by `x` into a board
that agrees with its start on `[x, x+m)` and has a stone on `x − 1`. -/
theorem window_seg {m N x q k l K : Nat} {c c' B : Board} {t : List Nat}
    (h : Seg m c c' q k l t) (hc : c.length = m) (hB : B.length = N) (hx : x + m ≤ N)
    (hw : ∀ i, i < m → nth B (x + i) = nth c i) (ha : x = 0 ∨ nth B (x - 1) = true)
    (hK : ones B ≤ K + ones c) :
    Seg N B (mk N (fun j => if x ≤ j ∧ j < x + m then nth c' (j - x) else nth B j))
      (K + q) k l (t.map (x + ·)) := by
  have w : Win x c B := ⟨by omega, by rw [hc]; exact hw, ha⟩
  obtain ⟨r1, r2, r3, r4, r5⟩ := win_run x t c B K (by rw [hc]; exact h.bounds) w hK
  rw [h.exec] at r4
  have hc' : c'.length = m := by rw [← h.exec, length_execB, hc]
  refine ⟨by rw [r1]; exact h.legal, ?_, Nat.le_trans r3 (Nat.add_le_add_left h.peak K),
    by rw [r2]; exact h.eras, by simp [h.len], ?_⟩
  · apply board_ext
    · rw [length_execB, length_mk, hB]
    · intro j hj
      rw [length_execB] at hj
      rw [nth_mk_of_lt (by omega)]
      split
      · rename_i hj'
        have := r4.agree (j - x) (by rw [hc']; omega)
        rwa [Nat.add_sub_cancel' hj'.1] at this
      · exact r5 j (by rw [hc]; omega)
  · intro i hi
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hi
    have := h.bounds a ha'
    omega

/-! ## Running a reversible play backwards -/

theorem legalB_of_erasures_zero : ∀ (s : List Nat) (b : Board),
    legalE b s = true → erasures b s = 0 → legalB b s = true
  | [], _, _, _ => rfl
  | i :: rest, b, hl, he => by
    simp only [legalE_cons, Bool.and_eq_true] at hl
    simp only [erasures_cons] at he
    have hok : okMove b i = true := by
      cases hm : okMove b i
      · have hn : nth b i = true := by simpa [okE, hm] using hl.1
        have : isErase b i = true := by simp [isErase, hn, hm]
        rw [this] at he; simp at he
      · rfl
    have hr : erasures (toggle b i) rest = 0 := by omega
    simp [legalB, hok, legalB_of_erasures_zero rest _ hl.2 hr]

theorem Seg.reverse {n : Nat} {b b' : Board} {q l : Nat} {t : List Nat}
    (h : Seg n b b' q 0 l t) : Seg n b' b q 0 l t.reverse := by
  have hB := legalB_of_erasures_zero t b h.legal h.eras
  have hR := legal_reverse b t hB
  refine ⟨?_, ?_, ?_, ?_, by simp [h.len], ?_⟩
  · rw [← h.exec]; exact legalE_of_legalB _ _ hR
  · rw [← h.exec]; exact exec_reverse_cancel b t
  · rw [← h.exec, maxOnes_reverse]; exact h.peak
  · rw [← h.exec]; exact erasures_of_legalB _ _ hR
  · intro i hi; exact h.bounds i (List.mem_reverse.mp hi)

/-! ## Triangular numbers -/

/-- `T(p) = p(p−1)/2 + 1`. -/
def tri : Nat → Nat
  | 0 => 1
  | p + 1 => tri p + p

theorem tri_pos (p : Nat) : 1 ≤ tri p := by
  induction p with
  | zero => simp [tri]
  | succ p ih => simp only [tri]; omega

theorem tri_ge (p : Nat) : p ≤ tri p := by
  induction p with
  | zero => simp [tri]
  | succ p ih => have := tri_pos p; simp only [tri]; omega

theorem two_mul_tri (p : Nat) : 2 * tri p = p * (p - 1) + 2 := by
  induction p with
  | zero => simp [tri]
  | succ p ih =>
    simp only [tri, Nat.add_sub_cancel]
    have h1 : (p + 1) * p = p * p + p := Nat.succ_mul p p
    rcases Nat.eq_zero_or_pos p with h0 | hp
    · subst h0; simp [tri]
    · have h2 : p * (p - 1) = p * p - p := Nat.mul_sub_one p p
      have h3 : p ≤ p * p := Nat.le_mul_self p
      omega

theorem tri_eq (p : Nat) : tri p = p * (p - 1) / 2 + 1 := by
  have := two_mul_tri p
  omega

/-! ## The construction without erasure -/

/-- **Triangular construction.**  For `p ≥ 2` and `p ≤ n ≤ T(p)` there is a
plan with peak `p`, no erasure and `4n − 2p − 1` moves. -/
theorem tri_spec : ∀ p, 2 ≤ p → ∀ n, p ≤ n → n ≤ tri p →
    ∃ t, Seg n (empty n) (target n) p 0 (4 * n - 2 * p - 1) t := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ih =>
    intro hp n hpn hn
    rcases Nat.lt_or_ge p 2 with hp2 | hp2
    · have e1 : p = 1 := by omega
      subst e1
      have hn2 : n = 2 := by simp [tri] at hn; omega
      subst hn2
      obtain ⟨t, ht⟩ := first_block_spec 2 2 (by omega) (Nat.le_refl _)
      exact ⟨t, by simpa using ht.cast (blk_single_eq_target 2 (by omega))⟩
    · have htri : tri (p + 1) = tri p + p := rfl
      have hge := tri_ge p
      obtain ⟨a, ha1, hap, hb1, hb2⟩ : ∃ a, 1 ≤ a ∧ a ≤ p ∧ p ≤ n - a ∧ n - a ≤ tri p := by
        rcases Nat.le_total (n - tri p) 1 with h | h
        · exact ⟨1, by omega, by omega, by omega, by omega⟩
        · exact ⟨n - tri p, by omega, by omega, by omega, by omega⟩
      have hn1 : 1 ≤ n := by omega
      -- step 1: a stone on cell a − 1
      obtain ⟨t1, h1⟩ := first_block_spec n a ha1 (by omega)
      -- step 2: the (p)-plan on cells [a, n) above the held stone
      obtain ⟨t2, h2⟩ := ih hp2 (n - a) hb1 hb2
      have h2w := window_seg (x := a) (K := 1) (B := blk n (a - 1) 1 n) h2
        (length_empty _) (length_blk _ _ _ _) (by omega)
        (by intro i hi; rw [nth_blk _ _ _ (by omega), nth_empty]; simp; omega)
        (Or.inr (by rw [nth_blk _ _ _ (by omega)]; simp; try omega))
        (by rw [ones_empty]; exact ones_blk_le_of_ge n (a - 1) 1 n (Nat.le_refl _))
      have hb2' : mk n (fun j => if a ≤ j ∧ j < a + (n - a) then nth (target (n - a)) (j - a)
          else nth (blk n (a - 1) 1 n) j) = blk n (a - 1) 1 (n - 1) := by
        unfold blk
        apply mk_congr
        intro j hj
        split
        · rw [nth_target _ _ (by omega)]
          apply Bool.eq_iff_iff.mpr; simp; omega
        · rw [nth_mk_of_lt hj]
          apply Bool.eq_iff_iff.mpr; simp; omega
      have h2w' := h2w.cast hb2'
      -- step 3: undo step 1 under the final stone
      obtain ⟨t3, h3⟩ := first_block_spec a a ha1 (Nat.le_refl _)
      have h3r := Seg.reverse h3
      have hc1 : 1 ≤ ones (blk a (a - 1) 1 a) := by
        unfold blk; rw [ones_or_single, ones_run]; split <;> omega
      have h3w := window_seg (x := 0) (K := 1) (B := blk n (a - 1) 1 (n - 1)) h3r
        (length_blk _ _ _ _) (length_blk _ _ _ _) (by omega)
        (by
          intro i hi
          rw [nth_blk _ _ _ (by omega), nth_blk _ _ _ (by omega)]
          apply Bool.eq_iff_iff.mpr; simp; omega)
        (Or.inl rfl)
        (Nat.le_trans (ones_blk_le n (a - 1) 1 (n - 1)) (by omega))
      have hb3 : mk n (fun j => if 0 ≤ j ∧ j < 0 + a then nth (empty a) (j - 0)
          else nth (blk n (a - 1) 1 (n - 1)) j) = target n := by
        rw [target_eq_mk n hn1]
        apply mk_congr
        intro j hj
        split
        · rw [nth_empty]; apply Bool.eq_iff_iff.mpr; simp; omega
        · rw [nth_blk _ _ _ hj]; apply Bool.eq_iff_iff.mpr; simp; omega
      have h3w' := h3w.cast hb3
      have h := ((h1.peak_mono (q' := p + 1) (by omega)).append
        (h2w'.peak_mono (q' := p + 1) (by omega))).append
        (h3w'.peak_mono (q' := p + 1) (by omega))
      have el : 2 * a - 1 + (4 * (n - a) - 2 * p - 1) + (2 * a - 1) = 4 * n - 2 * (p + 1) - 1 := by
        omega
      rw [el] at h
      exact ⟨_, h⟩

/-! ## Blocks with one erasure each -/

/-- **Construction with erasures.**  For `p ≥ 3`, `e ≥ 0` and
`A ≤ n ≤ T(p) + e·T(p−1)` (`A = (p−1)(e+1)+1`) there is a plan with peak
`p`, exactly `e` erasures and `4n − 2(p−1)(e+1) − 3` moves. -/
theorem blocks_spec (p : Nat) (hp : 3 ≤ p) : ∀ e n, (p - 1) * (e + 1) + 1 ≤ n →
    n ≤ tri p + e * tri (p - 1) →
    ∃ t, Seg n (empty n) (target n) p e (4 * n - 2 * ((p - 1) * (e + 1)) - 3) t := by
  have hu := tri_ge (p - 1)
  have hv := tri_ge p
  intro e
  induction e with
  | zero =>
    intro n hA hN
    simp only [Nat.zero_add, Nat.mul_one, Nat.zero_mul, Nat.add_zero] at hA hN ⊢
    obtain ⟨t, ht⟩ := tri_spec p (by omega) n (by omega) hN
    have el : 4 * n - 2 * p - 1 = 4 * n - 2 * (p - 1) - 3 := by omega
    rw [el] at ht
    exact ⟨t, ht⟩
  | succ e ih =>
    intro n hA hN
    have hW : (p - 1) * (e + 1 + 1) = (p - 1) * (e + 1) + (p - 1) := Nat.mul_succ _ _
    have hV : (e + 1) * tri (p - 1) = e * tri (p - 1) + tri (p - 1) := Nat.succ_mul _ _
    have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
    have hle : (p - 1) * e ≤ e * tri (p - 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
    rw [hW] at hA ⊢
    rw [hV] at hN
    obtain ⟨n', h1, h2, h3, h4⟩ : ∃ n', (p - 1) * (e + 1) + 1 ≤ n' ∧
        n' ≤ tri p + e * tri (p - 1) ∧ p - 1 ≤ n - n' ∧ n - n' ≤ tri (p - 1) := by
      rcases Nat.le_total ((p - 1) * (e + 1) + 1) (n - tri (p - 1)) with h | h
      · exact ⟨n - tri (p - 1), h, by omega, by omega, by omega⟩
      · exact ⟨(p - 1) * (e + 1) + 1, Nat.le_refl _, by omega, by omega, by omega⟩
    have hn1 : 1 ≤ n := by omega
    -- the first n' cells with e erasures, ending on a stone at n' − 1
    obtain ⟨t1, ht1⟩ := ih n' h1 h2
    have h1w := window_seg (x := 0) (K := 0) (B := empty n) ht1
      (length_empty _) (length_empty _) (by omega)
      (by intro i hi; rw [nth_empty, nth_empty])
      (Or.inl rfl) (by rw [ones_empty]; exact Nat.zero_le _)
    have hb1 : mk n (fun j => if 0 ≤ j ∧ j < 0 + n' then nth (target n') (j - 0)
        else nth (empty n) j) = blk n (n' - 1) 1 n := by
      unfold blk
      apply mk_congr
      intro j hj
      split
      · rw [nth_target _ _ (by omega)]; apply Bool.eq_iff_iff.mpr; simp; omega
      · rw [nth_empty]; apply Bool.eq_iff_iff.mpr; simp; omega
    have h1w' := (h1w.cast hb1).peak_mono (q' := p) (by omega)
    -- a (p−1)-plan on [n', n) above the held stone
    obtain ⟨t2, ht2⟩ := tri_spec (p - 1) (by omega) (n - n') h3 h4
    have h2w := window_seg (x := n') (K := 1) (B := blk n (n' - 1) 1 n) ht2
      (length_empty _) (length_blk _ _ _ _) (by omega)
      (by intro i hi; rw [nth_blk _ _ _ (by omega), nth_empty]; simp; omega)
      (Or.inr (by rw [nth_blk _ _ _ (by omega)]; simp; try omega))
      (by rw [ones_empty]; exact ones_blk_le_of_ge n (n' - 1) 1 n (Nat.le_refl _))
    have hb2 : mk n (fun j => if n' ≤ j ∧ j < n' + (n - n') then nth (target (n - n')) (j - n')
        else nth (blk n (n' - 1) 1 n) j) = blk n (n' - 1) 1 (n - 1) := by
      unfold blk
      apply mk_congr
      intro j hj
      split
      · rw [nth_target _ _ (by omega)]
        apply Bool.eq_iff_iff.mpr; simp; omega
      · rw [nth_mk_of_lt hj]
        apply Bool.eq_iff_iff.mpr; simp; omega
    have h2w' := (h2w.cast hb2).peak_mono (q' := p) (by omega)
    -- erase the held stone: its lower neighbour is empty
    have h3 := (erase_step n (n' - 1) (n - 1) (by omega) (by omega) (by omega)).peak_mono
      (q' := p) (by omega)
    have h := ((h1w'.append h2w').append h3).cast (blk_single_eq_target n hn1)
    have el : 4 * n' - 2 * ((p - 1) * (e + 1)) - 3 + (4 * (n - n') - 2 * (p - 1) - 1) + 1 =
        4 * n - 2 * ((p - 1) * (e + 1) + (p - 1)) - 3 := by omega
    rw [el] at h
    exact ⟨_, h⟩

/-! ## The exact values -/

theorem estar_le (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (h : n ≤ (p - 1) * (e + 1) + 1) :
    estar n p ≤ e := by
  unfold estar
  have hq : (n - 1 + (p - 1) - 1) / (p - 1) < e + 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : (e + 2) * (p - 1) = (p - 1) * (e + 1) + (p - 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_succ _ _
    omega
  omega

/-- **Exact value up to the triangular frontier.**  For `p ≥ 3` and
`1 ≤ n ≤ T(p) + e·T(p−1)`:
`M*(n, p, e) = 2n − 1 + 2·max(0, n − A)`, `A = (p−1)(e+1)+1`. -/
theorem mstar_exact (p e n : Nat) (hp : 3 ≤ p) (hn : 1 ≤ n)
    (hN : n ≤ tri p + e * tri (p - 1)) :
    MstarIs n p e (2 * n - 1 + 2 * (n - ((p - 1) * (e + 1) + 1))) := by
  refine ⟨?_, fun s hs => Contraction.length_ge n p e (by omega) hn s hs⟩
  rcases Nat.le_total n ((p - 1) * (e + 1) + 1) with hA | hA
  · obtain ⟨t, ht, hl⟩ := theoremA_upper n p (by omega) hn
    refine ⟨t, ht.mono_budget (estar_le n p e (by omega) hn hA), ?_⟩
    rw [hl]; omega
  · obtain ⟨t, ht⟩ := blocks_spec p hp e n hA hN
    refine ⟨t, ⟨ht.bounds, ht.legal, ht.peak, Nat.le_of_eq ht.eras, ht.exec⟩, ?_⟩
    rw [ht.len]; omega

/-- The band just past saturation: `M*(A + j, p, e) = 2(A + j) − 1 + 2j` for
`j ≤ p − 2`. -/
theorem near_band_exact (p e j : Nat) (hp : 3 ≤ p) (hj : j ≤ p - 2) :
    MstarIs ((p - 1) * (e + 1) + 1 + j) p e
      (2 * ((p - 1) * (e + 1) + 1 + j) - 1 + 2 * j) := by
  have hu := tri_ge (p - 1)
  have hle : (p - 1) * e ≤ e * tri (p - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left e hu
  have hW0 : (p - 1) * (e + 1) = (p - 1) * e + (p - 1) := Nat.mul_succ _ _
  have htp : tri p = tri (p - 1) + (p - 1) := by
    cases p with
    | zero => omega
    | succ q => simp [tri]
  have h := mstar_exact p e ((p - 1) * (e + 1) + 1 + j) hp (by omega) (by omega)
  have el : (p - 1) * (e + 1) + 1 + j - ((p - 1) * (e + 1) + 1) = j := by omega
  rw [el] at h
  exact h

/-- `p = 4`, the interior: `M*(n, 4, e) = 4n − 6e − 9` for `3e + 4 ≤ n ≤ 4e + 7`. -/
theorem mstar_p4_interior (e n : Nat) (h1 : 3 * e + 4 ≤ n) (h2 : n ≤ 4 * e + 7) :
    MstarIs n 4 e (4 * n - 6 * e - 9) := by
  have h := mstar_exact 4 e n (by omega) (by omega) (by simp [tri]; omega)
  have el : 2 * n - 1 + 2 * (n - ((4 - 1) * (e + 1) + 1)) = 4 * n - 6 * e - 9 := by omega
  rw [el] at h
  exact h

/-- `p = 5`: `M*(n, 5, e) = 4n − 8e − 11` for `4e + 5 ≤ n ≤ 7e + 11`. -/
theorem mstar_p5_interior (e n : Nat) (h1 : 4 * e + 5 ≤ n) (h2 : n ≤ 7 * e + 11) :
    MstarIs n 5 e (4 * n - 8 * e - 11) := by
  have h := mstar_exact 5 e n (by omega) (by omega) (by simp [tri]; omega)
  have el : 2 * n - 1 + 2 * (n - ((5 - 1) * (e + 1) + 1)) = 4 * n - 8 * e - 11 := by omega
  rw [el] at h
  exact h

end Triangular
end ErasurePebbling
