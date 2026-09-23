import ErasurePebbling.Board

/-!
# Theorem A, upper bound: the block sweep (RC-02 §4, 上界（構成）)

With `p ≥ 2` pebbles, sweep the chain in blocks.  The first block puts
pebbles on cells `0, …, k−1` (`k = min p n`) in ascending order and
takes them off again in descending order down to cell `1`, then removes
cell `0` (reversibly: its predecessor is the free entrance), leaving a
single *stepping stone* on cell `k−1`.  Every later block stands on a
stone `s`, climbs `s+1, …, s+k` (`k ≤ p−1`, so the peak is `p`), descends
reversibly to `s+1`, and then erases the stone `s` – irreversibly,
because cell `s−1` is empty.  Each cell is placed exactly once and every
cell but the last removed exactly once, so the play has `2n − 1` moves,
and the number of irreversible removals is the number of stones erased,
`⌈(n−p)/(p−1)⌉ = ⌈(n−1)/(p−1)⌉ − 1 = e*(n, p)`.

`theoremA_upper` packages this as: for `p ≥ 2` and `n ≥ 1` there is a
clean plan with peak `p`, `e*(n,p)` erasures and exactly `2n − 1` moves.
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

/-! ## Play segments -/

/-- A play segment `t` from `b` to `b'` inside a chain of length `n`:
admissible, peak at most `q`, exactly `k` irreversible removals, `l`
moves. -/
structure Seg (n : Nat) (b b' : Board) (q k l : Nat) (t : List Nat) : Prop where
  legal : legalE b t = true
  exec : execB b t = b'
  peak : maxOnes b t ≤ q
  eras : erasures b t = k
  len : t.length = l
  bounds : ∀ i ∈ t, i < n

theorem Seg.nil {n : Nat} {b : Board} {q : Nat} (h : ones b ≤ q) : Seg n b b q 0 0 [] :=
  ⟨rfl, rfl, by simpa [maxOnes] using h, rfl, rfl, by simp⟩

theorem Seg.append {n : Nat} {b b' b'' : Board} {q k k' l l' : Nat} {t t' : List Nat}
    (h1 : Seg n b b' q k l t) (h2 : Seg n b' b'' q k' l' t') :
    Seg n b b'' q (k + k') (l + l') (t ++ t') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [legalE_append, h1.legal, h1.exec, h2.legal]; rfl
  · rw [exec_append, h1.exec, h2.exec]
  · rw [maxOnes_append, h1.exec]
    exact Nat.max_le.mpr ⟨h1.peak, h2.peak⟩
  · rw [erasures_append, h1.exec, h1.eras, h2.eras]
  · rw [List.length_append, h1.len, h2.len]
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact h1.bounds i h
    · exact h2.bounds i h

theorem Seg.single {n : Nat} {b : Board} {q : Nat} {i : Nat}
    (hok : okE b i = true) (h1 : ones b ≤ q) (h2 : ones (toggle b i) ≤ q) (hi : i < n) :
    Seg n b (toggle b i) q (if isErase b i then 1 else 0) 1 [i] := by
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_⟩
  · simp [hok]
  · simp only [maxOnes]
    exact Nat.max_le.mpr ⟨h1, h2⟩
  · simp
  · intro j hj
    simp at hj; subst hj; exact hi

theorem Seg.cast {n : Nat} {b b' b'' : Board} {q k l : Nat} {t : List Nat}
    (h : Seg n b b' q k l t) (e : b' = b'') : Seg n b b'' q k l t := e ▸ h

theorem Seg.cast_src {n : Nat} {b b' b'' : Board} {q k l : Nat} {t : List Nat}
    (h : Seg n b b'' q k l t) (e : b = b') : Seg n b' b'' q k l t := e ▸ h

theorem Seg.peak_mono {n : Nat} {b b' : Board} {q q' k l : Nat} {t : List Nat}
    (h : Seg n b b' q k l t) (hq : q ≤ q') : Seg n b b' q' k l t :=
  ⟨h.legal, h.exec, Nat.le_trans h.peak hq, h.eras, h.len, h.bounds⟩

/-! ## The boards of the sweep -/

/-- Cells `[s, s+a)` pebbled, plus cell `t` (use `t = n` for "no extra cell"). -/
def blk (n s a t : Nat) : Board :=
  mk n (fun i => decide (s ≤ i ∧ i < s + a) || decide (i = t))

@[simp] theorem length_blk (n s a t : Nat) : (blk n s a t).length = n := length_mk n _

theorem nth_blk {n : Nat} (s a t : Nat) {i : Nat} (hi : i < n) :
    nth (blk n s a t) i = (decide (s ≤ i ∧ i < s + a) || decide (i = t)) :=
  nth_mk_of_lt hi

theorem ones_blk_le (n s a t : Nat) : ones (blk n s a t) ≤ a + 1 := by
  unfold blk
  rw [ones_or_single, ones_run]
  split <;> omega

theorem ones_blk_le_of_ge (n s a t : Nat) (ht : n ≤ t) : ones (blk n s a t) ≤ a := by
  unfold blk
  rw [ones_or_single, ones_run]
  rw [if_neg (fun h => by omega)]
  omega

theorem blk_zero_eq_empty (n : Nat) : blk n 0 0 n = empty n := by
  rw [empty_eq_mk]
  apply mk_congr
  intro i hi
  simp
  omega

theorem blk_single_eq_target (n : Nat) (hn : 1 ≤ n) : blk n (n - 1) 1 n = target n := by
  rw [target_eq_mk n hn]
  apply mk_congr
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simp
  omega

/-- The top cell of a run may be regarded as the extra cell. -/
theorem blk_top (n s a : Nat) (h : s + a < n) : blk n s (a + 1) n = blk n s a (s + a) := by
  apply mk_congr
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simp
  omega

/-- A single pebble on `t`, in the two available spellings. -/
theorem blk_single (n s t : Nat) (h : t < n) : blk n s 0 t = blk n t 1 n := by
  apply mk_congr
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simp
  omega

/-! ## The four kinds of moves -/

/-- Placing the cell just above a non-empty run. -/
theorem place_step (n s a t q : Nat) (hn : s + a < n) (ha : 1 ≤ a ∨ s + a = 0) (ht : ¬ s + a = t)
    (hq1 : ones (blk n s a t) ≤ q) (hq2 : ones (blk n s (a + 1) t) ≤ q) :
    Seg n (blk n s a t) (blk n s (a + 1) t) q 0 1 [s + a] := by
  have hok : okMove (blk n s a t) (s + a) = true := by
    unfold blk
    rw [okMove_mk]
    rcases ha with ha | ha
    · have h1 : s + a - 1 < n := by omega
      rw [if_pos h1]
      simp; omega
    · simp [ha]
  have hcur : nth (blk n s a t) (s + a) = false := by
    rw [nth_blk _ _ _ hn]; simp; omega
  have htog : toggle (blk n s a t) (s + a) = blk n s (a + 1) t := by
    unfold blk
    rw [toggle_mk _ hn]
    apply mk_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    by_cases hi' : i = s + a
    · subst hi'; simp; omega
    · simp [hi']; omega
  have h := Seg.single (n := n) (q := q) (okE_of_okMove hok) hq1 (by rw [htog]; exact hq2) hn
  rw [isErase_eq_false_of_okMove hok] at h
  simpa [htog] using h

/-- Removing the top cell of a run of length at least two: reversible. -/
theorem remove_top_step (n s a t q : Nat) (hn : s + a < n) (ha : 1 ≤ a) (ht : ¬ s + a = t)
    (hq1 : ones (blk n s (a + 1) t) ≤ q) (hq2 : ones (blk n s a t) ≤ q) :
    Seg n (blk n s (a + 1) t) (blk n s a t) q 0 1 [s + a] := by
  have hok : okMove (blk n s (a + 1) t) (s + a) = true := by
    unfold blk
    rw [okMove_mk]
    have h1 : s + a - 1 < n := by omega
    rw [if_pos h1]
    simp; omega
  have htog : toggle (blk n s (a + 1) t) (s + a) = blk n s a t := by
    unfold blk
    rw [toggle_mk _ hn]
    apply mk_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    by_cases hi' : i = s + a
    · subst hi'; simp; omega
    · simp [hi']; omega
  have h := Seg.single (n := n) (q := q) (okE_of_okMove hok) hq1 (by rw [htog]; exact hq2) hn
  rw [isErase_eq_false_of_okMove hok] at h
  simpa [htog] using h

/-- Removing cell `0` when it is the only cell of its run: reversible
(the entrance is free). -/
theorem remove_free_step (n t : Nat) (ht : 0 < t) (hn : t < n) :
    Seg n (blk n 0 1 t) (blk n t 1 n) 2 0 1 [0] := by
  have h0 : 0 < n := by omega
  have hok : okMove (blk n 0 1 t) 0 = true := by simp [okMove]
  have htog : toggle (blk n 0 1 t) 0 = blk n t 1 n := by
    unfold blk
    rw [toggle_mk _ h0]
    apply mk_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    by_cases hi' : i = 0
    · subst hi'; simp; omega
    · simp [hi']; omega
  have h := Seg.single (n := n) (q := 2) (okE_of_okMove hok)
    (ones_blk_le n 0 1 t) (by rw [htog]; exact Nat.le_trans (ones_blk_le n t 1 n) (by omega)) h0
  rw [isErase_eq_false_of_okMove hok] at h
  simpa [htog] using h

/-- Erasing a stone `s ≥ 1` whose lower neighbour is empty: irreversible. -/
theorem erase_step (n s t : Nat) (hs : 1 ≤ s) (hst : s < t) (hn : t < n) :
    Seg n (blk n s 1 t) (blk n t 1 n) 2 1 1 [s] := by
  have hsn : s < n := by omega
  have hcur : nth (blk n s 1 t) s = true := by
    rw [nth_blk _ _ _ hsn]; simp
  have hnok : okMove (blk n s 1 t) s = false := by
    unfold blk
    rw [okMove_mk]
    have h1 : s - 1 < n := by omega
    rw [if_pos h1]
    simp; omega
  have hok : okE (blk n s 1 t) s = true := by simp [okE, hcur]
  have her : isErase (blk n s 1 t) s = true := by simp [isErase, hcur, hnok]
  have htog : toggle (blk n s 1 t) s = blk n t 1 n := by
    unfold blk
    rw [toggle_mk _ hsn]
    apply mk_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    by_cases hi' : i = s
    · subst hi'; simp; omega
    · simp [hi']; omega
  have h := Seg.single (n := n) (q := 2) hok
    (ones_blk_le n s 1 t) (by rw [htog]; exact Nat.le_trans (ones_blk_le n t 1 n) (by omega)) hsn
  rw [her] at h
  simpa [htog] using h

/-! ## The three move sequences -/

/-- `up s k = [s+1, …, s+k]`. -/
def up (s : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => up s k ++ [s + k + 1]

/-- `up0 k = [0, …, k−1]`. -/
def up0 : Nat → List Nat
  | 0 => []
  | k + 1 => up0 k ++ [k]

/-- `down s j = [s+j, …, s+1]`. -/
def down (s : Nat) : Nat → List Nat
  | 0 => []
  | j + 1 => (s + j + 1) :: down s j

theorem up_spec (n s : Nat) : ∀ k, s + k < n →
    Seg n (blk n s 1 n) (blk n s (k + 1) n) (k + 1) 0 k (up s k) := by
  intro k
  induction k with
  | zero => intro _; exact Seg.nil (ones_blk_le_of_ge n s 1 n (Nat.le_refl _))
  | succ k ih =>
      intro hk
      have h1 := (ih (by omega)).peak_mono (q' := k + 2) (by omega)
      have h2 := place_step n s (k + 1) n (k + 2) (by omega) (Or.inl (by omega)) (by omega)
        (Nat.le_trans (ones_blk_le_of_ge n s (k + 1) n (Nat.le_refl _)) (by omega))
        (ones_blk_le_of_ge n s (k + 2) n (Nat.le_refl _))
      have h3 : s + (k + 1) = s + k + 1 := by omega
      rw [h3] at h2
      have := h1.append h2
      simpa [up] using this

theorem up0_spec (n : Nat) : ∀ k, k ≤ n →
    Seg n (blk n 0 0 n) (blk n 0 k n) k 0 k (up0 k) := by
  intro k
  induction k with
  | zero => intro _; exact Seg.nil (ones_blk_le_of_ge n 0 0 n (Nat.le_refl _))
  | succ k ih =>
      intro hk
      have h1 := (ih (by omega)).peak_mono (q' := k + 1) (by omega)
      have h2 : Seg n (blk n 0 k n) (blk n 0 (k + 1) n) (k + 1) 0 1 [k] := by
        have h := place_step n 0 k n (k + 1) (by omega) (by omega) (by omega)
          (Nat.le_trans (ones_blk_le_of_ge n 0 k n (Nat.le_refl _)) (by omega))
          (ones_blk_le_of_ge n 0 (k + 1) n (Nat.le_refl _))
        simpa only [Nat.zero_add] using h
      have := h1.append h2
      simpa [up0] using this

theorem down_spec (n s t : Nat) (hn : t < n) : ∀ j, s + j + 1 ≤ t →
    Seg n (blk n s (j + 1) t) (blk n s 1 t) (j + 2) 0 j (down s j) := by
  intro j
  induction j with
  | zero => intro _; exact Seg.nil (ones_blk_le n s 1 t)
  | succ j ih =>
      intro hj
      have h1 := remove_top_step n s (j + 1) t (j + 3) (by omega) (by omega) (by omega)
        (ones_blk_le n s (j + 2) t) (Nat.le_trans (ones_blk_le n s (j + 1) t) (by omega))
      have h2 := (ih (by omega)).peak_mono (q' := j + 3) (by omega)
      have := h1.append h2
      have e : s + (j + 1) = s + j + 1 := by omega
      have el : 1 + j = j + 1 := Nat.add_comm _ _
      rw [el] at this
      simpa [down, e] using this

/-! ## Blocks and the sweep -/

/-- A block standing on stone `s ≥ 1`: climb `k ≥ 1` cells, descend, erase the stone. -/
theorem block_spec (n s k : Nat) (hs : 1 ≤ s) (hk : 1 ≤ k) (hn : s + k < n) :
    Seg n (blk n s 1 n) (blk n (s + k) 1 n) (k + 1) 1 (2 * k)
      (up s k ++ down s (k - 1) ++ [s]) := by
  have h1 := up_spec n s k hn
  have h1' := h1.cast (blk_top n s k hn)
  have h2 := down_spec n s (s + k) hn (k - 1) (by omega)
  have e : k - 1 + 1 = k := by omega
  rw [e] at h2
  have h2' := h2.peak_mono (q' := k + 1) (by omega)
  have h3 := (erase_step n s (s + k) hs (by omega) hn).peak_mono (q' := k + 1) (by omega)
  have := (h1'.append h2').append h3
  have el : k + (k - 1) + 1 = 2 * k := by omega
  simpa [el] using this

/-- The first block, from the empty board: `k ≥ 1` cells, peak `k`, no erasure,
`2k − 1` moves, leaving a stone on cell `k − 1`. -/
theorem first_block_spec (n k : Nat) (hk : 1 ≤ k) (hn : k ≤ n) :
    ∃ t, Seg n (empty n) (blk n (k - 1) 1 n) k 0 (2 * k - 1) t := by
  rcases Nat.lt_or_ge k 2 with h | h
  · -- k = 1: the single move [0]
    have hk1 : k = 1 := by omega
    subst hk1
    have h := place_step n 0 0 n 1 (by omega) (Or.inr rfl) (by omega)
      (Nat.le_trans (ones_blk_le_of_ge n 0 0 n (Nat.le_refl _)) (Nat.zero_le _))
      (ones_blk_le_of_ge n 0 1 n (Nat.le_refl _))
    simp only [Nat.add_zero] at h
    exact ⟨[0], h.cast_src (blk_zero_eq_empty n)⟩
  · have h1 := (up0_spec n k hn).cast_src (blk_zero_eq_empty n)
    have hb : blk n 0 k n = blk n 0 (k - 1) (k - 1) := by
      have := blk_top n 0 (k - 1) (by omega)
      have e : k - 1 + 1 = k := by omega
      rw [e, Nat.zero_add] at this
      exact this
    have h1' := h1.cast hb
    have h2 := down_spec n 0 (k - 1) (by omega) (k - 2) (by omega)
    have e2 : k - 2 + 1 = k - 1 := by omega
    rw [e2] at h2
    have h2' := h2.peak_mono (q' := k) (by omega)
    have h3 := (remove_free_step n (k - 1) (by omega) (by omega)).peak_mono (q' := k) (by omega)
    have := (h1'.append h2').append h3
    have el : k + (k - 2) + 1 = 2 * k - 1 := by omega
    rw [el] at this
    exact ⟨_, by simpa using this⟩

/-- The sweep from a stone `s ≥ 1` over the remaining `r = n − 1 − s` cells,
in blocks of `p − 1`: `2r` moves and `⌈r/(p−1)⌉` erasures. -/
theorem sweep_spec (n p : Nat) (hp : 2 ≤ p) : ∀ r s, 1 ≤ s → s + r = n - 1 →
    ∃ t, Seg n (blk n s 1 n) (blk n (n - 1) 1 n) p ((r + p - 2) / (p - 1)) (2 * r) t := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro s hs hr
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have e : s = n - 1 := by omega
      subst e
      refine ⟨[], ?_⟩
      have hq : (0 + p - 2) / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
      rw [hq]
      exact Seg.nil (Nat.le_trans (ones_blk_le n (n - 1) 1 n) (by omega))
    · -- block of k = min (p-1) r cells
      have hn : 1 ≤ n := by omega
      rcases Nat.lt_or_ge r (p - 1) with hlt | hge
      · -- last block: k = r, then nothing remains
        have hb := block_spec n s r hs hpos (by omega)
        have e : s + r = n - 1 := hr
        rw [e] at hb
        have hq : (r + p - 2) / (p - 1) = 1 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [hq]
        exact ⟨_, hb.peak_mono (by omega)⟩
      · have hb := block_spec n s (p - 1) hs (by omega) (by omega)
        obtain ⟨t, ht⟩ := ih (r - (p - 1)) (by omega) (s + (p - 1)) (by omega) (by omega)
        have := (hb.peak_mono (q' := p) (by omega)).append ht
        have hq : 1 + (r - (p - 1) + p - 2) / (p - 1) = (r + p - 2) / (p - 1) := by
          have e : r + p - 2 = (r - (p - 1) + p - 2) + (p - 1) := by omega
          rw [e, Nat.add_div_right _ (by omega), Nat.add_comm]
        have el : 2 * (p - 1) + 2 * (r - (p - 1)) = 2 * r := by omega
        rw [hq, el] at this
        exact ⟨_, this⟩

/-- **Theorem A, upper bound (construction).**  For `p ≥ 2` and `n ≥ 1` the
chain of length `n` has a clean plan with peak `p`, `e*(n, p)` irreversible
removals and exactly `2n − 1` moves. -/
theorem theoremA_upper (n p : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    ∃ t, IsPlay n p (estar n p) t ∧ t.length = 2 * n - 1 := by
  rcases Nat.lt_or_ge n (p + 1) with hle | hgt
  · -- n ≤ p: the first block alone
    obtain ⟨t, ht⟩ := first_block_spec n n hn (Nat.le_refl _)
    have ht' := (ht.cast (blk_single_eq_target n hn)).peak_mono (q' := p) (by omega)
    refine ⟨t, ⟨ht'.bounds, ht'.legal, ht'.peak, ?_, ht'.exec⟩, ht'.len⟩
    rw [ht'.eras]; exact Nat.zero_le _
  · -- n > p: first block of p cells, then the sweep from stone p − 1
    obtain ⟨t1, h1⟩ := first_block_spec n p (by omega) (by omega)
    obtain ⟨t2, h2⟩ := sweep_spec n p hp (n - p) (p - 1) (by omega) (by omega)
    have h := (h1.peak_mono (q' := p) (Nat.le_refl _)).append h2
    have h' := h.cast (blk_single_eq_target n hn)
    have he : 0 + (n - p + p - 2) / (p - 1) = estar n p := by
      unfold estar
      have e : n - 1 + (p - 1) - 1 = (n - p + p - 2) + (p - 1) := by omega
      rw [e, Nat.add_div_right _ (by omega), Nat.zero_add, Nat.add_sub_cancel]
    have hl : 2 * p - 1 + 2 * (n - p) = 2 * n - 1 := by omega
    rw [he, hl] at h'
    exact ⟨_, ⟨h'.bounds, h'.legal, h'.peak, Nat.le_of_eq h'.eras, h'.exec⟩, h'.len⟩

/-- Budget monotonicity: a plan with `e` erasures is a plan with `e' ≥ e`. -/
theorem IsPlay.mono_budget {n p e e' : Nat} {s : List Nat} (h : IsPlay n p e s) (he : e ≤ e') :
    IsPlay n p e' s :=
  ⟨h.bounds, h.legal, h.peak, Nat.le_trans h.budget he, h.final⟩

theorem IsPlay.mono_peak {n p p' e : Nat} {s : List Nat} (h : IsPlay n p e s) (hp : p ≤ p') :
    IsPlay n p' e s :=
  ⟨h.bounds, h.legal, Nat.le_trans h.peak hp, h.budget, h.final⟩

/-- Theorem A, `⇐`: if `e ≥ e*(n, p)` then `M*(n, p, e) ≤ 2n − 1`. -/
theorem mstar_le_floor_of_estar_le (n p e : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) (he : estar n p ≤ e) :
    MstarLe n p e (2 * n - 1) := by
  obtain ⟨t, ht, hl⟩ := theoremA_upper n p hp hn
  exact ⟨t, ht.mono_budget he, Nat.le_of_eq hl⟩

end ErasurePebbling
