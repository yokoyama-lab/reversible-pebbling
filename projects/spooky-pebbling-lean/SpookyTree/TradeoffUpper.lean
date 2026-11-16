/- 一般空間の構成。木の高さと部分木のペブル予算を分離する。 -/
import SpookyTree.SharpFinal

namespace SpookyTree

theorem block_spec_cap {h budget Λ : ℕ} (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ budget + 1) :
    ∀ (n k : ℕ) (y : Node) (c : Config), k ≤ n → 1 ≤ k → y.length + k = h → k < budget →
      Pat (cst .ghost) k y c →
      Runs h k y budget c (block budget Λ n k y) ∧ Pat (cst .empty) k y (run c (block budget Λ n k y)) := by
  intro n
  induction n with
  | zero => intro k y c hkn hk; omega
  | succ n ih =>
    intro k y c hkn hk hy hd hP
    by_cases hfin : k ≤ Λ + 1
    · -- 最下段のブロック: 全部置いて、上から全部外す
      have hblock : block budget Λ (n + 1) k y = placeInt .unghost k y ++ removeInt k y := by
        rw [block, if_pos hfin]
      rw [hblock]
      have hP' : Pat (glue .ghost k (cst .ghost)) (0 + k) y c := by
        rw [glue_cst, Nat.zero_add]; exact hP
      obtain ⟨hR1, hQ1⟩ := placeInt_spec (h := h) (j := 0) (pl := .unghost) (X := .ghost)
        (Or.inr ⟨rfl, rfl⟩) (g := cst .ghost) (fun h0 => absurd h0 (by decide)) k y c
        (by omega) hP'
      obtain ⟨hR2, hQ2⟩ := removeInt_spec (h := h) (j := 0) (g := cst .ghost)
        (fun h0 => absurd h0 (by decide)) k y _ (by omega) hQ1
      have hpk : pcPat (glue Cell.pebble k (cst Cell.ghost)) (0 + k) ≤ budget := by
        have h1 := pcPat_glue_peb (cst .ghost) 0 k
        rw [pcPat_cst (X := .ghost) (by decide)] at h1
        have h2 : 2 ^ k ≤ 2 ^ (Λ + 1) := Nat.pow_le_pow_right (by norm_num) hfin
        omega
      have hR1' := hR1.mono hpk
      have hR2' := hR2.mono hpk
      have hQ2' := (Pat_glue_short (cst .ghost) (Nat.le_of_eq (Nat.zero_add k))).mp hQ2
      rw [Nat.zero_add] at hR1' hR2' hQ2'
      exact ⟨Runs_append.mpr ⟨hR1', hR2'⟩, by rw [run_append]; exact hQ2'⟩
    · -- 前線のあるブロック
      obtain ⟨L, hLdef⟩ : ∃ L, L = blockLen budget Λ k := ⟨_, rfl⟩
      have hL1 : 1 ≤ L := by rw [hLdef]; exact blockLen_pos hΛ
      have hLΛ : L ≤ Λ := by rw [hLdef]; exact blockLen_le hΛ
      have hcond : L = 1 ∨ 2 ^ Λ ≤ budget - k := by
        rw [hLdef]; unfold blockLen
        split_ifs with hc
        · exact Or.inl rfl
        · exact Or.inr (by omega)
      have hblock : block budget Λ (n + 1) k y =
          onFront (compute .unghost (k - L)) L y ++ placeInt .unghost L y ++ removeInt L y ++
            onFront (fun a => [⟨.ghost, a⟩]) L y ++ onFront (block budget Λ n (k - L)) L y := by
        rw [block, if_neg hfin, ← hLdef]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + L := ⟨k - L, by omega⟩
      have hjL : j + L - L = j := by omega
      rw [hjL] at hblock
      rw [hblock]
      have hj1 : 1 ≤ j := by omega
      have h2L : 2 ^ L ≤ 2 ^ Λ := Nat.pow_le_pow_right (by norm_num) hLΛ
      have h2L1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have h2Λ : 2 ^ (Λ + 1) = 2 * 2 ^ Λ := by rw [pow_succ]; ring
      have hA : 2 ^ L + j ≤ budget := by
        rcases hcond with hL | hc
        · rw [hL]; omega
        · omega
      -- 1. 前線を計算する
      have hP1 : Pat (glue .ghost L (cst .ghost)) (j + L) y c := by rw [glue_cst]; exact hP
      obtain ⟨hR1, hQ1⟩ := onFront_spec (j := j) (p := j + 1) (w := 1) (e := 0) (ci := .ghost)
        (g0 := cst .ghost) (g1 := scp) (f := compute .unghost j)
        (fun a c' ha hPa => compute_spec (Or.inr ⟨rfl, rfl⟩) j a c' hj1 ha hPa)
        (by rw [pcPat_cst (X := .ghost) (by decide)]; omega) (le_of_eq (pcPat_scp_pos hj1))
        (by decide) L y c hy hP1
      -- 2. 内部を置く
      obtain ⟨hR2, hQ2⟩ := placeInt_spec (j := j) (pl := .unghost) (X := .ghost)
        (Or.inr ⟨rfl, rfl⟩) (g := scp) (fun _ => scp_zero) L y _ hy hQ1
      -- 3. 内部を外す
      obtain ⟨hR3, hQ3⟩ := removeInt_spec (j := j) (g := scp) (fun _ => scp_zero) L y _ hy hQ2
      -- 4. 前線をゴーストにする
      obtain ⟨hR4, hQ4⟩ := onFront_spec (j := j) (p := 0) (w := 1) (e := 0) (ci := .empty)
        (g0 := scp) (g1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
        (fun a c' ha hPa => ghostRoot_spec hj1 a c' ha hPa)
        (le_of_eq (pcPat_scp_pos hj1)) (by rw [pcPat_cst (X := .ghost) (by decide)]; omega)
        (by decide) L y _ hy hQ3
      -- 5. 前線の各頂点のブロックを処理する（帰納法の仮定）
      obtain ⟨hR5, hQ5⟩ := onFront_spec (j := j) (p := budget) (w := 0) (e := 0) (ci := .empty)
        (g0 := cst .ghost) (g1 := cst .empty) (f := block budget Λ n j)
        (fun a c' ha hPa => ih j a c' (by omega) hj1 ha (by omega) hPa)
        (le_of_eq (pcPat_cst (X := .ghost) (by decide) j))
        (le_of_eq (pcPat_cst (X := .empty) (by decide) j))
        (by decide) L y _ hy hQ4
      -- ペブル数の上限
      have hpk1 : j + 1 + (2 ^ L - 1) * (1 + 0) ≤ budget := by omega
      have hpk2 : pcPat (glue Cell.pebble L scp) (j + L) ≤ budget := by
        have h1 := pcPat_glue_peb scp j L
        rw [pcPat_scp_pos hj1] at h1
        omega
      have hpk4 : 0 + (2 ^ L - 1) * (1 + 0) ≤ budget := by omega
      have hpk5 : budget + (2 ^ L - 1) * (0 + 0) ≤ budget := by omega
      refine ⟨?_, ?_⟩
      · simp only [Runs_append, run_append]
        exact ⟨⟨⟨⟨hR1.mono hpk1, hR2.mono hpk2⟩, hR3.mono hpk2⟩, hR4.mono hpk4⟩, hR5.mono hpk5⟩
      · simp only [run_append]
        rw [glue_cst] at hQ5
        exact hQ5

def strategyCap (h budget Λ : ℕ) : List Move :=
  compute .pebble h [] ++ block budget Λ (h - 1) (h - 1) [false] ++
    block budget Λ (h - 1) (h - 1) [true]

theorem strategy_cap_spec {h budget Λ : ℕ} (hh : 2 ≤ h) (hb : h ≤ budget) (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ budget + 1) :
    Runs h h [] (budget + 1) (fun _ => Cell.empty) (strategyCap h budget Λ) ∧
    run (fun _ => Cell.empty) (strategyCap h budget Λ) [] = .pebble ∧
    ∀ z : Node, z.length < h → z ≠ [] → run (fun _ => Cell.empty) (strategyCap h budget Λ) z = .empty := by
  have h4 : 4 ≤ 2 ^ (Λ + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Λ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hstrat : strategyCap (k + 1) budget Λ =
      compute .pebble (k + 1) [] ++ block budget Λ k k [false] ++ block budget Λ k k [true] := by
    simp [strategyCap]
  rw [hstrat]
  -- 1. 木全体を計算する
  obtain ⟨hR1, hQ1⟩ := compute_spec (h := k + 1) (pl := .pebble) (X := .empty)
    (Or.inl ⟨rfl, rfl⟩) (k + 1) [] (fun _ => Cell.empty) (by omega) (by simp) (fun w _ => rfl)
  obtain ⟨hroot1, hG0, hG1⟩ := Pat_succ.mp hQ1
  rw [scp_zero] at hroot1
  rw [scp_shift] at hG0 hG1
  simp only [List.nil_append] at hG0 hG1
  -- 2. 左の子のブロック
  obtain ⟨hR2, hQ2⟩ := block_spec_cap (h := k + 1) hΛ hcap k k [false] _ le_rfl (by omega) (by simp; omega) (by omega) hG0
  have hU2 := hR2.under
  have hL2 := Runs.lift0 (y := []) (q := 1) hR2 (by
    simp only [List.nil_append]
    rw [hroot1, pc_of_Pat _ _ _ hG1, pcPat_cst (X := .ghost) (by decide)]
    simp)
  have hroot2 := (run_outside hU2 _ (not_prefix_parent [] false)).trans hroot1
  have hG1' := (Pat_run_disj hU2 (disj01 [])).mpr hG1
  -- 3. 右の子のブロック
  obtain ⟨hR3, hQ3⟩ := block_spec_cap (h := k + 1) hΛ hcap k k [true] _ le_rfl (by omega) (by simp; omega) (by omega) hG1'
  have hU3 := hR3.under
  have hL3 := Runs.lift1 (y := []) (q := 1) hR3 (by
    simp only [List.nil_append]
    rw [hroot2, pc_of_Pat _ _ _ hQ2, pcPat_cst (X := .empty) (by decide)]
    simp)
  have hroot3 := (run_outside hU3 _ (not_prefix_parent [] true)).trans hroot2
  have hE0 := (Pat_run_disj hU3 (disj10 [])).mpr hQ2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Runs_append, run_append]
    exact ⟨⟨hR1.mono (by omega), hL2⟩, hL3⟩
  · simp only [run_append]
    exact hroot3
  · intro z hz hne
    simp only [run_append]
    match z, hz, hne with
    | [], _, hne => exact absurd rfl hne
    | false :: w, hz, _ => exact hE0 w (by simpa using hz)
    | true :: w, hz, _ => exact hQ3 w (by simpa using hz)


theorem time_upper_bound_cap {h budget Λ : ℕ} (hh : 2 ≤ h) (hb : h ≤ budget) (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ budget + 1)
    (hstart : 2 ^ Λ ≤ budget - (h - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (budget + 1) T ms ∧
      T + 3 ≤ 2 * ((h - 1) / Λ + 2) * 2 ^ h := by
  obtain ⟨hR, hroot, hothers⟩ := strategy_cap_spec hh hb hΛ hcap
  refine ⟨(strategyCap h budget Λ).length, seqOf (strategyCap h budget Λ), valid_of_runs hR hroot hothers, ?_⟩
  have h4 : 4 ≤ 2 ^ (Λ + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Λ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hlen : (strategyCap (k + 1) budget Λ).length = (compute .pebble (k + 1) []).length +
      (block budget Λ k k [false]).length + (block budget Λ k k [true]).length := by
    simp [strategyCap, Nat.add_assoc]
  have e1 : (compute .pebble (k + 1) []).length + 3 = 2 ^ (k + 1 + 1) :=
    length_compute .pebble (k + 1) [] (by omega)
  have e2 := length_block_le (h := budget) hΛ k k [false]
  have e3 := length_block_le (h := budget) hΛ k k [true]
  have e4 := nb_le (h := budget) hΛ k k (by omega)
  have e5 : 2 ^ Λ - (budget - k) = 0 := by omega
  have e6 : 1 ≤ 2 ^ Λ := Nat.one_le_two_pow
  have e7 : nb budget Λ k k ≤ k / Λ + 1 := by simpa [e5] using e4
  have e8 : nb budget Λ k k * 2 ^ k ≤ (k / Λ + 1) * 2 ^ k := Nat.mul_le_mul_right _ e7
  have e9 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e10 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  rw [hlen, Nat.add_sub_cancel, e9]
  rw [e10] at e1
  nlinarith [e1, e2, e3, e8]

end SpookyTree
