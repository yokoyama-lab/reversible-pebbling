/-
# 根をブロック根とする一般空間の構成（手数 `2⌈h/Λ⌉·2^h − 3`）

`TradeoffUpper.lean` の `strategyCap` は木全体を計算してから根の子をブロック根にするので、
上の段の頂点を 1 回余計に置き直す（手数の主項 `(h−1)/Λ + 2`）。
ここでは根自身を最初のブロック根として扱う（紙の構成 (U)）。幅 `Λ`、`j = h − Λ ≥ 1` として
1. 前線（深さ `Λ` の `2^Λ` 個）を左から計算して持つ（前線より下はゴースト）
2. 根から深さ `Λ − 1` までの内部を置く（根を含む）
3. 根を残して内部を外す（`removeInt (Λ−1)` を左右の子に）
4. 前線をゴーストにする
5. 前線の各頂点の部分木（全部ゴースト）を `block` で空にする

* `strategy_step_spec`: 空の盤から合法で、ペブルは `budget + 1` 個以下、終わると根だけペブル。
* `time_upper_bound_step`: 手数 `T + 3 ≤ 2 (⌊(h−1)/Λ⌋ + 1) · 2^h`（`= 2⌈h/Λ⌉·2^h`）。
* `time_upper_bound_step_kss`: 同じことを KSS の意味論（`ValidK`）で。
-/
import SpookyTree.TradeoffUpper

namespace SpookyTree

/-- 根をブロック根とする構成。 -/
def strategyStep (h budget Λ : ℕ) : List Move :=
  onFront (compute .pebble (h - Λ)) Λ [] ++ placeInt .pebble Λ [] ++
    removeInt (Λ - 1) [false] ++ removeInt (Λ - 1) [true] ++
    onFront (fun a => [⟨.ghost, a⟩]) Λ [] ++
    onFront (block budget Λ (h - Λ) (h - Λ)) Λ []

theorem onFront_succ_nil (f : Node → List Move) (L : ℕ) :
    onFront f (L + 1) [] = onFront f L [false] ++ onFront f L [true] := rfl

/-- 根がペブルのまま、左の子の部分木で `l0`、右の子の部分木で `l1` を打つ。 -/
theorem runs_two {h k p q : ℕ} {F G : ℕ → Cell} {l0 l1 : List Move} {c : Config}
    (hroot : c [] = .pebble) (hP0 : Pat F k [false] c) (hP1 : Pat F k [true] c)
    (h0 : ∀ c' : Config, Pat F k [false] c' →
      Runs h k [false] p c' l0 ∧ Pat G k [false] (run c' l0))
    (h1 : ∀ c' : Config, Pat F k [true] c' →
      Runs h k [true] p c' l1 ∧ Pat G k [true] (run c' l1))
    (hF : pcPat F k ≤ q) (hG : pcPat G k ≤ q) :
    Runs h (k + 1) [] (p + (1 + q)) c (l0 ++ l1) ∧ run c (l0 ++ l1) [] = .pebble ∧
      Pat G k [false] (run c (l0 ++ l1)) ∧ Pat G k [true] (run c (l0 ++ l1)) := by
  obtain ⟨hR0, hQ0⟩ := h0 c hP0
  have hU0 := hR0.under
  have hL0 := Runs.lift0 (y := []) (q := 1 + q) hR0 (by
    simp only [List.nil_append]
    rw [hroot, if_pos rfl, pc_of_Pat _ _ _ hP1]
    omega)
  have hroot1 := (run_outside hU0 c (not_prefix_parent [] false)).trans hroot
  have hP1' := (Pat_run_disj hU0 (disj01 [])).mpr hP1
  obtain ⟨hR1, hQ1⟩ := h1 _ hP1'
  have hU1 := hR1.under
  have hL1 := Runs.lift1 (y := []) (q := 1 + q) hR1 (by
    simp only [List.nil_append]
    rw [hroot1, if_pos rfl, pc_of_Pat _ _ _ hQ0]
    omega)
  have hroot2 := (run_outside hU1 _ (not_prefix_parent [] true)).trans hroot1
  have hQ0' := (Pat_run_disj hU1 (disj10 [])).mpr hQ0
  refine ⟨Runs_append.mpr ⟨hL0, hL1⟩, ?_, ?_, ?_⟩
  · rw [run_append]; exact hroot2
  · rw [run_append]; exact hQ0'
  · rw [run_append]; exact hQ1

/-- **仕様.** `1 ≤ Λ < h`、`2^(Λ+1) ≤ budget + 1`、前線の計算のピーク `2^Λ + (h − Λ) ≤ budget + 1` なら、
`strategyStep` は空の盤から合法で、ペブルは `budget + 1` 個以下、終わると根だけペブル・他は空。 -/
theorem strategy_step_spec {h budget Λ : ℕ} (hΛ : 1 ≤ Λ) (hΛh : Λ < h)
    (hcap : 2 ^ (Λ + 1) ≤ budget + 1) (hfront : 2 ^ Λ + (h - Λ) ≤ budget + 1) :
    Runs h h [] (budget + 1) (fun _ => Cell.empty) (strategyStep h budget Λ) ∧
    run (fun _ => Cell.empty) (strategyStep h budget Λ) [] = .pebble ∧
    ∀ z : Node, z.length < h → z ≠ [] →
      run (fun _ => Cell.empty) (strategyStep h budget Λ) z = .empty := by
  obtain ⟨L', rfl⟩ : ∃ L', Λ = L' + 1 := ⟨Λ - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, h = j + L' + 1 := ⟨h - (L' + 1), by omega⟩
  have hj1 : 1 ≤ j := by omega
  have hjsub : j + L' + 1 - (L' + 1) = j := by omega
  rw [hjsub] at hfront
  have h2L : 2 ^ (L' + 1 + 1) = 2 * 2 ^ (L' + 1) := by rw [pow_succ]; ring
  have h2L' : 2 ^ (L' + 1) = 2 * 2 ^ L' := by rw [pow_succ]; ring
  have hP1 : 1 ≤ 2 ^ L' := Nat.one_le_two_pow
  have hjb : j < budget := by omega
  have hs : strategyStep (j + L' + 1) budget (L' + 1) =
      onFront (compute .pebble j) (L' + 1) [] ++ placeInt .pebble (L' + 1) [] ++
        (removeInt L' [false] ++ removeInt L' [true]) ++
        (onFront (fun a => [⟨.ghost, a⟩]) L' [false] ++ onFront (fun a => [⟨.ghost, a⟩]) L' [true]) ++
        (onFront (block budget (L' + 1) j j) L' [false] ++
          onFront (block budget (L' + 1) j j) L' [true]) := by
    simp only [strategyStep, hjsub, Nat.add_sub_cancel]
    rw [onFront_succ_nil (fun a => [⟨.ghost, a⟩]) L', onFront_succ_nil (block budget (L' + 1) j j) L']
    simp only [List.append_assoc]
  rw [hs]
  -- 1. 前線を計算する
  have hP0 : Pat (glue .empty (L' + 1) (cst .empty)) (j + (L' + 1)) [] (fun _ => Cell.empty) := by
    rw [glue_cst]; intro w _; rfl
  obtain ⟨hR1, hQ1⟩ := onFront_spec (h := j + L' + 1) (j := j) (p := j + 1) (w := 1) (e := 0)
    (ci := .empty) (g0 := cst .empty) (g1 := scp) (f := compute .pebble j)
    (fun a c' ha hPa => compute_spec (Or.inl ⟨rfl, rfl⟩) j a c' hj1 ha hPa)
    (by rw [pcPat_cst (X := .empty) (by decide)]; omega) (le_of_eq (pcPat_scp_pos hj1))
    (by decide) (L' + 1) [] _ (by simp only [List.length_nil]; omega) hP0
  -- 2. 内部を置く（根を含む）
  obtain ⟨hR2, hQ2⟩ := placeInt_spec (h := j + L' + 1) (j := j) (pl := .pebble) (X := .empty)
    (Or.inl ⟨rfl, rfl⟩) (g := scp) (fun _ => scp_zero) (L' + 1) [] _
    (by simp only [List.length_nil]; omega) hQ1
  have hpk2 : pcPat (glue .pebble (L' + 1) scp) (j + (L' + 1)) ≤ budget + 1 := by
    have h1 := pcPat_glue_peb scp j (L' + 1)
    rw [pcPat_scp_pos hj1] at h1
    have : 2 ^ (L' + 1) * (1 + 1) = 2 * 2 ^ (L' + 1) := by ring
    omega
  have hQ2' : Pat (glue .pebble (L' + 1) scp) (j + L' + 1) [] _ := hQ2
  obtain ⟨hr2, hA0, hA1⟩ := Pat_succ.mp hQ2'
  rw [glue_succ_zero] at hr2
  rw [glue_succ_shift] at hA0 hA1
  simp only [List.nil_append] at hA0 hA1
  -- 3. 根を残して内部を外す
  have hX : pcPat (glue .pebble L' scp) (j + L') + 1 = 2 * 2 ^ L' := by
    have h1 := pcPat_glue_peb scp j L'
    rw [pcPat_scp_pos hj1] at h1
    rw [h1]; ring
  obtain ⟨hR3, hr3, hB0, hB1⟩ := runs_two (h := j + L' + 1) (k := j + L')
    (p := pcPat (glue .pebble L' scp) (j + L')) (q := pcPat (glue .pebble L' scp) (j + L'))
    (F := glue .pebble L' scp) (G := glue .empty L' scp) hr2 hA0 hA1
    (fun c' hP => removeInt_spec (h := j + L' + 1) (j := j) (g := scp) (fun _ => scp_zero) L'
      [false] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (fun c' hP => removeInt_spec (h := j + L' + 1) (j := j) (g := scp) (fun _ => scp_zero) L'
      [true] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    le_rfl (pcPat_glue_le .empty scp _ L')
  -- 4. 前線をゴーストにする
  have hE1 : pcPat (glue .empty L' scp) (j + L') = 2 ^ L' := by
    rw [pcPat_glue_ne (by decide) scp j L', pcPat_scp_pos hj1, mul_one]
  have hE2 : pcPat (glue .empty L' (cst .ghost)) (j + L') = 0 := by
    rw [pcPat_glue_ne (by decide) _ j L', pcPat_cst (X := .ghost) (by decide), mul_zero]
  obtain ⟨hR4, hr4, hC0, hC1⟩ := runs_two (h := j + L' + 1) (k := j + L')
    (p := 0 + (2 ^ L' - 1) * (1 + 0)) (q := 2 ^ L')
    (F := glue .empty L' scp) (G := glue .empty L' (cst .ghost)) hr3 hB0 hB1
    (fun c' hP => onFront_spec (h := j + L' + 1) (j := j) (p := 0) (w := 1) (e := 0)
      (ci := .empty) (g0 := scp) (g1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
      (fun a c'' ha hPa => ghostRoot_spec hj1 a c'' ha hPa)
      (le_of_eq (pcPat_scp_pos hj1)) (by rw [pcPat_cst (X := .ghost) (by decide)]; omega)
      (by decide) L' [false] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (fun c' hP => onFront_spec (h := j + L' + 1) (j := j) (p := 0) (w := 1) (e := 0)
      (ci := .empty) (g0 := scp) (g1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
      (fun a c'' ha hPa => ghostRoot_spec hj1 a c'' ha hPa)
      (le_of_eq (pcPat_scp_pos hj1)) (by rw [pcPat_cst (X := .ghost) (by decide)]; omega)
      (by decide) L' [true] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (le_of_eq hE1) (by rw [hE2]; exact Nat.zero_le _)
  -- 5. 前線の各頂点の部分木を空にする
  have hE3 : pcPat (glue .empty L' (cst .empty)) (j + L') = 0 := by
    rw [glue_cst, pcPat_cst (X := .empty) (by decide)]
  have hblk : ∀ (a : Node) (c'' : Config), a.length + j = j + L' + 1 →
      Pat (cst .ghost) j a c'' →
      Runs (j + L' + 1) j a budget c'' (block budget (L' + 1) j j a) ∧
        Pat (cst .empty) j a (run c'' (block budget (L' + 1) j j a)) :=
    fun a c'' ha hPa => block_spec_cap (h := j + L' + 1) (budget := budget) (Λ := L' + 1)
      hΛ hcap j j a c'' le_rfl hj1 ha hjb hPa
  obtain ⟨hR5, hr5, hD0, hD1⟩ := runs_two (h := j + L' + 1) (k := j + L')
    (p := budget + (2 ^ L' - 1) * (0 + 0)) (q := 0)
    (F := glue .empty L' (cst .ghost)) (G := glue .empty L' (cst .empty)) hr4 hC0 hC1
    (fun c' hP => onFront_spec (h := j + L' + 1) (j := j) (p := budget) (w := 0) (e := 0)
      (ci := .empty) (g0 := cst .ghost) (g1 := cst .empty) (f := block budget (L' + 1) j j)
      hblk (le_of_eq (pcPat_cst (X := .ghost) (by decide) j))
      (le_of_eq (pcPat_cst (X := .empty) (by decide) j))
      (by decide) L' [false] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (fun c' hP => onFront_spec (h := j + L' + 1) (j := j) (p := budget) (w := 0) (e := 0)
      (ci := .empty) (g0 := cst .ghost) (g1 := cst .empty) (f := block budget (L' + 1) j j)
      hblk (le_of_eq (pcPat_cst (X := .ghost) (by decide) j))
      (le_of_eq (pcPat_cst (X := .empty) (by decide) j))
      (by decide) L' [true] c' (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (le_of_eq hE2) (le_of_eq hE3)
  rw [glue_cst] at hD0 hD1
  -- ペブル数の上限
  have hpk1 : j + 1 + (2 ^ (L' + 1) - 1) * (1 + 0) ≤ budget + 1 := by omega
  have hpk3 : pcPat (glue .pebble L' scp) (j + L') + (1 + pcPat (glue .pebble L' scp) (j + L'))
      ≤ budget + 1 := by omega
  have hpk4 : 0 + (2 ^ L' - 1) * (1 + 0) + (1 + 2 ^ L') ≤ budget + 1 := by omega
  have hpk5 : budget + (2 ^ L' - 1) * (0 + 0) + (1 + 0) ≤ budget + 1 := by simp
  have hR3' := hR3.mono hpk3
  have hR4' := hR4.mono hpk4
  have hR5' := hR5.mono hpk5
  simp only [Runs_append, run_append] at hR3' hR4' hR5' hr5 hD0 hD1
  refine ⟨?_, ?_, ?_⟩
  · simp only [Runs_append, run_append, and_assoc]
    exact ⟨hR1.mono hpk1, hR2.mono hpk2, hR3'.1, hR3'.2, hR4'.1, hR4'.2, hR5'.1, hR5'.2⟩
  · simp only [run_append]
    exact hr5
  · intro z hz hne
    simp only [run_append]
    match z, hz, hne with
    | [], _, hne => exact absurd rfl hne
    | false :: w, hz, _ => exact hD0 w (by simp only [List.length_cons] at hz; omega)
    | true :: w, hz, _ => exact hD1 w (by simp only [List.length_cons] at hz; omega)

/-! ## 手数 -/

/-- ブロックの数の細かい上界: 深さが十分なら（幅がずっと `Λ`）、`nb ≤ ⌊(k−2)/Λ⌋ + 1`。 -/
theorem nb_le_step {budget Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ (n k : ℕ), 2 ^ Λ ≤ budget - k → nb budget Λ n k ≤ (k - 2) / Λ + 1 := by
  intro n
  induction n with
  | zero => intro k _; simp [nb]
  | succ n ih =>
    intro k hk
    rw [nb]
    split_ifs with hfin
    · exact Nat.le_add_left 1 _
    · have hbl : blockLen budget Λ k = Λ := by
        unfold blockLen; rw [if_neg (by omega)]
      rw [hbl]
      have h1 := ih (k - Λ) (by omega)
      have hdiv : (k - 2) / Λ = (k - Λ - 2) / Λ + 1 := by
        rw [Nat.div_eq_sub_div (by omega) (by omega), show k - 2 - Λ = k - Λ - 2 by omega]
      generalize (k - Λ - 2) / Λ = q1 at h1 hdiv
      generalize (k - 2) / Λ = q at hdiv ⊢
      omega

/-- **手数.** `1 ≤ Λ < h`、`2^(Λ+1) ≤ budget + 1`、`2^Λ ≤ budget − (h − Λ)` なら、
ペブル `budget + 1` 個で `T + 3 ≤ 2 (⌊(h−1)/Λ⌋ + 1) · 2^h`（`= 2⌈h/Λ⌉ · 2^h`）の妥当な手順がある。 -/
theorem time_upper_bound_step {h budget Λ : ℕ} (hΛ : 1 ≤ Λ) (hΛh : Λ < h)
    (hcap : 2 ^ (Λ + 1) ≤ budget + 1) (hstart : 2 ^ Λ ≤ budget - (h - Λ)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (budget + 1) T ms ∧
      T + 3 ≤ 2 * ((h - 1) / Λ + 1) * 2 ^ h := by
  have h2Λ : 2 ≤ 2 ^ Λ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Λ := Nat.pow_le_pow_right (by norm_num) hΛ
  obtain ⟨hR, hroot, hothers⟩ := strategy_step_spec hΛ hΛh hcap (by omega)
  refine ⟨(strategyStep h budget Λ).length, seqOf (strategyStep h budget Λ),
    valid_of_runs hR hroot hothers, ?_⟩
  obtain ⟨L', rfl⟩ : ∃ L', Λ = L' + 1 := ⟨Λ - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, h = j + L' + 1 := ⟨h - (L' + 1), by omega⟩
  have hj1 : 1 ≤ j := by omega
  have hjsub : j + L' + 1 - (L' + 1) = j := by omega
  rw [hjsub] at hstart
  simp only [strategyStep, hjsub, Nat.add_sub_cancel, List.length_append]
  -- 各部分の手数
  have hB : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ j * 2 = M + 3 := ⟨2 ^ j * 2 - 3, by omega⟩
  have hc : ∀ a, (compute Op.pebble j a).length ≤ M := fun a => by
    have := length_compute .pebble j a hj1
    rw [pow_succ] at this
    omega
  have e1 := length_onFront_le hc (L' + 1) []
  have e2 := length_placeInt .pebble (L' + 1) []
  have e3 := length_removeInt L' [false]
  have e3' := length_removeInt L' [true]
  have e4 := length_onFront_le (f := fun a => [⟨Op.ghost, a⟩]) (N := 1) (fun a => by simp) (L' + 1) []
  have e5 := length_onFront_le (fun a => length_block_le (h := budget) hΛ j j a) (L' + 1) []
  -- ブロックの数
  have hnb := nb_le_step (budget := budget) hΛ j j hstart
  have hdiv : (j + L') / (L' + 1) = (j - 1) / (L' + 1) + 1 := by
    rw [Nat.div_eq_sub_div (by omega) (by omega), show j + L' - (L' + 1) = j - 1 by omega]
  have hmono : (j - 2) / (L' + 1) ≤ (j - 1) / (L' + 1) := Nat.div_le_div_right (by omega)
  have hnbD : nb budget (L' + 1) j j ≤ (j + L') / (L' + 1) := by omega
  generalize nb budget (L' + 1) j j = N at e5 hnbD
  generalize (j + L') / (L' + 1) = D at hnbD ⊢
  -- 算術
  have hP : 2 ^ (L' + 1) = 2 * 2 ^ L' := by rw [pow_succ]; ring
  have hH : 2 ^ (j + L' + 1) = 2 * (2 ^ L' * 2 ^ j) := by rw [pow_succ, pow_add]; ring
  rw [hH]
  rw [hP] at e1 e2 e4 e5
  have hP1 : 1 ≤ 2 ^ L' := Nat.one_le_two_pow
  generalize 2 ^ L' = P at e1 e2 e3 e3' e4 e5 hP1 ⊢
  generalize 2 ^ j = Q at e5 hM hB ⊢
  have hND : P * Q * N ≤ P * Q * D := Nat.mul_le_mul_left _ hnbD
  have e5' : (onFront (block budget (L' + 1) j j) (L' + 1) []).length ≤ 4 * (P * Q * N) := by
    calc _ ≤ 2 * P * (2 * N * Q) := e5
      _ = 4 * (P * Q * N) := by ring
  have e1' : (onFront (compute Op.pebble j) (L' + 1) []).length + 6 * P ≤ 4 * (P * Q) := by
    have : 2 * P * M + 6 * P = 4 * (P * Q) := by
      have h' : 2 * P * (Q * 2) = 2 * P * (M + 3) := by rw [hM]
      linarith
    omega
  have hgoal : 2 * (D + 1) * (2 * (P * Q)) = 4 * (P * Q * D) + 4 * (P * Q) := by ring
  rw [hgoal]
  omega

/-- **手数（KSS の意味論）.** 同じ手順を KSS の意味論の手順に直したもの。 -/
theorem time_upper_bound_step_kss {h budget Λ : ℕ} (hΛ : 1 ≤ Λ) (hΛh : Λ < h)
    (hcap : 2 ^ (Λ + 1) ≤ budget + 1) (hstart : 2 ^ Λ ≤ budget - (h - Λ)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h (budget + 1) T ms ∧
      T + 3 ≤ 2 * ((h - 1) / Λ + 1) * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_step hΛ hΛh hcap hstart
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

end SpookyTree
