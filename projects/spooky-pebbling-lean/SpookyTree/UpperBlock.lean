/-
# 上界の本体: ブロックの手順とその仕様・手数

ブロック根 `y`（高さ `k`、深さ `h − k ≥ 1`）について、`T(y)` が全部ゴーストの配置から全部空の配置へ移す手順 `block`。
木全体の根はペブルのまま外にあるので、`T(y)` の中で使えるペブルは `h` 個。

ブロックの幅 `L` は 2 通りだけ使う（パラメータ `Λ ≥ 1`、`2^(Λ+1) ≤ h + 1`）:
* 高さ `k ≤ Λ + 1` なら最下段: `T(y)` を全部置いて（`2^k − 1 ≤ h` 個）、上から全部 unpebble する。
* 深さ `h − k < 2^Λ` なら `L = 1`、そうでなければ `L = Λ`。
  1. 前線（`L` 段下の `2^L` 個）を左から順に計算して持つ（ペブルは `2^L − 1 + (k − L + 1)` 個以下）
  2. 内部を全部置く（`2^(L+1) − 1` 個）
  3. 内部を上から全部 unpebble する（跡を残さない）
  4. 前線を全部 ghost にする
  5. 前線の各頂点について、同じ手順を繰り返す

置く手の数は、`T(y)` の各頂点につき「その頂点の上にあるブロック根の数」。
-/
import SpookyTree.UpperProg

namespace SpookyTree

theorem pcPat_scp_pos {j : ℕ} (hj : 1 ≤ j) : pcPat scp j = 1 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact pcPat_scp j'

/-- ブロックの幅: 深さ `h − k` が `2^Λ` 未満なら 1、そうでなければ `Λ`。 -/
def blockLen (h Λ k : ℕ) : ℕ := if h - k < 2 ^ Λ then 1 else Λ

theorem blockLen_pos {h Λ k : ℕ} (hΛ : 1 ≤ Λ) : 1 ≤ blockLen h Λ k := by
  unfold blockLen; split_ifs <;> omega

theorem blockLen_le {h Λ k : ℕ} (hΛ : 1 ≤ Λ) : blockLen h Λ k ≤ Λ := by
  unfold blockLen; split_ifs <;> omega

/-- 高さ `k` のブロック根 `y`（`T(y)` は全部ゴースト）を空にする手順。第 1 引数は再帰の燃料。 -/
def block (h Λ : ℕ) : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | n + 1, k, y =>
    if k ≤ Λ + 1 then placeInt .unghost k y ++ removeInt k y
    else
      onFront (compute .unghost (k - blockLen h Λ k)) (blockLen h Λ k) y ++
        placeInt .unghost (blockLen h Λ k) y ++ removeInt (blockLen h Λ k) y ++
        onFront (fun a => [⟨.ghost, a⟩]) (blockLen h Λ k) y ++
        onFront (block h Λ n (k - blockLen h Λ k)) (blockLen h Λ k) y

/-- **ブロックの仕様.** 深さ 1 以上のブロック根 `y`（高さ `k`）の `T(y)` が全部ゴーストなら、`block` は合法で、
`T(y)` 内のペブル数は `h` 以下、終わると `T(y)` は全部空。 -/
theorem block_spec {h Λ : ℕ} (hΛ : 1 ≤ Λ) (hcap : 2 ^ (Λ + 1) ≤ h + 1) :
    ∀ (n k : ℕ) (y : Node) (c : Config), k ≤ n → 1 ≤ k → y.length + k = h → 1 ≤ y.length →
      Pat (cst .ghost) k y c →
      Runs h k y h c (block h Λ n k y) ∧ Pat (cst .empty) k y (run c (block h Λ n k y)) := by
  intro n
  induction n with
  | zero => intro k y c hkn hk; omega
  | succ n ih =>
    intro k y c hkn hk hy hd hP
    by_cases hfin : k ≤ Λ + 1
    · -- 最下段のブロック: 全部置いて、上から全部外す
      have hblock : block h Λ (n + 1) k y = placeInt .unghost k y ++ removeInt k y := by
        rw [block, if_pos hfin]
      rw [hblock]
      have hP' : Pat (glue .ghost k (cst .ghost)) (0 + k) y c := by
        rw [glue_cst, Nat.zero_add]; exact hP
      obtain ⟨hR1, hQ1⟩ := placeInt_spec (h := h) (j := 0) (pl := .unghost) (X := .ghost)
        (Or.inr ⟨rfl, rfl⟩) (g := cst .ghost) (fun h0 => absurd h0 (by decide)) k y c
        (by omega) hP'
      obtain ⟨hR2, hQ2⟩ := removeInt_spec (h := h) (j := 0) (g := cst .ghost)
        (fun h0 => absurd h0 (by decide)) k y _ (by omega) hQ1
      have hpk : pcPat (glue Cell.pebble k (cst Cell.ghost)) (0 + k) ≤ h := by
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
      obtain ⟨L, hLdef⟩ : ∃ L, L = blockLen h Λ k := ⟨_, rfl⟩
      have hL1 : 1 ≤ L := by rw [hLdef]; exact blockLen_pos hΛ
      have hLΛ : L ≤ Λ := by rw [hLdef]; exact blockLen_le hΛ
      have hcond : L = 1 ∨ 2 ^ Λ ≤ h - k := by
        rw [hLdef]; unfold blockLen
        split_ifs with hc
        · exact Or.inl rfl
        · exact Or.inr (by omega)
      have hblock : block h Λ (n + 1) k y =
          onFront (compute .unghost (k - L)) L y ++ placeInt .unghost L y ++ removeInt L y ++
            onFront (fun a => [⟨.ghost, a⟩]) L y ++ onFront (block h Λ n (k - L)) L y := by
        rw [block, if_neg hfin, ← hLdef]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + L := ⟨k - L, by omega⟩
      have hjL : j + L - L = j := by omega
      rw [hjL] at hblock
      rw [hblock]
      have hj1 : 1 ≤ j := by omega
      have h2L : 2 ^ L ≤ 2 ^ Λ := Nat.pow_le_pow_right (by norm_num) hLΛ
      have h2L1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have h2Λ : 2 ^ (Λ + 1) = 2 * 2 ^ Λ := by rw [pow_succ]; ring
      have hA : 2 ^ L + j ≤ h := by
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
      obtain ⟨hR5, hQ5⟩ := onFront_spec (j := j) (p := h) (w := 0) (e := 0) (ci := .empty)
        (g0 := cst .ghost) (g1 := cst .empty) (f := block h Λ n j)
        (fun a c' ha hPa => ih j a c' (by omega) hj1 ha (by omega) hPa)
        (le_of_eq (pcPat_cst (X := .ghost) (by decide) j))
        (le_of_eq (pcPat_cst (X := .empty) (by decide) j))
        (by decide) L y _ hy hQ4
      -- ペブル数の上限
      have hpk1 : j + 1 + (2 ^ L - 1) * (1 + 0) ≤ h := by omega
      have hpk2 : pcPat (glue Cell.pebble L scp) (j + L) ≤ h := by
        have h1 := pcPat_glue_peb scp j L
        rw [pcPat_scp_pos hj1] at h1
        omega
      have hpk4 : 0 + (2 ^ L - 1) * (1 + 0) ≤ h := by omega
      have hpk5 : h + (2 ^ L - 1) * (0 + 0) ≤ h := by omega
      refine ⟨?_, ?_⟩
      · simp only [Runs_append, run_append]
        exact ⟨⟨⟨⟨hR1.mono hpk1, hR2.mono hpk2⟩, hR3.mono hpk2⟩, hR4.mono hpk4⟩, hR5.mono hpk5⟩
      · simp only [run_append]
        rw [glue_cst] at hQ5
        exact hQ5

/-! ## 手数 -/

theorem length_onFront_le {f : Node → List Move} {N : ℕ} (hf : ∀ a, (f a).length ≤ N) :
    ∀ (L : ℕ) (y : Node), (onFront f L y).length ≤ 2 ^ L * N := by
  intro L
  induction L with
  | zero => intro y; simpa [onFront] using hf y
  | succ L ih =>
    intro y
    rw [onFront, List.length_append, pow_succ]
    have h0 := ih (y ++ [false])
    have h1 := ih (y ++ [true])
    linarith

theorem length_placeInt (pl : Op) :
    ∀ (L : ℕ) (y : Node), (placeInt pl L y).length + 1 = 2 ^ L := by
  intro L
  induction L with
  | zero => intro y; simp [placeInt]
  | succ L ih =>
    intro y
    have h0 := ih (y ++ [false])
    have h1 := ih (y ++ [true])
    simp only [placeInt, List.length_append, List.length_cons, List.length_nil, pow_succ]
    omega

theorem length_removeInt : ∀ (L : ℕ) (y : Node), (removeInt L y).length + 1 = 2 ^ L := by
  intro L
  induction L with
  | zero => intro y; simp [removeInt]
  | succ L ih =>
    intro y
    have h0 := ih (y ++ [false])
    have h1 := ih (y ++ [true])
    simp only [removeInt, List.length_append, List.length_cons, pow_succ]
    omega

theorem length_compute (pl : Op) :
    ∀ (k : ℕ) (y : Node), 1 ≤ k → (compute pl k y).length + 3 = 2 ^ (k + 1)
  | 0, _, hk => absurd hk (by decide)
  | 1, y, _ => by simp [compute, placeInt]
  | k + 2, y, _ => by
    have h0 : (compute pl (k + 1) (y ++ [false])).length + 3 = 2 ^ (k + 2) :=
      length_compute pl (k + 1) (y ++ [false]) (by omega)
    have h1 : (compute pl (k + 1) (y ++ [true])).length + 3 = 2 ^ (k + 2) :=
      length_compute pl (k + 1) (y ++ [true]) (by omega)
    simp only [compute, onFront, placeInt, List.length_append, List.length_cons, List.length_nil]
    rw [pow_succ]
    omega

/-- 高さ `k` から下に向かって数えたブロックの数。第 1 引数は燃料（`block` と同じ再帰）。 -/
def nb (h Λ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => if k ≤ Λ + 1 then 1 else 1 + nb h Λ n (k - blockLen h Λ k)

/-- ブロックの手数は `2 ·（ブロックの数）· 2^k` 以下。 -/
theorem length_block_le {h Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ (n k : ℕ) (y : Node), (block h Λ n k y).length ≤ 2 * nb h Λ n k * 2 ^ k := by
  intro n
  induction n with
  | zero => intro k y; simp [block]
  | succ n ih =>
    intro k y
    by_cases hfin : k ≤ Λ + 1
    · rw [block, if_pos hfin, nb, if_pos hfin, List.length_append]
      have h1 := length_placeInt .unghost k y
      have h2 := length_removeInt k y
      omega
    · obtain ⟨L, hLdef⟩ : ∃ L, L = blockLen h Λ k := ⟨_, rfl⟩
      have hL1 : 1 ≤ L := by rw [hLdef]; exact blockLen_pos hΛ
      have hLΛ : L ≤ Λ := by rw [hLdef]; exact blockLen_le hΛ
      rw [block, if_neg hfin, nb, if_neg hfin, ← hLdef]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + L := ⟨k - L, by omega⟩
      have hjL : j + L - L = j := by omega
      rw [hjL]
      have hj1 : 1 ≤ j := by omega
      simp only [List.length_append]
      have hB : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      obtain ⟨M, hM⟩ : ∃ M, 2 ^ j * 2 = M + 3 := ⟨2 ^ j * 2 - 3, by omega⟩
      have hc : ∀ a, (compute Op.unghost j a).length ≤ M := fun a => by
        have := length_compute .unghost j a hj1
        rw [pow_succ] at this
        omega
      have e1 := length_onFront_le hc L y
      have e2 := length_placeInt .unghost L y
      have e3 := length_removeInt L y
      have e4 := length_onFront_le (f := fun a => [⟨Op.ghost, a⟩]) (N := 1) (fun a => by simp) L y
      have e5 := length_onFront_le (fun a => ih j a) L y
      have hAM : 2 ^ L * M + 3 * 2 ^ L = 2 * (2 ^ j * 2 ^ L) := by
        have h : 2 ^ L * (2 ^ j * 2) = 2 ^ L * (M + 3) := by rw [hM]
        linarith
      rw [pow_add]
      nlinarith [e1, e2, e3, e4, e5, hAM]

/-- ブロックの数の上界。 -/
theorem nb_le {h Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ (n k : ℕ), k ≤ h → nb h Λ n k ≤ (2 ^ Λ - (h - k)) + k / Λ + 1 := by
  intro n
  induction n with
  | zero => intro k _; simp [nb]
  | succ n ih =>
    intro k hk
    rw [nb]
    split_ifs with hfin
    · exact Nat.le_add_left 1 _
    · unfold blockLen
      split_ifs with hc
      · have h1 := ih (k - 1) (by omega)
        have hdiv : (k - 1) / Λ ≤ k / Λ := Nat.div_le_div_right (by omega)
        generalize (k - 1) / Λ = q1 at h1 hdiv
        generalize k / Λ = q at hdiv ⊢
        omega
      · have h1 := ih (k - Λ) (by omega)
        have hdiv : k / Λ = (k - Λ) / Λ + 1 := Nat.div_eq_sub_div (by omega) (by omega)
        generalize (k - Λ) / Λ = q1 at h1 hdiv
        generalize k / Λ = q at hdiv ⊢
        omega

end SpookyTree
