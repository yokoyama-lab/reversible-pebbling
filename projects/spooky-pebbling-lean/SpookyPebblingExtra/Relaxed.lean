/-
# KSS の緩和漸化式 (1) は、厳密値が分かっている範囲では 1 手も損をしない

Kornerup–Sadun–Soloveichik, *Tight Bounds on the Spooky Pebble Game*, arXiv:2110.08973v3 §4 は、
厳密な漸化式（Cor 4.12: `T_UG(n,s) = min_k [2k-1 + T_UP(k,s) + T_UG(n-k,s-1)]`、
`Unghost.lean` の `decomp_ug_exact`）の頭の項 `T_UP(k,s)` を **`T_UG(k,s) - 1`** に置き換えた
**緩和漸化式**（Cor 4.12 の直後の式 (1)）を解析している:

$$T(n,s) = \begin{cases}
  2 & (s \ge 1 \text{ かつ } n = 1)\\
  \infty & (s < 2 \text{ かつ } s < n)\\
  \min_{k}\ \bigl[\,2k-2 + T(k,s) + T(n-k,\,s-1)\,\bigr] & (\text{それ以外})
\end{cases}$$

Lemma 4.10（`UGvsUP.lean` の `TUG_le_TUP_succ`: `T_UG ≤ T_UP + 1`）により `T ≤ T_UG`、すなわち
(1) は**下界**を与える。緩和なので一般には真に小さくなりうる。

## このファイルが示すこと

`relaxed n s : ℕ∞` を式 (1) そのものとして**関数として定義し**（`⊤` ＝ 不可能）、次を示す。

* **`relaxed_eq_TUG`（主定理）**: `2 ≤ s`・`1 ≤ n`・`n + 1 ≤ B4 s` なら
  **`relaxed n s = T_UG(n,s)`**。すなわち層1 で厳密値が分かっている範囲
  （補題3 の `n ≤ s`、定理B の `s ≤ n ≤ θ(s)`、定理F の `θ(s) ≤ n ≤ B_4(s)-1`）では、
  緩和は 1 手も損をしない。
* **`relaxed_le_TUG`**: `relaxed n s ≤ T_UG(n,s)`（`s ≥ 2`・`n ≥ 1`・無条件。KSS の「(1) は下界」）。
* **`two_mul_le_relaxed`・`relaxed_ge_slope4`・`relaxed_ge_slope6`**: 定理A・D と同じ望遠鏡を
  **`relaxed` の上で**回した下界 `2n`、`4n-2s`、`6n-s(s+3)`（`s ≥ 2`・`n ≥ 1`・無条件）。
  頭に「一段低い傾きの下界」、尻尾に帰納法の仮定を入れると、ここでも `k` が消える:
  `(2k-2) + (4k-2s) + (6(n-k)-(s-1)(s+2)) = 6n - s(s+3)`。
* **`relaxed_cap2`**: `relaxed n 2 = n²-n+2`（尻尾の上限が 1 になり `k = n-1` が強制される）。
* **具体値の検算**（展開補題 3 本だけから手で回したもの。定義が空虚でないことの証拠）:
  `relaxed 3 2 = 8`、`relaxed 4 2 = 14`、`relaxed 8 3 = 30`、`relaxed 9 3 = 36` ほか。
* **`relaxed_lt_TUG_at_B4_two`**: `relaxed 4 2 = 14 < 16 = T_UG(4,2)`。`B_4(2) = 4` なので
  `n = 4` は主定理の範囲の **1 つ外**であり、`s = 2` では範囲 `n + 1 ≤ B4 s` は緩められない
  （`not_relaxed_eq_TUG_at_B4`: 仮定を `n ≤ B4 s` に広げた言明は偽）。

## 定義と KSS の式 (1) との接点

定義は `n` についての整礎再帰（`termination_by n`）なので、そのままでは展開できない。
**式 (1) との照合は次の 3 本の展開補題で行う**（定義と KSS を結ぶ唯一の接点）:

* `relaxed_one : 1 ≤ s → relaxed 1 s = 2`
* `relaxed_top : s < 2 → s < n → relaxed n s = ⊤`
* `relaxed_step : 2 ≤ n → 2 ≤ s → relaxed n s = (Finset.Ico 1 n).inf fun k => …`

`n ≥ 1` のとき、この 3 本の仮定は場合を尽くしている（`n = 1` なら `s ≥ 1` か `s = 0 < n`。
`n ≥ 2` なら `s ≥ 2` か `s < 2 ≤ n`）。

## KSS との違い 2 点

* **`k` の範囲**: KSS は `k ∈ [1, n]` と書くが、`k = n` の項は `T(0, s-1)` を参照し、KSS は
  `T(0,·)` を定義していない。**このファイルでは分解定理（`decomp_ug_exact`）と同じく
  `1 ≤ k < n`（`Finset.Ico 1 n`）とする。**
* **`n = 0` の値**: KSS は定義していない。**ここでは `relaxed 0 s = 0` と置く**（`relaxed_zero`）。
  `1 ≤ k < n` の下では漸化式が `relaxed 0 ·` を参照することは無いので、この選択は `n ≥ 1` の
  値に一切影響しない。主定理を含め、以下の主張はすべて `n ≥ 1` に限る。

## 示していないこと

* **「`B_4(s)` より先では必ず損をする」は `s = 2` の 1 点（`n = 4`）以外は未証明。**
  リポジトリ外の数値実験（Python の DP、`s = 2..7`・`n ≤ 140`。**このファイルでは再現して
  いない**）では「一致する最大の `n`」がちょうど `B_4(s) - 1 = 3, 8, 17, 31, 51, 78` だが、
  `s ≥ 3` では `T_UG(B_4(s), s)` の厳密値が Lean に載っていないので、ここでは主張しない。
* `relaxed` の閉形式（数値上は `max_m (2mn - c_m(s))`）は `s = 2` の行（`relaxed_cap2`）以外
  示していない。

## 層

一般証明（無条件）。有界の全数検査には頼らない。具体値の検算は展開補題からの等式変形で、
定義の簡約（`decide`）にも依らない。

## 置き場所

このファイルは `SpookyPebbling` ライブラリの外（`SpookyPebblingExtra`）に置く。本体ライブラリの
モジュール数・行数は原稿側の検査器が凍結値と照合しているため、本体には足さない。
ビルドは `lake build SpookyPebblingExtra`。
-/
import SpookyPebbling.Slope6Exact
import SpookyPebbling.Cap2Exact

namespace Spooky

/-! ## 定義 -/

/-- **KSS の緩和漸化式 (1)**（arXiv:2110.08973v3 §4、Cor 4.12 の直後）。値域は `ℕ∞` で、
`⊤` は「不可能」。

* 第 1 節 `s ≥ 1` かつ `n = 1` → `2`
* 第 2 節 `s < 2` かつ `s < n` → `⊤`
* 第 3 節 それ以外 → `min_{1 ≤ k < n} [2k-2 + T(k,s) + T(n-k,s-1)]`

**`k` の範囲は KSS の `[1,n]` ではなく `1 ≤ k < n`**（`k = n` は未定義の `T(0,·)` を参照する）。
**`n = 0` は KSS が定義していないので `0` を返す**（漸化式からは参照されない）。

整礎再帰なので直接は展開できない。`relaxed_one`・`relaxed_top`・`relaxed_step` を使う。 -/
noncomputable def relaxed (n s : ℕ) : ℕ∞ :=
  if n = 0 then 0
  else if n = 1 ∧ 1 ≤ s then 2
  else if s < 2 ∧ s < n then ⊤
  else (Finset.Ico 1 n).attach.inf fun k =>
    ((2 * k.1 - 2 : ℕ) : ℕ∞) + relaxed k.1 s + relaxed (n - k.1) (s - 1)
termination_by n
decreasing_by
  · exact (Finset.mem_Ico.mp k.2).2
  · have := Finset.mem_Ico.mp k.2
    omega

/-! ## 展開補題（定義と KSS の式 (1) を結ぶ唯一の接点） -/

/-- `n = 0` は KSS が定義していない。ここでは `0` と置く（漸化式からは参照されない）。 -/
theorem relaxed_zero (s : ℕ) : relaxed 0 s = 0 := by
  rw [relaxed, if_pos rfl]

/-- **式 (1) 第 1 節**: `s ≥ 1` かつ `n = 1` なら `2`。 -/
theorem relaxed_one {s : ℕ} (hs : 1 ≤ s) : relaxed 1 s = 2 := by
  rw [relaxed, if_neg (by omega), if_pos ⟨rfl, hs⟩]

/-- **式 (1) 第 2 節**: `s < 2` かつ `s < n` なら `∞`。 -/
theorem relaxed_top {n s : ℕ} (hs : s < 2) (hn : s < n) : relaxed n s = ⊤ := by
  rw [relaxed, if_neg (by omega), if_neg (by omega), if_pos ⟨hs, hn⟩]

/-- **式 (1) 第 3 節**: `n ≥ 2`・`s ≥ 2` なら `1 ≤ k < n` にわたる最小値。 -/
theorem relaxed_step {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s) :
    relaxed n s = (Finset.Ico 1 n).inf fun k =>
      ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1) := by
  rw [relaxed, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact Finset.inf_attach (Finset.Ico 1 n) fun k =>
    ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1)

/-! ## 最小値の出し入れ -/

/-- どの `k`（`1 ≤ k < n`）の項も上界を与える。 -/
theorem relaxed_le_term {n s k : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s) (hk : 1 ≤ k) (hkn : k < n) :
    relaxed n s ≤ ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1) := by
  rw [relaxed_step hn hs]
  exact Finset.inf_le (Finset.mem_Ico.mpr ⟨hk, hkn⟩)

/-- すべての `k`（`1 ≤ k < n`）の項の下界は `relaxed n s` の下界。 -/
theorem le_relaxed {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s) {a : ℕ∞}
    (h : ∀ k, 1 ≤ k → k < n →
      a ≤ ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1)) :
    a ≤ relaxed n s := by
  rw [relaxed_step hn hs]
  exact Finset.le_inf fun k hk => h k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2

/-- 最小値はある `k` で達成される（添字集合 `Ico 1 n` は `n ≥ 2` で空でない）。 -/
theorem relaxed_step_attained {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s) :
    ∃ k, 1 ≤ k ∧ k < n ∧
      relaxed n s = ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1) := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf (Finset.Ico 1 n)
    ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    (fun k => ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1))
  exact ⟨k, (Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2, by
    rw [relaxed_step hn hs]; exact hkeq⟩

/-- 式 (1) を 1 段だけ回して値を決める形: `k₀` の項が `v` で、どの `k` の項も `v` 以上。 -/
theorem relaxed_eq_of {n s : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ s) {v : ℕ∞} (k₀ : ℕ)
    (hk₀ : 1 ≤ k₀) (hk₀n : k₀ < n)
    (hv : ((2 * k₀ - 2 : ℕ) : ℕ∞) + relaxed k₀ s + relaxed (n - k₀) (s - 1) = v)
    (hall : ∀ k, 1 ≤ k → k < n →
      v ≤ ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k s + relaxed (n - k) (s - 1)) :
    relaxed n s = v :=
  le_antisymm (hv ▸ relaxed_le_term hn hs hk₀ hk₀n) (le_relaxed hn hs hall)

/-! ## 上限 2 の行の閉形式 `relaxed n 2 = n² - n + 2`

尻尾の上限が 1 になるので、`n - k ≥ 2` の項はすべて `⊤`（式 (1) 第 2 節）。
**`k = n-1` だけが有限**で、`(2n-4) + relaxed (n-1) 2 + 2`。 -/

theorem relaxed_cap2 : ∀ n, 1 ≤ n → relaxed n 2 = ((n * n - n + 2 : ℕ) : ℕ∞) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [relaxed_one (by omega)]
      norm_num
    · have hterm : ((2 * (n - 1) - 2 : ℕ) : ℕ∞) + relaxed (n - 1) 2
          + relaxed (n - (n - 1)) (2 - 1) = ((n * n - n + 2 : ℕ) : ℕ∞) := by
        rw [ih (n - 1) (by omega) (by omega), show n - (n - 1) = 1 by omega,
          relaxed_one (by omega)]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        have h1 : m + 2 - 1 = m + 1 := by omega
        have hA : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
        have hB : (m + 2) * (m + 2) = m * m + 4 * m + 4 := by ring
        rw [h1]
        norm_cast
        omega
      refine relaxed_eq_of hge le_rfl (n - 1) (by omega) (by omega) hterm ?_
      intro k hk hkn
      rcases Nat.lt_or_ge k (n - 1) with h | h
      · rw [relaxed_top (n := n - k) (s := 2 - 1) (by omega) (by omega)]
        simp
      · have hk1 : k = n - 1 := by omega
        subst hk1
        rw [hterm]

/-! ## (A) `relaxed ≤ T_UG` — KSS の「(1) は下界」 -/

/-- (A) の基底（`s = 2`）。両辺とも閉形式がある: `n²-n+2 ≤ n²+n-4`（`n ≥ 3`）。 -/
theorem relaxed_le_TUG_two {n : ℕ} (hn : 1 ≤ n) : relaxed n 2 ≤ (TUG n 2 : ℕ∞) := by
  rw [relaxed_cap2 n hn]
  norm_cast
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · rw [TUG_eq_of_le' (n := n) (s := 2) hn (by omega)]
    interval_cases n <;> norm_num
  · have h := TUG_cap2 hge
    have hsq : n ≤ n * n := Nat.le_mul_self n
    omega

/-- **(A)**: `relaxed n s ≤ T_UG(n,s)`（`s ≥ 2`・すべての `n ≥ 1`・無条件）。

Cor 4.12 の等号を与える `k` を取り、頭の `T_UP(k,s)` を Lemma 4.10 で `T_UG(k,s) - 1` 以上に
置き換える。`relaxed` は `min` なので、その `k` の項で上から押さえられる。 -/
theorem relaxed_le_TUG {s : ℕ} (hs : 2 ≤ s) : ∀ n, 1 ≤ n → relaxed n s ≤ (TUG n s : ℕ∞) := by
  induction s, hs using Nat.le_induction with
  | base => exact fun n hn => relaxed_le_TUG_two hn
  | succ s hs ih =>
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
        intro hn
        rcases Nat.lt_or_ge n 2 with hlt | hge
        · have hn1 : n = 1 := by omega
          subst hn1
          rw [relaxed_one (by omega), TUG_eq_of_le' le_rfl (by omega)]
          norm_num
        · obtain ⟨⟨k, hk, hkn, hkeq⟩, -⟩ :=
            decomp_ug_exact (n := n) (s := s + 1) (by omega) hge
          have h1 := relaxed_le_term (n := n) (s := s + 1) (k := k) hge (by omega) hk hkn
          have h2 : relaxed k (s + 1) ≤ (TUG k (s + 1) : ℕ∞) := ihn k hkn hk
          have h3 : relaxed (n - k) s ≤ (TUG (n - k) s : ℕ∞) := ih (n - k) (by omega)
          have h4 := TUG_le_TUP_succ (n := k) (s := s + 1) hk
            (UPLengths_nonempty (by omega) hk)
          rw [Nat.add_sub_cancel] at h1 hkeq
          calc relaxed n (s + 1)
              ≤ ((2 * k - 2 : ℕ) : ℕ∞) + relaxed k (s + 1) + relaxed (n - k) s := h1
            _ ≤ ((2 * k - 2 : ℕ) : ℕ∞) + (TUG k (s + 1) : ℕ∞) + (TUG (n - k) s : ℕ∞) :=
                add_le_add (add_le_add le_rfl h2) h3
            _ ≤ (TUG n (s + 1) : ℕ∞) := by
                norm_cast
                omega

/-- `s ≥ 2`・`n ≥ 1` では `relaxed` は有限。 -/
theorem relaxed_ne_top {n s : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : relaxed n s ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (relaxed_le_TUG hs n hn)

/-! ## (B) 下界の望遠鏡を `relaxed` の上で回す

`ℕ∞` の上の算術は、`⊤` なら自明、有限なら `ℕ` に落として `omega`、の 2 通りに割る。 -/

private theorem tele2 {a b : ℕ∞} {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (ha : ((2 * k : ℕ) : ℕ∞) ≤ a) (hb : ((2 * (n - k) : ℕ) : ℕ∞) ≤ b) :
    ((2 * n : ℕ) : ℕ∞) ≤ ((2 * k - 2 : ℕ) : ℕ∞) + a + b := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b =>
      norm_cast at ha hb ⊢
      omega

private theorem tele4 {a b : ℕ∞} {n k s : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (ha : ((2 * k : ℕ) : ℕ∞) ≤ a)
    (hb : ((4 * (n - k) : ℕ) : ℕ∞) ≤ b + ((2 * s : ℕ) : ℕ∞)) :
    ((4 * n : ℕ) : ℕ∞) ≤ ((2 * k - 2 : ℕ) : ℕ∞) + a + b + ((2 * (s + 1) : ℕ) : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b =>
      norm_cast at ha hb ⊢
      omega

private theorem tele6 {a b : ℕ∞} {n k s : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (ha : ((4 * k : ℕ) : ℕ∞) ≤ a + ((2 * (s + 1) : ℕ) : ℕ∞))
    (hb : ((6 * (n - k) : ℕ) : ℕ∞) ≤ b + ((s * (s + 3) : ℕ) : ℕ∞)) :
    ((6 * n : ℕ) : ℕ∞) ≤
      ((2 * k - 2 : ℕ) : ℕ∞) + a + b + (((s + 1) * (s + 1 + 3) : ℕ) : ℕ∞) := by
  have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * s + 4 := by ring
  induction a using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b =>
      norm_cast at ha hb ⊢
      omega

/-- **傾き 2 の下界**: `relaxed n s ≥ 2n`（`s ≥ 2`・すべての `n ≥ 1`・無条件）。 -/
theorem two_mul_le_relaxed {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, 1 ≤ n → ((2 * n : ℕ) : ℕ∞) ≤ relaxed n s := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn
      rw [relaxed_cap2 n hn]
      norm_cast
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hA : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      have hsq : m ≤ m * m := Nat.le_mul_self m
      omega
  | succ s hs ih =>
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
        intro hn
        rcases Nat.lt_or_ge n 2 with hlt | hge
        · have hn1 : n = 1 := by omega
          subst hn1
          rw [relaxed_one (by omega)]
          norm_num
        · refine le_relaxed hge (by omega) fun k hk hkn => ?_
          rw [Nat.add_sub_cancel]
          exact tele2 hk hkn (ihn k hkn hk) (ih (n - k) (by omega))

/-- **傾き 4 の下界**（定理A の `relaxed` 版）: `relaxed n s ≥ 4n - 2s`。
頭に傾き 2 の下界、尻尾に帰納法の仮定: `(2k-2) + 2k + (4(n-k) - 2(s-1)) = 4n - 2s`。 -/
theorem relaxed_ge_slope4 {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, 1 ≤ n → ((4 * n : ℕ) : ℕ∞) ≤ relaxed n s + ((2 * s : ℕ) : ℕ∞) := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn
      rw [relaxed_cap2 n hn]
      norm_cast
      rcases Nat.lt_or_ge n 3 with hlt | hge
      · interval_cases n <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
        have hA : (m + 3) * (m + 3) = m * m + 6 * m + 9 := by ring
        omega
  | succ s hs ih =>
      intro n hn
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := by omega
        subst hn1
        rw [relaxed_one (by omega)]
        norm_cast
        omega
      · obtain ⟨k, hk, hkn, hkeq⟩ := relaxed_step_attained (n := n) (s := s + 1) hge (by omega)
        rw [hkeq, Nat.add_sub_cancel]
        exact tele4 hk hkn (two_mul_le_relaxed (by omega) k hk) (ih (n - k) (by omega))

/-- **傾き 6 の下界**（定理D の `relaxed` 版）: `relaxed n s ≥ 6n - s(s+3)`。
頭に傾き 4 の下界、尻尾に帰納法の仮定:
`(2k-2) + (4k-2s) + (6(n-k) - (s-1)(s+2)) = 6n - s(s+3)`。 -/
theorem relaxed_ge_slope6 {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, 1 ≤ n → ((6 * n : ℕ) : ℕ∞) ≤ relaxed n s + ((s * (s + 3) : ℕ) : ℕ∞) := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn
      rw [relaxed_cap2 n hn]
      norm_cast
      rcases Nat.lt_or_ge n 4 with hlt | hge
      · interval_cases n <;> norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        have hA : (m + 4) * (m + 4) = m * m + 8 * m + 16 := by ring
        omega
  | succ s hs ih =>
      intro n hn
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := by omega
        subst hn1
        rw [relaxed_one (by omega)]
        have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * s + 4 := by ring
        norm_cast
        omega
      · obtain ⟨k, hk, hkn, hkeq⟩ := relaxed_step_attained (n := n) (s := s + 1) hge (by omega)
        rw [hkeq, Nat.add_sub_cancel]
        exact tele6 hk hkn (relaxed_ge_slope4 (by omega) k hk) (ih (n - k) (by omega))

/-! ## (C) 主定理 -/

/-- **主定理**: 層1 で厳密値が分かっている範囲 `n + 1 ≤ B_4(s)` では、KSS の緩和漸化式 (1) は
`T_UG` と**一致する**（`s ≥ 2`・`n ≥ 1`）。

範囲を 3 つに割り、(A) の `≤` と (B) の `≥` で挟む:
`n ≤ s` は補題3（`2n`）、`s ≤ n ≤ θ(s)` は定理B（`4n-2s`）、
`θ(s) ≤ n ≤ B_4(s)-1` は定理F（`6n-s(s+3)`）。 -/
theorem relaxed_eq_TUG {n s : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) (hB : n + 1 ≤ B4 s) :
    relaxed n s = (TUG n s : ℕ∞) := by
  have hle := relaxed_le_TUG hs n hn
  have h2 := two_mul_le_relaxed hs n hn
  have h4 := relaxed_ge_slope4 hs n hn
  have h6 := relaxed_ge_slope6 hs n hn
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (relaxed_ne_top hs hn)
  rw [← hr] at hle h2 h4 h6 ⊢
  norm_cast at hle h2 h4 h6 ⊢
  rcases Nat.lt_or_ge n s with h | h
  · have := TUG_eq_of_le' hn h.le
    omega
  · rcases Nat.lt_or_ge n (theta s) with h' | h'
    · have := TUG_eq_slope4 hs h h'.le
      omega
    · have := TUG_eq_slope6 hs h' hB
      omega

/-! ## 具体値の検算（定義が空虚でないこと・式 (1) に忠実であることの証拠）

**展開補題 3 本（`relaxed_one`・`relaxed_top`・`relaxed_step`）だけ**から、式 (1) を 1 段ずつ
手で回す。閉形式 `relaxed_cap2` も (A)(B)(C) も使わない。各値は「最小を与える `k₀`」を明示し、
残りの `k` は `interval_cases` で全部開いて比べる。

式 (1) をそのまま書いた Python の DP（リポジトリ外・`1 ≤ k < n`）の値と一致する:
`relaxed · 2 = 2, 4, 8, 14, 22, 32, 44, 58`、`relaxed · 3 = 2, 4, 6, 10, 14, 18, 24, 30, 36`。 -/

section Values

/-- `relaxed n s = v` を式 (1) の 1 段の展開で確かめる。`k0` は最小を与える `k`。
既に確かめた値は `[local simp]` で渡す。 -/
local macro "relaxed_unfold " k0:num : tactic =>
  `(tactic| (
    refine relaxed_eq_of (by norm_num) (by norm_num) $k0 (by norm_num) (by norm_num) ?_ ?_
    · norm_num [relaxed_one, relaxed_top]
    · intro k hk hkn
      interval_cases k <;> norm_num [relaxed_one, relaxed_top]))

/-! ### 上限 2 の行 -/

@[local simp] theorem relaxed_1_2 : relaxed 1 2 = 2 := relaxed_one (by norm_num)
@[local simp] theorem relaxed_2_2 : relaxed 2 2 = 4 := by relaxed_unfold 1
@[local simp] theorem relaxed_3_2 : relaxed 3 2 = 8 := by relaxed_unfold 2
@[local simp] theorem relaxed_4_2 : relaxed 4 2 = 14 := by relaxed_unfold 3
@[local simp] theorem relaxed_5_2 : relaxed 5 2 = 22 := by relaxed_unfold 4
@[local simp] theorem relaxed_6_2 : relaxed 6 2 = 32 := by relaxed_unfold 5
@[local simp] theorem relaxed_7_2 : relaxed 7 2 = 44 := by relaxed_unfold 6
@[local simp] theorem relaxed_8_2 : relaxed 8 2 = 58 := by relaxed_unfold 7

/-! ### 上限 3 の行（`θ(3) = 6`、`B_4(3) = 9`） -/

@[local simp] theorem relaxed_1_3 : relaxed 1 3 = 2 := relaxed_one (by norm_num)
@[local simp] theorem relaxed_2_3 : relaxed 2 3 = 4 := by relaxed_unfold 1
@[local simp] theorem relaxed_3_3 : relaxed 3 3 = 6 := by relaxed_unfold 1
@[local simp] theorem relaxed_4_3 : relaxed 4 3 = 10 := by relaxed_unfold 1
@[local simp] theorem relaxed_5_3 : relaxed 5 3 = 14 := by relaxed_unfold 2
@[local simp] theorem relaxed_6_3 : relaxed 6 3 = 18 := by relaxed_unfold 3
@[local simp] theorem relaxed_7_3 : relaxed 7 3 = 24 := by relaxed_unfold 3
@[local simp] theorem relaxed_8_3 : relaxed 8 3 = 30 := by relaxed_unfold 4
theorem relaxed_9_3 : relaxed 9 3 = 36 := by relaxed_unfold 5

/-- 閉形式 `relaxed_cap2` と手で回した値の突き合わせ（`4·4 - 4 + 2 = 14`）。 -/
example : relaxed 4 2 = ((4 * 4 - 4 + 2 : ℕ) : ℕ∞) := relaxed_cap2 4 (by norm_num)

/-- 不可能の節も値を持つ: 上限 1 では長さ 2 の鎖は `⊤`、上限 0 では長さ 1 でも `⊤`。 -/
example : relaxed 2 1 = ⊤ ∧ relaxed 1 0 = ⊤ :=
  ⟨relaxed_top (by norm_num) (by norm_num), relaxed_top (by norm_num) (by norm_num)⟩

end Values

/-! ## 範囲は緩められない（`s = 2` の証人）

`B_4(2) = 4` なので `n = 4`・`s = 2` は主定理の範囲 `n + 1 ≤ B4 s` の **1 つ外**。
そこでは `relaxed 4 2 = 14 < 16 = T_UG(4,2)` で、緩和は真に 2 手の損をする。
したがって主定理の仮定を `n ≤ B4 s` に広げた言明は**偽**である。

⚠ これは `s = 2` の 1 点だけの主張。`s ≥ 3` で `n = B_4(s)` が真に損をするかは、
`T_UG(B_4(s), s)` の厳密値が Lean に無いので示していない。 -/

theorem TUG_4_2 : TUG 4 2 = 16 := by
  have h := TUG_cap2 (n := 4) (by norm_num)
  omega

/-- **範囲の鋭さ（`s = 2`）**: `n = B_4(2) = 4` では `relaxed < T_UG`。 -/
theorem relaxed_lt_TUG_at_B4_two : relaxed 4 2 < (TUG 4 2 : ℕ∞) := by
  rw [relaxed_4_2, TUG_4_2]
  norm_num

/-- 上を「主定理の範囲を 1 つ広げた言明の反例」として述べ直したもの。 -/
theorem not_relaxed_eq_TUG_at_B4 :
    ¬ ∀ n s : ℕ, 2 ≤ s → 1 ≤ n → n ≤ B4 s → relaxed n s = (TUG n s : ℕ∞) := by
  intro h
  have h4 : (4 : ℕ) ≤ B4 2 := by decide
  exact (ne_of_lt relaxed_lt_TUG_at_B4_two) (h 4 2 le_rfl (by norm_num) h4)

end Spooky
