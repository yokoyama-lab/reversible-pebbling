/-
# 上包絡 — `T_UP(n,s) = max_m (2mn - β_m(s))`（すべての `n ≥ 1`・`s ≥ 2`）

`SlopeTight.lean` の定理E' は、すべての傾き `2m` について下界 `T_UP(n,s) ≥ 2mn - β_m(s)` を
与える。ここでは**上界**、すなわち各傾きがその折れ目の間で実際に達成されることを示す。
合わせて、`T_UP` は直線族 `2mn - β_m(s)` の上包絡に**一致する**。

## 主張

折れ目を

* `brk 0 s = 1`（傾き 2 の区間の左端を表す約束）
* `brk 1 s = s`
* `brk m 2 = m`（`m ≥ 2`）
* `brk (m+1) (s+1) = brk m (s+1) + brk (m+1) s`（`s ≥ 2`）

で定める。`s ≥ 2` のとき次が成り立つ。

* **`TUP_eq_envelope`**: `brk m s ≤ n ≤ brk (m+1) s` なら `T_UP(n,s) = 2(m+1)n - β_{m+1}(s)`。
* **`exists_brk_interval`**: どの `n ≥ 1` もある `m` の区間 `[brk m s, brk (m+1) s]` に入る。
* **`TUP_upper_envelope`**: したがって、ある `m ≥ 1` で `T_UP(n,s) = 2mn - β_m(s)`、
  かつすべての `m ≥ 1` で `T_UP(n,s) ≥ 2mn - β_m(s)`。これが `max_m` の引き算なしの形。
* **`TUG_eq_envelope`**: 同じ区間で `T_UG` は `T_UP ± 1`（符号は `Keystone.lean` の `delta_sign`）。
* **`bb_succ_eq_add_brk`**: `β_{m+1}(s) = β_m(s) + 2·brk m s`（`m ≥ 1`）。すなわち折れ目は
  隣り合う 2 直線の交点 `(β_{m+1}(s) - β_m(s))/2` である。`Breakpoints.lean` の `m = 2, 3` を
  すべての `m` に広げたもの。`brk 2 s = θ(s) - 1`、`brk 3 s = B_4(s) - 1`（`brk_two`・`brk_three`）。

## 証明（上界）

`m` の帰納法と、その中で `s` の帰納法。使う構成は `T_UP` の分解の `≤` 側
（`Upper.lean` の `decomp_le`。`Keystone.lean` の `TUP_le_split` の形で使う）だけである。

傾き `2(m+2)` の区間は `[brk (m+1) (s+1), brk (m+2) (s+1)]`。折れ目の漸化式から、これは

* 頭の区間 `[brk m (s+1), brk (m+1) (s+1)]`（上限 `s+1`・傾き `2(m+1)`。`m` の帰納法の仮定）
* 尻尾の区間 `[brk (m+1) s, brk (m+2) s]`（上限 `s`・傾き `2(m+2)`。`s` の帰納法の仮定）

の**和にちょうど一致する**（左端どうし・右端どうしの和が、それぞれ区間の左端・右端）。
したがって区間内のどの `n` も `n = k + q`（`k` は頭の区間、`q` は尻尾の区間）と分けられ、

`T_UP(n,s+1) ≤ (2k-1) + (2(m+1)k - β_{m+1}(s+1)) + (2(m+2)q - β_{m+2}(s))`
`           = 2(m+2)n - β_{m+2}(s+1)`

となる（`β` の漸化式 `β_{m+2}(s+1) = β_{m+1}(s+1) + β_{m+2}(s) + 1`。`k` の項は消える）。
分け方は 2 通りで足りる。`n` が小さい側では頭を左端に固定し、大きい側では尻尾を右端に固定する。

底は 2 つ。`m = 0`（傾き 2）は補題4 `T_UP(n,s) = 2n-1`（`n ≤ s`）。`s = 2` は閉形式
`T_UP(n,2) = n²+n-3` で、区間は `{m+1, m+2}` の 2 点（`m = 0` では `{2}` の 1 点に退化する）。

## 層

一般証明（無条件）。有界の全数検査には頼らない。`example` の具体値は、定義の展開（`simp`）と
定理の組み合わせで出している。

## 示していないこと

* `max` を `Finset.sup` などの演算子で書いた形は述べていない（`TUP_upper_envelope` の
  「ある `m` で等号、すべての `m` で `≥`」がその内容）。
* `T_P`（空から終端に置く手数）の閉じた式は述べていない（KSS Thm 4.11 で `T_UG` から移せるが未記述）。
* 鎖以外の DAG には何も言っていない。

## 置き場所

`Relaxed.lean`・`Keystone.lean` と同じ理由で `SpookyPebblingExtra` に置く。
ビルドは `lake build SpookyPebblingExtra.Envelope`。
-/
import SpookyPebblingExtra.Keystone
import SpookyPebblingExtra.Breakpoints

namespace Spooky

/-! ## 折れ目 `brk m s` -/

/-- 折れ目。`m ≥ 1` では、傾き `2m` の直線と傾き `2(m+1)` の直線の交点の `n` 座標
（＝傾き `2m` の区間の右端）。`brk 0 s = 1` は傾き 2 の区間の左端を表す約束。
`s < 2` の値は使わない。 -/
def brk : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, s => s
  | (t + 2), 0 => t + 2
  | (t + 2), 1 => t + 2
  | (t + 2), 2 => t + 2
  | (t + 2), (s + 3) => brk (t + 1) (s + 3) + brk (t + 2) (s + 2)
termination_by m s => (m, s)

@[simp] theorem brk_zero (s : ℕ) : brk 0 s = 1 := by
  simp [brk]

@[simp] theorem brk_one (s : ℕ) : brk 1 s = s := by
  simp [brk]

theorem brk_base {m : ℕ} (hm : 2 ≤ m) : brk m 2 = m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
  simp [brk]

/-- 折れ目の漸化式。`brk 0 s = 1` の約束により `m = 0` でも成り立つ（`s + 1 = 1 + s`）。 -/
theorem brk_step {m s : ℕ} (hs : 2 ≤ s) :
    brk (m + 1) (s + 1) = brk m (s + 1) + brk (m + 1) s := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  cases m with
  | zero => simp; omega
  | succ t => simp [brk]

theorem le_brk : ∀ m s, 2 ≤ s → m ≤ brk m s := by
  intro m
  induction m with
  | zero => intro s _; omega
  | succ m _ =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          cases m with
          | zero => simp
          | succ t => rw [brk_base (by omega)]
      | succ s hs ihs => rw [brk_step hs]; omega

theorem brk_pos {s : ℕ} (hs : 2 ≤ s) (m : ℕ) : 1 ≤ brk m s := by
  cases m with
  | zero => simp
  | succ t => have := le_brk (t + 1) s hs; omega

/-- 折れ目は `m` について広義単調（`s = 2` では `brk 1 2 = brk 2 2 = 2` で等号になる）。 -/
theorem brk_le_succ {s : ℕ} (hs : 2 ≤ s) (m : ℕ) : brk m s ≤ brk (m + 1) s := by
  rcases Nat.eq_or_lt_of_le hs with rfl | h3
  · cases m with
    | zero => simp
    | succ t =>
        cases t with
        | zero => rw [brk_one, brk_base (by omega)]
        | succ u => rw [brk_base (by omega), brk_base (by omega)]; omega
  · obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
    rw [brk_step (by omega)]
    omega

/-! ## 区間ごとの上界 -/

/-- **上界（構成）**: `brk m s ≤ n ≤ brk (m+1) s` なら `T_UP(n,s) ≤ 2(m+1)n - β_{m+1}(s)`。 -/
theorem TUP_le_envelope : ∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s →
    TUP n s + bb (m + 1) s ≤ 2 * (m + 1) * n := by
  intro m
  induction m with
  | zero =>
      -- 傾き 2: `1 ≤ n ≤ s` で `T_UP = 2n - 1`
      intro s hs n h1 h2
      rw [brk_zero] at h1
      have h2' : n ≤ s := by simpa using h2
      have h := TUP_eq_of_le' (k := n) (s := s) h1 h2'
      have hb : bb (0 + 1) s = 1 := bb_one s
      omega
  | succ m ihm =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          -- 底 `s = 2`: 区間は `{m+1, m+2}`。閉形式 `T_UP(n,2) = n²+n-3` から等号
          intro n h1 h2
          have hb : bb (m + 1 + 1) 2 = (m + 1) * (m + 1) + (m + 1) + 3 :=
            bb_base (m := m + 1) (by omega)
          have hR : brk (m + 1 + 1) 2 = m + 1 + 1 := brk_base (by omega)
          have hL1 : m + 1 ≤ brk (m + 1) 2 := le_brk (m + 1) 2 le_rfl
          have hL2 : 2 ≤ brk (m + 1) 2 := by
            cases m with
            | zero => simp
            | succ t => rw [brk_base (by omega)]; omega
          have hc := TUP_cap2 (n := n) (by omega)
          rcases (by omega : n = m + 1 ∨ n = m + 1 + 1) with rfl | rfl
          · nlinarith [hc, hb]
          · nlinarith [hc, hb]
      | succ s hs ihs =>
          -- 区間 `[brk (m+1) (s+1), brk (m+2) (s+1)]` ＝ 頭の区間 ＋ 尻尾の区間
          intro n h1 h2
          have hstepR : brk (m + 1 + 1) (s + 1) = brk (m + 1) (s + 1) + brk (m + 1 + 1) s :=
            brk_step hs
          have hstepL : brk (m + 1) (s + 1) = brk m (s + 1) + brk (m + 1) s := brk_step hs
          have hbb : bb (m + 1 + 1) (s + 1) = bb (m + 1) (s + 1) + bb (m + 1 + 1) s + 1 :=
            bb_step (m := m + 1) (by omega) hs
          have hposH : 1 ≤ brk m (s + 1) := brk_pos (by omega) m
          have hposT : 1 ≤ brk (m + 1) s := brk_pos hs (m + 1)
          have hmonoT : brk (m + 1) s ≤ brk (m + 1 + 1) s := brk_le_succ hs (m + 1)
          rcases Nat.le_total n (brk m (s + 1) + brk (m + 1 + 1) s) with hc | hc
          · -- 小さい側: 頭を左端 `brk m (s+1)` に固定する
            obtain ⟨q, rfl⟩ : ∃ q, n = brk m (s + 1) + q := ⟨n - brk m (s + 1), by omega⟩
            have hle := TUP_le_split (n := brk m (s + 1) + q) (k := brk m (s + 1)) (q := q) hs
              hposH (by omega) rfl
            have hhead := ihm (s + 1) (by omega) (brk m (s + 1)) le_rfl (by omega)
            have htail := ihs q (by omega) (by omega)
            nlinarith [hle, hhead, htail]
          · -- 大きい側: 尻尾を右端 `brk (m+2) s` に固定する
            obtain ⟨k, rfl⟩ : ∃ k, n = k + brk (m + 1 + 1) s :=
              ⟨n - brk (m + 1 + 1) s, by omega⟩
            have hle := TUP_le_split (n := k + brk (m + 1 + 1) s) (k := k)
              (q := brk (m + 1 + 1) s) hs (by omega) (by omega) rfl
            have hhead := ihm (s + 1) (by omega) k (by omega) (by omega)
            have htail := ihs (brk (m + 1 + 1) s) hmonoT le_rfl
            nlinarith [hle, hhead, htail]

/-! ## 区間上の厳密値と上包絡 -/

/-- **区間上の厳密値**: `brk m s ≤ n ≤ brk (m+1) s` なら `T_UP(n,s) = 2(m+1)n - β_{m+1}(s)`。 -/
theorem TUP_eq_envelope {m s n : ℕ} (hs : 2 ≤ s) (h1 : brk m s ≤ n) (h2 : n ≤ brk (m + 1) s) :
    TUP n s + bb (m + 1) s = 2 * (m + 1) * n := by
  have hn : 1 ≤ n := le_trans (brk_pos hs m) h1
  exact le_antisymm (TUP_le_envelope m s hs n h1 h2)
    (TUP_ge_slope_tight (m + 1) (by omega) s hs n hn)

/-- 区間は `n ≥ 1` を覆う: どの `n` もある傾きの区間に入る。 -/
theorem exists_brk_interval {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) :
    ∃ m, brk m s ≤ n ∧ n ≤ brk (m + 1) s := by
  have hex : ∃ m, n ≤ brk (m + 1) s := ⟨n, by have := le_brk (n + 1) s hs; omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, brk_zero]; exact hn
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    omega

/-- **上包絡**: `T_UP(n,s) = max_{m ≥ 1} (2mn - β_m(s))`（`s ≥ 2`・`n ≥ 1`）。
引き算と `max` を避けて「ある `m` で等号、すべての `m` で `≥`」と述べる。 -/
theorem TUP_upper_envelope {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) :
    (∃ m, 1 ≤ m ∧ TUP n s + bb m s = 2 * m * n) ∧
      (∀ m, 1 ≤ m → 2 * m * n ≤ TUP n s + bb m s) := by
  obtain ⟨m, h1, h2⟩ := exists_brk_interval hs hn
  exact ⟨⟨m + 1, by omega, TUP_eq_envelope hs h1 h2⟩,
    fun m hm => TUP_ge_slope_tight m hm s hs n hn⟩

/-- **`T_UG` の区間上の厳密値**: `T_UP` の値に `δ` の符号（`Keystone.lean`）を足したもの。
`n < θ(s)` では `2(m+1)n - β_{m+1}(s) + 1`、`θ(s) ≤ n` では `2(m+1)n - β_{m+1}(s) - 1`。 -/
theorem TUG_eq_envelope {m s n : ℕ} (hs : 2 ≤ s) (h1 : brk m s ≤ n) (h2 : n ≤ brk (m + 1) s) :
    (n + 1 ≤ theta s → TUG n s + bb (m + 1) s = 2 * (m + 1) * n + 1) ∧
      (theta s ≤ n → TUG n s + bb (m + 1) s + 1 = 2 * (m + 1) * n) := by
  have hn : 1 ≤ n := le_trans (brk_pos hs m) h1
  have hup := TUP_eq_envelope hs h1 h2
  obtain ⟨hpos, hneg⟩ := delta_sign hs hn
  exact ⟨fun h => by have := hpos h; omega, fun h => by have := hneg h; omega⟩

/-! ## 折れ目は β の階差の半分（すべての傾き） -/

/-- `β_{m+1}(s) = β_m(s) + 2·brk m s`（`m ≥ 1`・`s ≥ 2`）。 -/
theorem bb_succ_eq_add_brk : ∀ m, 1 ≤ m → ∀ s, 2 ≤ s → bb (m + 1) s = bb m s + 2 * brk m s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro s hs
      have h2 : bb (1 + 1) s = 2 * s + 1 := bb_two s hs
      rw [bb_one, brk_one]
      omega
  | succ m hm ihm =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          have hA : bb (m + 1 + 1) 2 = (m + 1) * (m + 1) + (m + 1) + 3 :=
            bb_base (m := m + 1) (by omega)
          have hB : bb (m + 1) 2 = m * m + m + 3 := bb_base hm
          have hX : brk (m + 1) 2 = m + 1 := brk_base (by omega)
          rw [hA, hB, hX]
          ring
      | succ s hs ihs =>
          have hA : bb (m + 1 + 1) (s + 1) = bb (m + 1) (s + 1) + bb (m + 1 + 1) s + 1 :=
            bb_step (m := m + 1) (by omega) hs
          have hB : bb (m + 1) (s + 1) = bb m (s + 1) + bb (m + 1) s + 1 := bb_step hm hs
          have hBm := ihm (s + 1) (by omega)
          have hX : brk (m + 1) (s + 1) = brk m (s + 1) + brk (m + 1) s := brk_step hs
          omega

/-- 折れ目の位置としての読み: `brk m s = (β_{m+1}(s) - β_m(s))/2`。 -/
theorem brk_eq_half_diff {m s : ℕ} (hm : 1 ≤ m) (hs : 2 ≤ s) :
    (bb (m + 1) s - bb m s) / 2 = brk m s := by
  have h := bb_succ_eq_add_brk m hm s hs
  omega

/-- 傾き 4→6 の折れ目は `θ(s) - 1`（`Delta.lean` の定理C の範囲の右端）。 -/
theorem brk_two {s : ℕ} (hs : 2 ≤ s) : brk 2 s + 1 = theta s := by
  have h1 : bb 3 s = bb 2 s + 2 * brk 2 s := bb_succ_eq_add_brk 2 (by omega) s hs
  have h2 := bb_three_eq_two_add hs
  have h3 := succ_le_theta hs
  omega

/-- 傾き 6→8 の折れ目は `B_4(s) - 1`（`Slope6Exact.lean` の定理F の範囲の右端）。 -/
theorem brk_three {s : ℕ} (hs : 2 ≤ s) : brk 3 s + 1 = B4 s := by
  have h1 : bb 4 s = bb 3 s + 2 * brk 3 s := bb_succ_eq_add_brk 3 (by omega) s hs
  have h2 := bb_four_eq_three_add s hs
  have h3 := theta_lt_B4 hs
  omega

/-! ## 具体値との突き合わせ -/

/-- 原稿 P1 の表 2 の折れ目（`s = 3` と `s = 6`、傾き 8→10・10→12・12→14）。 -/
example : brk 4 3 = 12 ∧ brk 5 3 = 17 ∧ brk 6 3 = 23 ∧
    brk 4 6 = 111 ∧ brk 5 6 = 217 ∧ brk 6 6 = 392 := by
  simp [brk]

/-- 原稿 P1 の表 1 の右端（`s = 3`・`n = 24`。傾き 14 の区間 `[23, 30]` に入る）。 -/
example : TUP 24 3 = 199 ∧ TUG 24 3 = 198 := by
  have h := TUP_eq_envelope (m := 6) (s := 3) (n := 24) (by omega) (by simp [brk])
    (by simp [brk])
  have hb : bb (6 + 1) 3 = 137 := by simp [bb]
  have hd := (delta_sign (s := 3) (n := 24) (by omega) (by omega)).2 (by decide)
  omega

end Spooky
