/-
# 要石 — `θ(s) ≤ n` なら `T_UP(n,s) = T_UG(n,s) + 1`（`δ = -1`。`n` に上限なし）

`δ = T_UG - T_UP` の符号は、`Sign.lean` の `delta_sign_flip` で `s ≤ n ≤ B_4(s) - 1` の範囲だけ
決まっていた。`s = 2` は `Cap2Exact.lean` で全ての `n ≥ 3` について済んでいる。
ここでは **`s ≥ 2`・`θ(s) ≤ n` の全域**で `T_UG(n,s) ≤ T_UP(n,s)` を示す。
`|δ| = 1`（`UGvsUP.lean` の `TUG_TUP_diff_one`）と合わせて `T_UP = T_UG + 1` になる。
`θ(s) < B_4(s)` なので、`s ≥ 3`・`n ≥ B_4(s)` はこの特別な場合である（`keystone`）。

## 証明

`U = T_UP`、`G = T_UG` と書く。使うのは、両方向が証明済みの 2 本の分解
（`Upper.lean` の `decomp_exact`、`Unghost.lean` の `decomp_ug_le'`）と、
傾き 2・4 の領域の閉形式（`Theta.lean`・`Delta.lean`）、`s = 2` の閉形式だけである。
傾き 6 以降の厳密値（定理F）も、上包絡の構成も使わない。

**補題1（`TUP_succ_ge_two`）** `U(m+1,s) ≥ U(m,s) + 2`（`m ≥ 1`）。
**補題2（`TUP_succ_ge_four`）** `U(m+1,s) ≥ U(m,s) + 4`（`m ≥ s`）。

どちらも `U(m+1,s+1)` の最適な分割 `m+1 = k+q` を取り、`U(m,s+1)` には 1 つ小さい分割を入れる。

* `k ≥ 2` なら頭を縮める（`m = (k-1)+q`）。差は `2 + (U(k,s+1) - U(k-1,s+1)) ≥ 2 + 2`。
* `k = 1` なら尻尾を縮める（`m = 1+(q-1)`）。差は `U(q,s) - U(q-1,s)` で、`s` の帰納法。

底の `s = 2` は `U(n,2) = n²+n-3` から出る。

**本体（`TUG_le_TUP_of_theta_le`）** `s` の帰納法。`θ(s+1) ≤ n` とし、`U(n,s+1)` の最適な
分割 `n = k+q` を取る（`U(n,s+1) = 2k-1 + U(k,s+1) + U(q,s)`）。

* **場合A `θ(s) ≤ q`**: 帰納法の仮定で `G(q,s) ≤ U(q,s)`。同じ `k` を Cor 4.12 に入れて
  `G(n,s+1) ≤ 2k-1 + U(k,s+1) + G(q,s) ≤ U(n,s+1)`。
* **場合B `q < θ(s)`**: `n ≥ θ(s+1) = θ(s)+s+1` なので `k ≥ s+2`。分割を 1 つずらして
  `n = (k-1)+(q+1)` を Cor 4.12 に入れる。頭は補題2（`k-1 ≥ s+1`）で 4 手得をし、
  尻尾は `q+1 ≤ θ(s)` が傾き 2・4 の領域に収まるので閉形式から `G(q+1,s) ≤ U(q,s) + 5`
  （`TUG_succ_le_TUP_add_five`）。掃きの 2 手と合わせて
  `G(n,s+1) ≤ (2k-3) + (U(k,s+1)-4) + (U(q,s)+5) = U(n,s+1) - 1`。

場合B は実際に起きる（`n = θ(s+1)` で `k = s+2`、`q = θ(s)-1` が最適な分割の 1 つ）。
分解の最適な `k` は存在量化で 1 つ渡されるだけなので、両方の場合が要る。

## 層

一般証明（無条件）。有界の全数検査には頼らない。`example` の具体値（`T_UG(9,3) = 38`、
`T_UP(9,3) = 39`）も定理の組み合わせで出しており、定義の簡約には依らない。

## 示していないこと

* `n ≥ B_4(s)` での `T_UP`・`T_UG` の**値**（上包絡 `max_m (2mn - β_m(s))` に一致すること）は
  示していない。ここで決まるのは差の符号だけである。
* 鎖以外の DAG には何も言っていない。

## 置き場所

`Relaxed.lean` と同じ理由で `SpookyPebblingExtra` に置く（本体ライブラリのモジュール数・行数は
原稿側の検査器が凍結値と照合している）。ビルドは `lake build SpookyPebblingExtra.Keystone`。
-/
import SpookyPebbling.SlopeTight
import SpookyPebbling.Slope6Exact
import SpookyPebbling.Cap2Exact

namespace Spooky

/-! ## 分解を引き算なしの形に直す

`decomp_exact`・`decomp_ug_le'` は `n - k` と `s - 1` で書かれている。以下では分割を
`n = k + q`、上限を `s + 1` と書いて、`omega` に渡す項の形を揃える。 -/

/-- `T_UP` の分解の `≤` 側: どの分割 `n = k + q` も上界を与える。 -/
theorem TUP_le_split {s n k q : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k) (hq : 1 ≤ q) (hn : n = k + q) :
    TUP n (s + 1) + 1 ≤ 2 * k + TUP k (s + 1) + TUP q s := by
  subst hn
  have h := decomp_le (n := k + q) (s := s + 1) (k := k) (by omega) hk (by omega)
  rw [show k + q - k = q from by omega, show s + 1 - 1 = s from rfl] at h
  omega

/-- `T_UP` の分解の `=` 側: 等号を与える分割 `n = k + q` が在る。 -/
theorem TUP_split_attained {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) :
    ∃ k q, 1 ≤ k ∧ 1 ≤ q ∧ n = k + q ∧
      TUP n (s + 1) + 1 = 2 * k + TUP k (s + 1) + TUP q s := by
  obtain ⟨⟨k, hk, hkn, hkeq⟩, -⟩ := decomp_exact (n := n) (s := s + 1) (by omega) hn
  rw [show s + 1 - 1 = s from rfl] at hkeq
  exact ⟨k, n - k, hk, by omega, by omega, by omega⟩

/-- KSS Cor 4.12 の `≤` 側: どの分割 `n = k + q` も `T_UG` の上界を与える。 -/
theorem TUG_le_split {s n k q : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k) (hq : 1 ≤ q) (hn : n = k + q) :
    TUG n (s + 1) + 1 ≤ 2 * k + TUP k (s + 1) + TUG q s := by
  subst hn
  have h := decomp_ug_le' (n := k + q) (s := s + 1) (k := k) (by omega) hk (by omega)
  rw [show k + q - k = q from by omega, show s + 1 - 1 = s from rfl] at h
  omega

/-! ## `T_UP` の増分 -/

/-- **補題1**: 鎖を 1 つ伸ばすと `T_UP` は 2 以上増える（`s ≥ 2`・`m ≥ 1`）。 -/
theorem TUP_succ_ge_two {s : ℕ} (hs : 2 ≤ s) :
    ∀ m, 1 ≤ m → TUP m s + 2 ≤ TUP (m + 1) s := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro m hm
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · obtain rfl : m = 1 := by omega
        have h1 : TUP 1 2 = 2 * 1 - 1 := TUP_eq_of_le' (by omega) (by omega)
        have h2 : TUP (1 + 1) 2 = 2 * (1 + 1) - 1 := TUP_eq_of_le' (by omega) (by omega)
        omega
      · have h1 := TUP_cap2 (n := m) hge
        have h2 := TUP_cap2 (n := m + 1) (by omega)
        have e : (m + 1) * (m + 1) + (m + 1) = m * m + m + 2 * m + 2 := by ring
        omega
  | succ s hs ih =>
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
        intro hm
        obtain ⟨k, q, hk, hq, hkq, hkeq⟩ :=
          TUP_split_attained (s := s) (n := m + 1) hs (by omega)
        rcases Nat.lt_or_ge k 2 with hk1 | hk2
        · -- `k = 1`: 尻尾が `m`。尻尾を 1 つ縮める
          have hk1' : k = 1 := by omega
          have hqm : q = m := by omega
          rw [hk1', hqm] at hkeq
          have hup : TUP 1 (s + 1) = 2 * 1 - 1 := TUP_eq_of_le' (by omega) (by omega)
          rcases Nat.lt_or_ge m 2 with hm1 | hm2
          · have hm1' : m = 1 := by omega
            rw [hm1'] at hkeq ⊢
            have h2 : TUP 1 s = 2 * 1 - 1 := TUP_eq_of_le' (by omega) (by omega)
            omega
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
            have hle := TUP_le_split (n := j + 1) (k := 1) (q := j) hs le_rfl (by omega)
              (by omega)
            have hih := ih j (by omega)
            omega
        · -- `k ≥ 2`: 頭を 1 つ縮める
          obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
          have hle := TUP_le_split (n := m) (k := i) (q := q) hs (by omega) hq (by omega)
          have hih := ihm i (by omega) (by omega)
          omega

/-- **補題2**: `m ≥ s` では `T_UP` は 4 以上増える（`s ≥ 2`）。

範囲 `m ≥ s` は緩められない（`T_UP(s,s) - T_UP(s-1,s) = 2`）。 -/
theorem TUP_succ_ge_four {s : ℕ} (hs : 2 ≤ s) :
    ∀ m, s ≤ m → TUP m s + 4 ≤ TUP (m + 1) s := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro m hm
      have h1 := TUP_cap2 (n := m) hm
      have h2 := TUP_cap2 (n := m + 1) (by omega)
      have e : (m + 1) * (m + 1) + (m + 1) = m * m + m + 2 * m + 2 := by ring
      omega
  | succ s hs ih =>
      intro m hm
      obtain ⟨k, q, hk, hq, hkq, hkeq⟩ :=
        TUP_split_attained (s := s) (n := m + 1) hs (by omega)
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · -- `k = 1`: 尻尾が `m ≥ s + 1`。尻尾を 1 つ縮めて `s` の帰納法
        have hk1' : k = 1 := by omega
        have hqm : q = m := by omega
        rw [hk1', hqm] at hkeq
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hle := TUP_le_split (n := j + 1) (k := 1) (q := j) hs le_rfl (by omega) (by omega)
        have hih := ih j (by omega)
        omega
      · -- `k ≥ 2`: 頭を 1 つ縮めて補題1
        obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        have hle := TUP_le_split (n := m) (k := i) (q := q) hs (by omega) hq (by omega)
        have hih := TUP_succ_ge_two (s := s + 1) (by omega) i (by omega)
        omega

/-! ## 尻尾を 1 つ伸ばす代価（傾き 2・4 の領域） -/

/-- `1 ≤ q < θ(s)` なら `T_UG(q+1,s) ≤ T_UP(q,s) + 5`。

`q + 1 ≤ s` では差は 3（`2(q+1)` と `2q-1`）、`s ≤ q` では差はちょうど 5
（`4(q+1)-2s` と `4q-2s-1`）。定数 5 は改善できない。 -/
theorem TUG_succ_le_TUP_add_five {s q : ℕ} (hs : 2 ≤ s) (hq : 1 ≤ q)
    (hqθ : q + 1 ≤ theta s) : TUG (q + 1) s ≤ TUP q s + 5 := by
  rcases Nat.lt_or_ge q s with hlt | hge
  · have h1 : TUG (q + 1) s = 2 * (q + 1) := TUG_eq_of_le' (by omega) (by omega)
    have h2 : TUP q s = 2 * q - 1 := TUP_eq_of_le' hq (by omega)
    omega
  · have h1 := TUG_eq_slope4 (s := s) (n := q + 1) hs (by omega) hqθ
    have h2 := TUP_eq_slope4 (s := s) (n := q) hs hge hqθ
    omega

/-! ## 本体 -/

/-- **要石（不等式の形）**: `s ≥ 2`・`θ(s) ≤ n` なら `T_UG(n,s) ≤ T_UP(n,s)`。`n` に上限なし。 -/
theorem TUG_le_TUP_of_theta_le {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, theta s ≤ n → TUG n s ≤ TUP n s := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn
      have hth : theta 2 = 3 := rfl
      have h := TUP_eq_TUG_add_one_cap2 (n := n) (by omega)
      omega
  | succ s hs ih =>
      intro n hn
      have hthS : theta (s + 1) = theta s + (s + 1) := theta_succ s
      have hth1 : s ≤ theta s := le_theta s
      obtain ⟨k, q, hk, hq, rfl, hkeq⟩ := TUP_split_attained (s := s) (n := n) hs (by omega)
      rcases Nat.lt_or_ge q (theta s) with hB | hA
      · -- 場合B: 尻尾が `θ(s)` に届かない。分割を 1 つずらす
        obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        have hi : s + 1 ≤ i := by omega
        have hle := TUG_le_split (n := i + 1 + q) (k := i) (q := q + 1) hs (by omega) (by omega)
          (by omega)
        have h4 := TUP_succ_ge_four (s := s + 1) (by omega) i hi
        have h5 := TUG_succ_le_TUP_add_five hs hq (by omega)
        omega
      · -- 場合A: 尻尾が `θ(s)` 以上。同じ分割を Cor 4.12 に入れる
        have hle := TUG_le_split (n := k + q) (k := k) (q := q) hs hk hq rfl
        have hih := ih q hA
        omega

/-- **要石**: `s ≥ 2`・`θ(s) ≤ n` なら `T_UP(n,s) = T_UG(n,s) + 1`（`δ = -1`）。`n` に上限なし。 -/
theorem TUP_eq_TUG_add_one_of_theta_le {s n : ℕ} (hs : 2 ≤ s) (hn : theta s ≤ n) :
    TUP n s = TUG n s + 1 := by
  have hn1 : 1 ≤ n := by have := le_theta s; omega
  have hle := TUG_le_TUP_of_theta_le hs n hn
  rcases TUG_TUP_diff_one hn1 (by omega) (UPLengths_nonempty hs hn1)
    (UGLengths_nonempty hs hn1) with h | h
  · omega
  · exact h

/-- **決定点の形**: `s ≥ 3`・`n ≥ B_4(s)` で `T_UG(n,s) ≤ T_UP(n,s)`。 -/
theorem keystone {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUG n s ≤ TUP n s := by
  have hB := theta_lt_B4 (s := s) (by omega)
  exact TUG_le_TUP_of_theta_le (by omega) n (by omega)

/-- **決定点の系**: `s ≥ 3`・`n ≥ B_4(s)` で `T_UP(n,s) = T_UG(n,s) + 1`（`δ = -1`）。 -/
theorem keystone_delta {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUP n s = TUG n s + 1 := by
  have hB := theta_lt_B4 (s := s) (by omega)
  exact TUP_eq_TUG_add_one_of_theta_le (by omega) (by omega)

/-- **`δ` の符号（範囲の制限なし）**: `s ≥ 2`・`n ≥ 1` で

* `n < θ(s)` なら `T_UG = T_UP + 1`（`δ = +1`）
* `θ(s) ≤ n` なら `T_UP = T_UG + 1`（`δ = -1`）

`Sign.lean` の `delta_sign_flip` から仮定 `s ≤ n ≤ B_4(s) - 1` を外したもの。 -/
theorem delta_sign {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) :
    (n + 1 ≤ theta s → TUG n s = TUP n s + 1) ∧ (theta s ≤ n → TUP n s = TUG n s + 1) := by
  refine ⟨fun h => ?_, fun h => TUP_eq_TUG_add_one_of_theta_le hs h⟩
  rcases Nat.lt_or_ge n s with hlt | hge
  · have h1 : TUG n s = 2 * n := TUG_eq_of_le' hn (by omega)
    have h2 : TUP n s = 2 * n - 1 := TUP_eq_of_le' hn (by omega)
    omega
  · exact TUG_eq_TUP_add_one hs hge h

/-! ## 具体値との突き合わせ

`s = 3` では既存の範囲は `n ≤ B_4(3) - 1 = 8` まで。その 1 つ先の `n = 9` で、
下界（定理E' の `m = 4`）と Cor 4.12 の `k = 5` の項から `T_UG(9,3) = 38` が決まり、
要石から `T_UP(9,3) = 39` が出る（原稿 P1 の表 1 の値と一致）。 -/

example : TUG 9 3 = 38 ∧ TUP 9 3 = 39 := by
  have hlb := TUG_ge_slope8_tight (s := 3) (n := 9) (by omega) (by omega)
  have hbb := bb_four_three
  have hub : TUG 9 3 + 1 ≤ 2 * 5 + TUP 5 3 + TUG 4 2 :=
    TUG_le_split (s := 2) (n := 9) (k := 5) (q := 4) le_rfl (by omega) (by omega) rfl
  have hup := TUP_eq_slope4 (s := 3) (n := 5) (by omega) (by omega) (by decide)
  have hg := TUG_cap2 (n := 4) (by omega)
  have hd := keystone_delta (s := 3) (n := 9) le_rfl (by decide)
  omega

end Spooky
