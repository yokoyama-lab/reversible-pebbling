/-
# 定理E' — 任意の傾きの**緊密な**下界

定理E（`SlopeE.lean`）は $m\ge4$ で緩む（$c_4(3)=38$ に対し実測の折れ目は 34）。
**なぜ緩むかが分かった**:

> 定理E の望遠鏡は頭の項に $T_{UP}(k,s)\ge T_{UG}(k,s)-1$（Lemma 4.10）を使う。
> ところが**最大点は $\delta=-1$ の領域にあり、そこでは $T_{UP}=T_{UG}+1$**。
> つまり 1 段ごとに 2 だけ損をしている。

**直し方**: $T_{UG}$ ではなく **$T_{UP}$ 自身の分解**（`Decomp.lean`、$\ge$ 方向も層1）で
望遠鏡を回せば、$T_{UG}\to T_{UP}$ の変換が要らず損が出ない:

$$(2k-1) + \bigl(2(m{-}1)k-\beta_{m-1}(s)\bigr) + \bigl(2m(n{-}k)-\beta_m(s{-}1)\bigr)
  = 2mn - \bigl(\beta_{m-1}(s)+\beta_m(s-1)+1\bigr).$$

`2k + 2(m-1)k - 2mk = 0` でここでも **`k` が消える**。得られる係数は

$$\beta_1(s)=1,\qquad \beta_m(2)=m^2-m+3,\qquad
  \beta_m(s)=\beta_{m-1}(s)+\beta_m(s-1)+1\ (s\ge3).$$

底の $s=2$ は `Cap2.lean` の閉形式 $T_{UP}(n,2)=n^2+n-3$ から出る
（$2mn \le n^2+n+m^2-m$ は $(n-m)(n-m+1)\ge0$ そのもの）。

## 既知の結果と一致し、$m\ge4$ で真に強い

* $\beta_2(s)=2s+1$ → `TUP_ge_slope4`（定理A の $T_{UP}$ 版）と一致
* $\beta_3(s)=s(s+3)-1$ → `TUP_ge_slope6'`（`Sign.lean`）と一致
* $\beta_4(3)+1 = 34 < 38 = c_4(3)$ — **定理E より真に強い**

## 緊密性（層2）

`notes/spooky-pebbling` で $m\le8$・$s\le7$ を全数照合した結果、
**$\max_n(2mn-T_{UP}(n,s)) = \beta_m(s)$ が破れ 0**、かつ $m\ge3$ で
$\max_n(2mn-T_{UG}(n,s)) = \beta_m(s)+1$。すなわちこの下界は**その範囲で緊密**。
一般の緊密性（構成側）は未証明。
-/
import SpookyPebbling.Lemma48Gen

namespace Spooky

/-! ## 係数 `β_m(s)` -/

/-- 緊密な係数。`β_1=1`、`β_m(2)=m²-m+3`、`β_m(s)=β_{m-1}(s)+β_m(s-1)+1`。 -/
def bb : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | (t + 2), 0 => t * t + 3 * t + 5
  | (t + 2), 1 => t * t + 3 * t + 5
  | (t + 2), 2 => t * t + 3 * t + 5
  | (t + 2), (s + 3) => bb (t + 1) (s + 3) + bb (t + 2) (s + 2) + 1
termination_by m s => (m, s)

@[simp] theorem bb_one (s : ℕ) : bb 1 s = 1 := by
  match s with
  | 0 => simp [bb]
  | 1 => simp [bb]
  | 2 => simp [bb]
  | (_ + 3) => simp [bb]

theorem bb_base {m : ℕ} (hm : 1 ≤ m) : bb (m + 1) 2 = m * m + m + 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [bb]
  ring

theorem bb_step {m s : ℕ} (hm : 1 ≤ m) (hs : 2 ≤ s) :
    bb (m + 1) (s + 1) = bb m (s + 1) + bb (m + 1) s + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  simp [bb]

/-- `(n-M)² + (n-M) ≥ 0` の ℕ 版。底 `s=2` の評価はこれそのもの。 -/
theorem sq_ineq (M n : ℕ) : 2 * M * n + M ≤ n * n + n + M * M := by
  rcases Nat.lt_or_ge n M with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, M = n + e := ⟨M - n, by omega⟩
    have he : 0 < e := by omega
    have hee : e ≤ e * e := Nat.le_mul_of_pos_left e he
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d, n = M + d := ⟨n - M, by omega⟩
    nlinarith

theorem bb_ge : ∀ m, 1 ≤ m → ∀ s, 2 ≤ s → 2 * m ≤ bb m s + 1 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro s _; rw [bb_one]
  | succ m hm ih =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          have hb := bb_base hm
          have hmm : m ≤ m * m := Nat.le_mul_of_pos_left m hm
          omega
      | succ s hs ihs => rw [bb_step hm hs]; omega

/-! ## 主定理 -/

/-- **定理E'**: `T_UP(n,s) ≥ 2mn - β_m(s)`（`m ≥ 1`・`s ≥ 2`・すべての `n ≥ 1`）。 -/
theorem TUP_ge_slope_tight : ∀ m, 1 ≤ m → ∀ s, 2 ≤ s → ∀ n, 1 ≤ n →
    2 * m * n ≤ TUP n s + bb m s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro s hs n hn
      have h := two_mul_sub_one_le_TUP hn (UPLengths_nonempty hs hn)
      rw [bb_one]
      omega
  | succ m hm ihm =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          -- 底 `s = 2`: 上限 2 の閉形式 `T_UP(n,2) = n²+n-3` から
          intro n hn
          have hb : bb (m + 1) 2 = m * m + m + 3 := bb_base hm
          have hkey := sq_ineq (m + 1) n
          have hMM : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
          rcases Nat.lt_or_ge n 2 with hlt | hge
          · have hn1 : n = 1 := by omega
            subst hn1
            have h1 : TUP 1 2 = 1 := TUP_eq_of_le' (by omega) (by omega)
            omega
          · have hc := TUP_cap2 hge
            omega
      | succ s hs ihs =>
          intro n hn
          have hbb : bb (m + 1) (s + 1) = bb m (s + 1) + bb (m + 1) s + 1 := bb_step hm hs
          rcases Nat.lt_or_ge n 2 with hlt | hge
          · have hn1 : n = 1 := by omega
            subst hn1
            have h1 : TUP 1 (s + 1) = 1 := TUP_eq_of_le' (by omega) (by omega)
            have h2 := bb_ge (m + 1) (by omega) (s + 1) (by omega)
            omega
          · obtain ⟨ms, hlen, hrun⟩ :=
              Nat.sInf_mem (UPLengths_nonempty (n := n) (s := s + 1) (by omega) (by omega))
            obtain ⟨k, hk, hkn, hbound⟩ := decomp_ge (by omega) hrun
            obtain ⟨q, rfl⟩ : ∃ q, n = k + q := ⟨n - k, by omega⟩
            have hq : 1 ≤ q := by omega
            rw [show k + q - k = q from by omega, show s + 1 - 1 = s from rfl] at hbound
            have hhead : 2 * m * k ≤ TUP k (s + 1) + bb m (s + 1) := ihm (s + 1) (by omega) k hk
            have htail : 2 * (m + 1) * q ≤ TUP q s + bb (m + 1) s := ihs q hq
            have e1 : 2 * (m + 1) * (k + q) = 2 * (m * k) + 2 * k + 2 * ((m + 1) * q) := by ring
            have e2 : 2 * m * k = 2 * (m * k) := by ring
            have e3 : 2 * (m + 1) * q = 2 * ((m + 1) * q) := by ring
            have hlen' : ms.length = TUP (k + q) (s + 1) := hlen
            omega

/-- **`T_UG` 版**: `T_UG(n,s) ≥ 2mn - β_m(s) - 1`。 -/
theorem TUG_ge_slope_tight {m s n : ℕ} (hm : 1 ≤ m) (hs : 2 ≤ s) (hn : 1 ≤ n) :
    2 * m * n ≤ TUG n s + bb m s + 1 := by
  have h1 := TUP_ge_slope_tight m hm s hs n hn
  have h2 := TUP_le_TUG_succ hn (by omega) (UGLengths_nonempty hs hn)
  omega

/-! ## 既知の結果との突き合わせ -/

theorem bb_two : ∀ s, 2 ≤ s → bb 2 s = 2 * s + 1 := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => have h : bb 2 2 = 1 * 1 + 1 + 3 := bb_base (m := 1) (by omega); omega
  | succ s hs ih =>
      have hstep : bb 2 (s + 1) = bb 1 (s + 1) + bb 2 s + 1 := bb_step (m := 1) (by omega) hs
      rw [bb_one] at hstep
      omega

theorem bb_three : ∀ s, 2 ≤ s → bb 3 s + 1 = s * (s + 3) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => have h : bb 3 2 = 2 * 2 + 2 + 3 := bb_base (m := 2) (by omega); omega
  | succ s hs ih =>
      have hstep : bb 3 (s + 1) = bb 2 (s + 1) + bb 3 s + 1 := bb_step (m := 2) (by omega) hs
      have h2 : bb 2 (s + 1) = 2 * (s + 1) + 1 := bb_two (s + 1) (by omega)
      have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * (s + 1) + 2 := by ring
      omega

/-- `m = 2` は `TUP_ge_slope4`（定理A の `T_UP` 版）と一致する。 -/
example {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : 4 * n ≤ TUP n s + 2 * s + 1 := by
  have h := TUP_ge_slope_tight 2 (by omega) s hs n hn
  rw [bb_two s hs] at h
  omega

/-- `m = 3` は `TUP_ge_slope6'`（`Sign.lean`）と一致する。 -/
example {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : 6 * n + 1 ≤ TUP n s + s * (s + 3) := by
  have h := TUP_ge_slope_tight 3 (by omega) s hs n hn
  have h3 := bb_three s hs
  omega

/-! ## `m ≥ 4` で定理E より真に強い -/

theorem bb_four_three : bb 4 3 = 33 := by
  have h1 : bb 4 2 = 3 * 3 + 3 + 3 := bb_base (m := 3) (by omega)
  have h2 : bb 3 3 + 1 = 3 * (3 + 3) := bb_three 3 (by omega)
  have h3 : bb 4 3 = bb 3 3 + bb 4 2 + 1 := bb_step (m := 3) (by omega) (by omega)
  omega

/-- **定理E は `c_4(3)=38`、定理E' は `34`。実測の折れ目も 34 なので E' は緊密で E は緩い。** -/
theorem slope8_strictly_better : bb 4 3 + 1 = 34 ∧ cc 4 3 = 38 :=
  ⟨by rw [bb_four_three], cc_four_three⟩

/-- 傾き 8 の緊密な下界（`m = 4`）。 -/
theorem TUG_ge_slope8_tight {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) :
    8 * n ≤ TUG n s + bb 4 s + 1 := by
  have h := TUG_ge_slope_tight (m := 4) (by omega) hs hn
  omega

end Spooky
