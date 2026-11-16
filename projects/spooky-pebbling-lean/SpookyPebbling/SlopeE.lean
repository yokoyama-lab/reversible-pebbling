/-
# 定理E — 任意の傾き `2m` の下界 `T_UG(n,s) ≥ 2mn - c_m(s)`

定理A（傾き 4）と定理D（傾き 6）で回した望遠鏡は、**傾きをいくつにしても回る**。
係数は 2 変数の漸化式で決まる:

$$c_1(s) = 0,\qquad c_m(1) = 2(m-1),\qquad c_m(s) = c_{m-1}(s) + c_m(s-1) + 2 .$$

## 望遠鏡（`m` と `s` の二重帰納）

Cor 4.12 の各項に、頭は **1 段低い傾き**の下界（`m-1`。Lemma 4.10 で `T_UG` から `T_UP` へ
落とすので `-1` が付く）、尻尾は**同じ傾きで 1 段低い上限**の下界（`s-1`）を入れる:

$$(2k-1) + \bigl(2(m{-}1)k - c_{m-1}(s) - 1\bigr) + \bigl(2m(n{-}k) - c_m(s{-}1)\bigr)
  = 2mn - c_m(s) .$$

`2k + 2(m-1)k - 2mk = 0` で **`k` が消える**。定理A・定理D はこの `m=2,3` の場合で、
実際 `c_2(s) = 2s`・`c_3(s) = s(s+3)` が漸化式から出る（下で確かめている）。

**`m ≥ 4` では緩い**（`c_4(3)` は漸化式 38・実測 34）。緊密にするには別の材料が要る。
-/
import SpookyPebbling.Lemma48

namespace Spooky

/-! ## 係数 `c_m(s)` -/

/-- 定理E の係数。`c_1 = 0`、`c_m(1) = 2(m-1)`、`c_m(s) = c_{m-1}(s) + c_m(s-1) + 2`。 -/
def cc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | (m + 2), 0 => 2 * (m + 1)
  | (m + 2), 1 => 2 * (m + 1)
  | (m + 2), (s + 2) => cc (m + 1) (s + 2) + cc (m + 2) (s + 1) + 2
termination_by m s => (m, s)

@[simp] theorem cc_one (s : ℕ) : cc 1 s = 0 := by cases s <;> simp [cc]

theorem cc_base {m : ℕ} (hm : 1 ≤ m) : cc (m + 1) 1 = 2 * m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp [cc]

theorem cc_step {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    cc (m + 1) (s + 1) = cc m (s + 1) + cc (m + 1) s + 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  simp [cc]

theorem cc_ge_base {m : ℕ} (hm : 1 ≤ m) : ∀ s, 1 ≤ s → 2 * m ≤ cc (m + 1) s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact le_of_eq (cc_base hm).symm
  | succ s hs ih =>
      rw [cc_step hm hs]
      omega

/-! ## 主定理 -/

/-- **定理E**: `T_UG(n,s) ≥ 2mn - c_m(s)`（`m ≥ 1`・`s ≥ 1`・到達可能な `n`）。 -/
theorem TUG_ge_slope : ∀ m, 1 ≤ m → ∀ s, 1 ≤ s → ∀ n, 1 ≤ n → (UGLengths n s).Nonempty →
    2 * m * n ≤ TUG n s + cc m s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro s _ n hn hne
      have := two_mul_le_TUG hn hne
      simp only [cc_one]
      omega
  | succ m hm ihm =>
      intro s hs
      induction s, hs using Nat.le_induction with
      | base =>
          intro n hn hne
          -- 上限 1 で unghost できるのは長さ 1 の鎖だけ
          have hn1 : n = 1 := by
            by_contra hc
            obtain ⟨L, ms, _, hrun⟩ := hne
            exact not_run_ug_cap_one (by omega) hrun
          subst hn1
          have h2 : TUG 1 1 = 2 := TUG_eq_of_le' (by omega) (by omega)
          have hb : cc (m + 1) 1 = 2 * m := cc_base hm
          omega
      | succ s hs ihs =>
          intro n hn hne
          rcases Nat.lt_or_ge n 2 with hlt | hge
          · -- `n = 1`
            have hn1 : n = 1 := by omega
            subst hn1
            have h2 : TUG 1 (s + 1) = 2 := TUG_eq_of_le' (by omega) (by omega)
            have hge2 := cc_ge_base hm (s + 1) (by omega)
            omega
          · -- `n ≥ 2`: Cor 4.12 の望遠鏡
            obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
            obtain ⟨k, hk, hkn, hbound, msT, hrunT⟩ := decomp_ug_ge' (by omega) hrun
            obtain ⟨q, rfl⟩ : ∃ q, n = k + q := ⟨n - k, by omega⟩
            have hq : 1 ≤ q := by omega
            have hnk : k + q - k = q := by omega
            rw [hnk] at hbound hrunT
            have hTne : (UGLengths q (s + 1 - 1)).Nonempty := ⟨msT.length, msT, rfl, hrunT⟩
            rw [show s + 1 - 1 = s from rfl] at hTne hbound
            -- 頭: 1 段低い傾き（Lemma 4.10 で `T_UG` から `T_UP` へ）
            have hUPne : (UPLengths k (s + 1)).Nonempty := UPLengths_nonempty (by omega) hk
            have hhead : 2 * m * k ≤ TUG k (s + 1) + cc m (s + 1) :=
              ihm (s + 1) (by omega) k hk (UGLengths_nonempty (by omega) hk)
            have hlem : TUG k (s + 1) ≤ TUP k (s + 1) + 1 := TUG_le_TUP_succ hk hUPne
            -- 尻尾: 同じ傾きで 1 段低い上限
            have htail : 2 * (m + 1) * q ≤ TUG q s + cc (m + 1) s := ihs q hq hTne
            -- `k` が消える
            have e1 : 2 * (m + 1) * (k + q)
                = 2 * (m * k) + 2 * k + 2 * ((m + 1) * q) := by ring
            have e2 : 2 * m * k = 2 * (m * k) := by ring
            have e3 : 2 * (m + 1) * q = 2 * ((m + 1) * q) := by ring
            have hccs : cc (m + 1) (s + 1) = cc m (s + 1) + cc (m + 1) s + 2 :=
              cc_step hm (by omega)
            have hlen' : ms.length = TUG (k + q) (s + 1) := hlen
            omega

/-! ## 定理A・定理D はこの特別な場合 -/

theorem cc_two : ∀ s, 1 ≤ s → cc 2 s = 2 * s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact cc_base (by omega)
  | succ s hs ih =>
      have hstep : cc 2 (s + 1) = cc 1 (s + 1) + cc 2 s + 2 := cc_step (m := 1) (by omega) hs
      rw [cc_one] at hstep
      omega

theorem cc_three : ∀ s, 1 ≤ s → cc 3 s = s * (s + 3) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => have := cc_base (m := 2) (by omega); omega
  | succ s hs ih =>
      have h2 : cc 2 (s + 1) = 2 * (s + 1) := cc_two (s + 1) (by omega)
      have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * (s + 1) + 2 := by ring
      have hstep : cc 3 (s + 1) = cc 2 (s + 1) + cc 3 s + 2 := cc_step (m := 2) (by omega) hs
      omega

/-- **定理A を定理E から再導出**（`m = 2`）。独立に証明した `TUG_ge_slope4` と一致する。 -/
theorem TUG_ge_slope4_of_E {s : ℕ} (hs : 2 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    4 * n ≤ TUG n s + 2 * s := by
  have h := TUG_ge_slope 2 (by omega) s (by omega) n hn (UGLengths_nonempty hs hn)
  rw [cc_two s (by omega)] at h
  omega

/-- **定理D を定理E から再導出**（`m = 3`）。独立に証明した `TUG_ge_slope6` と一致する。 -/
theorem TUG_ge_slope6_of_E {s : ℕ} (hs : 2 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    6 * n ≤ TUG n s + s * (s + 3) := by
  have h := TUG_ge_slope 3 (by omega) s (by omega) n hn (UGLengths_nonempty hs hn)
  rw [cc_three s (by omega)] at h
  omega

/-- 傾き 8 の下界（`m = 4`）。 -/
theorem TUG_ge_slope8 {s : ℕ} (hs : 2 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    8 * n ≤ TUG n s + cc 4 s :=
  TUG_ge_slope 4 (by omega) s (by omega) n hn (UGLengths_nonempty hs hn)

/-- **`m ≥ 4` では緩いことの記録**: 漸化式は `c_4(3) = 38` を出すが、
実測の折れ目からは 34（`notes/spooky-pebbling/theorem_slope6.py` の表）。
`m ≤ 3` は `cc_two` / `cc_three` のとおり厳密。 -/
theorem cc_four_three : cc 4 3 = 38 := by
  have h1 : cc 4 1 = 6 := cc_base (m := 3) (by omega)
  have h2 : cc 4 2 = cc 3 2 + cc 4 1 + 2 := cc_step (m := 3) (by omega) (by omega)
  have h3 : cc 4 3 = cc 3 3 + cc 4 2 + 2 := cc_step (m := 3) (by omega) (by omega)
  have h4 : cc 3 2 = 2 * (2 + 3) := cc_three 2 (by omega)
  have h5 : cc 3 3 = 3 * (3 + 3) := cc_three 3 (by omega)
  omega

end Spooky
