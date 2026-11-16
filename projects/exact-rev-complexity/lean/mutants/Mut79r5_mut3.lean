/-
  **完全二分木の自己同型を「子を入れ替えるビット」で与え、群であることを $h$ に依らず示す**
  （第79夜 周5・2026-10-10）。

  第79夜 周4（`LevelCertT3.lean`）では Aut($T_3$) を**置換の表 8 本**で与え、群であることを
  `∀ t₁ ∈ tab, ∀ t₂ ∈ tab, ∃ t₃ ∈ tab, ∀ x < 8, …` の `decide` で片づけた。
  この形は $h$ で**二重指数**に膨らむ（表の本数 $2^{2^{h-1}-1}$、合成の検査はその 2 乗）ので、
  $h=4$ で 128 本 × 128 本 × 16 点 ＝ 26 万点の `decide` が最初の壁になる。

  ここでは表をやめ、自己同型を**ビット関数** `b : ℕ → Bool`（`b u = true` ⟺ 節点 `u` で
  左右の子を入れ替える）で与える。heap 番号（根 = 1、`v` の子 = `2v`, `2v+1`）で

      swapAct b 0 = 0,  swapAct b 1 = 1,
      swapAct b (2u + r) = 2 * swapAct b u + (if b u then 1 - r else r)   （u ≥ 1, r < 2）

  とすると、合成が**閉形式**になる（★ `swapAct_comp`）:

      swapAct b ∘ swapAct c = swapAct (fun u => xor (c u) (b (swapAct c u)))

  ⇒ 群であることの検査が **1 つの定理**になり、$h$ にも表の本数にも依らない。
  逆元・恒等元・深さの保存・子の集合の**厳密な**同変（周 3 の「さもなくば free」が不要）も同様。

  ⚠ **新しい数値は 1 つも足していない。** $M^*$ の値は 1 つも触っていない。
  ここで作ったのは、商レベル集合証書の機構を $h$ 一般に運ぶための道具である。

  公式は Lean に書く前に `autoresearch/tools/night79r5_swapact_check.py` で
  $h=2,3,4$（族 2/8/128 元・合成 4/64/16384 対）について外で検算し、
  さらに $h=3$ の族が周 4 の `tabT3`（生成した Aut($T_3$)）と**集合として一致**することを確かめた。
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Image

set_option autoImplicit false

namespace TreeAut

/-! ## 1. 定義 -/

/-- 子の入れ替えビット `b` が定める木の自己同型（heap 番号）。 -/
def swapAct (b : ℕ → Bool) (v : ℕ) : ℕ :=
  if _h : v ≤ 1 then v
  else 2 * swapAct b (v / 2) + (if b (v / 2) then 1 - v % 2 else v % 2)
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- 逆向きの作用（`invAct b` が `swapAct b` の左逆写像になる）。 -/
def invAct (b : ℕ → Bool) (w : ℕ) : ℕ :=
  if _h : w ≤ 1 then w
  else 2 * invAct b (w / 2) + (if b (w / 2) then 1 - w % 2 else w % 2)
termination_by w
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## 2. 定義式 -/

theorem swapAct_le_one (b : ℕ → Bool) (v : ℕ) (h : v ≤ 1) : swapAct b v = v := by
  rw [swapAct, dif_pos h]

theorem invAct_le_one (b : ℕ → Bool) (w : ℕ) (h : w ≤ 1) : invAct b w = w := by
  rw [invAct, dif_pos h]

theorem swapAct_eq (b : ℕ → Bool) (u r : ℕ) (hu : 1 ≤ u) (hr : r < 2) :
    swapAct b (2 * u + r) = 2 * swapAct b u + (if b u then 1 - r else r) := by
  have hv : ¬ (2 * u + r ≤ 1) := by omega
  have hdiv : (2 * u + r) / 2 = u := by omega
  have hmod : (2 * u + r) % 2 = r := by omega
  conv_lhs => rw [swapAct]
  rw [dif_neg hv, hdiv, hmod]

theorem invAct_eq (b : ℕ → Bool) (x s : ℕ) (hx : 1 ≤ x) (hs : s < 2) :
    invAct b (2 * x + s) = 2 * invAct b x + (if b (invAct b x) then 1 - s else s) := by
  have hv : ¬ (2 * x + s ≤ 1) := by omega
  have hdiv : (2 * x + s) / 2 = x := by omega
  have hmod : (2 * x + s) % 2 = s := by omega
  conv_lhs => rw [invAct]
  rw [dif_neg hv, hdiv, hmod]

/-- heap 番号の分解（`v ≥ 2` なら `v = 2u + r`、`u ≥ 1`、`r < 2`）。 -/
theorem split_two {v : ℕ} (hv : 2 ≤ v) : ∃ u r, 1 ≤ u ∧ r < 2 ∧ v = 2 * u + r :=
  ⟨v / 2, v % 2, by omega, by omega, by omega⟩

/-! ## 3. 正値性・恒等元 -/

theorem swapAct_pos (b : ℕ → Bool) (v : ℕ) (h : 1 ≤ v) : 1 ≤ swapAct b v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.lt_or_ge v 2 with hv | hv
    · rw [swapAct_le_one b v (by omega)]; omega
    · obtain ⟨u, r, hu, hr, rfl⟩ := split_two hv
      have hiu := ih u (by omega) hu
      rw [swapAct_eq b u r hu hr]
      omega

theorem swapAct_id (v : ℕ) : swapAct (fun _ => false) v = v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.lt_or_ge v 2 with hv | hv
    · exact swapAct_le_one _ v (by omega)
    · obtain ⟨u, r, hu, hr, rfl⟩ := split_two hv
      rw [swapAct_eq _ u r hu hr, ih u (by omega)]
      simp

/-! ## 4. ★ 合成の閉形式 -/

/-- ★ **合成は同じ形で閉じる**（$h$ にも木の大きさにも依らない）。
これが周 4 の `tabT3_comp`（表の 2 乗の `decide`）を置き換える。 -/
theorem swapAct_comp (b c : ℕ → Bool) (v : ℕ) :
    swapAct b (swapAct c v) = swapAct (fun u => xor (c u) (b (swapAct c u))) v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.lt_or_ge v 2 with hv | hv
    · rw [swapAct_le_one c v (by omega), swapAct_le_one b v (by omega),
        swapAct_le_one (fun u => xor (c u) (b (swapAct c u))) v (by omega)]
    · obtain ⟨u, r, hu, hr, rfl⟩ := split_two hv
      have hw : 1 ≤ swapAct c u := swapAct_pos c u hu
      have hs : (if c u then 1 - r else r) < 2 := by cases c u <;> simp <;> omega
      rw [swapAct_eq c u r hu hr, swapAct_eq b (swapAct c u) _ hw hs,
        swapAct_eq (fun u => xor (c u) (b (swapAct c u))) u r hu hr, ih u (by omega)]
      cases hcu : c u <;> cases hbw : b (swapAct c u) <;> simp [hcu, hbw] <;> omega

/-! ## 5. 逆元 -/

theorem invAct_swapAct (b : ℕ → Bool) (v : ℕ) : invAct b (swapAct b v) = v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.lt_or_ge v 2 with hv | hv
    · rw [swapAct_le_one b v (by omega), invAct_le_one b v (by omega)]
    · obtain ⟨u, r, hu, hr, rfl⟩ := split_two hv
      have hw : 1 ≤ swapAct b u := swapAct_pos b u hu
      have hs : (if b u then 1 - r else r) < 2 := by cases b u <;> simp <;> omega
      rw [swapAct_eq b u r hu hr, invAct_eq b (swapAct b u) _ hw hs, ih u (by omega)]
      cases hbu : b u <;> simp [hbu] <;> omega

/-! ## 6. 深さの保存（内部頂点は内部頂点へ・葉は葉へ） -/

theorem swapAct_depth (b : ℕ → Bool) (d : ℕ) : ∀ v, 2 ^ d ≤ v → v < 2 ^ (d + 1) →
    2 ^ d ≤ swapAct b v ∧ swapAct b v < 2 ^ (d + 1) := by
  induction d with
  | zero =>
    intro v h1 h2
    have hv : v = 1 := by simp at h1 h2; omega
    subst hv
    rw [swapAct_le_one b 1 (by omega)]
    simp
  | succ d ih =>
    intro v h1 h2
    have e1 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have e2 : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    have hv : 2 ≤ v := by
      have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      omega
    obtain ⟨u, r, hu, hr, rfl⟩ := split_two hv
    have hu1 : 2 ^ d ≤ u := by omega
    have hu2 : u < 2 ^ (d + 1) := by omega
    obtain ⟨g1, g2⟩ := ih u hu1 hu2
    have hs : (if b u then 1 - r else r) < 2 := by cases b u <;> simp <;> omega
    rw [swapAct_eq b u r hu hr]
    omega

/-! ## 7. 子の集合の厳密な同変 -/

/-- ★ **子の集合は像と厳密に一致する**。周 3 の `hpredg`（「像か、さもなくば free」）が
`∀ v` について無条件に出るので、木ごとの `decide` が 1 つ消える。 -/
theorem swapAct_children (b : ℕ → Bool) (v : ℕ) (hv : 1 ≤ v) :
    ({2 * v, 2 * v + 1} : Finset ℕ).image (swapAct b) =
      ({2 * swapAct b v, 2 * swapAct b v + 1} : Finset ℕ) := by
  have h0 : swapAct b (2 * v) = 2 * swapAct b v + (if b v then 1 else 0) := by
    have h := swapAct_eq b v 0 hv (by omega)
    simpa using h
  have h1 : swapAct b (2 * v + 1) = 2 * swapAct b v + (if b v then 0 else 1) := by
    have h := swapAct_eq b v 1 hv (by omega)
    simpa using h
  cases hbv : b v <;>
    simp [Finset.image_insert, h0, h1, hbv, Finset.pair_comm]

#print axioms swapAct_eq
#print axioms swapAct_id
#print axioms swapAct_comp
#print axioms invAct_swapAct
#print axioms swapAct_depth
#print axioms swapAct_children

end TreeAut
