/-
  **「互いに素なビット帯での再帰的な貪欲 ＝ 軌道の大域最小」の到達可能性側を、$h$ 一般に示す**
  （第 81 夜 周 5・2026-10-12）。

  ## どの穴を埋めるか

  周 4（`GreedyMin.lean`）は残る紙 ① を 3 つに割り、**最小性**だけを取った:

      ★ `canonCode_le_codeAt` : ∀ b m v, 1 ≤ v →
          canonCode m (invAct b v) C ≤ codeAt m v (C.image (swapAct b))

  残っていたのは **(b) 到達可能性**（貪欲のコードを実現する `b` が存在すること）と
  **(c) 橋**（`codeAt h 1 C` = `keyCert h C`）である。本ファイルは **(b)** を取る。

  証人は**名指しの貪欲ビット**である:

      bG h C u := decide (canonCode (h - depB u - 1) (2u) C < canonCode (h - depB u - 1) (2u+1) C)

  すなわち「**左の子のコードが右より小さければ、その節点で左右を入れ替える**」。
  部分木の高さ `h - depB u - 1` が要るので、heap 番号の深さ `depB` を先に入れた
  （`Nat.log` は使わない。`invAct` が深さを保つことも示す ⇒ `invAct_depB`）。

  ## ここで示すこと

  - ★ `reach_aux` : `depB v + m = h` なる全ての節点で
        `codeAt m v (C.image (swapAct b)) = canonCode m (invAct b v) C`
    （`b` は貪欲則を満たす**任意の**ビット関数。`bG` はその 1 つ ⇒ `bG_spec`）。
  - ★ `reach_root` : `codeAt h 1 (C.image (swapAct (bG h C))) = canonCode h 1 C`。
  - ★★ `canonCode_isLeast` : 周 4 の最小性と合わせて
        **`canonCode h 1 C` は軌道 `{codeAt h 1 (C.image (swapAct b)) | b}` の最小元**。
    これで残る紙 ① は **(c) 橋だけ**になる。

  `decide` は 1 つも使っていない（`bG` の定義の中の `decide` は Bool への変換であって、
  証明の中で核に展開させるものではない）。$h$ にも木の大きさにも依らない。

  定義が証書のものと同じであることは Lean に書く**前**に外で確かめた
  （`autoresearch/tools/night81r5_reachcheck.py`: `depB` の保存・`reach_aux`・`reach_root`・
  軌道最小との一致を $h\le4$ の全配置 $2^{15}$ 個で。`bad_dep=bad_reach=bad_inner=bad_orbit=0`）。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。
-/
import GreedyMin

set_option autoImplicit false

namespace TreeAut

open Finset

/-! ## 1. heap 番号の深さ（根 = 0） -/

/-- heap 番号 `v` の深さ。`Nat.log` を使わず `swapAct` と同じ形の再帰で書く。 -/
def depB (v : ℕ) : ℕ :=
  if _h : v ≤ 1 then 0 else depB (v / 2) + 1
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem depB_le_one (v : ℕ) (h : v ≤ 1) : depB v = 0 := by
  rw [depB, dif_pos h]

theorem depB_eq (u r : ℕ) (hu : 1 ≤ u) (hr : r < 2) : depB (2 * u + r) = depB u + 1 := by
  have hv : ¬ (2 * u + r ≤ 1) := by omega
  have hdiv : (2 * u + r) / 2 = u := by omega
  conv_lhs => rw [depB]
  rw [dif_neg hv, hdiv]

theorem depB_two_mul (v : ℕ) (hv : 1 ≤ v) : depB (2 * v) = depB v + 1 := by
  have h := depB_eq v 0 hv (by omega)
  simpa using h

theorem depB_two_mul_succ (v : ℕ) (hv : 1 ≤ v) : depB (2 * v + 1) = depB v + 1 :=
  depB_eq v 1 hv (by omega)

/-- ★ `invAct b` は**深さを保つ**（部分木の高さが対応する相手でも同じであること）。 -/
theorem invAct_depB (b : ℕ → Bool) (w : ℕ) : depB (invAct b w) = depB w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w 2 with hw | hw
    · rw [invAct_le_one b w (by omega)]
    · obtain ⟨x, s, hx, hs, rfl⟩ := split_two hw
      have hx1 : 1 ≤ invAct b x := invAct_pos b x hx
      have hs' : (if b (invAct b x) then 1 - s else s) < 2 := by
        cases b (invAct b x) <;> simp <;> omega
      rw [invAct_eq b x s hx hs, depB_eq _ _ hx1 hs', depB_eq x s hx hs, ih x (by omega)]

/-! ## 2. ★ 貪欲ビット（到達可能性の証人） -/

/-- ★ 高さ `h` の木の節点 `u` で「左の子のコードが右より小さければ左右を入れ替える」ビット。
部分木の高さは `h - depB u - 1`。 -/
def bG (h : ℕ) (C : Finset ℕ) (u : ℕ) : Bool :=
  decide (canonCode (h - depB u - 1) (2 * u) C < canonCode (h - depB u - 1) (2 * u + 1) C)

/-- `bG` は貪欲則を満たす（`reach_aux` の仮定の形）。 -/
theorem bG_spec (h : ℕ) (C : Finset ℕ) (u m : ℕ) (hm : h - depB u - 1 = m) :
    (bG h C u = true ↔ canonCode m (2 * u) C < canonCode m (2 * u + 1) C) := by
  simp only [bG, hm, decide_eq_true_eq]

/-! ## 3. ★ 到達可能性（本ファイルの主定理） -/

/-- ★★ **貪欲則を満たすビット関数は、貪欲のコードをちょうど実現する**。
`b` に課すのは「節点 `u`（部分木の高さ `m`）で `b u = true` ⟺ 左の子のコードが右より小さい」
だけで、`bG` はその 1 つ（`bG_spec`）。$h$ にも木の大きさにも依らない。 -/
theorem reach_aux (C : Finset ℕ) (h : ℕ) (b : ℕ → Bool)
    (hb : ∀ u m : ℕ, 1 ≤ u → h - depB u - 1 = m →
      (b u = true ↔ canonCode m (2 * u) C < canonCode m (2 * u + 1) C)) :
    ∀ (m v : ℕ), 1 ≤ v → depB v + m = h →
      codeAt m v (C.image (swapAct b)) = canonCode m (invAct b v) C := by
  intro m
  induction m with
  | zero => intro v _ _; simp [codeAt, canonCode]
  | succ m ih =>
    intro v hv hd
    have hu : 1 ≤ invAct b v := invAct_pos b v hv
    have hdu : depB (invAct b v) = depB v := invAct_depB b v
    have hm : h - depB (invAct b v) - 1 = m := by omega
    have hiff := hb (invAct b v) m hu hm
    have h0 : invAct b (2 * v) = 2 * invAct b v + (if b (invAct b v) then 1 else 0) := by
      have hq := invAct_eq b v 0 hv (by omega)
      cases hbb : b (invAct b v) <;> simp [hbb] at hq ⊢ <;> omega
    have h1 : invAct b (2 * v + 1) = 2 * invAct b v + (if b (invAct b v) then 0 else 1) := by
      have hq := invAct_eq b v 1 hv (by omega)
      cases hbb : b (invAct b v) <;> simp [hbb] at hq ⊢ <;> omega
    have hmem : (if v ∈ C.image (swapAct b) then (1:ℕ) else 0)
        = (if invAct b v ∈ C then (1:ℕ) else 0) := by
      simp only [mem_image_swapAct]
    have hA := ih (2 * v) (by omega) (by rw [depB_two_mul v hv]; omega)
    have hB := ih (2 * v + 1) (by omega) (by rw [depB_two_mul_succ v hv]; omega)
    rw [h0] at hA
    rw [h1] at hB
    rw [codeAt_succ, canonCode_succ, hmem]
    rcases lt_or_ge (canonCode m (2 * invAct b v) C) (canonCode m (2 * invAct b v + 1) C)
      with hlt | hge
    · have hbt : b (invAct b v) = true := hiff.mpr hlt
      simp only [hbt, if_true, Nat.add_zero] at hA hB
      rw [hA, hB, max_eq_right (le_of_lt hlt), min_eq_left (le_of_lt hlt)]
    · have hbf : b (invAct b v) = false := by
        rcases hbb : b (invAct b v) with _ | _
        · rfl
        · exact absurd (hiff.mp hbb) (by omega)
      simp only [hbf, Bool.false_eq_true, if_false, Nat.add_zero] at hA hB
      rw [hA, hB, max_eq_left hge, min_eq_right hge]

/-- ★ 根に当てた形（`invAct b 1 = 1`・`depB 1 = 0`）。 -/
theorem reach_root (C : Finset ℕ) (h : ℕ) :
    codeAt h 1 (C.image (swapAct (bG h C))) = canonCode h 1 C := by
  have hmain := reach_aux C h (bG h C) (fun u m hu hm => bG_spec h C u m hm) h 1 (le_refl 1)
    (by rw [depB_le_one 1 (le_refl 1)]; omega)
  rwa [invAct_le_one _ 1 (le_refl 1)] at hmain

/-! ## 4. ★★ 最小性（周 4）＋ 到達可能性（本周） = 軌道の最小元 -/

/-- ★★ **証書の `canon` は軌道の最小元である**。
周 4 の `canonCode_le_root`（下界）と本周の `reach_root`（達成）を合わせた形。 -/
theorem canonCode_isLeast (C : Finset ℕ) (h : ℕ) :
    IsLeast {k : ℕ | ∃ b : ℕ → Bool, k = codeAt h 1 (C.image (swapAct b))}
      (canonCode h 1 C) := by
  constructor
  · exact ⟨bG h C, (reach_root C h).symm⟩
  · rintro k ⟨b, rfl⟩
    exact canonCode_le_root C b h

#print axioms depB_le_one
#print axioms depB_eq
#print axioms invAct_depB
#print axioms bG_spec
#print axioms reach_aux
#print axioms reach_root
#print axioms canonCode_isLeast

end TreeAut
