/-
  **「互いに素なビット帯での再帰的な貪欲 ＝ 軌道の大域最小」の最小性側を、$h$ 一般に示す**
  （第 81 夜 周 4・2026-10-12）。

  ## どの穴を埋めるか

  第 81 夜 周 3（`KeyCert.lean`）で、証書が最小化している鍵は

      `keyCert h C = bitkey (C.image (relabCert h))`   （preorder ビットマスク）

  だと名指しした。残る紙 ① は「証書の再帰的 `canon` が、その鍵の**軌道最小元**である」
  という一文で、周 3 は $h\le4$ の**全配置**（$2^{15}$ 個）で機械照合しただけだった
  （$h=7$ は $2^{127}$ 配置なので全数では閉じない）。

  本ファイルはその一文の**最小性側**を $h$ 一般に機械で示す:

      ★ `canonCode_le_codeAt` : ∀ b : ℕ → Bool, ∀ m v, 1 ≤ v →
          canonCode m (invAct b v) C ≤ codeAt m v (C.image (swapAct b))

  すなわち**軌道のどの元のコードも、貪欲が与えるコード以上**である。
  帯の幅は $2^m-1$ ビットで、右（上位）の帯が左（下位）の帯を支配する
  （`band_lt` / `band_mono_aux`）——紙に残っていた「互いに素なビット帯の単調性」が、
  この 2 本の算術補題そのものである。

  ## ここで示すこと / 示さないこと

  - ★ 示す: **最小性**（貪欲のコード ≤ 軌道の全元のコード）。$h$・木の大きさに依らない。
  - ✗ 示さない（同じ一文の残り半分）:
    * **到達可能性**: 貪欲のコードを実現する $b$ が存在すること。
    * **橋**: `codeAt h 1 C` が `keyCert h C`（= 2 × preorder ビットマスク）と等しいこと。
      周 3 の `lean_def_cross_check`（$h\le7$ の全頂点）と本周の
      `night81r4_codecheck.py`（$h\le4$ の全配置）がプログラムの層で確かめている。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。

  定義が証書のものと同じであることは Lean に書く前に外で確かめた
  （`autoresearch/tools/night81r4_codecheck.py`: `codeAt` = 証書のコード、
  `canonCode` = 証書の `canon` のコード。$h\le4$ の全配置）。
-/
import TreeAut

set_option autoImplicit false

namespace TreeAut

open Finset

/-! ## 0. `swapAct` の右逆（`invAct` は両側逆） -/

theorem invAct_pos (b : ℕ → Bool) (w : ℕ) (h : 1 ≤ w) : 1 ≤ invAct b w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w 2 with hw | hw
    · rw [invAct_le_one b w (by omega)]; omega
    · obtain ⟨x, s, hx, hs, rfl⟩ := split_two hw
      have := ih x (by omega) hx
      rw [invAct_eq b x s hx hs]
      omega

/-- ★ `swapAct b` は `invAct b` の左逆でもある（`invAct_swapAct` の裏返し）。 -/
theorem swapAct_invAct (b : ℕ → Bool) (w : ℕ) : swapAct b (invAct b w) = w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w 2 with hw | hw
    · rw [invAct_le_one b w (by omega), swapAct_le_one b w (by omega)]
    · obtain ⟨x, s, hx, hs, rfl⟩ := split_two hw
      have hx1 : 1 ≤ invAct b x := invAct_pos b x hx
      have hs' : (if b (invAct b x) then 1 - s else s) < 2 := by
        cases b (invAct b x) <;> simp <;> omega
      rw [invAct_eq b x s hx hs, swapAct_eq b (invAct b x) _ hx1 hs', ih x (by omega)]
      cases hb : b (invAct b x) <;> simp [hb] <;> omega

/-- 像の要素であることは、逆像が元の集合に属することと同値。 -/
theorem mem_image_swapAct (b : ℕ → Bool) (C : Finset ℕ) (v : ℕ) :
    v ∈ C.image (swapAct b) ↔ invAct b v ∈ C := by
  constructor
  · intro hv
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hv
    rw [← hue, invAct_swapAct]
    exact hu
  · intro hv
    exact Finset.mem_image.mpr ⟨invAct b v, hv, swapAct_invAct b v⟩

/-! ## 1. 部分木のコード（preorder ビットマスクの局所版）と、貪欲の値 -/

/-- 高さ `m`・根 `v` の部分木が持つコード。根のビットが最下位、左部分木が次の帯、
右部分木が最上位の帯（幅はどちらも $2^m-1$ ビット）。証書 `night76_cert_spec.md` §1.2
のコードと同じもの。 -/
def codeAt : ℕ → ℕ → Finset ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, v, C =>
      (if v ∈ C then 1 else 0) + 2 * codeAt m (2 * v) C + 2 ^ 2 ^ m * codeAt m (2 * v + 1) C

/-- 証書の `canon` が作るコード（各節点で **max を下位・min を上位**に置く貪欲）。 -/
def canonCode : ℕ → ℕ → Finset ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, v, C =>
      (if v ∈ C then 1 else 0)
        + 2 * max (canonCode m (2 * v) C) (canonCode m (2 * v + 1) C)
        + 2 ^ 2 ^ m * min (canonCode m (2 * v) C) (canonCode m (2 * v + 1) C)

theorem codeAt_succ (m v : ℕ) (C : Finset ℕ) :
    codeAt (m + 1) v C =
      (if v ∈ C then 1 else 0) + 2 * codeAt m (2 * v) C + 2 ^ 2 ^ m * codeAt m (2 * v + 1) C :=
  rfl

theorem canonCode_succ (m v : ℕ) (C : Finset ℕ) :
    canonCode (m + 1) v C =
      (if v ∈ C then 1 else 0)
        + 2 * max (canonCode m (2 * v) C) (canonCode m (2 * v + 1) C)
        + 2 ^ 2 ^ m * min (canonCode m (2 * v) C) (canonCode m (2 * v + 1) C) :=
  rfl

/-! ## 2. ★ 帯の算術（紙に残っていた一文はこの 2 本） -/

/-- 上の帯の底 $2^{2^m}$ は、帯の幅 $2^{2^m-1}$ のちょうど 2 倍。 -/
theorem two_pow_band (m : ℕ) : (2:ℕ) ^ 2 ^ m = 2 * 2 ^ (2 ^ m - 1) := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ m = k + 1 := ⟨2 ^ m - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  ring

/-- 高さ $m+1$ の帯の幅は、下の帯の底 × 下の帯の幅。 -/
theorem two_pow_band_succ (m : ℕ) :
    (2:ℕ) ^ (2 ^ (m + 1) - 1) = 2 ^ 2 ^ m * 2 ^ (2 ^ m - 1) := by
  rw [← pow_add]
  congr 1
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
  omega

/-- ★ **帯からはみ出さない**: 根 1 ビット ＋ 幅 $2^m-1$ の帯 2 本は、幅 $2^{m+1}-1$ に収まる。 -/
theorem band_lt {m a L R : ℕ} (ha : a ≤ 1)
    (hL : L < 2 ^ (2 ^ m - 1)) (hR : R < 2 ^ (2 ^ m - 1)) :
    a + 2 * L + 2 ^ 2 ^ m * R < 2 ^ (2 ^ (m + 1) - 1) := by
  rw [two_pow_band_succ]
  have hbase : a + 2 * L < 2 ^ 2 ^ m := by rw [two_pow_band]; omega
  calc a + 2 * L + 2 ^ 2 ^ m * R
      < 2 ^ 2 ^ m + 2 ^ 2 ^ m * R := Nat.add_lt_add_right hbase _
    _ = 2 ^ 2 ^ m * (R + 1) := by ring
    _ ≤ 2 ^ 2 ^ m * 2 ^ (2 ^ m - 1) := Nat.mul_le_mul (le_refl _) hR

/-- ★★ **上の帯が下の帯を支配する**。
`min` を上位・`max` を下位に置いた値は、上位が `min` 以上で、等号のときだけ下位が `max` 以上
であるような任意の値以下である。$P = 2Q$（帯の底 = 幅の 2 倍）だけを使う。 -/
theorem band_mono_aux {P Q a L R X Y : ℕ} (hPQ : P = 2 * Q)
    (hL : L < Q) (hR : R < Q) (hminY : min L R ≤ Y) (hEq : Y = min L R → max L R ≤ X) :
    a + 2 * max L R + P * min L R ≤ a + 2 * X + P * Y := by
  rcases eq_or_lt_of_le hminY with he | hlt
  · have hX := hEq he.symm
    rw [← he]
    exact Nat.add_le_add_right (by omega) _
  · have hmax : max L R < Q := max_lt hL hR
    have hchain : a + 2 * max L R + P * min L R < a + 2 * X + P * Y :=
      calc a + 2 * max L R + P * min L R
          = a + P * min L R + 2 * max L R := by ring
        _ < a + P * min L R + P := by
              subst hPQ
              exact Nat.add_lt_add_left (by omega) _
        _ = a + P * (min L R + 1) := by ring
        _ ≤ a + P * Y := Nat.add_le_add_left (Nat.mul_le_mul (le_refl _) hlt) _
        _ ≤ a + 2 * X + P * Y := Nat.add_le_add_right (Nat.le_add_right a (2 * X)) _
    exact le_of_lt hchain

/-! ## 3. コードは帯に収まる -/

theorem codeAt_lt (m : ℕ) : ∀ (v : ℕ) (C : Finset ℕ), codeAt m v C < 2 ^ (2 ^ m - 1) := by
  induction m with
  | zero => intro v C; simp [codeAt]
  | succ m ih =>
    intro v C
    rw [codeAt_succ]
    exact band_lt (by split <;> omega) (ih (2 * v) C) (ih (2 * v + 1) C)

theorem canonCode_lt (m : ℕ) : ∀ (v : ℕ) (C : Finset ℕ), canonCode m v C < 2 ^ (2 ^ m - 1) := by
  induction m with
  | zero => intro v C; simp [canonCode]
  | succ m ih =>
    intro v C
    rw [canonCode_succ]
    have hL := ih (2 * v) C
    have hR := ih (2 * v + 1) C
    exact band_lt (by split <;> omega) (max_lt hL hR) (lt_of_le_of_lt (min_le_left _ _) hL)

/-! ## 4. ★ 最小性（本ファイルの主定理） -/

/-- ★★ **貪欲のコードは軌道の全元のコード以下**。
`b : ℕ → Bool`（子の入れ替えビット）が与える自己同型 `swapAct b` で `C` を動かしても、
高さ `m` の部分木のコードが貪欲の値を下回ることはない。$h$ にも木の大きさにも依らない。 -/
theorem canonCode_le_codeAt (C : Finset ℕ) (b : ℕ → Bool) :
    ∀ (m v : ℕ), 1 ≤ v → canonCode m (invAct b v) C ≤ codeAt m v (C.image (swapAct b)) := by
  intro m
  induction m with
  | zero => intro v _; simp [canonCode, codeAt]
  | succ m ih =>
    intro v hv
    have hu : 1 ≤ invAct b v := invAct_pos b v hv
    have h0 : invAct b (2 * v) = 2 * invAct b v + (if b (invAct b v) then 1 else 0) := by
      have h := invAct_eq b v 0 hv (by omega)
      cases hb : b (invAct b v) <;> simp [hb] at h ⊢ <;> omega
    have h1 : invAct b (2 * v + 1) = 2 * invAct b v + (if b (invAct b v) then 0 else 1) := by
      have h := invAct_eq b v 1 hv (by omega)
      cases hb : b (invAct b v) <;> simp [hb] at h ⊢ <;> omega
    have hmem : (if v ∈ C.image (swapAct b) then (1:ℕ) else 0)
        = (if invAct b v ∈ C then (1:ℕ) else 0) := by
      simp only [mem_image_swapAct]
    have hA := ih (2 * v) (by omega)
    have hB := ih (2 * v + 1) (by omega)
    rw [h0] at hA
    rw [h1] at hB
    rw [codeAt_succ, canonCode_succ, hmem]
    cases hb : b (invAct b v) with
    | false =>
        simp only [hb, if_false] at hA hB
        refine band_mono_aux (two_pow_band m) (canonCode_lt m (2 * invAct b v) C)
          (canonCode_lt m (2 * invAct b v + 1) C) ?_ ?_
        · simp at hA hB
          omega
        · intro hY
          simp at hA hB
          omega
    | true =>
        simp only [hb, if_true] at hA hB
        refine band_mono_aux (two_pow_band m) (canonCode_lt m (2 * invAct b v) C)
          (canonCode_lt m (2 * invAct b v + 1) C) ?_ ?_
        · simp at hA hB
          omega
        · intro hY
          simp at hA hB
          omega

/-- 根に当てた形（`invAct b 1 = 1`）。 -/
theorem canonCode_le_root (C : Finset ℕ) (b : ℕ → Bool) (h : ℕ) :
    canonCode h 1 C ≤ codeAt h 1 (C.image (swapAct b)) := by
  have hroot := canonCode_le_codeAt C b h 1 (le_refl 1)
  rwa [invAct_le_one b 1 (le_refl 1)] at hroot

#print axioms swapAct_invAct
#print axioms band_lt
#print axioms band_mono_aux
#print axioms codeAt_lt
#print axioms canonCode_lt
#print axioms canonCode_le_codeAt
#print axioms canonCode_le_root

end TreeAut
