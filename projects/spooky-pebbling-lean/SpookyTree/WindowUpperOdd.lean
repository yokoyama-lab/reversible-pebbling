/-
# 窓の上界・m = 2・h 奇数（紙の定理 B-odd）: 構成と手数

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_ODD_2026-11.md`（補題 O1〜O4，4 節の閉じた式）。
`h = 2H + 1`，`X = 2^H`，`δ = h + 5`，`f = p − δ`，`g = ⌊p/2⌋`。

構成は `WindowUpper.lean` の `stratW`（紙の B★ の m = 2）と同じ骨格で，最終段だけを紙どおり
「部分木の高さ `t` が `2^t ≤ p` なら F，そうでなければ M」にした（`finW`）。
* 紙の F（`Fst`）: 全部ゴーストの部分木を下から全部置き（unghost），上から全部外す。
* 段 1 の内部（`rootP`）の手数は紙の Λ と同じ閉じた形 `|rootP| + 4·2^e ≤ 2ef + 5`（`e = ⌊log₂ f⌋`）で抑える
  （`length_rootP_odd`。`stratW` の証明で使った粗い `2fh` では足りない）。
* 最終段の手数は，前線の部分木の高さが 2 通り（`lo`，`lo + 1`）しかないことを使い，
  1 個あたりの手数を `2^t` の 1 次式（係数は `X` 倍してから整数）で上から抑えて足す（`length_onSp_mul`）。
  2 つの高さで等号なので，紙の閉じた式とちょうど一致する。

紙との違い: 前線の形（`WindowUpper.lean` と同じく ⌈n/2⌉・⌊n/2⌋ に再帰的に割る）。深さの分布
（深さ `e` が `2^e − u` 個，深さ `e + 1` が `2u` 個）と内部の頂点の深さの分布は紙の F_{e,u} と同じなので，
手数の上界は紙の T_B★ と同じ式になる。
-/
import SpookyTree.WindowUpper

namespace SpookyTree

/-! ## 紙の F -/

/-- 紙の F: 全部ゴーストの高さ `j` の部分木を，下から全部置いて（unghost）上から全部外す。 -/
def Fst (j : ℕ) (a : Node) : List Move := placeInt .unghost j a ++ removeInt j a

theorem Fst_spec_odd {h j : ℕ} {a : Node} {c : Config} (_hj : 1 ≤ j) (ha : a.length + j = h)
    (hP : Pat (cst .ghost) j a c) :
    Runs h j a (2 ^ j - 1) c (Fst j a) ∧ Pat (cst .empty) j a (run c (Fst j a)) := by
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  have hk := pcPat_peb_succ j
  have hP' : Pat (glue .ghost j (cst .pebble)) (0 + j) a c := by
    rw [Nat.zero_add]; exact (Pat_glue_short (cst .pebble) le_rfl).mpr hP
  obtain ⟨hR1, hQ1⟩ := placeInt_spec (h := h) (j := 0) hug (g := cst .pebble)
    (fun h0 => absurd h0 (by decide)) j a c (by omega) hP'
  obtain ⟨hR2, hQ2⟩ := removeInt_spec (h := h) (j := 0) (g := cst .pebble)
    (fun h0 => absurd h0 (by decide)) j a _ (by omega) hQ1
  rw [glue_cst, Nat.zero_add] at hR1 hR2
  rw [Nat.zero_add] at hQ2
  refine ⟨Runs_append.mpr ⟨hR1.mono (by omega), ?_⟩, ?_⟩
  · exact hR2.mono (by omega)
  · show Pat (cst .empty) j a (run c (placeInt .unghost j a ++ removeInt j a))
    rw [run_append]; exact (Pat_glue_short (cst .pebble) le_rfl).mp hQ2

theorem length_Fst (j : ℕ) (a : Node) : (Fst j a).length + 2 = 2 * 2 ^ j := by
  unfold Fst
  rw [List.length_append]
  have h1 := length_placeInt .unghost j a
  have h2 := length_removeInt j a
  omega

/-! ## 最終段: 高さで F と M を選ぶ -/

/-- 最終段（紙の 2.3 節，m = 2）: 部分木の高さ `t` が `2^t ≤ p`（`2^t − 1 ≤ Q = p − 1`）なら F，そうでなければ M。 -/
def finW (h p g : ℕ) (a : Node) : List Move :=
  if 2 ^ (h - a.length) ≤ p then Fst (h - a.length) a else Mst h (h - a.length) g a

theorem finW_spec {h p g j : ℕ} {a : Node} {c : Config} (ha : a.length + j = h) (hj : 1 ≤ j)
    (hM : ¬ 2 ^ j ≤ p → Shp 1 3 j g) (hg1 : g + 8 ≤ p) (hg2 : 2 * g ≤ p)
    (hP : Pat (cst .ghost) j a c) :
    Runs h j a (p - 1) c (finW h p g a) ∧ Pat (cst .empty) j a (run c (finW h p g a)) := by
  have hj' : h - a.length = j := by omega
  unfold finW
  rw [hj']
  split_ifs with hF
  · obtain ⟨hR, hQ⟩ := Fst_spec_odd hj ha hP
    exact ⟨hR.mono (by omega), hQ⟩
  · have hS := hM hF
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    have hp3 : 2 ^ 3 - 1 + (g - 1) * 1 ≤ p - 1 := by rw [h8]; omega
    exact Mst_spec hS ha hP (by omega) (by omega) hp3

theorem length_finW_F {h p g j : ℕ} {a : Node} (ha : a.length + j = h) (hF : 2 ^ j ≤ p) :
    (finW h p g a).length + 2 = 2 * 2 ^ j := by
  have hj' : h - a.length = j := by omega
  unfold finW
  rw [hj', if_pos hF]
  exact length_Fst j a

theorem length_finW_M {h p g j : ℕ} {a : Node} (ha : a.length + j = h) (hF : ¬ 2 ^ j ≤ p)
    (hS : Shp 1 3 j g) : (finW h p g a).length + (4 * g + 2) ≤ 4 * 2 ^ j := by
  have hj' : h - a.length = j := by omega
  unfold finW
  rw [hj', if_neg hF]
  have := length_Mst hS ha
  omega

/-! ## 段 1 の内部の手数（紙の Λ）

`rootP k n y` は内部の頂点 `w` を `max(深さ, 1)` 回置く（紙の補題 8 の Λ）。その手数は `2Λ − 1` で，
`2^e ≤ n < 2^{e+1}` なら `2Λ − 1 = 2en − 4·2^e + 5`。ここでは `≤` を示す。 -/

theorem cB_one_odd (pl : Op) : ∀ (k : ℕ) (y : Node), cB pl k 1 y = []
  | 0, _ => rfl
  | k + 1, y => by rw [cB, if_pos le_rfl]

theorem clB_one_odd : ∀ (k : ℕ) (y : Node), clB k 1 y = []
  | 0, _ => rfl
  | k + 1, y => by rw [clB, if_pos le_rfl]

theorem length_cB_indep (pl pl' : Op) :
    ∀ (k n : ℕ) (y : Node), (cB pl k n y).length = (cB pl' k n y).length := by
  intro k
  induction k with
  | zero => intro n y; rfl
  | succ k ih =>
    intro n y
    by_cases hn : n ≤ 1
    · have e1 : cB pl (k + 1) n y = [] := by rw [cB, if_pos hn]
      have e2 : cB pl' (k + 1) n y = [] := by rw [cB, if_pos hn]
      rw [e1, e2]
    · have e1 : cB pl (k + 1) n y = cB pl k ((n + 1) / 2) (y ++ [false]) ++
          cB pl k (n / 2) (y ++ [true]) ++ [⟨pl, y⟩] ++
            (gh ((n + 1) / 2) (y ++ [false]) ++ gh (n / 2) (y ++ [true])) := by
        rw [cB, if_neg hn]
      have e2 : cB pl' (k + 1) n y = cB pl' k ((n + 1) / 2) (y ++ [false]) ++
          cB pl' k (n / 2) (y ++ [true]) ++ [⟨pl', y⟩] ++
            (gh ((n + 1) / 2) (y ++ [false]) ++ gh (n / 2) (y ++ [true])) := by
        rw [cB, if_neg hn]
      rw [e1, e2]
      simp only [List.length_append, List.length_singleton, ih]

theorem length_cB_two_odd (pl : Op) (k m : ℕ) (y : Node) (hm : 2 ≤ m) :
    (cB pl k m y).length + 3 ≤ 2 * m := by
  have := length_cB pl k m y (by omega)
  rw [if_neg (by omega)] at this
  omega

theorem base_odd {n e : ℕ} (_hn : 1 ≤ n) (he : 2 ^ e ≤ n) : 4 * 2 ^ e ≤ 2 * e * n + 5 := by
  rcases e with _ | _ | e
  · simp
  · norm_num at he ⊢; omega
  · have h4 : 4 ≤ 2 * (e + 1 + 1) := by omega
    have := Nat.mul_le_mul h4 he
    omega

/-- 子 1 個ぶん（comp_B と clr_B）の手数。 -/
theorem kid_odd {k m e : ℕ} {y : Node} (hm : 2 ≤ m)
    (ih : (clB k m y).length + 4 * 2 ^ e ≤ 2 * e * m + 5) :
    (cB .unghost k m y).length + (clB k m y).length + 3 + 4 * 2 ^ e ≤ 2 * m + 2 * e * m + 5 := by
  have := length_cB_two_odd .unghost k m y hm
  omega

theorem length_clB_odd : ∀ (k n e : ℕ) (y : Node), 1 ≤ n → 2 ^ e ≤ n → n < 2 ^ (e + 1) →
    (clB k n y).length + 4 * 2 ^ e ≤ 2 * e * n + 5 := by
  intro k
  induction k with
  | zero =>
    intro n e y hn he _
    have := base_odd hn he
    have e0 : clB 0 n y = [] := rfl
    rw [e0, List.length_nil, Nat.zero_add]
    exact this
  | succ k ih =>
    intro n e y hn he he'
    by_cases h1 : n ≤ 1
    · rw [clB, if_pos h1, List.length_nil, Nat.zero_add]; exact base_odd hn he
    · rw [clB, if_neg h1]
      simp only [List.length_append, List.length_singleton]
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
        rcases e with _ | e'
        · simp at he'; omega
        · exact ⟨e', rfl⟩
      have hY : (2 : ℕ) ^ (e' + 1) = 2 * 2 ^ e' := by rw [pow_succ]; ring
      have hY2 : (2 : ℕ) ^ (e' + 1 + 1) = 2 * (2 * 2 ^ e') := by rw [pow_succ, hY]; ring
      have hY1 : 1 ≤ 2 ^ e' := Nat.one_le_two_pow
      rw [hY] at he ⊢
      rw [hY2] at he'
      have hs := half_sum n
      have hLR1 : n / 2 ≤ (n + 1) / 2 := by omega
      have hLR2 : (n + 1) / 2 ≤ n / 2 + 1 := by omega
      generalize hL : (n + 1) / 2 = L at hs hLR1 hLR2 ⊢
      generalize hR : n / 2 = R at hs hLR1 hLR2 ⊢
      rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h2 | h3 | h4
      · -- n = 2: 子はどちらも前線
        obtain rfl : L = 1 := by omega
        obtain rfl : R = 1 := by omega
        rw [cB_one_odd, cB_one_odd, clB_one_odd, clB_one_odd]
        simp only [List.length_nil]
        subst h2
        have : 2 ^ e' ≤ 1 := by omega
        nlinarith
      · -- n = 3: 子は 2 と 1
        obtain rfl : L = 2 := by omega
        obtain rfl : R = 1 := by omega
        rw [cB_one_odd, clB_one_odd]
        simp only [List.length_nil]
        subst h3
        have k2 := ih 2 1 (y ++ [false]) (by norm_num) (by norm_num) (by norm_num)
        have c2 := length_cB_two_odd .unghost k 2 (y ++ [false]) le_rfl
        have : 2 ^ e' ≤ 1 := by omega
        norm_num at k2
        nlinarith
      · have hL2 : 2 ≤ L := by omega
        have hR2 : 2 ≤ R := by omega
        have heR : 2 ^ e' ≤ R := by omega
        by_cases hLY : L < 2 * 2 ^ e'
        · -- 左右とも e'
          have kL := kid_odd (y := y ++ [false]) (k := k) hL2
            (ih L e' (y ++ [false]) (by omega) (by omega) (by rw [hY]; exact hLY))
          have kR := kid_odd (y := y ++ [true]) (k := k) hR2
            (ih R e' (y ++ [true]) (by omega) heR (by rw [hY]; omega))
          have hm : e' * L + e' * R = e' * n := by rw [← mul_add, hs]
          nlinarith
        · -- 左は e' + 1，右は e'（n = 2^{e'+2} − 1）
          have hLe : L = 2 * 2 ^ e' := by omega
          have hRe : R + 1 = 2 * 2 ^ e' := by omega
          have kL := kid_odd (y := y ++ [false]) (k := k) hL2
            (ih L (e' + 1) (y ++ [false]) (by omega) (by rw [hY]; omega) (by rw [hY2]; omega))
          have kR := kid_odd (y := y ++ [true]) (k := k) hR2
            (ih R e' (y ++ [true]) (by omega) (by omega) (by rw [hY]; omega))
          rw [hY] at kL
          have hm : (e' + 1) * n = (e' + 1) * L + (e' + 1) * R := by rw [← mul_add, hs]
          nlinarith

theorem length_rootP_eq (k n : ℕ) (y : Node) (hn : ¬ n ≤ 1) :
    (rootP k n y).length = (clB (k + 1) n y).length := by
  unfold rootP
  rw [clB, if_neg hn]
  simp only [List.length_append, List.length_singleton, length_cB_indep .pebble .unghost]

/-- **段 1 の内部の手数（紙の Λ）.** `2^e ≤ n < 2^{e+1}`（`n ≥ 2`）なら `|rootP| + 4·2^e ≤ 2en + 5`。 -/
theorem length_rootP_odd (k n e : ℕ) (y : Node) (hn : 2 ≤ n) (he : 2 ^ e ≤ n)
    (he' : n < 2 ^ (e + 1)) : (rootP k n y).length + 4 * 2 ^ e ≤ 2 * e * n + 5 := by
  rw [length_rootP_eq k n y (by omega)]
  exact length_clB_odd (k + 1) n e y (by omega) he he'

/-! ## 前線への写しの手数（係数 `M` 倍） -/

theorem length_onSp_mul {h lo hi M α β γ : ℕ} (hlo : 1 ≤ lo) {f : Node → List Move}
    (hf : ∀ (a : Node) (j : ℕ), a.length + j = h → lo ≤ j → j ≤ hi →
      M * (f a).length + β ≤ α * 2 ^ j + γ) :
    ∀ (k n : ℕ) (y : Node), Shp lo hi k n → y.length + k = h →
      M * (onSp f k n y).length + β * n ≤ α * 2 ^ k + γ * n := by
  intro k
  induction k with
  | zero => intro n y hS _; have := hS.pos hlo; omega
  | succ k ih =>
    intro n y hS hy
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [onSp, if_pos hn, h1, mul_one, mul_one]
      exact hf y (k + 1) hy h2 h3
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [onSp, if_neg hn, List.length_append, mul_add]
      have a := ih _ (y ++ [false]) hL (by simp; omega)
      have b := ih _ (y ++ [true]) hR (by simp; omega)
      have hs := half_sum n
      have e1 : β * n = β * ((n + 1) / 2) + β * (n / 2) := by rw [← mul_add, hs]
      have e2 : γ * n = γ * ((n + 1) / 2) + γ * (n / 2) := by rw [← mul_add, hs]
      have e3 : α * 2 ^ (k + 1) = α * 2 ^ k + α * 2 ^ k := by rw [pow_succ]; ring
      rw [e1, e2, e3]
      omega

/-! ## 全体の構成（最終段を引数にした `stratW`） -/

/-- 構成 B★（m = 2）。最終段 `Fin` を引数にとる（`stratW` は `Fin = Mst`）。 -/
def stratG (h f : ℕ) (Fin : Node → List Move) : List Move :=
  onSp (fun a => compute .pebble (h - a.length) a) h f [] ++ (rootP (h - 1) f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) (h - 1) ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) (h - 1) (f / 2) [true]) ++
    (onSp Fin (h - 1) ((f + 1) / 2) [false] ++ onSp Fin (h - 1) (f / 2) [true])))

theorem stratG_eq (k f : ℕ) (Fin : Node → List Move) : stratG (k + 1) f Fin =
    onSp (fun a => compute .pebble (k + 1 - a.length) a) (k + 1) f [] ++ (rootP k f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) k ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) k (f / 2) [true]) ++
    (onSp Fin k ((f + 1) / 2) [false] ++ onSp Fin k (f / 2) [true]))) := by
  rw [stratG, Nat.add_sub_cancel]

/-- **構成の仕様.** 空の盤から合法で，ペブル数は `p` 以下，終わると根だけペブル・他は空。 -/
theorem stratG_spec {k f p lo hi : ℕ} {Fin : Node → List Move} (hlo : 1 ≤ lo)
    (hS : Shp lo hi (k + 1) f) (hf2 : 2 ≤ f)
    (hFin : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      Pat (cst .ghost) j a c' → Runs (k + 1) j a (p - 1) c' (Fin a) ∧
        Pat (cst .empty) j a (run c' (Fin a)))
    (hp0 : hi + 1 + (f - 1) * 1 ≤ p) (hpR : f + k + 4 ≤ p) (hp : 1 ≤ p) :
    Runs (k + 1) (k + 1) [] p (fun _ => Cell.empty) (stratG (k + 1) f Fin) ∧
    run (fun _ => Cell.empty) (stratG (k + 1) f Fin) [] = .pebble ∧
    ∀ z : Node, z.length < k + 1 → z ≠ [] →
      run (fun _ => Cell.empty) (stratG (k + 1) f Fin) z = .empty := by
  have hpe : PlOk .pebble .empty := Or.inl ⟨rfl, rfl⟩
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hl0 : ([false] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hl1 : ([true] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  -- 1. 段 1 の前線を計算する
  have hP0 : SP (cst .empty) (k + 1) (cst .empty) f [] (fun _ => Cell.empty) :=
    (SP_cst _ _ _).mpr (fun w _ => rfl)
  obtain ⟨hR1, hQ1⟩ := onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := hi + 1) (w := 1)
    (ci := .empty) (by decide) (G0 := cst .empty) (G1 := scp)
    (f := fun a => compute .pebble (k + 1 - a.length) a)
    (fun a j c' ha hj1 hj2 hPa => by
      have hj : k + 1 - a.length = j := by omega
      simp only [hj]
      obtain ⟨hR, hQ⟩ := compute_spec hpe j a c' (by omega) ha hPa
      exact ⟨hR.mono (by omega), hQ⟩)
    (fun j _ _ => (pcPat_cst_le (by decide) j).trans (Nat.zero_le 1)) pw_scp (k + 1) f []
    (fun _ => Cell.empty) hS (by simp) hP0
  -- 2. 根を置き，内部を空にする
  obtain ⟨hR2, hr2, hQ2L, hQ2R⟩ := rootP_spec (h := k + 1) hlo hS hn (by simp) hQ1
  -- 3. 前線をゴーストにする
  have hghost : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      Pat scp j a c' → Runs (k + 1) j a 0 c' [⟨.ghost, a⟩] ∧
        Pat (cst .ghost) j a (run c' [⟨.ghost, a⟩]) :=
    fun a j c' ha hj1 _ hPa => ghostRoot_spec (by omega) a c' ha hPa
  have pw_g0 : ∀ j, lo ≤ j → j ≤ hi → pcPat (cst Cell.ghost) j ≤ 0 :=
    fun j _ _ => pcPat_cst_le (by decide) j
  have pw_g1 : ∀ j, lo ≤ j → j ≤ hi → pcPat (cst Cell.ghost) j ≤ 1 :=
    fun j _ _ => (pcPat_cst_le (by decide) j).trans (Nat.zero_le 1)
  have pw_e0 : ∀ j, lo ≤ j → j ≤ hi → pcPat (cst Cell.empty) j ≤ 0 :=
    fun j _ _ => pcPat_cst_le (by decide) j
  obtain ⟨hR3a, hQ3a⟩ := onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := 0) (w := 1)
    (ci := .empty) (by decide) (G0 := scp) (G1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
    hghost pw_scp pw_g1 k _ [false] _ hSL hl0 hQ2L
  have b3R := pcSP_cst_le (G := scp) (X := .empty) (by decide) pw_scp k (f / 2) hSR
  have b3L := pcSP_cst_le (G := cst .ghost) (X := .empty) (by decide) pw_g0 k ((f + 1) / 2) hSL
  obtain ⟨hR3, hr3, hQ3L, hQ3R⟩ := pair_spec (y := []) (P := p) hR3a hQ3a hQ2R
    (fun c' hc' => onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := 0) (w := 1)
      (ci := .empty) (by decide) (G0 := scp) (G1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
      hghost pw_scp pw_g1 k _ [true] c' hSR hl1 hc')
    (by rw [hr2, if_pos rfl]; omega) (by rw [hr2, if_pos rfl]; omega)
  -- 4. 前線の各頂点の部分木に最終段
  obtain ⟨hR4a, hQ4a⟩ := onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
    (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
    (f := Fin) hFin pw_g0 pw_e0 k _ [false] _ hSL hl0 hQ3L
  have b4R := pcSP_cst_le (G := cst .ghost) (X := .empty) (by decide) pw_g0 k (f / 2) hSR
  have b4L := pcSP_cst_le (G := cst .empty) (X := .empty) (by decide) pw_e0 k ((f + 1) / 2) hSL
  obtain ⟨hR4, hr4, hQ4L, hQ4R⟩ := pair_spec (y := []) (P := p) hR4a hQ4a hQ3R
    (fun c' hc' => onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
      (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
      (f := Fin) hFin pw_g0 pw_e0 k _ [true] c' hSR hl1 hc')
    (by rw [hr3, hr2, if_pos rfl]; omega) (by rw [hr3, hr2, if_pos rfl]; omega)
  rw [stratG_eq]
  refine ⟨Runs_append.mpr ⟨hR1.mono hp0, Runs_append.mpr ⟨hR2.mono (by omega),
    Runs_append.mpr ⟨hR3, hR4⟩⟩⟩, ?_, ?_⟩
  · rw [run_append, run_append, run_append, hr4, hr3, hr2]
  · intro z hz hne
    rw [run_append, run_append, run_append]
    have hD0 := (SP_cst (X := .empty) k _ [false]).mp hQ4L
    have hD1 := (SP_cst (X := .empty) k _ [true]).mp hQ4R
    match z, hz, hne with
    | [], _, hne => exact absurd rfl hne
    | false :: w, hz, _ => exact hD0 w (by simp only [List.length_cons] at hz; omega)
    | true :: w, hz, _ => exact hD1 w (by simp only [List.length_cons] at hz; omega)

/-- **手数（段 1 の前線の計算とゴースト化）.** -/
theorem length_stratG_le {k f lo hi : ℕ} {Fin : Node → List Move} (hlo : 1 ≤ lo)
    (hS : Shp lo hi (k + 1) f) (hf2 : 2 ≤ f) :
    (stratG (k + 1) f Fin).length + 2 * f ≤ 2 * 2 ^ (k + 1) + (rootP k f []).length +
      (onSp Fin k ((f + 1) / 2) [false]).length + (onSp Fin k (f / 2) [true]).length := by
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hl0 : ([false] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hl1 : ([true] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  rw [stratG_eq]
  simp only [List.length_append]
  have hA := length_onSp (h := k + 1) (lo := lo) (hi := hi) (α := 2) (β := 3) (γ := 0) hlo
    (f := fun a => compute .pebble (k + 1 - a.length) a)
    (fun a j ha hj1 _ => by
      have hj : k + 1 - a.length = j := by omega
      simp only [hj]
      have := length_compute .pebble j a (by omega)
      rw [pow_succ] at this
      omega) (k + 1) f [] hS (by simp)
  have hgh : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      ((fun a => [(⟨.ghost, a⟩ : Move)]) a).length + 0 ≤ 0 * 2 ^ j + 1 := by
    intro a j _ _ _; simp
  have hCL := length_onSp (h := k + 1) hlo hgh k _ [false] hSL hl0
  have hCR := length_onSp (h := k + 1) hlo hgh k _ [true] hSR hl1
  simp only [zero_mul, one_mul, add_zero, Nat.zero_add] at hA hCL hCR
  omega

/-! ## 算術の道具 -/

/-- `H ≥ 5` なら `4H + 10 ≤ 2^H`（紙の補題 O1 (a) の `2^{H−1} ≥ 2H + 5`）。 -/
theorem pow_ge_odd : ∀ H : ℕ, 5 ≤ H → 4 * H + 10 ≤ 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ H _ ih => rw [pow_succ]; omega

/-- 割った前線の左右の子の大きさの関係。 -/
theorem half_le_odd (f : ℕ) : f / 2 ≤ (f + 1) / 2 := by omega

end SpookyTree
