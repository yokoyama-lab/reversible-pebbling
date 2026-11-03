/-
# 窓の上界・m = 3・h ≡ 1 (mod 3)（紙の定理 B3，r = 1）: 構成と手数の一般形

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 3 節（構成 B★ の m = 3．手順は WINDOW_UB 2.3 節）。
構成は 3 段:
* 段 1（keep）: `WindowUpperOdd.lean` の `stratG`（= `WindowUpperGen.lean` の `wgStrat`）。大きさ `f` の前線，深さ `e`。
* 段 2（G 段，keep なし）: `g2Stg`（`WindowUpperGen.lean` の `wgStg (r+1)` と同じ手順で，次の段を引数にした形）。
  同じ大きさ `f` の前線，深さ `e`。
* 最終段: `finW`（`WindowUpperOdd.lean`．部分木の高さ `t` が `2^t ≤ p` なら F，そうでなければ M）。

手数は，段 2 の部分木の高さと最終段の部分木の高さがどちらも 2 通りしかないことを使い，
「高さ `lo` で `A` 以下，高さ `lo + 1` で `B` 以下」の手順を前線に写した手数を ℤ で
`2^lo·|onSp| ≤ 2^lo·n·(2A − B) + 2^k·(B − A)` と抑える（`length_onSp_two`．2 つの高さで等号）。
段の内部の手数（`rootP`・`clB`）は `2f(e+1)` で粗く抑える（`WindowUpperGen.lean` と同じ）。

紙との違い（`WindowUpperOdd.lean`・`WindowUpperGen.lean` と同じもの）: 前線は「右の u 個を割る」でなく
`⌈n/2⌉・⌊n/2⌋` に再帰的に割る（深さの分布は同じ）。G 段の手 2 は `cB` と `clB` で打つ。
手数は紙の閉じた式（補題 P4）でなく上界。
-/
import SpookyTree.WindowUpperOdd
import SpookyTree.WindowUpperGen

namespace SpookyTree

/-! ## 高さが 2 通りの前線への写しの手数（ℤ） -/

/-- **高さが 2 通りの前線.** 前線の部分木の高さが `lo` か `lo + 1` で，1 個あたりの手数がそれぞれ
`A`・`B` 以下なら `2^lo·|onSp f k n y| ≤ 2^lo·n·(2A − B) + 2^k·(B − A)`。 -/
theorem length_onSp_two {h lo : ℕ} (hlo : 1 ≤ lo) {f : Node → List Move} {A B : ℤ}
    (hA : ∀ a : Node, a.length + lo = h → ((f a).length : ℤ) ≤ A)
    (hB : ∀ a : Node, a.length + (lo + 1) = h → ((f a).length : ℤ) ≤ B) :
    ∀ (k n : ℕ) (y : Node), Shp lo (lo + 1) k n → y.length + k = h →
      (2 : ℤ) ^ lo * ((onSp f k n y).length : ℤ) ≤
        2 ^ lo * (n : ℤ) * (2 * A - B) + 2 ^ k * (B - A) := by
  have hpos : (0 : ℤ) < 2 ^ lo := by positivity
  intro k
  induction k with
  | zero => intro n y hS _; have := hS.pos hlo; omega
  | succ k ih =>
    intro n y hS hy
    by_cases hn : n ≤ 1
    · obtain ⟨h1, h2, h3⟩ := hS.front hn
      rw [onSp, if_pos hn, h1]
      rcases (show k + 1 = lo ∨ k + 1 = lo + 1 by omega) with hk | hk
      · have a := hA y (by omega)
        have := mul_le_mul_of_nonneg_left a hpos.le
        rw [hk]
        push_cast
        linarith
      · have a := hB y (by omega)
        have := mul_le_mul_of_nonneg_left a hpos.le
        rw [hk, pow_succ]
        push_cast
        linarith
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [onSp, if_neg hn, List.length_append]
      have a := ih _ (y ++ [false]) hL (by simp; omega)
      have b := ih _ (y ++ [true]) hR (by simp; omega)
      have hs : (n : ℤ) = (((n + 1) / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) := by
        have := half_sum n
        exact_mod_cast this.symm
      rw [hs, pow_succ]
      push_cast
      push_cast at a b
      linarith

/-- `length_onSp_two` を `2^lo` で割った形（`k = lo + D`）。 -/
theorem length_onSp_two' {h lo D : ℕ} (hlo : 1 ≤ lo) {f : Node → List Move} {A B : ℤ}
    (hA : ∀ a : Node, a.length + lo = h → ((f a).length : ℤ) ≤ A)
    (hB : ∀ a : Node, a.length + (lo + 1) = h → ((f a).length : ℤ) ≤ B)
    {n : ℕ} {y : Node} (hS : Shp lo (lo + 1) (lo + D) n) (hy : y.length + (lo + D) = h) :
    ((onSp f (lo + D) n y).length : ℤ) ≤ (n : ℤ) * (2 * A - B) + 2 ^ D * (B - A) := by
  have hpos : (0 : ℤ) < 2 ^ lo := by positivity
  have := length_onSp_two hlo hA hB (lo + D) n y hS hy
  rw [pow_add] at this
  have e : (2 : ℤ) ^ lo * (n : ℤ) * (2 * A - B) + 2 ^ lo * 2 ^ D * (B - A) =
      2 ^ lo * ((n : ℤ) * (2 * A - B) + 2 ^ D * (B - A)) := by ring
  rw [e] at this
  exact le_of_mul_le_mul_left this hpos

/-! ## 最終段（高さの上限を引数にした M） -/

/-- `finW_spec` の M の高さの上限 `hM` を一般にした形。 -/
theorem finW_spec3 {h p g j hM : ℕ} {a : Node} {c : Config} (ha : a.length + j = h) (hj : 1 ≤ j)
    (hMs : ¬ 2 ^ j ≤ p → Shp 1 hM j g) (hg1 : 2 ^ hM + g ≤ p) (hg0 : hM + g + 2 ≤ p)
    (hg2 : 2 * g ≤ p) (hP : Pat (cst .ghost) j a c) :
    Runs h j a (p - 1) c (finW h p g a) ∧ Pat (cst .empty) j a (run c (finW h p g a)) := by
  have hj' : h - a.length = j := by omega
  unfold finW
  rw [hj']
  split_ifs with hF
  · obtain ⟨hR, hQ⟩ := Fst_spec_odd hj ha hP
    exact ⟨hR.mono (by omega), hQ⟩
  · have hS := hMs hF
    exact Mst_spec hS ha hP (by omega) (by omega) (by omega)

theorem length_finW_F3 {h p g j : ℕ} {a : Node} (ha : a.length + j = h) (hF : 2 ^ j ≤ p) :
    ((finW h p g a).length : ℤ) ≤ 2 * 2 ^ j - 2 := by
  have := length_finW_F (g := g) ha hF
  have : ((finW h p g a).length : ℤ) + 2 = 2 * 2 ^ j := by exact_mod_cast this
  linarith

theorem length_finW_M3 {h p g j hM : ℕ} {a : Node} (ha : a.length + j = h) (hF : ¬ 2 ^ j ≤ p)
    (hS : Shp 1 hM j g) : ((finW h p g a).length : ℤ) ≤ 4 * 2 ^ j - 4 * g - 2 := by
  have hj' : h - a.length = j := by omega
  have hl : (finW h p g a).length + (4 * g + 2) ≤ 4 * 2 ^ j := by
    unfold finW
    rw [hj', if_neg hF]
    have := length_Mst hS ha
    omega
  have : ((finW h p g a).length : ℤ) + (4 * g + 2) ≤ 4 * 2 ^ j := by exact_mod_cast hl
  linarith

/-! ## 段 2（G 段，keep なし．次の段を引数に） -/

/-- 段 2 の手続き（紙の G 段）。高さ `t` の全部ゴーストの部分木 `T(a)` を全部空にする。
大きさ `f` の割った前線を計算し，内部を `cB`（根だけペブル）→ `clB`（全部空）で片づけ，
前線をゴーストにしてから前線の各頂点の部分木に `Fin`。 -/
def g2Stg (h f : ℕ) (Fin : Node → List Move) (t : ℕ) (a : Node) : List Move :=
  onSp (fun z => compute .unghost (h - z.length) z) t f a ++ cB .unghost t f a ++ clB t f a ++
    onSp (fun z => [⟨.ghost, z⟩]) t f a ++ onSp Fin t f a

/-- **段 2 の仕様.** 高さ `t ∈ [lo, hi]` の全部ゴーストの部分木を，ペブル数 `p − 1` 以下で全部空にする。
最終段の部分木の高さは `[lo − e − 1, hi − e]` に入る。 -/
theorem g2Stg_spec {h p f e lo hi : ℕ} {Fin : Node → List Move} (hf2 : 2 ≤ f)
    (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hPf : f + h + 3 ≤ p) (hlo : e + 2 ≤ lo)
    (hhi : hi ≤ h)
    (hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → lo - e - 1 ≤ j →
      j ≤ hi - e → Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (Fin z) ∧ Pat (cst .empty) j z (run c' (Fin z))) :
    ∀ (t : ℕ) (a : Node) (c : Config), lo ≤ t → t ≤ hi → a.length + t = h →
      Pat (cst .ghost) t a c →
      Runs h t a (p - 1) c (g2Stg h f Fin t a) ∧
        Pat (cst .empty) t a (run c (g2Stg h f Fin t a)) := by
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  intro t a c ht1 ht2 ha hP
  have hlo' : 1 ≤ lo - e - 1 := by omega
  have hS : Shp (lo - e - 1) (hi - e) t f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  have pw_g0 : ∀ j, lo - e - 1 ≤ j → j ≤ hi - e → pcPat (cst Cell.ghost) j ≤ 0 :=
    fun j _ _ => pcPat_cst_le (by decide) j
  have pw_g1 : ∀ j, lo - e - 1 ≤ j → j ≤ hi - e → pcPat (cst Cell.ghost) j ≤ 1 :=
    fun j _ _ => (pcPat_cst_le (by decide) j).trans (Nat.zero_le 1)
  have pw_e0 : ∀ j, lo - e - 1 ≤ j → j ≤ hi - e → pcPat (cst Cell.empty) j ≤ 0 :=
    fun j _ _ => pcPat_cst_le (by decide) j
  have hP0 : SP (cst .ghost) t (cst .ghost) f a c := (SP_cst t f a).mpr hP
  -- 1. 前線を計算する
  obtain ⟨hR1, hQ1⟩ := onSp_spec (h := h) (lo := lo - e - 1) (hi := hi - e) (p := hi - e + 1)
    (w := 1) (ci := .ghost) (by decide) (G0 := cst .ghost) (G1 := scp)
    (f := fun z => compute .unghost (h - z.length) z)
    (fun z j c' hz hj1 hj2 hPz => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      obtain ⟨hR, hQ⟩ := compute_spec hug j z c' (by omega) hz hPz
      exact ⟨hR.mono (by omega), hQ⟩)
    pw_g1 pw_scp t f a c hS ha hP0
  -- 2. 内部を計算する（根だけペブル，他の内部はゴースト）
  obtain ⟨hR2, hQ2⟩ := cB_spec (h := h) hlo' hug t f a _ hS ha hQ1
  -- 3. 内部を全部空にする
  obtain ⟨hR3, hQ3⟩ := clB_spec (h := h) hlo' t f a _ hS ha hQ2
  -- 4. 前線をゴーストにする
  obtain ⟨hR4, hQ4⟩ := onSp_spec (h := h) (lo := lo - e - 1) (hi := hi - e) (p := 0) (w := 1)
    (ci := .empty) (by decide) (G0 := scp) (G1 := cst .ghost) (f := fun z => [⟨.ghost, z⟩])
    (fun z j c' hz hj1 _ hPz => ghostRoot_spec (by omega) z c' hz hPz)
    pw_scp pw_g1 t f a _ hS ha hQ3
  -- 5. 前線の各頂点の部分木に最終段
  obtain ⟨hR5, hQ5⟩ := onSp_spec (h := h) (lo := lo - e - 1) (hi := hi - e) (p := p - 1) (w := 0)
    (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
    (f := Fin) hFin pw_g0 pw_e0 t f a _ hS ha hQ4
  have hstg : g2Stg h f Fin t a =
      onSp (fun z => compute .unghost (h - z.length) z) t f a ++ cB .unghost t f a ++ clB t f a ++
        onSp (fun z => [⟨.ghost, z⟩]) t f a ++ onSp Fin t f a := rfl
  rw [hstg]
  refine ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨Runs_append.mpr
    ⟨hR1.mono (by omega), ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact hR2.mono (by omega)
  · rw [run_append]; exact hR3.mono (by omega)
  · rw [run_append, run_append]; exact hR4.mono (by omega)
  · rw [run_append, run_append, run_append]
    exact hR5.mono (by omega)
  · rw [run_append, run_append, run_append, run_append]
    exact (SP_cst t f a).mp hQ5

/-- 段 2 の手数の上界（紙の補題 8 の代わり）: 高さ `t = l + e + 1` の部分木で，最終段の高さ `l`・`l + 1` の
手数がそれぞれ `A`・`B` 以下なら `|g2Stg| ≤ 2·2^t + 2f(e+1) + f(2A − B) + 2^{e+1}(B − A)`。 -/
def m3Psi (f e t : ℕ) (A B : ℤ) : ℤ :=
  2 * 2 ^ t + 2 * (f : ℤ) * (e + 1) + (f : ℤ) * (2 * A - B) + 2 ^ (e + 1) * (B - A)

theorem length_g2Stg {h f e l : ℕ} {Fin : Node → List Move} (hf2 : 2 ≤ f)
    (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hl : 1 ≤ l) {a : Node}
    (ha : a.length + (l + (e + 1)) = h) {A B : ℤ}
    (hA : ∀ z : Node, z.length + l = h → ((Fin z).length : ℤ) ≤ A)
    (hB : ∀ z : Node, z.length + (l + 1) = h → ((Fin z).length : ℤ) ≤ B) :
    ((g2Stg h f Fin (l + (e + 1)) a).length : ℤ) ≤ m3Psi f e (l + (e + 1)) A B := by
  have hS : Shp l (l + 1) (l + (e + 1)) f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  have hA1 := length_onSp (h := h) (lo := l) (hi := l + 1) (α := 2) (β := 3) (γ := 0)
    hl (f := fun z => compute .unghost (h - z.length) z)
    (fun z j hz hj1 _ => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      have := length_compute .unghost j z (by omega)
      rw [pow_succ] at this
      omega) (l + (e + 1)) f a hS ha
  have hB1 := length_cB_le .unghost (l + (e + 1)) f a (by omega)
  have hC1 := length_clB_depth (l + (e + 1)) f a (e + 1) (le_of_lt he2)
  have hD1 := length_onSp (h := h) (lo := l) (hi := l + 1) (α := 0) (β := 0) (γ := 1)
    hl (f := fun z => [(⟨.ghost, z⟩ : Move)]) (fun z j _ _ _ => by simp) (l + (e + 1)) f a hS ha
  have hE1 := length_onSp_two' (h := h) (D := e + 1) hl hA hB hS ha
  have hstg : g2Stg h f Fin (l + (e + 1)) a =
      onSp (fun z => compute .unghost (h - z.length) z) (l + (e + 1)) f a ++
        cB .unghost (l + (e + 1)) f a ++ clB (l + (e + 1)) f a ++
        onSp (fun z => [⟨.ghost, z⟩]) (l + (e + 1)) f a ++ onSp Fin (l + (e + 1)) f a := rfl
  rw [hstg]
  simp only [List.length_append]
  simp only [zero_mul, one_mul, add_zero, Nat.zero_add] at hA1 hD1
  unfold m3Psi
  have hA1' : ((onSp (fun z => compute .unghost (h - z.length) z) (l + (e + 1)) f a).length : ℤ) +
      3 * f ≤ 2 * 2 ^ (l + (e + 1)) := by exact_mod_cast hA1
  have hB1' : ((cB .unghost (l + (e + 1)) f a).length : ℤ) + 2 ≤ 2 * f := by exact_mod_cast hB1
  have hC1' : ((clB (l + (e + 1)) f a).length : ℤ) ≤ 2 * f * (e + 1) := by exact_mod_cast hC1
  have hD1' : ((onSp (fun z => [(⟨.ghost, z⟩ : Move)]) (l + (e + 1)) f a).length : ℤ) ≤ f := by
    exact_mod_cast hD1
  push_cast
  linarith

/-! ## 全体の構成と手数の一般形 -/

/-- 全体の手数の上界: 段 1 の前線の部分木（高さ `k₁`・`k₁ + 1`）の手数が `A`・`B` 以下なら
`T ≤ 2·2^h − 2f + 2f(e+1) + f(2A − B) + 2^{e+1}(B − A)`。 -/
def m3Phi (f e h : ℕ) (A B : ℤ) : ℤ :=
  2 * 2 ^ h - 2 * (f : ℤ) + 2 * (f : ℤ) * (e + 1) + (f : ℤ) * (2 * A - B) + 2 ^ (e + 1) * (B - A)

/-- 構成 B★（m = 3）。 -/
def m3Strat (h p f g : ℕ) : List Move :=
  stratG h f (fun a => g2Stg h f (finW h p g) (h - a.length) a)

/-- **構成 B★（m = 3）の合法性と手数の一般形.** `h = l + 2e + 2`（最終段の部分木の高さは `l, l+1, l+2`），
`f = p − h − 5`，`2^e ≤ f < 2^{e+1}`。最終段の 1 個あたりの手数が高さ `l + i` で `φᵢ` 以下なら
`T ≤ m3Phi f e h (m3Psi … φ₀ φ₁) (m3Psi … φ₁ φ₂)`。 -/
theorem m3_assemble {h p f g e l : ℕ} (hh : h = l + 2 * e + 2) (hf : f + h + 5 = p)
    (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hl : 1 ≤ l)
    (hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l ≤ j → j ≤ l + 2 →
      Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)))
    {φ₀ φ₁ φ₂ : ℤ}
    (h0 : ∀ z : Node, z.length + l = h → ((finW h p g z).length : ℤ) ≤ φ₀)
    (h1 : ∀ z : Node, z.length + (l + 1) = h → ((finW h p g z).length : ℤ) ≤ φ₁)
    (h2 : ∀ z : Node, z.length + (l + 2) = h → ((finW h p g z).length : ℤ) ≤ φ₂) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      (T : ℤ) ≤ m3Phi f e h (m3Psi f e (l + (e + 1)) φ₀ φ₁) (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hS : Shp (l + (e + 1)) (l + (e + 1) + 1) (k + 1) f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  -- 合法性
  have hFin2 : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → l + (e + 1) ≤ j →
      j ≤ l + (e + 1) + 1 → Pat (cst .ghost) j a c' →
      Runs (k + 1) j a (p - 1) c' (g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) ∧
        Pat (cst .empty) j a
          (run c' (g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a)) := by
    intro a j c' ha hj1 hj2 hPa
    have hj : k + 1 - a.length = j := by omega
    rw [hj]
    refine g2Stg_spec (h := k + 1) (p := p) (lo := l + (e + 1)) (hi := l + (e + 1) + 1) hf2 he1 he2
      (by omega) (by omega) (by omega) ?_ j a c' hj1 hj2 ha hPa
    intro z j' c'' hz hj'1 hj'2 hPz
    exact hFin z j' c'' hz (by omega) (by omega) hPz
  obtain ⟨hR, hroot, hothers⟩ := stratG_spec (k := k) (f := f) (p := p) (lo := l + (e + 1))
    (hi := l + (e + 1) + 1)
    (Fin := fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) (by omega) hS hf2
    hFin2 (by omega) (by omega) (by omega)
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  -- 手数
  have hlen := length_stratG_le (Fin := fun a => g2Stg (k + 1) f (finW (k + 1) p g)
    (k + 1 - a.length) a) (by omega) hS hf2
  have hroot' := length_rootP_depth k f [] (e + 1) hf2 (le_of_lt he2)
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  -- 段 2 の部分木 1 個の手数
  have hA : ∀ a : Node, a.length + (l + (e + 1)) = k + 1 →
      (((fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) a).length : ℤ) ≤
        m3Psi f e (l + (e + 1)) φ₀ φ₁ := by
    intro a ha
    have hj : k + 1 - a.length = l + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) hf2 he1 he2 hl ha h0 h1
  have hB : ∀ a : Node, a.length + (l + (e + 1) + 1) = k + 1 →
      (((fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) a).length : ℤ) ≤
        m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂ := by
    intro a ha
    have hj : k + 1 - a.length = l + 1 + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) (l := l + 1) hf2 he1 he2 (by omega) (by omega) h1
      (fun z hz => h2 z (by omega))
  have hkD : k = l + (e + 1) + e := by omega
  rw [hkD] at hSL hSR
  have hL := length_onSp_two' (h := k + 1) (D := e) (y := [false]) (by omega) hA hB hSL
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hR' := length_onSp_two' (h := k + 1) (D := e) (y := [true]) (by omega) hA hB hSR
    (by simp only [List.length_cons, List.length_nil]; omega)
  rw [← hkD] at hL hR'
  have hsz : ((f : ℕ) : ℤ) = (((f + 1) / 2 : ℕ) : ℤ) + ((f / 2 : ℕ) : ℤ) := by
    exact_mod_cast hs.symm
  generalize (stratG (k + 1) f fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a).length
    = T at hlen ⊢
  have hlen' : (T : ℤ) + 2 * f ≤ 2 * 2 ^ (k + 1) + ((rootP k f []).length : ℤ) +
      ((onSp (fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) k
        ((f + 1) / 2) [false]).length : ℤ) +
      ((onSp (fun a => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - a.length) a) k
        (f / 2) [true]).length : ℤ) := by exact_mod_cast hlen
  have hroot'' : ((rootP k f []).length : ℤ) ≤ 2 * f * (e + 1) := by exact_mod_cast hroot'
  unfold m3Phi
  generalize m3Psi f e (l + (e + 1)) φ₀ φ₁ = A at hL hR' ⊢
  generalize m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂ = B at hL hR' ⊢
  rw [show (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e by ring]
  rw [hsz] at hlen' hroot'' ⊢
  linarith

end SpookyTree
