/-
# 窓の上界（定理 B，m = 2）: 構成 B★ の Lean 版

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_2026-11.md` の 2〜6 節（定理 B）。ここでは `m = 2` だけ。

**主張（`window_upper_bound_m2`）.** `H = ⌊h/2⌋`、`f = p − h − 5`、`e = ⌊log₂ f⌋` として
`h + 13 ≤ p ≤ 2^H − 1`、`2^{h−e+3} ≤ p(p−1)` なら、ペブル `p` 個の妥当な手順で
`T + 2f² + 1 ≤ 2·3·(2^h − 1)`（紙の `T ≤ 2(m+1)(2^h−1) − 2(p−h−5)^m − 1`、`m = 2`）のものがある。

**構成（`stratW`）.**
1. 段 1（G 段、keep）: 根の下の大きさ `f` の割った前線の各頂点を `compute`（紙の comp）。
2. `rootP`（紙の comp_B・p 根・clr_B）: 根だけペブル、内部は空。
3. 前線を全部ゴーストにする。
4. 前線の各頂点の部分木に最終段 `Mst`（紙の M）: 大きさ `g = ⌊p/2⌋` の割った前線 X を計算し、
   内部 K∖X を置いて外し（`plSp`・`rmSp`）、X の各頂点に `DF`（紙の D_F）。
紙との違い: 前線は「右の u 個を割る」でなく `⌈n/2⌉・⌊n/2⌋` に再帰的に割る。段 1 の内部の手数は
紙の閉じた式 Λ でなく粗い上界 `2fh` を使う（定理 B の余裕に収まる）。
-/
import SpookyTree.WindowUpperInt
import SpookyTree.StepLimit

namespace SpookyTree

/-! ## D_F -/

/-- 紙の D_F: `z` がペブルで下が全部ゴーストの部分木（高さ `j`）を、下から置いて上から外して全部空にする。 -/
def DF (j : ℕ) (z : Node) : List Move :=
  onFront (placeInt .unghost (j - 1)) 1 z ++ removeInt j z

theorem pcPat_peb_succ (i : ℕ) : pcPat (cst Cell.pebble) i + 1 = 2 ^ i := by
  have := pcPat_glue_peb (cst Cell.pebble) 0 i
  rw [glue_cst, Nat.zero_add] at this
  simpa [pcPat] using this

theorem DF_spec {h j : ℕ} {z : Node} {c : Config} (hj : 1 ≤ j) (hz : z.length + j = h)
    (hP : Pat scp j z c) :
    Runs h j z (2 ^ j - 1) c (DF j z) ∧ Pat (cst .empty) j z (run c (DF j z)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  have h2 : 2 ^ (j' + 1) = 2 ^ j' * 2 := pow_succ 2 j'
  have hpj : 1 ≤ 2 ^ j' := Nat.one_le_two_pow
  have hk0 := pcPat_peb_succ j'
  have hk1 := pcPat_peb_succ (j' + 1)
  have hf : ∀ (a : Node) (c' : Config), a.length + j' = h → Pat (cst .ghost) j' a c' →
      Runs h j' a (2 ^ j' - 1) c' (placeInt .unghost j' a) ∧
        Pat (cst .pebble) j' a (run c' (placeInt .unghost j' a)) := by
    intro a c' ha hPa
    have hPa' : Pat (glue .ghost j' (cst .pebble)) (0 + j') a c' := by
      rw [Nat.zero_add]; exact (Pat_glue_short (cst .pebble) le_rfl).mpr hPa
    obtain ⟨hR, hQ⟩ := placeInt_spec (h := h) (j := 0) hug (g := cst .pebble)
      (fun h0 => absurd h0 (by decide)) j' a c' (by omega) hPa'
    rw [glue_cst, Nat.zero_add] at hR hQ
    exact ⟨hR.mono (by omega), hQ⟩
  obtain ⟨hR1, hQ1⟩ := onFront_spec (h := h) (j := j') (p := 2 ^ j' - 1) (w := 2 ^ j' - 1)
    (e := 1) (ci := .pebble) (g0 := cst .ghost) (g1 := cst .pebble) (f := placeInt .unghost j')
    hf (by rw [pcPat_cst (X := .ghost) (by decide)]; omega) (by omega) (by simp)
    1 z c (by omega) hP
  rw [glue_cst] at hQ1
  have hQ1' : Pat (glue .pebble (j' + 1) (cst .pebble)) (0 + (j' + 1)) z
      (run c (onFront (placeInt .unghost j') 1 z)) := by
    rw [glue_cst, Nat.zero_add]; exact hQ1
  obtain ⟨hR2, hQ2⟩ := removeInt_spec (h := h) (j := 0) (g := cst .pebble)
    (fun h0 => absurd h0 (by decide)) (j' + 1) z _ (by omega) hQ1'
  rw [glue_cst, Nat.zero_add] at hR2
  rw [Nat.zero_add] at hQ2
  have hD : DF (j' + 1) z = onFront (placeInt .unghost j') 1 z ++ removeInt (j' + 1) z := by
    unfold DF; rw [Nat.add_sub_cancel]
  rw [hD]
  have h21 : (2 : ℕ) ^ 1 - 1 = 1 := by norm_num
  refine ⟨Runs_append.mpr ⟨hR1.mono ?_, hR2.mono (by omega)⟩, ?_⟩
  · rw [h21, one_mul, h2]; omega
  · rw [run_append]; exact (Pat_glue_short (cst .pebble) le_rfl).mp hQ2

theorem length_DF {j : ℕ} (hj : 1 ≤ j) (z : Node) : (DF j z).length + 3 ≤ 2 * 2 ^ j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold DF
  rw [Nat.add_sub_cancel, List.length_append]
  have a := length_onFront_le (f := placeInt .unghost j') (N := 2 ^ j' - 1)
    (fun a => by have := length_placeInt .unghost j' a; omega) 1 z
  have b := length_removeInt (j' + 1) z
  have hpj : 1 ≤ 2 ^ j' := Nat.one_le_two_pow
  have h21 : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [h21] at a
  rw [pow_succ] at b ⊢
  omega

/-! ## 最終段 M -/

/-- 紙の M（大きさ `g` の割った前線 X）。`t` は部分木の高さ。 -/
def Mst (h t g : ℕ) (a : Node) : List Move :=
  onSp (fun z => compute .unghost (h - z.length) z) t g a ++ plSp .unghost t g a ++ rmSp t g a ++
    onSp (fun z => DF (h - z.length) z) t g a

/-- **M の仕様.** 全部ゴーストの部分木を全部空にする。ペブル数は
`max(hi + g, 2g − 1, 2^hi + g − 2)` 以下（`hi` は X の部分木の高さの上限）。 -/
theorem Mst_spec {h hi t g P : ℕ} {a : Node} {c : Config} (hS : Shp 1 hi t g)
    (ha : a.length + t = h) (hP : Pat (cst .ghost) t a c) (hp1 : hi + 1 + (g - 1) * 1 ≤ P)
    (hp2 : 2 * g - 1 ≤ P) (hp3 : 2 ^ hi - 1 + (g - 1) * 1 ≤ P) :
    Runs h t a P c (Mst h t g a) ∧ Pat (cst .empty) t a (run c (Mst h t g a)) := by
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  have hP0 : SP (cst .ghost) t (cst .ghost) g a c := (SP_cst t g a).mpr hP
  -- 1. X を計算する
  obtain ⟨hR1, hQ1⟩ := onSp_spec (h := h) (lo := 1) (hi := hi) (p := hi + 1) (w := 1)
    (ci := .ghost) (by decide) (G0 := cst .ghost) (G1 := scp)
    (f := fun z => compute .unghost (h - z.length) z)
    (fun z j c' hz hj1 hj2 hPz => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      obtain ⟨hR, hQ⟩ := compute_spec hug j z c' hj1 hz hPz
      exact ⟨hR.mono (by omega), hQ⟩)
    (fun j _ _ => (pcPat_cst_le (by decide) j).trans (Nat.zero_le 1)) pw_scp t g a c hS ha hP0
  -- 2. 内部を置く
  obtain ⟨hR2, hQ2⟩ := plSp_spec (h := h) (lo := 1) (hi := hi) le_rfl hug scp_zero t g a _ hS ha hQ1
  -- 3. 内部を外す
  obtain ⟨hR3, hQ3⟩ := rmSp_spec (h := h) (lo := 1) (hi := hi) le_rfl scp_zero t g a _ hS ha hQ2
  -- 4. X の各頂点に D_F
  obtain ⟨hR4, hQ4⟩ := onSp_spec (h := h) (lo := 1) (hi := hi) (p := 2 ^ hi - 1) (w := 1)
    (ci := .empty) (by decide) (G0 := scp) (G1 := cst .empty)
    (f := fun z => DF (h - z.length) z)
    (fun z j c' hz hj1 hj2 hPz => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      obtain ⟨hR, hQ⟩ := DF_spec hj1 hz hPz
      have : 2 ^ j ≤ 2 ^ hi := Nat.pow_le_pow_right (by norm_num) hj2
      exact ⟨hR.mono (by omega), hQ⟩)
    pw_scp (fun j _ _ => (pcPat_cst_le (by decide) j).trans (Nat.zero_le 1)) t g a _ hS ha hQ3
  have hpk := pcSP_peb_le (G := scp) pw_scp t g hS
  refine ⟨?_, ?_⟩
  · unfold Mst
    refine Runs_append.mpr ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨hR1.mono hp1, hR2.mono (by omega)⟩,
      ?_⟩, ?_⟩
    · rw [run_append]; exact hR3.mono (by omega)
    · rw [run_append, run_append]; exact hR4.mono hp3
  · unfold Mst
    rw [run_append, run_append, run_append]
    exact (SP_cst t g a).mp hQ4

/-! ## 手数の道具 -/

theorem length_onSp {h lo hi α β γ : ℕ} (hlo : 1 ≤ lo) {f : Node → List Move}
    (hf : ∀ (a : Node) (j : ℕ), a.length + j = h → lo ≤ j → j ≤ hi →
      (f a).length + β ≤ α * 2 ^ j + γ) :
    ∀ (k n : ℕ) (y : Node), Shp lo hi k n → y.length + k = h →
      (onSp f k n y).length + β * n ≤ α * 2 ^ k + γ * n := by
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
      rw [onSp, if_neg hn, List.length_append]
      have a := ih _ (y ++ [false]) hL (by simp; omega)
      have b := ih _ (y ++ [true]) hR (by simp; omega)
      have hs := half_sum n
      have e1 : β * n = β * ((n + 1) / 2) + β * (n / 2) := by rw [← mul_add, hs]
      have e2 : γ * n = γ * ((n + 1) / 2) + γ * (n / 2) := by rw [← mul_add, hs]
      have e3 : α * 2 ^ (k + 1) = α * 2 ^ k + α * 2 ^ k := by rw [pow_succ]; ring
      rw [e1, e2, e3]
      omega

theorem length_plSp {lo hi : ℕ} (pl : Op) :
    ∀ (k n : ℕ) (y : Node), Shp lo hi k n → (plSp pl k n y).length + 1 ≤ n := by
  intro k
  induction k with
  | zero => intro n y hS; have := hS.one; simp [plSp]; omega
  | succ k ih =>
    intro n y hS
    by_cases hn : n ≤ 1
    · rw [plSp, if_pos hn]; have := hS.one; simp; omega
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [plSp, if_neg hn]
      simp only [List.length_append, List.length_singleton]
      have a := ih _ (y ++ [false]) hL
      have b := ih _ (y ++ [true]) hR
      have hs := half_sum n
      omega

theorem length_rmSp {lo hi : ℕ} :
    ∀ (k n : ℕ) (y : Node), Shp lo hi k n → (rmSp k n y).length + 1 ≤ n := by
  intro k
  induction k with
  | zero => intro n y hS; have := hS.one; simp [rmSp]; omega
  | succ k ih =>
    intro n y hS
    by_cases hn : n ≤ 1
    · rw [rmSp, if_pos hn]; have := hS.one; simp; omega
    · obtain ⟨hL, hR⟩ := hS.child hn
      rw [rmSp, if_neg hn]
      simp only [List.length_cons, List.length_append]
      have a := ih _ (y ++ [false]) hL
      have b := ih _ (y ++ [true]) hR
      have hs := half_sum n
      omega

theorem length_Mst {h hi t g : ℕ} {a : Node} (hS : Shp 1 hi t g) (ha : a.length + t = h) :
    (Mst h t g a).length + (4 * g + 2) ≤ 4 * 2 ^ t + 0 := by
  unfold Mst
  simp only [List.length_append]
  have h1 := length_onSp (h := h) (lo := 1) (hi := hi) (α := 2) (β := 3) (γ := 0) le_rfl
    (f := fun z => compute .unghost (h - z.length) z)
    (fun z j hz hj1 _ => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      have := length_compute .unghost j z hj1
      rw [pow_succ] at this
      omega) t g a hS ha
  have h2 := length_plSp (pl := .unghost) t g a hS
  have h3 := length_rmSp t g a hS
  have h4 := length_onSp (h := h) (lo := 1) (hi := hi) (α := 2) (β := 3) (γ := 0) le_rfl
    (f := fun z => DF (h - z.length) z)
    (fun z j hz hj1 _ => by
      have hj : h - z.length = j := by omega
      simp only [hj]
      have := length_DF hj1 z
      omega) t g a hS ha
  omega

/-! ## 全体の構成 -/

/-- 構成 B★（m = 2）。`f` は段 1 の前線の大きさ、`g` は最終段の前線の大きさ。 -/
def stratW (h f g : ℕ) : List Move :=
  onSp (fun a => compute .pebble (h - a.length) a) h f [] ++ (rootP (h - 1) f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) (h - 1) ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) (h - 1) (f / 2) [true]) ++
    (onSp (fun a => Mst h (h - a.length) g a) (h - 1) ((f + 1) / 2) [false] ++
      onSp (fun a => Mst h (h - a.length) g a) (h - 1) (f / 2) [true])))

theorem stratW_eq (k f g : ℕ) : stratW (k + 1) f g =
    onSp (fun a => compute .pebble (k + 1 - a.length) a) (k + 1) f [] ++ (rootP k f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) k ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) k (f / 2) [true]) ++
    (onSp (fun a => Mst (k + 1) (k + 1 - a.length) g a) k ((f + 1) / 2) [false] ++
      onSp (fun a => Mst (k + 1) (k + 1 - a.length) g a) k (f / 2) [true]))) := by
  rw [stratW, Nat.add_sub_cancel]

/-- **構成 B★ の仕様（m = 2）.** 空の盤から合法で、ペブル数は `p` 以下、終わると根だけペブル・他は空。 -/
theorem stratW_spec {k f g p lo hi hiM : ℕ} (hlo : 1 ≤ lo) (hS : Shp lo hi (k + 1) f)
    (hf2 : 2 ≤ f) (hSM : ∀ t, lo ≤ t → t ≤ hi → Shp 1 hiM t g)
    (hp0 : hi + 1 + (f - 1) * 1 ≤ p) (hpR : f + k + 4 ≤ p)
    (hp1 : hiM + 1 + (g - 1) * 1 ≤ p - 1) (hp2 : 2 * g - 1 ≤ p - 1)
    (hp3 : 2 ^ hiM - 1 + (g - 1) * 1 ≤ p - 1) (hp : 1 ≤ p) :
    Runs (k + 1) (k + 1) [] p (fun _ => Cell.empty) (stratW (k + 1) f g) ∧
    run (fun _ => Cell.empty) (stratW (k + 1) f g) [] = .pebble ∧
    ∀ z : Node, z.length < k + 1 → z ≠ [] →
      run (fun _ => Cell.empty) (stratW (k + 1) f g) z = .empty := by
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
  -- 2. 根を置き、内部を空にする
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
  -- 4. 前線の各頂点の部分木に最終段 M
  have hM : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      Pat (cst .ghost) j a c' → Runs (k + 1) j a (p - 1) c' (Mst (k + 1) (k + 1 - a.length) g a) ∧
        Pat (cst .empty) j a (run c' (Mst (k + 1) (k + 1 - a.length) g a)) := by
    intro a j c' ha hj1 hj2 hPa
    have hj : k + 1 - a.length = j := by omega
    rw [hj]
    exact Mst_spec (hSM j hj1 hj2) ha hPa hp1 hp2 hp3
  obtain ⟨hR4a, hQ4a⟩ := onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
    (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
    (f := fun a => Mst (k + 1) (k + 1 - a.length) g a) hM pw_g0 pw_e0
    k _ [false] _ hSL hl0 hQ3L
  have b4R := pcSP_cst_le (G := cst .ghost) (X := .empty) (by decide) pw_g0 k (f / 2) hSR
  have b4L := pcSP_cst_le (G := cst .empty) (X := .empty) (by decide) pw_e0 k ((f + 1) / 2) hSL
  obtain ⟨hR4, hr4, hQ4L, hQ4R⟩ := pair_spec (y := []) (P := p) hR4a hQ4a hQ3R
    (fun c' hc' => onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
      (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
      (f := fun a => Mst (k + 1) (k + 1 - a.length) g a) hM pw_g0 pw_e0
      k _ [true] c' hSR hl1 hc')
    (by rw [hr3, hr2, if_pos rfl]; omega) (by rw [hr3, hr2, if_pos rfl]; omega)
  rw [stratW_eq]
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

/-- **手数.** -/
theorem length_stratW {k f g lo hi hiM : ℕ} (hlo : 1 ≤ lo) (hS : Shp lo hi (k + 1) f)
    (hf2 : 2 ≤ f) (hSM : ∀ t, lo ≤ t → t ≤ hi → Shp 1 hiM t g) :
    (stratW (k + 1) f g).length + 3 * f + (4 * g + 2) * f ≤
      6 * 2 ^ (k + 1) + 2 * f * (k + 1) + f := by
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hl0 : ([false] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hl1 : ([true] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  rw [stratW_eq]
  simp only [List.length_append]
  have hA := length_onSp (h := k + 1) (lo := lo) (hi := hi) (α := 2) (β := 3) (γ := 0) hlo
    (f := fun a => compute .pebble (k + 1 - a.length) a)
    (fun a j ha hj1 _ => by
      have hj : k + 1 - a.length = j := by omega
      simp only [hj]
      have := length_compute .pebble j a (by omega)
      rw [pow_succ] at this
      omega) (k + 1) f [] hS (by simp)
  have hB := length_rootP k f [] hf2
  have hgh : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      ((fun a => [(⟨.ghost, a⟩ : Move)]) a).length + 0 ≤ 0 * 2 ^ j + 1 := by
    intro a j _ _ _; simp
  have hCL := length_onSp (h := k + 1) hlo hgh k _ [false] hSL hl0
  have hCR := length_onSp (h := k + 1) hlo hgh k _ [true] hSR hl1
  have hm : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      ((fun a => Mst (k + 1) (k + 1 - a.length) g a) a).length + (4 * g + 2) ≤ 4 * 2 ^ j + 0 := by
    intro a j ha hj1 hj2
    have hj : k + 1 - a.length = j := by omega
    simp only [hj]
    exact length_Mst (hSM j hj1 hj2) ha
  have hDL := length_onSp (h := k + 1) hlo hm k _ [false] hSL hl0
  have hDR := length_onSp (h := k + 1) hlo hm k _ [true] hSR hl1
  have e1 : (4 * g + 2) * f = (4 * g + 2) * ((f + 1) / 2) + (4 * g + 2) * (f / 2) := by
    rw [← mul_add, hs]
  have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [e1, e2]
  rw [e2] at hA
  simp only [zero_mul, one_mul, add_zero, Nat.add_zero] at hA hCL hCR hDL hDR
  omega

/-! ## 定理 B（m = 2） -/

theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- (B2) から出る算術: `X·4Y ≤ p(p−1)`、`g + 1 ≤ Y`、`p ≤ 2g + 1` なら `2X + 1 ≤ p`。 -/
theorem B2_arith {X Y g p : ℕ} (h1 : X * (Y * 4) ≤ p * (p - 1)) (hY : g + 1 ≤ Y)
    (hgp : p ≤ 2 * g + 1) (hp : 1 ≤ p) : 2 * X + 1 ≤ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1
  by_contra hc
  have hq : q + 1 ≤ 2 * X := by omega
  have hY4 : 2 * q + 4 ≤ Y * 4 := by omega
  have m1 : X * (2 * q + 4) ≤ X * (Y * 4) := Nat.mul_le_mul_left X hY4
  have m2 : (q + 1) * (q + 2) ≤ 2 * X * (q + 2) := Nat.mul_le_mul_right (q + 2) hq
  nlinarith

/-- 定理 B（m = 2）の核: `e = ⌊log₂ f⌋`・`d = ⌊log₂ g⌋` の性質と (B2) から出る `2·2^{h−e−d} + 1 ≤ p` を仮定に取る形。 -/
theorem window_upper_core {h p f g e d : ℕ} (hf : f = p - h - 5) (hg : g = p / 2)
    (hlo : h + 13 ≤ p) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hd1 : 2 ^ d ≤ g)
    (hd2 : g < 2 ^ (d + 1)) (hed : e + d + 3 ≤ h) (hX : 2 * 2 ^ (h - e - d) + 1 ≤ p) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧ T + 2 * f ^ 2 + 1 ≤ 2 * 3 * (2 ^ h - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hS : Shp (k + 1 - e - 1) (k + 1 - e) (k + 1) f :=
    ⟨e + 1, e, by omega, by omega, by omega, he1, by omega⟩
  have hSM : ∀ t, k + 1 - e - 1 ≤ t → t ≤ k + 1 - e → Shp 1 (k + 1 - e - d) t g :=
    fun t h1 h2 => ⟨d + 1, d, by omega, by omega, by omega, hd1, by omega⟩
  have hXn := lt_two_pow' (k + 1 - e - d)
  obtain ⟨hR, hroot, hothers⟩ := stratW_spec (k := k) (f := f) (g := g) (p := p)
    (lo := k + 1 - e - 1) (hi := k + 1 - e) (hiM := k + 1 - e - d) (by omega) hS (by omega) hSM
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hlen := length_stratW (by omega) hS (by omega) hSM
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  generalize (stratW (k + 1) f g).length = T at hlen ⊢
  have m1 : f * (f + k + 6) ≤ f * (2 * g + 1) := Nat.mul_le_mul_left f (by omega)
  have m2 : f * (f + k + 6) = f * f + f * k + 6 * f := by ring
  have m3 : f * (2 * g + 1) = 2 * (f * g) + f := by ring
  have m4 : (4 * g + 2) * f = 4 * (f * g) + 2 * f := by ring
  have m5 : 2 * f * (k + 1) = 2 * (f * k) + 2 * f := by ring
  have m6 : f ^ 2 = f * f := by ring
  have m7 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [m6]
  rw [m4, m5] at hlen
  omega

/-- **定理 B（m = 2）.** 紙の定理 B の `m = 2` の場合（`WINDOW_UB_2026-11.md` 0 節の表）:
`H = ⌊h/2⌋`、`e = ⌊log₂(p − h − 5)⌋` として (B1) `h + 13 ≤ p ≤ 2^H − 1`、(B2) `2^{h−e+3} ≤ p(p−1)` なら、
ペブル `p` 個で `T + 2(p − h − 5)² + 1 ≤ 2·(2+1)·(2^h − 1)` の妥当な手順がある。 -/
theorem window_upper_bound_m2 {h p : ℕ} (hlo : h + 13 ≤ p) (hhi : p ≤ 2 ^ (h / 2) - 1)
    (hB2 : 2 ^ (h - Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      T + 2 * (p - h - 5) ^ 2 + 1 ≤ 2 * (2 + 1) * (2 ^ h - 1) := by
  have hf0 : p - h - 5 ≠ 0 := by omega
  have hg0 : p / 2 ≠ 0 := by omega
  have he1 : 2 ^ Nat.log 2 (p - h - 5) ≤ p - h - 5 := Nat.pow_log_le_self 2 hf0
  have he2 : p - h - 5 < 2 ^ (Nat.log 2 (p - h - 5) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hd1 : 2 ^ Nat.log 2 (p / 2) ≤ p / 2 := Nat.pow_log_le_self 2 hg0
  have hd2 : p / 2 < 2 ^ (Nat.log 2 (p / 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  generalize Nat.log 2 (p - h - 5) = e at he1 he2 hB2
  generalize Nat.log 2 (p / 2) = d at hd1 hd2
  have hH1 : 1 ≤ 2 ^ (h / 2) := Nat.one_le_two_pow
  have heH : e < h / 2 := by
    by_contra hc
    have : 2 ^ (h / 2) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdH : d + 1 < h / 2 := by
    by_contra hc
    have : 2 ^ (h / 2) ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    omega
  have hed : e + d + 3 ≤ h := by omega
  have hX : 2 * 2 ^ (h - e - d) + 1 ≤ p := by
    have h1 : 2 ^ (h - e + 3) = 2 ^ (h - e - d) * (2 ^ (d + 1) * 4) := by
      rw [show h - e + 3 = (h - e - d) + (d + 1) + 2 by omega, pow_add, pow_add]; ring
    rw [h1] at hB2
    exact B2_arith (g := p / 2) hB2 (by omega) (by omega) (by omega)
  have := window_upper_core (f := p - h - 5) (g := p / 2) rfl rfl hlo he1 he2 hd1 hd2 hed hX
  simpa using this

/-- **定理 B（m = 2）を最小手数で.** `T(T_h, p) ≤ 2·3·(2^h − 1) − 2(p − h − 5)² − 1`。 -/
theorem Ttree_window_upper_m2 {h p : ℕ} (hlo : h + 13 ≤ p) (hhi : p ≤ 2 ^ (h / 2) - 1)
    (hB2 : 2 ^ (h - Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    Ttree h p ≤ 2 * (2 + 1) * (2 ^ h - 1) - 2 * (p - h - 5) ^ 2 - 1 := by
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound_m2 hlo hhi hB2
  have := Ttree_le_of_valid hV
  omega

/-- **定理 B（m = 2，KSS の意味論）.** 同じ手順を KSS の意味論の手順に直したもの。 -/
theorem window_upper_bound_m2_kss {h p : ℕ} (hlo : h + 13 ≤ p) (hhi : p ≤ 2 ^ (h / 2) - 1)
    (hB2 : 2 ^ (h - Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h p T ms ∧
      T + 2 * (p - h - 5) ^ 2 + 1 ≤ 2 * (2 + 1) * (2 ^ h - 1) := by
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound_m2 hlo hhi hB2
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

theorem TtreeK_window_upper_m2 {h p : ℕ} (hlo : h + 13 ≤ p) (hhi : p ≤ 2 ^ (h / 2) - 1)
    (hB2 : 2 ^ (h - Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    TtreeK h p ≤ 2 * (2 + 1) * (2 ^ h - 1) - 2 * (p - h - 5) ^ 2 - 1 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_upper_m2 hlo hhi hB2

end SpookyTree
