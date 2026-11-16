/-
# 窓の上界（定理 B，一般の m ≥ 2）: 構成 B★ を G 段 m − 1 回に一般化した Lean 版

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_2026-11.md` の 0 節と 2〜6 節（定理 B）。
`m = 2` の版は `WindowUpper.lean`（`window_upper_bound_m2`）。ここではその部品（`onSp`・`cB`・`clB`・`rootP`・`Mst`）を
そのまま使い、段 2..m−1 の G 段（keep なし）を `wgStg` の再帰で重ねる。

**主張（`window_upper_bound`）.** 整数 `m ≥ 2`，`H = ⌊h/m⌋`，`f = p − h − 5`，`e = ⌊log₂ f⌋` として
(B1) `h + 13 ≤ p ≤ 2^H − 1`，(B2) `2^{h−(m−1)e+3} ≤ p(p−1)` なら，ペブル `p` 個の妥当な手順で
`T + 2f^m + 1 ≤ 2(m+1)(2^h − 1)` のものがある（紙の `T(T_h,p) ≤ 2(m+1)(2^h−1) − 2(p−h−5)^m − 1` と同じ式．弱めていない）。
紙の仮定 `h ≥ m` は (B1) から出る（`2^H ≥ 14` なので `H ≥ 1`，`m ≤ mH ≤ h`）ので仮定に置かない。

**構成.**
* 段 1（`wgStrat`，keep）: `stratW` と同じ。最終段 `Mst` の代わりに前線の各頂点で `wgStg (m − 2)` を打つ。
* `wgStg 0 = Mst`（紙の最終段 M）。
* `wgStg (r+1)`（紙の G 段，keep なし）: 部分木は全部ゴースト。大きさ `f` の割った前線の各頂点を `compute .unghost`，
  内部を `cB .unghost`（根だけペブル，他の内部はゴースト）→ `clB`（内部を全部空），前線を全部 ghost，
  前線の各頂点の部分木に `wgStg r`。外のペブルは根の 1 個だけなので，予算は段によらず `p − 1`。
紙との違い（`m = 2` 版と同じもの）: 前線は「右の u 個を割る」でなく `⌈n/2⌉・⌊n/2⌋` に再帰的に割る。
G 段の手 2 は紙の「comp_B(c); p x; r x; clr_B(c)」を `cB`（x を置いて子をゴースト化）と `clB`（x を外して内部を空に）で打つ
（子を一度余分に計算し直すので手数は紙より多い）。手数は紙の閉じた式（補題 8）でなく上界
（内部 1 回あたり `2f(e+1)` 程度，`clB` の深さが `e + 1` で抑えられることを使う）。それでも定理 B の余裕に収まる。
-/
import SpookyTree.WindowUpper

namespace SpookyTree

/-! ## 内部の手数を前線の深さで抑える -/

/-- `clB` の手数は `2n·D` 以下（`n ≤ 2^D`。`m = 2` 版の `length_clB` は高さ `k` で抑えていた）。 -/
theorem length_clB_depth : ∀ (k n : ℕ) (y : Node) (D : ℕ), n ≤ 2 ^ D →
    (clB k n y).length ≤ 2 * n * D := by
  intro k
  induction k with
  | zero => intro n y D _; simp [clB]
  | succ k ih =>
    intro n y D hD
    by_cases h1 : n ≤ 1
    · rw [clB, if_pos h1]; simp
    · rw [clB, if_neg h1]
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := by
        cases D with
        | zero => simp at hD; omega
        | succ D' => exact ⟨D', rfl⟩
      rw [pow_succ] at hD
      simp only [List.length_append, List.length_singleton]
      have a := length_cB_le .unghost k ((n + 1) / 2) (y ++ [false]) (by omega)
      have b := length_cB_le .unghost k (n / 2) (y ++ [true]) (by omega)
      have c := ih ((n + 1) / 2) (y ++ [false]) D' (by omega)
      have d := ih (n / 2) (y ++ [true]) D' (by omega)
      have hs := half_sum n
      have e : 2 * ((n + 1) / 2) * D' + 2 * (n / 2) * D' = 2 * n * D' := by
        rw [← add_mul, ← mul_add, hs]
      have f : 2 * n * (D' + 1) = 2 * n * D' + 2 * n := by ring
      rw [f]
      omega

/-- `rootP` の手数は `2n·D` 以下（`2 ≤ n ≤ 2^D`）。 -/
theorem length_rootP_depth (k n : ℕ) (y : Node) (D : ℕ) (hn : 2 ≤ n) (hD : n ≤ 2 ^ D) :
    (rootP k n y).length ≤ 2 * n * D := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := by
    cases D with
    | zero => simp at hD; omega
    | succ D' => exact ⟨D', rfl⟩
  rw [pow_succ] at hD
  unfold rootP
  simp only [List.length_append, List.length_singleton]
  have a := length_cB_le .pebble k ((n + 1) / 2) (y ++ [false]) (by omega)
  have b := length_cB_le .pebble k (n / 2) (y ++ [true]) (by omega)
  have c := length_clB_depth k ((n + 1) / 2) (y ++ [false]) D' (by omega)
  have d := length_clB_depth k (n / 2) (y ++ [true]) D' (by omega)
  have hs := half_sum n
  have e : 2 * ((n + 1) / 2) * D' + 2 * (n / 2) * D' = 2 * n * D' := by
    rw [← add_mul, ← mul_add, hs]
  have f : 2 * n * (D' + 1) = 2 * n * D' + 2 * n := by ring
  rw [f]
  omega

/-! ## 段 2..m の再帰 -/

/-- 段の手続き。`wgStg h f g r t a` は高さ `t` の全部ゴーストの部分木 `T(a)` を全部空にする。
`r = 0` は最終段 M（`Mst`），`r + 1` は G 段（keep なし）の後に前線の各頂点で `r`。 -/
def wgStg (h f g : ℕ) : ℕ → ℕ → Node → List Move
  | 0, t, a => Mst h t g a
  | r + 1, t, a =>
      onSp (fun z => compute .unghost (h - z.length) z) t f a ++ cB .unghost t f a ++ clB t f a ++
        onSp (fun z => [⟨.ghost, z⟩]) t f a ++ onSp (fun z => wgStg h f g r (h - z.length) z) t f a

/-- **段の仕様.** 高さ `t ∈ [lo, hi]` の全部ゴーストの部分木を，ペブル数 `P` 以下で全部空にする。
`r` 回の G 段の後の最終段の部分木の高さは `[lo − r(e+1), hi − re]` に入る。 -/
theorem wgStg_spec {h f g e d hiM P : ℕ} (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1))
    (hd1 : 2 ^ d ≤ g) (hd2 : g < 2 ^ (d + 1)) (hPf : f + h + 2 ≤ P)
    (hp1 : hiM + 1 + (g - 1) * 1 ≤ P) (hp2 : 2 * g - 1 ≤ P)
    (hp3 : 2 ^ hiM - 1 + (g - 1) * 1 ≤ P) :
    ∀ (r lo hi : ℕ), r * (e + 1) + d + 2 ≤ lo → hi ≤ hiM + d + r * e → hi ≤ h →
    ∀ (t : ℕ) (a : Node) (c : Config), lo ≤ t → t ≤ hi → a.length + t = h →
      Pat (cst .ghost) t a c →
      Runs h t a P c (wgStg h f g r t a) ∧ Pat (cst .empty) t a (run c (wgStg h f g r t a)) := by
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  have hg1 : 1 ≤ g := le_trans Nat.one_le_two_pow hd1
  intro r
  induction r with
  | zero =>
    intro lo hi hlo hhi _ t a c ht1 ht2 ha hP
    simp only [zero_mul, Nat.zero_add, Nat.add_zero] at hlo hhi
    have hS : Shp 1 hiM t g := ⟨d + 1, d, hg1, le_of_lt hd2, by omega, hd1, by omega⟩
    show Runs h t a P c (Mst h t g a) ∧ Pat (cst .empty) t a (run c (Mst h t g a))
    exact Mst_spec hS ha hP hp1 hp2 hp3
  | succ r ih =>
    intro lo hi hlo hhi hhh t a c ht1 ht2 ha hP
    have q1 : (r + 1) * (e + 1) = r * (e + 1) + (e + 1) := by ring
    have q2 : (r + 1) * e = r * e + e := by ring
    rw [q1] at hlo
    rw [q2] at hhi
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
    -- 5. 前線の各頂点の部分木に次の段
    have hM : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → lo - e - 1 ≤ j →
        j ≤ hi - e → Pat (cst .ghost) j z c' →
        Runs h j z P c' (wgStg h f g r (h - z.length) z) ∧
          Pat (cst .empty) j z (run c' (wgStg h f g r (h - z.length) z)) := by
      intro z j c' hz hj1 hj2 hPz
      have hj : h - z.length = j := by omega
      rw [hj]
      exact ih (lo - e - 1) (hi - e) (by omega) (by omega) (by omega) j z c' hj1 hj2 hz hPz
    obtain ⟨hR5, hQ5⟩ := onSp_spec (h := h) (lo := lo - e - 1) (hi := hi - e) (p := P) (w := 0)
      (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
      (f := fun z => wgStg h f g r (h - z.length) z) hM pw_g0 pw_e0 t f a _ hS ha hQ4
    have hstg : wgStg h f g (r + 1) t a =
        onSp (fun z => compute .unghost (h - z.length) z) t f a ++ cB .unghost t f a ++ clB t f a ++
          onSp (fun z => [⟨.ghost, z⟩]) t f a ++
            onSp (fun z => wgStg h f g r (h - z.length) z) t f a := rfl
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

/-! ## 段の手数 -/

/-- 段 `r` の手数の上界で引く量。 -/
def wgS (f g : ℕ) : ℕ → ℕ
  | 0 => 4 * g + 2
  | r + 1 => f * wgS f g r + 2

/-- 段 `r` の手数の上界で足す量。 -/
def wgC (f e : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => f * wgC f e r + 2 * f * (e + 1)

/-- **段の手数.** `|wgStg r t a| + wgS r ≤ (2r + 4)·2^t + wgC r`。 -/
theorem length_wgStg {h f g e d hiM : ℕ} (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1))
    (hd1 : 2 ^ d ≤ g) (hd2 : g < 2 ^ (d + 1)) :
    ∀ (r lo hi : ℕ), r * (e + 1) + d + 2 ≤ lo → hi ≤ hiM + d + r * e →
    ∀ (t : ℕ) (a : Node), lo ≤ t → t ≤ hi → a.length + t = h →
      (wgStg h f g r t a).length + wgS f g r ≤ (2 * r + 4) * 2 ^ t + wgC f e r := by
  have hg1 : 1 ≤ g := le_trans Nat.one_le_two_pow hd1
  intro r
  induction r with
  | zero =>
    intro lo hi hlo hhi t a ht1 ht2 ha
    simp only [zero_mul, Nat.zero_add, Nat.add_zero] at hlo hhi
    have hS : Shp 1 hiM t g := ⟨d + 1, d, hg1, le_of_lt hd2, by omega, hd1, by omega⟩
    have := length_Mst hS ha
    simp only [wgS, wgC, wgStg]
    omega
  | succ r ih =>
    intro lo hi hlo hhi t a ht1 ht2 ha
    have q1 : (r + 1) * (e + 1) = r * (e + 1) + (e + 1) := by ring
    have q2 : (r + 1) * e = r * e + e := by ring
    rw [q1] at hlo
    rw [q2] at hhi
    have hlo' : 1 ≤ lo - e - 1 := by omega
    have hS : Shp (lo - e - 1) (hi - e) t f :=
      ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
    have hA := length_onSp (h := h) (lo := lo - e - 1) (hi := hi - e) (α := 2) (β := 3) (γ := 0)
      hlo' (f := fun z => compute .unghost (h - z.length) z)
      (fun z j hz hj1 _ => by
        have hj : h - z.length = j := by omega
        simp only [hj]
        have := length_compute .unghost j z (by omega)
        rw [pow_succ] at this
        omega) t f a hS ha
    have hB := length_cB_le .unghost t f a (by omega)
    have hC := length_clB_depth t f a (e + 1) (le_of_lt he2)
    have hD := length_onSp (h := h) (lo := lo - e - 1) (hi := hi - e) (α := 0) (β := 0) (γ := 1)
      hlo' (f := fun z => [(⟨.ghost, z⟩ : Move)]) (fun z j _ _ _ => by simp) t f a hS ha
    have hE := length_onSp (h := h) (lo := lo - e - 1) (hi := hi - e) (α := 2 * r + 4)
      (β := wgS f g r) (γ := wgC f e r) hlo' (f := fun z => wgStg h f g r (h - z.length) z)
      (fun z j hz hj1 hj2 => by
        have hj : h - z.length = j := by omega
        simp only [hj]
        exact ih (lo - e - 1) (hi - e) (by omega) (by omega) j z hj1 hj2 hz) t f a hS ha
    have hstg : wgStg h f g (r + 1) t a =
        onSp (fun z => compute .unghost (h - z.length) z) t f a ++ cB .unghost t f a ++ clB t f a ++
          onSp (fun z => [⟨.ghost, z⟩]) t f a ++
            onSp (fun z => wgStg h f g r (h - z.length) z) t f a := rfl
    rw [hstg]
    simp only [List.length_append, wgS, wgC]
    simp only [zero_mul, one_mul, add_zero, Nat.zero_add] at hA hD
    have e1 : (2 * (r + 1) + 4) * 2 ^ t = (2 * r + 4) * 2 ^ t + 2 * 2 ^ t := by ring
    have e2 : wgS f g r * f = f * wgS f g r := mul_comm _ _
    have e3 : wgC f e r * f = f * wgC f e r := mul_comm _ _
    rw [e1]
    rw [e2, e3] at hE
    omega

/-- 手数の余裕: `wgC r + 2f^{r+1} + 2h + 10 ≤ wgS r`。 -/
theorem wgS_ge {f g e h : ℕ} (hf2 : 2 ≤ f) (h0 : 2 * f + 2 * h + 10 ≤ 4 * g + 2)
    (he4 : 4 * e ≤ 2 * h + 8) :
    ∀ r : ℕ, wgC f e r + 2 * f ^ (r + 1) + 2 * h + 10 ≤ wgS f g r := by
  intro r
  induction r with
  | zero => simp only [wgC, wgS, Nat.zero_add, pow_one]; omega
  | succ r ih =>
    simp only [wgC, wgS]
    obtain ⟨q, hq⟩ : ∃ q, 2 * h + 8 = 2 * e + q := ⟨2 * h + 8 - 2 * e, by omega⟩
    have hq2 : 2 * q ≤ f * q := Nat.mul_le_mul_right q hf2
    have hih : f * (wgC f e r + 2 * f ^ (r + 1) + 2 * h + 10) ≤ f * wgS f g r :=
      Nat.mul_le_mul_left f ih
    have hpow : f ^ (r + 1 + 1) = f * f ^ (r + 1) := by ring
    have hexp : f * (2 * h + 10) = f * (2 * e + 2) + f * q := by
      rw [show 2 * h + 10 = 2 * e + 2 + q by omega]; ring
    linarith

/-! ## 全体の構成（段 1 は keep） -/

/-- 構成 B★（一般の m）の段 1。前線の各頂点の部分木で `M` を打つ（`stratW` の `Mst` を一般化）。 -/
def wgStrat (h f : ℕ) (M : Node → List Move) : List Move :=
  onSp (fun a => compute .pebble (h - a.length) a) h f [] ++ (rootP (h - 1) f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) (h - 1) ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) (h - 1) (f / 2) [true]) ++
    (onSp M (h - 1) ((f + 1) / 2) [false] ++ onSp M (h - 1) (f / 2) [true])))

theorem wgStrat_eq (k f : ℕ) (M : Node → List Move) : wgStrat (k + 1) f M =
    onSp (fun a => compute .pebble (k + 1 - a.length) a) (k + 1) f [] ++ (rootP k f [] ++
    ((onSp (fun a => [⟨.ghost, a⟩]) k ((f + 1) / 2) [false] ++
      onSp (fun a => [⟨.ghost, a⟩]) k (f / 2) [true]) ++
    (onSp M k ((f + 1) / 2) [false] ++ onSp M k (f / 2) [true]))) := by
  rw [wgStrat, Nat.add_sub_cancel]

/-- **段 1 の仕様.** 前線の各部分木で `M` が（予算 `p − 1` で）全部ゴーストを全部空にするなら，
空の盤から合法で，ペブル数は `p` 以下，終わると根だけペブル・他は空。 -/
theorem wgStrat_spec {k f p lo hi : ℕ} {M : Node → List Move} (hlo : 1 ≤ lo)
    (hS : Shp lo hi (k + 1) f) (hf2 : 2 ≤ f)
    (hM : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      Pat (cst .ghost) j a c' → Runs (k + 1) j a (p - 1) c' (M a) ∧
        Pat (cst .empty) j a (run c' (M a)))
    (hp0 : hi + 1 + (f - 1) * 1 ≤ p) (hpR : f + k + 4 ≤ p) (hp : 1 ≤ p) :
    Runs (k + 1) (k + 1) [] p (fun _ => Cell.empty) (wgStrat (k + 1) f M) ∧
    run (fun _ => Cell.empty) (wgStrat (k + 1) f M) [] = .pebble ∧
    ∀ z : Node, z.length < k + 1 → z ≠ [] →
      run (fun _ => Cell.empty) (wgStrat (k + 1) f M) z = .empty := by
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
  -- 4. 前線の各頂点の部分木に M
  obtain ⟨hR4a, hQ4a⟩ := onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
    (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
    (f := M) hM pw_g0 pw_e0 k _ [false] _ hSL hl0 hQ3L
  have b4R := pcSP_cst_le (G := cst .ghost) (X := .empty) (by decide) pw_g0 k (f / 2) hSR
  have b4L := pcSP_cst_le (G := cst .empty) (X := .empty) (by decide) pw_e0 k ((f + 1) / 2) hSL
  obtain ⟨hR4, hr4, hQ4L, hQ4R⟩ := pair_spec (y := []) (P := p) hR4a hQ4a hQ3R
    (fun c' hc' => onSp_spec (h := k + 1) (lo := lo) (hi := hi) (p := p - 1) (w := 0)
      (ci := .empty) (by decide) (G0 := cst .ghost) (G1 := cst .empty)
      (f := M) hM pw_g0 pw_e0 k _ [true] c' hSR hl1 hc')
    (by rw [hr3, hr2, if_pos rfl]; omega) (by rw [hr3, hr2, if_pos rfl]; omega)
  rw [wgStrat_eq]
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

/-- **段 1 の手数.** -/
theorem length_wgStrat {k f lo hi e α β γ : ℕ} {M : Node → List Move} (hlo : 1 ≤ lo)
    (hS : Shp lo hi (k + 1) f) (hf2 : 2 ≤ f) (he2 : f ≤ 2 ^ (e + 1))
    (hm : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      (M a).length + β ≤ α * 2 ^ j + γ) :
    (wgStrat (k + 1) f M).length + 3 * f + β * f ≤
      2 * 2 ^ (k + 1) + 2 * f * (e + 1) + f + α * 2 ^ (k + 1) + γ * f := by
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hl0 : ([false] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hl1 : ([true] : Node).length + k = k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  rw [wgStrat_eq]
  simp only [List.length_append]
  have hA := length_onSp (h := k + 1) (lo := lo) (hi := hi) (α := 2) (β := 3) (γ := 0) hlo
    (f := fun a => compute .pebble (k + 1 - a.length) a)
    (fun a j ha hj1 _ => by
      have hj : k + 1 - a.length = j := by omega
      simp only [hj]
      have := length_compute .pebble j a (by omega)
      rw [pow_succ] at this
      omega) (k + 1) f [] hS (by simp)
  have hB := length_rootP_depth k f [] (e + 1) hf2 he2
  have hgh : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → lo ≤ j → j ≤ hi →
      ((fun a => [(⟨.ghost, a⟩ : Move)]) a).length + 0 ≤ 0 * 2 ^ j + 1 := by
    intro a j _ _ _; simp
  have hCL := length_onSp (h := k + 1) hlo hgh k _ [false] hSL hl0
  have hCR := length_onSp (h := k + 1) hlo hgh k _ [true] hSR hl1
  have hDL := length_onSp (h := k + 1) hlo hm k _ [false] hSL hl0
  have hDR := length_onSp (h := k + 1) hlo hm k _ [true] hSR hl1
  have e1 : β * f = β * ((f + 1) / 2) + β * (f / 2) := by rw [← mul_add, hs]
  have e1' : γ * f = γ * ((f + 1) / 2) + γ * (f / 2) := by rw [← mul_add, hs]
  have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e3 : α * (2 * 2 ^ k) = α * 2 ^ k + α * 2 ^ k := by ring
  rw [e1, e1', e2, e3]
  rw [e2] at hA
  simp only [zero_mul, one_mul, add_zero] at hA hCL hCR
  omega

/-! ## 定理 B（一般の m） -/

/-- 段 1 の後の構成全体（`m = r + 2`）。 -/
def wgAll (h f g r : ℕ) : List Move :=
  wgStrat h f (fun a => wgStg h f g r (h - a.length) a)

/-- 定理 B（一般の m）の核: `e = ⌊log₂ f⌋`・`d = ⌊log₂ g⌋` の性質と，(B1)(B2) から出る不等式を仮定に取る形。 -/
theorem window_upper_core_gen {r h p f g e d : ℕ} (hf : f = p - h - 5) (hg : g = p / 2)
    (hlo : h + 13 ≤ p) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hd1 : 2 ^ d ≤ g)
    (hd2 : g < 2 ^ (d + 1)) (hed : (r + 1) * (e + 1) + d + 2 ≤ h) (he4 : 4 * e ≤ 2 * h + 8)
    (hmh : r + 2 ≤ h + 1)
    (hX : 2 * 2 ^ (h - (r + 1) * e - d) + 1 ≤ p) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      T + 2 * f ^ (r + 2) + 1 ≤ 2 * (r + 2 + 1) * (2 ^ h - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hf8 : 8 ≤ f := by omega
  have hf2 : 2 ≤ f := by omega
  have q1 : (r + 1) * (e + 1) = r * (e + 1) + e + 1 := by ring
  have q2 : (r + 1) * e = r * e + e := by ring
  have q3 : (r + 1) * (e + 1) = (r + 1) * e + r + 1 := by ring
  set hiM := k + 1 - (r + 1) * e - d with hhiM
  have hXn := lt_two_pow' hiM
  have hS : Shp (k + 1 - e - 1) (k + 1 - e) (k + 1) f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  have hM : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → k + 1 - e - 1 ≤ j →
      j ≤ k + 1 - e → Pat (cst .ghost) j a c' →
      Runs (k + 1) j a (p - 1) c' (wgStg (k + 1) f g r (k + 1 - a.length) a) ∧
        Pat (cst .empty) j a (run c' (wgStg (k + 1) f g r (k + 1 - a.length) a)) := by
    intro a j c' ha hj1 hj2 hPa
    have hj : k + 1 - a.length = j := by omega
    rw [hj]
    exact wgStg_spec (hiM := hiM) (P := p - 1) hf2 he1 he2 hd1 hd2 (by omega) (by omega)
      (by omega) (by omega) r (k + 1 - e - 1) (k + 1 - e) (by omega) (by omega) (by omega)
      j a c' hj1 hj2 ha hPa
  obtain ⟨hR, hroot, hothers⟩ := wgStrat_spec (k := k) (f := f) (p := p)
    (M := fun a => wgStg (k + 1) f g r (k + 1 - a.length) a) (lo := k + 1 - e - 1)
    (hi := k + 1 - e) (by omega) hS hf2 hM (by omega) (by omega) (by omega)
  have hm : ∀ (a : Node) (j : ℕ), a.length + j = k + 1 → k + 1 - e - 1 ≤ j → j ≤ k + 1 - e →
      ((fun a => wgStg (k + 1) f g r (k + 1 - a.length) a) a).length + wgS f g r ≤
        (2 * r + 4) * 2 ^ j + wgC f e r := by
    intro a j ha hj1 hj2
    have hj : k + 1 - a.length = j := by omega
    simp only [hj]
    exact length_wgStg (h := k + 1) (hiM := hiM) hf2 he1 he2 hd1 hd2 r (k + 1 - e - 1)
      (k + 1 - e) (by omega) (by omega) j a hj1 hj2 ha
  have hlen := length_wgStrat (by omega) hS hf2 (le_of_lt he2) hm
  have hSge := wgS_ge (g := g) (e := e) (h := k + 1) hf2 (by omega) he4 r
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  generalize (wgStrat (k + 1) f fun a => wgStg (k + 1) f g r (k + 1 - a.length) a).length = T
    at hlen ⊢
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ (k + 1) = Y + 1 := ⟨2 ^ (k + 1) - 1, by
    have := Nat.one_le_two_pow (n := k + 1); omega⟩
  rw [hY] at hlen
  rw [hY, Nat.add_sub_cancel]
  -- 余裕: f(2h + 10 − 2e) ≥ 2m + 3
  obtain ⟨q, hq⟩ : ∃ q, 2 * (k + 1) + 10 = 2 * e + q := ⟨2 * (k + 1) + 10 - 2 * e, by omega⟩
  have hq2 : 2 * q ≤ f * q := Nat.mul_le_mul_right q hf2
  have hkey : 2 * (r + 2 + 1) + 1 ≤ 2 * q := by omega
  have hexp : f * (2 * (k + 1) + 10) = f * (2 * e) + f * q := by rw [hq]; ring
  have hpow : f ^ (r + 2) = f * f ^ (r + 1) := by ring
  have hmul : (wgC f e r + 2 * f ^ (r + 1) + 2 * (k + 1) + 10) * f ≤ wgS f g r * f :=
    Nat.mul_le_mul_right f hSge
  rw [hpow]
  linarith

/-- **定理 B（一般の m ≥ 2）.** 紙の定理 B（`WINDOW_UB_2026-11.md` 0 節の表）:
`H = ⌊h/m⌋`、`e = ⌊log₂(p − h − 5)⌋` として (B1) `h + 13 ≤ p ≤ 2^H − 1`、(B2) `2^{h−(m−1)e+3} ≤ p(p−1)` なら、
ペブル `p` 個で `T + 2(p − h − 5)^m + 1 ≤ 2(m+1)(2^h − 1)` の妥当な手順がある。 -/
theorem window_upper_bound {m h p : ℕ} (hm : 2 ≤ m) (hlo : h + 13 ≤ p)
    (hhi : p ≤ 2 ^ (h / m) - 1)
    (hB2 : 2 ^ (h - (m - 1) * Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      T + 2 * (p - h - 5) ^ m + 1 ≤ 2 * (m + 1) * (2 ^ h - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  have hm1 : r + 2 - 1 = r + 1 := by omega
  rw [hm1] at hB2
  have hf0 : p - h - 5 ≠ 0 := by omega
  have hg0 : p / 2 ≠ 0 := by omega
  have he1 : 2 ^ Nat.log 2 (p - h - 5) ≤ p - h - 5 := Nat.pow_log_le_self 2 hf0
  have he2 : p - h - 5 < 2 ^ (Nat.log 2 (p - h - 5) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hd1 : 2 ^ Nat.log 2 (p / 2) ≤ p / 2 := Nat.pow_log_le_self 2 hg0
  have hd2 : p / 2 < 2 ^ (Nat.log 2 (p / 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  generalize Nat.log 2 (p - h - 5) = e at he1 he2 hB2
  generalize Nat.log 2 (p / 2) = d at hd1 hd2
  have hmH : h / (r + 2) * (r + 2) ≤ h := Nat.div_mul_le_self h (r + 2)
  generalize h / (r + 2) = H at hhi hmH
  have hH1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have heH : e + 1 ≤ H := by
    by_contra hc
    have : 2 ^ H ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdH : d + 2 ≤ H := by
    by_contra hc
    have : 2 ^ H ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    omega
  -- (m − 1)(e + 1) + d + 2 ≤ mH ≤ h
  have hmul : (r + 1) * (e + 1) ≤ (r + 1) * H := Nat.mul_le_mul_left (r + 1) heH
  have hHm : H * (r + 2) = (r + 1) * H + H := by ring
  have hed : (r + 1) * (e + 1) + d + 2 ≤ h := by omega
  have h2H : H * 2 ≤ H * (r + 2) := Nat.mul_le_mul_left H (by omega)
  have he4 : 4 * e ≤ 2 * h + 8 := by omega
  have h1H : 1 * (r + 2) ≤ H * (r + 2) := Nat.mul_le_mul_right (r + 2) (by omega)
  have hmh : r + 2 ≤ h + 1 := by omega
  have q3 : (r + 1) * (e + 1) = (r + 1) * e + r + 1 := by ring
  have hX : 2 * 2 ^ (h - (r + 1) * e - d) + 1 ≤ p := by
    have h1 : 2 ^ (h - (r + 1) * e + 3) = 2 ^ (h - (r + 1) * e - d) * (2 ^ (d + 1) * 4) := by
      rw [show h - (r + 1) * e + 3 = (h - (r + 1) * e - d) + (d + 1) + 2 by omega, pow_add,
        pow_add]
      ring
    rw [h1] at hB2
    exact B2_arith (g := p / 2) hB2 (by omega) (by omega) (by omega)
  exact window_upper_core_gen (f := p - h - 5) (g := p / 2) rfl rfl hlo he1 he2 hd1 hd2 hed he4
    hmh hX

/-- **定理 B（一般の m）を最小手数で.** `T(T_h, p) ≤ 2(m+1)(2^h − 1) − 2(p − h − 5)^m − 1`。 -/
theorem Ttree_window_upper {m h p : ℕ} (hm : 2 ≤ m) (hlo : h + 13 ≤ p)
    (hhi : p ≤ 2 ^ (h / m) - 1)
    (hB2 : 2 ^ (h - (m - 1) * Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    Ttree h p ≤ 2 * (m + 1) * (2 ^ h - 1) - 2 * (p - h - 5) ^ m - 1 := by
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound hm hlo hhi hB2
  have := Ttree_le_of_valid hV
  omega

/-- **定理 B（一般の m，KSS の意味論）.** -/
theorem window_upper_bound_kss {m h p : ℕ} (hm : 2 ≤ m) (hlo : h + 13 ≤ p)
    (hhi : p ≤ 2 ^ (h / m) - 1)
    (hB2 : 2 ^ (h - (m - 1) * Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h p T ms ∧
      T + 2 * (p - h - 5) ^ m + 1 ≤ 2 * (m + 1) * (2 ^ h - 1) := by
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound hm hlo hhi hB2
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

theorem TtreeK_window_upper {m h p : ℕ} (hm : 2 ≤ m) (hlo : h + 13 ≤ p)
    (hhi : p ≤ 2 ^ (h / m) - 1)
    (hB2 : 2 ^ (h - (m - 1) * Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    TtreeK h p ≤ 2 * (m + 1) * (2 ^ h - 1) - 2 * (p - h - 5) ^ m - 1 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_upper hm hlo hhi hB2

end SpookyTree
