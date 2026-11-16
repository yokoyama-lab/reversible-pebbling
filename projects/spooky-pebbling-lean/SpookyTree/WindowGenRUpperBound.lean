/-
# 定理 B_{m,r}（一般の m ≥ 2・1 ≤ r ≤ m − 1）: 構成 B★ の合法性・ピーク・手数の上界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M5_UB_2026-11.md` の 2〜3 節（恒等式 E，補題 P1〜P3，W，Γ，定理 B_{m,r}）と
`tree-gap/paper/app_window_ub.tex` の構成 B★。`m = n + 2`，`H = K + 1`，`X = 2^H`，`h = mH + r`，`δ = h + 5`，`f = p − δ`。

構成は既存の m 段の B★（`gm_assemble`，`WindowGenM1Upper.lean`．B_{m,1} の Lean 版で使ったもの）をそのまま使う。
`gm_assemble` は剰余に依らず，最終段の部分木の高さ `l, …, l + m − 1`（`h = l + (m − 1)(e + 1)`）を引数に取る。
剰余 r で変わるのは `l` だけ（(αβ) は `e = H`，`l = H + r − m + 1`．(γ) は `e = H − 1`，`l = H + r`）。
* `genr_assemble`: 最終段の各部分木の手数を `2·2^t + (2·2^t − 2 min(2^t, p))` で抑え（F は `2·2^t − 2`，
  M は `4·2^t − 4g − 2 ≤ 4·2^t − 2p`），`T ≤ 2(m+1)2^h − 2f + 2(e+1)Σf^j − 2·G(δ)`，
  `G(δ) = L^{m−1} w (0)`，`L = (2f − 2^{e+1}, 2^{e+1} − f)`，`w_j = min(2^{l+j}, p)`（紙の恒等式 E の Lean 版）。
* `genr_caseA`（紙の (αβ)，`X + δ ≤ p ≤ 2X`）: 補題 W の核 `gmLit_pert` で `Gid − G(δ) ≤ (m−1)δp^{m−1}`。
* `genr_caseG`（紙の (γ)，`X + 1 ≤ p < X + δ`）: 最終段はすべて M で `G(δ) = p f^{m−1}`，`Gid ≤ p^m`，
  `p^m − p f^{m−1} ≤ (m−1)δp^{m−1}`（紙の補題 Γ より粗いが同じ次数）。
* **`genr_upper_bound`（定理 B_{m,r}）**: `H ≥ m + r + 1`，`2^{H−1} ≥ mH + r + 4`（紙の `H ≥ H0(m,r)` と同値），
  `X + 1 ≤ p ≤ 2X` なら妥当な手順があり `T ≤ (2(m+1) − 2σ_{m,r}(p/X))2^h + m2^m(h+5)X^{m−1}`。
  主項は補題 I（`genr_lemmaI`）で `2^h σ_{m,r}(p/X)` に直す。定数 `m2^m(h+5)` は紙と同じ。
-/
import SpookyTree.WindowGenRUpperAlg
import SpookyTree.StepLimit

namespace SpookyTree
namespace GenRUpper

/-- 理想の前線の節約 `Gid = L₀^{m−1} w (0)`（`m = n + 2`，`w_j = min(2^{H+r−m+1+j}, p)`）。 -/
def genrGid (n r H p : ℕ) : ℤ :=
  gmLit (2 * ((p : ℤ) - 2 ^ H)) (2 * 2 ^ H - p) (n + 1)
    (fun j => min (2 ^ (H + r - (n + 1) + j)) (p : ℤ)) 0

/-! ## 構成の組み立て（恒等式 E の Lean 版） -/

theorem genr_assemble {n h p f g e l hM : ℕ} (hh : h = l + n * (e + 1) + (e + 1))
    (hf : f + h + 5 = p) (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hl : 1 ≤ l)
    (hg : g = p / 2) (hg1 : 2 ^ hM + g ≤ p) (hg0 : hM + g + 2 ≤ p)
    (hMs : ∀ j, l ≤ j → j ≤ l + n + 1 → ¬ 2 ^ j ≤ p → Shp 1 hM j g) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 3) * 2 ^ h - 2 * f + 2 * ((e : ℤ) + 1) * gmSg f (n + 1) -
        2 * gmLit (2 * f - 2 ^ (e + 1)) (2 ^ (e + 1) - f) (n + 1)
          (fun j => min (2 ^ (l + j)) (p : ℤ)) 0 := by
  have hg2 : 2 * g ≤ p := by omega
  have hgp : p ≤ 2 * g + 1 := by omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l ≤ j → j ≤ l + n + 1 →
      Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := hM) hz (by omega) (hMs j hj1 hj2) hg1 hg0 hg2 hPz
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℤ,
      E = fun j => 2 * 2 ^ (l + j) + -2 * min (2 ^ (l + j)) (p : ℤ) := ⟨_, rfl⟩
  have hφ : ∀ i, i ≤ n + 1 → ∀ z : Node, z.length + (l + i) = h →
      ((finW h p g z).length : ℤ) ≤ (fun i => 2 * 2 ^ (l + i) + E i) i := by
    intro i hi z hz
    simp only [hE]
    by_cases hF : 2 ^ (l + i) ≤ p
    · have h1 := length_finW_F3 (g := g) hz hF
      have hFz : (2 : ℤ) ^ (l + i) ≤ p := by exact_mod_cast hF
      rw [min_eq_left hFz]
      linarith
    · have h1 := length_finW_M3 (p := p) (g := g) hz hF (hMs (l + i) (by omega) (by omega) hF)
      have hFz : (p : ℤ) ≤ 2 ^ (l + i) := by
        have : p ≤ 2 ^ (l + i) := by omega
        exact_mod_cast this
      rw [min_eq_right hFz]
      have hgz : (p : ℤ) ≤ 2 * g + 1 := by exact_mod_cast hgp
      linarith
  obtain ⟨T, ms, hV, hT⟩ := gm_assemble hh hf hf2 he1 he2 hl hFin hφ
  refine ⟨T, ms, hV, ?_⟩
  rw [gm_total hh, hE] at hT
  have hlin : gmLit (2 * (f : ℤ) - 2 ^ (e + 1)) (2 ^ (e + 1) - f) (n + 1)
      (fun j => 2 * 2 ^ (l + j) + -2 * min (2 ^ (l + j)) (p : ℤ)) 0 =
      2 * gmLit (2 * (f : ℤ) - 2 ^ (e + 1)) (2 ^ (e + 1) - f) (n + 1) (fun j => 2 ^ (l + j)) 0 +
        -2 * gmLit (2 * (f : ℤ) - 2 ^ (e + 1)) (2 ^ (e + 1) - f) (n + 1)
          (fun j => min (2 ^ (l + j)) (p : ℤ)) 0 :=
    gmLit_lin _ _ 2 (-2) (fun j => (2 : ℤ) ^ (l + j)) (fun j => min (2 ^ (l + j)) (p : ℤ)) (n + 1) 0
  have hp2 := gmLit_pow2 (2 * (f : ℤ) - 2 ^ (e + 1)) (2 ^ (e + 1) - f) l (n + 1) 0
  rw [show 2 * (f : ℤ) - 2 ^ (e + 1) + 2 * (2 ^ (e + 1) - f) = 2 ^ (e + 1) by ring] at hp2
  have hh2 : ((2 : ℤ) ^ (e + 1)) ^ (n + 1) * 2 ^ (l + 0) = 2 ^ h := by
    rw [← pow_mul, ← pow_add, hh]; congr 1; ring
  rw [hh2] at hp2
  rw [hlin, hp2] at hT
  linarith

/-! ## 場合 (αβ)（`X + δ ≤ p ≤ 2X`） -/

theorem genr_caseA {n r K p : ℕ} (hr1 : 1 ≤ r) (_hrn : r ≤ n + 1)
    (hH1 : n + r + 3 ≤ K + 1) (hH2 : 2 * ((n + 2) * (K + 1) + r + 4) ≤ 2 ^ (K + 1))
    (hp1 : 2 ^ (K + 1) + ((n + 2) * (K + 1) + r + 5) ≤ p) (hp2 : p ≤ 2 ^ (K + 1 + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * (K + 1) + r) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 3) * 2 ^ ((n + 2) * (K + 1) + r) - 2 * genrGid n r (K + 1) p +
        2 * ((n : ℤ) + 1) * ((((n + 2) * (K + 1) + r : ℕ) : ℤ) + 5) * (p : ℤ) ^ (n + 1) +
        4 * ((K : ℤ) + 2) * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by
  obtain ⟨h, hhdef⟩ : ∃ h, h = (n + 2) * (K + 1) + r := ⟨_, rfl⟩
  rw [← hhdef] at hH2 hp1 ⊢
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_succ, pow_succ]; ring
  have hnK : (n + 2) * (K + 1) = n * K + n + 2 * K + 2 := by ring
  have hnK2 : n * (K + 1 + 1) = n * K + 2 * n := by ring
  have hK1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  rw [q1] at hH2 hp1
  have hK : n + r + 2 ≤ K := by omega
  have hrK : 2 ^ (r + n + 2) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hh4 : h + 4 ≤ 2 ^ K := by omega
  obtain ⟨f, hf⟩ : ∃ f, f + h + 5 = p := ⟨p - (h + 5), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hh : h = (K + r - n) + n * (K + 1 + 1) + (K + 1 + 1) := by omega
  have hMs : ∀ j, K + r - n ≤ j → j ≤ K + r - n + n + 1 → ¬ 2 ^ j ≤ p →
      Shp 1 (r + n + 2) j g := by
    intro j hj1 hj2 hF
    have hjK : K + 1 + 1 ≤ j := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  obtain ⟨T, ms, hV, hT⟩ := genr_assemble (n := n) (h := h) (e := K + 1) (l := K + r - n)
    (hM := r + n + 2) hh hf (by omega) (by rw [q1]; omega) (by rw [q2]; omega) (by omega) hg
    (by omega) (by omega) hMs
  refine ⟨T, ms, hV, ?_⟩
  have hGid : genrGid n r (K + 1) p = gmLit (2 * ((p : ℤ) - 2 ^ (K + 1))) (2 * 2 ^ (K + 1) - p)
      (n + 1) (fun j => min (2 ^ (K + r - n + j)) (p : ℤ)) 0 := by
    unfold genrGid; rw [show K + 1 + r - (n + 1) = K + r - n by omega]
  rw [hGid]
  push_cast at hT
  -- 整数の事実
  have hfz : (f : ℤ) + h + 5 = p := by exact_mod_cast hf
  have hh0 : (0 : ℤ) ≤ h := by positivity
  have hpz : (0 : ℤ) ≤ p := by positivity
  have hX : (2 : ℤ) ^ (K + 1) = 2 * 2 ^ K := by ring
  have hX2 : (2 : ℤ) ^ (K + 1 + 1) = 4 * 2 ^ K := by ring
  have hp1z : 2 * (2 : ℤ) ^ K + (h + 5) ≤ p := by exact_mod_cast hp1
  have hp2z : (p : ℤ) ≤ 4 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  -- 補題 W
  have hD := gmLit_pert (α := 2 * (f : ℤ) - 2 ^ (K + 1 + 1)) (β := 2 ^ (K + 1 + 1) - f)
    (α₀ := 2 * ((p : ℤ) - 2 ^ (K + 1))) (β₀ := 2 * 2 ^ (K + 1) - p) (d := (h : ℤ) + 5)
    (c := p) (s := p) (by rw [hX2]; linarith) (by rw [hX2]; linarith) (by linarith)
    (by rw [hX, hX2]; linarith) (by rw [hX, hX2]; linarith) (by rw [hX]; linarith)
    (by linarith) (by linarith) hpz (w := fun j => min (2 ^ (K + r - n + j)) (p : ℤ))
    (fun j => (minw_two_sub (K + r - n) hpz j).2) n 0
  have ehD : ((n : ℤ) + 1) * ((h : ℤ) + 5) * p * (p : ℤ) ^ n =
      ((n : ℤ) + 1) * ((h : ℤ) + 5) * (p : ℤ) ^ (n + 1) := by ring
  -- 段の内部
  have hf2 : 2 ≤ f := by omega
  have hS := gmSg_le_two hf2 (n + 1)
  have hf0 : (0 : ℤ) ≤ f := by positivity
  have hfX : (f : ℤ) ≤ 2 ^ (K + 1 + 1) := by rw [hX2]; linarith
  have hfn : (f : ℤ) ^ (n + 1) ≤ ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := pow_le_pow_left₀ hf0 hfX _
  have s1 : gmSg f (n + 1) ≤ 2 * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by linarith
  have s2 := mul_le_mul_of_nonneg_left s1 (show (0 : ℤ) ≤ 2 * ((K : ℤ) + 1 + 1) by positivity)
  linarith [hT, hD, ehD, s2]

/-! ## 場合 (γ)（`X + 1 ≤ p < X + δ`） -/

theorem genr_caseG {n r K p : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n + 1)
    (hH1 : n + r + 3 ≤ K + 1) (hH2 : 2 * ((n + 2) * (K + 1) + r + 4) ≤ 2 ^ (K + 1))
    (hp1 : 2 ^ (K + 1) + 1 ≤ p) (hp2 : p < 2 ^ (K + 1) + ((n + 2) * (K + 1) + r + 5)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * (K + 1) + r) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 3) * 2 ^ ((n + 2) * (K + 1) + r) - 2 * genrGid n r (K + 1) p +
        2 * ((n : ℤ) + 1) * ((((n + 2) * (K + 1) + r : ℕ) : ℤ) + 5) * (p : ℤ) ^ (n + 1) +
        4 * ((K : ℤ) + 2) * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by
  obtain ⟨h, hhdef⟩ : ∃ h, h = (n + 2) * (K + 1) + r := ⟨_, rfl⟩
  rw [← hhdef] at hH2 hp2 ⊢
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_succ, pow_succ]; ring
  have hnK : (n + 2) * (K + 1) = n * K + n + 2 * K + 2 := by ring
  have hnK1 : n * (K + 1) = n * K + n := by ring
  have hK1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  rw [q1] at hH2 hp1 hp2
  have hK : n + r + 2 ≤ K := by omega
  have hrK : 2 ^ (r + n + 2) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hh4 : h + 4 ≤ 2 ^ K := by omega
  obtain ⟨f, hf⟩ : ∃ f, f + h + 5 = p := ⟨p - (h + 5), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hh : h = (K + 1 + r) + n * (K + 1) + (K + 1) := by omega
  -- 最終段の高さは K + 2 以上で，すべて M（2^t > p）
  have hbig : ∀ j, K + 1 + 1 ≤ j → p < 2 ^ j := by
    intro j hj
    have : 2 ^ (K + 1 + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hMs : ∀ j, K + 1 + r ≤ j → j ≤ K + 1 + r + n + 1 → ¬ 2 ^ j ≤ p →
      Shp 1 (r + n + 2) j g := by
    intro j hj1 hj2 _
    exact ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  obtain ⟨T, ms, hV, hT⟩ := genr_assemble (n := n) (h := h) (e := K) (l := K + 1 + r)
    (hM := r + n + 2) hh hf (by omega) (by omega) (by rw [q1]; omega) (by omega) hg
    (by omega) (by omega) hMs
  refine ⟨T, ms, hV, ?_⟩
  have hw : (fun j => min (2 ^ (K + 1 + r + j)) (p : ℤ)) = fun _ => (p : ℤ) := by
    funext j
    apply min_eq_right
    have := hbig (K + 1 + r + j) (by omega)
    exact_mod_cast this.le
  rw [hw, gmLit_const, show 2 * (f : ℤ) - 2 ^ (K + 1) + (2 ^ (K + 1) - f) = f by ring] at hT
  have hGid : genrGid n r (K + 1) p = gmLit (2 * ((p : ℤ) - 2 ^ (K + 1))) (2 * 2 ^ (K + 1) - p)
      (n + 1) (fun j => min (2 ^ (K + r - n + j)) (p : ℤ)) 0 := by
    unfold genrGid; rw [show K + 1 + r - (n + 1) = K + r - n by omega]
  -- 整数の事実
  have hfz : (f : ℤ) + h + 5 = p := by exact_mod_cast hf
  have hh0 : (0 : ℤ) ≤ h := by positivity
  have hpz : (0 : ℤ) ≤ p := by positivity
  have hf0 : (0 : ℤ) ≤ f := by positivity
  have hX : (2 : ℤ) ^ (K + 1) = 2 * 2 ^ K := by ring
  have hX2 : (2 : ℤ) ^ (K + 1 + 1) = 4 * 2 ^ K := by ring
  have hp1z : 2 * (2 : ℤ) ^ K + 1 ≤ p := by exact_mod_cast hp1
  have hp2z : (p : ℤ) < 2 * 2 ^ K + (h + 5) := by exact_mod_cast hp2
  have hh4z : (h : ℤ) + 4 ≤ 2 ^ K := by exact_mod_cast hh4
  -- Gid ≤ p^m
  have hG := genr_Gid_le (k := n + 1) (l := K + r - n) (H := K + 1) (p := (p : ℤ))
    (by rw [hX]; linarith) (by rw [hX]; linarith)
  rw [← hGid] at hG
  -- p^{n+1} − f^{n+1} ≤ (n+1)(p − f)p^n
  have hmv := gm_pow_sub_le hf0 (by linarith : (f : ℤ) ≤ p) n
  have hmv2 := mul_le_mul_of_nonneg_left hmv hpz
  have e1 : (p : ℤ) * (((n : ℤ) + 1) * (p - f) * (p : ℤ) ^ n) =
      ((n : ℤ) + 1) * ((h : ℤ) + 5) * (p : ℤ) ^ (n + 1) := by
    rw [show (p : ℤ) - f = (h : ℤ) + 5 by linarith]; ring
  have e2 : (p : ℤ) ^ (n + 1 + 1) = p * (p : ℤ) ^ (n + 1) := by ring
  -- 段の内部
  have hf2 : 2 ≤ f := by omega
  have hS := gmSg_le_two hf2 (n + 1)
  have hfX : (f : ℤ) ≤ 2 ^ (K + 1 + 1) := by rw [hX2]; linarith
  have hfn : (f : ℤ) ^ (n + 1) ≤ ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := pow_le_pow_left₀ hf0 hfX _
  have s1 : gmSg f (n + 1) ≤ 2 * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by linarith
  have s2 := mul_le_mul_of_nonneg_left s1 (show (0 : ℤ) ≤ 2 * ((K : ℤ) + 1) by positivity)
  have hY0 : (0 : ℤ) ≤ 2 * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by positivity
  have s3 : 2 * ((K : ℤ) + 1) * (2 * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1)) ≤
      2 * ((K : ℤ) + 2) * (2 * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith) hY0
  linarith [hT, hG, hmv2, e1, e2, s2, s3]

/-! ## 定理 B_{m,r} -/

theorem genr_upper_int {n r K p : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n + 1)
    (hH1 : n + r + 3 ≤ K + 1) (hH2 : 2 * ((n + 2) * (K + 1) + r + 4) ≤ 2 ^ (K + 1))
    (hp1 : 2 ^ (K + 1) + 1 ≤ p) (hp2 : p ≤ 2 ^ (K + 1 + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * (K + 1) + r) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 3) * 2 ^ ((n + 2) * (K + 1) + r) - 2 * genrGid n r (K + 1) p +
        2 * ((n : ℤ) + 1) * ((((n + 2) * (K + 1) + r : ℕ) : ℤ) + 5) * (p : ℤ) ^ (n + 1) +
        4 * ((K : ℤ) + 2) * ((2 : ℤ) ^ (K + 1 + 1)) ^ (n + 1) := by
  rcases le_or_gt (2 ^ (K + 1) + ((n + 2) * (K + 1) + r + 5)) p with hA | hG
  · exact genr_caseA hr1 hrn hH1 hH2 hA hp2
  · exact genr_caseG hr1 hrn hH1 hH2 hp1 hG

/-- **定理 B_{m,r}.** `m ≥ 2`，`1 ≤ r < m`，`H ≥ m + r + 1`，`2(mH + r + 4) ≤ 2^H`（紙の `H ≥ H0(m,r)`），
`X = 2^H`，`X + 1 ≤ p ≤ 2X` なら，ペブル `p` 個の妥当な手順（構成 B★）で
`T ≤ (2(m+1) − 2σ_{m,r}(p/X))·2^{mH+r} + m·2^m·(mH + r + 5)·X^{m−1}` のものがある。 -/
theorem genr_upper_bound {m r H p : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m)
    (hH1 : m + r + 1 ≤ H) (hH2 : 2 * (m * H + r + 4) ≤ 2 ^ H)
    (hp1 : 2 ^ H + 1 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (m * H + r) p T ms ∧
      (T : ℝ) ≤ (2 * ((m : ℝ) + 1) - 2 * genrSigma m r ((p : ℝ) / 2 ^ H)) * 2 ^ (m * H + r) +
        m * 2 ^ m * (((m * H + r : ℕ) : ℝ) + 5) * ((2 : ℝ) ^ H) ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  obtain ⟨T, ms, hV, hT⟩ := genr_upper_int (n := n) (r := r) (K := K) (p := p) hr1 (by omega)
    (by omega) hH2 hp1 hp2
  refine ⟨T, ms, hV, ?_⟩
  have hI := genr_lemmaI (k := n + 1) (l := K + 1 + r - (n + 1)) (H := K + 1) (r := r)
    (by omega) (p : ℤ)
  have hGid : (genrGid n r (K + 1) p : ℝ) =
      2 ^ ((n + 2) * (K + 1) + r) * genrSigma (n + 2) r ((p : ℝ) / 2 ^ (K + 1)) := by
    unfold genrGid
    rw [hI, show n + 1 + 1 = n + 2 from rfl, Int.cast_natCast]
  have hTr := (Int.cast_le (R := ℝ)).mpr hT
  push_cast at hTr
  rw [hGid] at hTr
  rw [show n + 2 - 1 = n + 1 by omega]
  push_cast
  -- 誤差項
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ (K + 1) := ⟨_, rfl⟩
  have hX0 : (0 : ℝ) < X := by rw [hXd]; positivity
  have h22 : (2 : ℝ) ^ (K + 1 + 1) = 2 * X := by rw [hXd, pow_succ]; ring
  rw [h22] at hTr
  rw [← hXd] at hTr ⊢
  have hpX : (p : ℝ) ≤ 2 * X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp2
    push_cast at this
    rw [h22] at this
    exact this
  have hpow1 : (p : ℝ) ^ (n + 1) ≤ (2 * X) ^ (n + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hpX _
  have hhK : 2 * K + 4 ≤ (n + 2) * (K + 1) + r + 5 := by nlinarith
  have hhKr : (2 : ℝ) * K + 4 ≤ ((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5 := by
    have := (Nat.cast_le (α := ℝ)).mpr hhK
    push_cast at this
    linarith
  have hZ0 : (0 : ℝ) ≤ (2 * X) ^ (n + 1) := by positivity
  have hhp : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hpow1
    (show (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) * (((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5) by positivity)
  have a2 : 4 * ((K : ℝ) + 2) * (2 * X) ^ (n + 1) ≤
      2 * (((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5) * (2 * X) ^ (n + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ0
  have e : ((n : ℝ) + 2) * 2 ^ (n + 2) * (((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5) * X ^ (n + 1) =
      2 * ((n : ℝ) + 1) * (((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5) * (2 * X) ^ (n + 1) +
        2 * (((n : ℝ) + 2) * ((K : ℝ) + 1) + r + 5) * (2 * X) ^ (n + 1) := by
    rw [mul_pow]; ring
  nlinarith [hTr, a1, a2, e]

theorem Ttree_genr_upper {m r H p : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m)
    (hH1 : m + r + 1 ≤ H) (hH2 : 2 * (m * H + r + 4) ≤ 2 ^ H)
    (hp1 : 2 ^ H + 1 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    (Ttree (m * H + r) p : ℝ) ≤
      (2 * ((m : ℝ) + 1) - 2 * genrSigma m r ((p : ℝ) / 2 ^ H)) * 2 ^ (m * H + r) +
        m * 2 ^ m * (((m * H + r : ℕ) : ℝ) + 5) * ((2 : ℝ) ^ H) ^ (m - 1) := by
  obtain ⟨T, ms, hV, hT⟩ := genr_upper_bound hm hr1 hr hH1 hH2 hp1 hp2
  have := Ttree_le_of_valid hV
  have : (Ttree (m * H + r) p : ℝ) ≤ T := by exact_mod_cast this
  linarith

theorem TtreeK_genr_upper {m r H p : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m)
    (hH1 : m + r + 1 ≤ H) (hH2 : 2 * (m * H + r + 4) ≤ 2 ^ H)
    (hp1 : 2 ^ H + 1 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    (TtreeK (m * H + r) p : ℝ) ≤
      (2 * ((m : ℝ) + 1) - 2 * genrSigma m r ((p : ℝ) / 2 ^ H)) * 2 ^ (m * H + r) +
        m * 2 ^ m * (((m * H + r : ℕ) : ℝ) + 5) * ((2 : ℝ) ^ H) ^ (m - 1) := by
  rw [← Ttree_eq_TtreeK]; exact Ttree_genr_upper hm hr1 hr hH1 hH2 hp1 hp2

end GenRUpper
end SpookyTree
