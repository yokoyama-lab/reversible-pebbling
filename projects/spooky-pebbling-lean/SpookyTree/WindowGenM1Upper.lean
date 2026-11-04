/-
# 窓の上界・一般の m・h ≡ 1 (mod m)（紙の定理 B_{m,1}）: 構成と手数の一般形

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 2 節（構成 B★．手順は WINDOW_UB 2.3 節）。
`WindowM3Upper.lean`（m = 3）・`WindowM4Upper.lean`（m = 4）の段の数を一般にしたもの:
* 段 1（keep）: `stratG`。
* 段 2..n+1（G 段，`n = m − 2` 個）: `gmFin … (k+1) = g2Stg … (gmFin … k)` の反復。
* 最終段: `gmFin … 0 = finW`（F または M）。最終段の部分木の高さは `l, …, l + n + 1`（`h = l + (n+1)(e+1)`）。

手数は `gmPsi`（`m3Psi` を k 段重ねたもの）で抑え，閉じた形 `gm_total` にする:
最終段の上界を `φ_i = 2·2^{l+i} + E_i` と書くと
  `T ≤ 2(n+2)·2^h − 2f + 2(e+1)·Σ_{r=1}^{n+1} f^r + (L^{n+1}E)(0)`，
`(Lφ)(i) = αφ(i) + βφ(i+1)`，`α = 2f − 2^{e+1}`，`β = 2^{e+1} − f`（`gmLit`）。
紙との違いは `WindowM3Upper.lean` と同じ（前線の割り方，G 段の手 2，手数は上界）。
-/
import SpookyTree.WindowM3Upper

namespace SpookyTree

/-! ## 段の反復 -/

/-- 最終段から数えて `k` 段目の手続き（`k = 0` は最終段 `finW`）。 -/
def gmFin (h p f g : ℕ) : ℕ → Node → List Move
  | 0 => finW h p g
  | k + 1 => fun z => g2Stg h f (gmFin h p f g k) (h - z.length) z

theorem gmFin_succ (h p f g k : ℕ) (z : Node) :
    gmFin h p f g (k + 1) z = g2Stg h f (gmFin h p f g k) (h - z.length) z := rfl

/-- **段の反復の合法性.** 最終段が高さ `[l, U]` で合法なら，`k` 段目は高さ `[l + k(e+1), U + ke]` で合法。 -/
theorem gmFin_spec {h p f g e l U : ℕ} (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1))
    (hPf : f + h + 3 ≤ p) (hl : 1 ≤ l)
    (hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l ≤ j → j ≤ U →
      Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z))) :
    ∀ (k : ℕ) (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l + k * (e + 1) ≤ j →
      j ≤ U + k * e → Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (gmFin h p f g k z) ∧
        Pat (cst .empty) j z (run c' (gmFin h p f g k z)) := by
  intro k
  induction k with
  | zero =>
    intro z j c' hz h1 h2 hP
    simp only [Nat.zero_mul, Nat.add_zero] at h1 h2
    exact hFin z j c' hz h1 h2 hP
  | succ k ih =>
    intro z j c' hz h1 h2 hP
    rw [Nat.succ_mul] at h1 h2
    rw [gmFin_succ]
    have hj : h - z.length = j := by omega
    rw [hj]
    refine g2Stg_spec (h := h) (p := p) (lo := j) (hi := j) hf2 he1 he2 hPf (by omega) (by omega)
      ?_ j z c' le_rfl le_rfl hz hP
    intro z' j' c'' hz' hj1 hj2 hP'
    exact ih z' j' c'' hz' (by omega) (by omega) hP'

/-! ## 手数 -/

/-- `k` 段目の部分木（高さ `l + k(e+1) + i`）の手数の上界。 -/
def gmPsi (f e l : ℕ) (φ : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, i => φ i
  | k + 1, i => m3Psi f e (l + k * (e + 1) + i + (e + 1)) (gmPsi f e l φ k i)
      (gmPsi f e l φ k (i + 1))

theorem length_gmFin {h p f g e l N : ℕ} (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1))
    (hl : 1 ≤ l) {φ : ℕ → ℤ}
    (hφ : ∀ i, i ≤ N → ∀ z : Node, z.length + (l + i) = h → ((finW h p g z).length : ℤ) ≤ φ i) :
    ∀ (k i : ℕ), i + k ≤ N → ∀ z : Node, z.length + (l + k * (e + 1) + i) = h →
      ((gmFin h p f g k z).length : ℤ) ≤ gmPsi f e l φ k i := by
  intro k
  induction k with
  | zero =>
    intro i hi z hz
    simp only [Nat.zero_mul, Nat.add_zero] at hz
    exact hφ i (by omega) z hz
  | succ k ih =>
    intro i hi z hz
    rw [gmFin_succ]
    have hj : h - z.length = l + k * (e + 1) + i + (e + 1) := by rw [Nat.succ_mul] at hz; omega
    rw [hj]
    show _ ≤ m3Psi f e (l + k * (e + 1) + i + (e + 1)) (gmPsi f e l φ k i) (gmPsi f e l φ k (i + 1))
    refine length_g2Stg (h := h) (l := l + k * (e + 1) + i) hf2 he1 he2 (by omega)
      (by rw [Nat.succ_mul] at hz; omega) ?_ ?_
    · intro z' hz'
      exact ih i (by omega) z' hz'
    · intro z' hz'
      exact ih (i + 1) (by omega) z' (by omega)

/-! ## 全体の構成と手数の一般形 -/

/-- 構成 B★（G 段 `n` 個，`m = n + 2`）。 -/
def gmStrat (h p f g n : ℕ) : List Move := stratG h f (gmFin h p f g n)

/-- **構成 B★ の合法性と手数の一般形.** `h = l + n(e+1) + (e+1)`，`f + h + 5 = p`，`2^e ≤ f < 2^{e+1}`。
最終段が高さ `[l, l + n + 1]` で合法で，高さ `l + i` の手数が `φ i` 以下なら
`T ≤ m3Phi f e h (gmPsi … n 0) (gmPsi … n 1)`。 -/
theorem gm_assemble {n h p f g e l : ℕ} (hh : h = l + n * (e + 1) + (e + 1)) (hf : f + h + 5 = p)
    (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hl : 1 ≤ l)
    (hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l ≤ j → j ≤ l + n + 1 →
      Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)))
    {φ : ℕ → ℤ}
    (hφ : ∀ i, i ≤ n + 1 → ∀ z : Node, z.length + (l + i) = h → ((finW h p g z).length : ℤ) ≤ φ i) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      (T : ℤ) ≤ m3Phi f e h (gmPsi f e l φ n 0) (gmPsi f e l φ n 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hS : Shp (l + n * (e + 1)) (l + n * (e + 1) + 1) (k + 1) f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  have hFin2 : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 → l + n * (e + 1) ≤ j →
      j ≤ l + n * (e + 1) + 1 → Pat (cst .ghost) j a c' →
      Runs (k + 1) j a (p - 1) c' (gmFin (k + 1) p f g n a) ∧
        Pat (cst .empty) j a (run c' (gmFin (k + 1) p f g n a)) := by
    intro a j c' ha hj1 hj2 hPa
    have hne : n * e + n = n * (e + 1) := by ring
    exact gmFin_spec (U := l + n + 1) hf2 he1 he2 (by omega) hl hFin n a j c' ha hj1 (by omega) hPa
  obtain ⟨hR, hroot, hothers⟩ := stratG_spec (k := k) (f := f) (p := p) (lo := l + n * (e + 1))
    (hi := l + n * (e + 1) + 1) (Fin := gmFin (k + 1) p f g n) (by omega) hS hf2
    hFin2 (by omega) (by omega) (by omega)
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  have hlen := length_stratG_le (Fin := gmFin (k + 1) p f g n) (by omega) hS hf2
  have hroot' := length_rootP_depth k f [] (e + 1) hf2 (le_of_lt he2)
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hA : ∀ a : Node, a.length + (l + n * (e + 1)) = k + 1 →
      ((gmFin (k + 1) p f g n a).length : ℤ) ≤ gmPsi f e l φ n 0 := by
    intro a ha
    exact length_gmFin (N := n + 1) hf2 he1 he2 hl hφ n 0 (by omega) a (by omega)
  have hB : ∀ a : Node, a.length + (l + n * (e + 1) + 1) = k + 1 →
      ((gmFin (k + 1) p f g n a).length : ℤ) ≤ gmPsi f e l φ n 1 := by
    intro a ha
    exact length_gmFin (N := n + 1) hf2 he1 he2 hl hφ n 1 (by omega) a (by omega)
  have hkD : k = l + n * (e + 1) + e := by omega
  rw [hkD] at hSL hSR
  have hL := length_onSp_two' (h := k + 1) (D := e) (y := [false]) (by omega) hA hB hSL
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hR' := length_onSp_two' (h := k + 1) (D := e) (y := [true]) (by omega) hA hB hSR
    (by simp only [List.length_cons, List.length_nil]; omega)
  rw [← hkD] at hL hR'
  have hsz : ((f : ℕ) : ℤ) = (((f + 1) / 2 : ℕ) : ℤ) + ((f / 2 : ℕ) : ℤ) := by
    exact_mod_cast hs.symm
  generalize (stratG (k + 1) f (gmFin (k + 1) p f g n)).length = T at hlen ⊢
  have hlen' : (T : ℤ) + 2 * f ≤ 2 * 2 ^ (k + 1) + ((rootP k f []).length : ℤ) +
      ((onSp (gmFin (k + 1) p f g n) k ((f + 1) / 2) [false]).length : ℤ) +
      ((onSp (gmFin (k + 1) p f g n) k (f / 2) [true]).length : ℤ) := by exact_mod_cast hlen
  have hroot'' : ((rootP k f []).length : ℤ) ≤ 2 * f * (e + 1) := by exact_mod_cast hroot'
  unfold m3Phi
  generalize gmPsi f e l φ n 0 = A at hL hR' ⊢
  generalize gmPsi f e l φ n 1 = B at hL hR' ⊢
  rw [show (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e by ring]
  rw [hsz] at hlen' hroot'' ⊢
  linarith

/-! ## 閉じた形 -/

/-- 作用素 `(Lφ)(i) = αφ(i) + βφ(i+1)` の `k` 回の反復。 -/
def gmLit (α β : ℤ) : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, E, i => E i
  | k + 1, E, i => α * gmLit α β k E i + β * gmLit α β k E (i + 1)

/-- `Σ_{r=1}^{k} f^r`。 -/
def gmSg (f : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => f + f * gmSg f k

theorem gmPsi_eq {f e l : ℕ} {E : ℕ → ℤ} : ∀ k i : ℕ,
    gmPsi f e l (fun i => 2 * 2 ^ (l + i) + E i) k i =
      2 * ((k : ℤ) + 1) * 2 ^ (l + k * (e + 1) + i) + 2 * ((e : ℤ) + 1) * gmSg f k +
        gmLit (2 * f - 2 ^ (e + 1)) (2 ^ (e + 1) - f) k E i := by
  intro k
  induction k with
  | zero => intro i; simp [gmPsi, gmLit, gmSg]
  | succ k ih =>
    intro i
    show m3Psi f e (l + k * (e + 1) + i + (e + 1)) _ _ = _
    rw [ih i, ih (i + 1)]
    have e1 : (2 : ℤ) ^ (l + (k + 1) * (e + 1) + i) = 2 ^ (l + k * (e + 1) + i) * 2 ^ (e + 1) := by
      rw [← pow_add]; congr 1; ring
    have e2 : (2 : ℤ) ^ (l + k * (e + 1) + (i + 1)) = 2 ^ (l + k * (e + 1) + i) * 2 := by
      rw [show l + k * (e + 1) + (i + 1) = (l + k * (e + 1) + i) + 1 by omega, pow_succ]
    have e3 : (2 : ℤ) ^ (l + k * (e + 1) + i + (e + 1)) =
        2 ^ (l + k * (e + 1) + i) * 2 ^ (e + 1) := pow_add _ _ _
    simp only [m3Psi, gmLit, gmSg]
    rw [e1, e2, e3]
    push_cast
    ring

/-- **全体の閉じた形.** -/
theorem gm_total {n f e l h : ℕ} (hh : h = l + n * (e + 1) + (e + 1)) {E : ℕ → ℤ} :
    m3Phi f e h (gmPsi f e l (fun i => 2 * 2 ^ (l + i) + E i) n 0)
        (gmPsi f e l (fun i => 2 * 2 ^ (l + i) + E i) n 1) =
      2 * ((n : ℤ) + 2) * 2 ^ h - 2 * f + 2 * ((e : ℤ) + 1) * gmSg f (n + 1) +
        gmLit (2 * f - 2 ^ (e + 1)) (2 ^ (e + 1) - f) (n + 1) E 0 := by
  rw [gmPsi_eq, gmPsi_eq]
  have e1 : (2 : ℤ) ^ h = 2 ^ (l + n * (e + 1) + 0) * 2 ^ (e + 1) := by
    rw [hh, ← pow_add]; simp
  have e2 : (2 : ℤ) ^ (l + n * (e + 1) + 1) = 2 ^ (l + n * (e + 1) + 0) * 2 := by
    simp [pow_succ]
  simp only [m3Phi, gmLit, gmSg]
  rw [e1, e2]
  push_cast
  ring

/-! ## 反復の性質 -/

theorem gmLit_mono {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {E E' : ℕ → ℤ} (hE : ∀ i, E i ≤ E' i) :
    ∀ k i, gmLit α β k E i ≤ gmLit α β k E' i := by
  intro k
  induction k with
  | zero => intro i; exact hE i
  | succ k ih =>
    intro i
    simp only [gmLit]
    have := mul_le_mul_of_nonneg_left (ih i) hα
    have := mul_le_mul_of_nonneg_left (ih (i + 1)) hβ
    linarith

/-- 等比の列と定数: `α + β = f`，`α + 2β = Q` なら `L^k(A·2^{b+i} + C) = A·Q^k·2^{b+i} + C·f^k`。 -/
theorem gmLit_geom {α β Q F A C : ℤ} {b : ℕ} (hf : α + β = F) (hq : α + 2 * β = Q) :
    ∀ k i, gmLit α β k (fun i => A * 2 ^ (b + i) + C) i = A * Q ^ k * 2 ^ (b + i) + C * F ^ k := by
  intro k
  induction k with
  | zero => intro i; simp [gmLit]
  | succ k ih =>
    intro i
    simp only [gmLit]
    rw [ih i, ih (i + 1)]
    have e2 : (2 : ℤ) ^ (b + (i + 1)) = 2 ^ (b + i) * 2 := by
      rw [show b + (i + 1) = (b + i) + 1 by omega, pow_succ]
    rw [e2, ← hf, ← hq]
    ring

/-- 1 点だけの列: `L^k 1_N (i) = β^k c`（`i + k = N`）。 -/
theorem gmLit_ind {α β c : ℤ} {N : ℕ} :
    ∀ k i, i + k ≤ N →
      gmLit α β k (fun j => if j = N then c else 0) i = if i + k = N then β ^ k * c else 0 := by
  intro k
  induction k with
  | zero => intro i _; simp [gmLit]
  | succ k ih =>
    intro i hi
    simp only [gmLit]
    rw [ih i (by omega), ih (i + 1) (by omega), if_neg (by omega)]
    by_cases hN : i + (k + 1) = N
    · rw [if_pos (by omega), if_pos hN]; ring
    · rw [if_neg (by omega), if_neg hN]; ring

/-- `Σ_{r=1}^{k} f^r ≤ k·f^k`（`f ≥ 1`）。 -/
theorem gmSg_le {f : ℕ} (hf : 1 ≤ f) : ∀ k, gmSg f k ≤ (k : ℤ) * (f : ℤ) ^ k := by
  have hf' : (1 : ℤ) ≤ f := by exact_mod_cast hf
  intro k
  induction k with
  | zero => simp [gmSg]
  | succ k ih =>
    simp only [gmSg]
    have h1 : (1 : ℤ) ≤ (f : ℤ) ^ k := one_le_pow₀ hf'
    have := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℤ) ≤ f)
    push_cast
    rw [pow_succ]
    nlinarith

theorem gmSg_nonneg (f : ℕ) : ∀ k, 0 ≤ gmSg f k := by
  intro k
  induction k with
  | zero => simp [gmSg]
  | succ k ih => simp only [gmSg]; positivity

/-- 平均値の不等式: `0 ≤ a ≤ b` なら `b^k − a^k ≤ k(b − a)b^{k−1}`（`k = n + 1`）。 -/
theorem gm_pow_sub_le {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : ℕ, b ^ (n + 1) - a ^ (n + 1) ≤ ((n : ℤ) + 1) * (b - a) * b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 0 ≤ b := ha.trans hab
    have han : a ^ (n + 1) ≤ b ^ (n + 1) := pow_le_pow_left₀ ha hab _
    have h1 := mul_le_mul_of_nonneg_left ih hb
    have h2 : a ^ (n + 1) * (b - a) ≤ b ^ (n + 1) * (b - a) :=
      mul_le_mul_of_nonneg_right han (by linarith)
    have e : b ^ (n + 1 + 1) - a ^ (n + 1 + 1) = b * (b ^ (n + 1) - a ^ (n + 1)) + a ^ (n + 1) * (b - a) := by
      ring
    rw [e]
    push_cast
    have e2 : b * (((n : ℤ) + 1) * (b - a) * b ^ n) = ((n : ℤ) + 1) * (b - a) * b ^ (n + 1) := by ring
    nlinarith

end SpookyTree
