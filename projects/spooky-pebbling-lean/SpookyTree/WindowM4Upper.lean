/-
# 窓の上界・m = 4・h ≡ 1 (mod 4)（紙の定理 B4，r = 1）: 構成と手数の一般形

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4_2026-11.md` の 3 節（構成 B★ の m = 4．手順は WINDOW_UB 2.3 節）。
`WindowM3Upper.lean` の 3 段を 4 段にしたもの:
* 段 1（keep）: `stratG`。大きさ `f` の前線，深さ `e`。
* 段 2・段 3（G 段，keep なし）: `g2Stg` を 2 回重ねる（段 3 は最終段 `finW` を，段 2 は段 3 を引数に取る）。
* 最終段: `finW`（F または M）。最終段の部分木の高さは `l, l+1, l+2, l+3`（`h = l + 3e + 3`）。

手数は `m3Psi`（G 段 1 個の上界）を 2 段重ね，`m3Phi`（段 1）に入れたもの。段の内部の手数は
`2f(e+1)` で粗く抑える（`WindowM3Upper.lean` と同じ）。紙との違いも `WindowM3Upper.lean` と同じ
（前線は `⌈n/2⌉・⌊n/2⌋` に再帰的に割る，G 段の手 2 は `cB`・`clB`，手数は閉じた式でなく上界）。
-/
import SpookyTree.WindowM3Upper

namespace SpookyTree

/-- 構成 B★（m = 4）。 -/
def m4Strat (h p f g : ℕ) : List Move :=
  stratG h f (fun a => g2Stg h f (fun z => g2Stg h f (finW h p g) (h - z.length) z) (h - a.length) a)

/-- **構成 B★（m = 4）の合法性と手数の一般形.** `h = l + 3e + 3`（最終段の部分木の高さは `l, …, l+3`），
`f = p − h − 5`，`2^e ≤ f < 2^{e+1}`。最終段の 1 個あたりの手数が高さ `l + i` で `φᵢ` 以下なら
`T ≤ m3Phi f e h Ψ₂₀ Ψ₂₁`，`Ψ₂ᵢ = m3Psi … Ψ₃ᵢ Ψ₃ᵢ₊₁`，`Ψ₃ᵢ = m3Psi … φᵢ φᵢ₊₁`。 -/
theorem m4_assemble {h p f g e l : ℕ} (hh : h = l + 3 * e + 3) (hf : f + h + 5 = p)
    (hf2 : 2 ≤ f) (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1)) (hl : 1 ≤ l)
    (hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → l ≤ j → j ≤ l + 3 →
      Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)))
    {φ₀ φ₁ φ₂ φ₃ : ℤ}
    (h0 : ∀ z : Node, z.length + l = h → ((finW h p g z).length : ℤ) ≤ φ₀)
    (h1 : ∀ z : Node, z.length + (l + 1) = h → ((finW h p g z).length : ℤ) ≤ φ₁)
    (h2 : ∀ z : Node, z.length + (l + 2) = h → ((finW h p g z).length : ℤ) ≤ φ₂)
    (h3 : ∀ z : Node, z.length + (l + 3) = h → ((finW h p g z).length : ℤ) ≤ φ₃) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      (T : ℤ) ≤ m3Phi f e h
        (m3Psi f e (l + (e + 1) + (e + 1)) (m3Psi f e (l + (e + 1)) φ₀ φ₁)
          (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂))
        (m3Psi f e (l + 1 + (e + 1) + (e + 1)) (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂)
          (m3Psi f e (l + 2 + (e + 1)) φ₂ φ₃)) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hS : Shp (l + (e + 1) + (e + 1)) (l + (e + 1) + (e + 1) + 1) (k + 1) f :=
    ⟨e + 1, e, by omega, le_of_lt he2, by omega, he1, by omega⟩
  -- 段 3 の合法性
  have hFin3 : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = k + 1 → l + (e + 1) ≤ j →
      j ≤ l + (e + 1) + 2 → Pat (cst .ghost) j z c' →
      Runs (k + 1) j z (p - 1) c' (g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) ∧
        Pat (cst .empty) j z
          (run c' (g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)) := by
    intro z j c' hz hj1 hj2 hPz
    have hj : k + 1 - z.length = j := by omega
    rw [hj]
    refine g2Stg_spec (h := k + 1) (p := p) (lo := l + (e + 1)) (hi := l + (e + 1) + 2) hf2 he1 he2
      (by omega) (by omega) (by omega) ?_ j z c' hj1 hj2 hz hPz
    intro z' j' c'' hz' hj'1 hj'2 hPz'
    exact hFin z' j' c'' hz' (by omega) (by omega) hPz'
  -- 段 2 の合法性
  have hFin2 : ∀ (a : Node) (j : ℕ) (c' : Config), a.length + j = k + 1 →
      l + (e + 1) + (e + 1) ≤ j → j ≤ l + (e + 1) + (e + 1) + 1 → Pat (cst .ghost) j a c' →
      Runs (k + 1) j a (p - 1) c'
        (g2Stg (k + 1) f (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)
          (k + 1 - a.length) a) ∧
        Pat (cst .empty) j a (run c'
          (g2Stg (k + 1) f (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)
            (k + 1 - a.length) a)) := by
    intro a j c' ha hj1 hj2 hPa
    have hj : k + 1 - a.length = j := by omega
    rw [hj]
    refine g2Stg_spec (h := k + 1) (p := p) (lo := l + (e + 1) + (e + 1))
      (hi := l + (e + 1) + (e + 1) + 1) hf2 he1 he2 (by omega) (by omega) (by omega) ?_ j a c'
      hj1 hj2 ha hPa
    intro z j' c'' hz hj'1 hj'2 hPz
    exact hFin3 z j' c'' hz (by omega) (by omega) hPz
  obtain ⟨hR, hroot, hothers⟩ := stratG_spec (k := k) (f := f) (p := p)
    (lo := l + (e + 1) + (e + 1)) (hi := l + (e + 1) + (e + 1) + 1)
    (Fin := fun a => g2Stg (k + 1) f (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)
      (k + 1 - a.length) a) (by omega) hS hf2
    hFin2 (by omega) (by omega) (by omega)
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  -- 手数: 段 3 の部分木 1 個
  have L30 : ∀ z : Node, z.length + (l + (e + 1)) = k + 1 →
      (((fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) z).length : ℤ) ≤
        m3Psi f e (l + (e + 1)) φ₀ φ₁ := by
    intro z hz
    have hj : k + 1 - z.length = l + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) hf2 he1 he2 hl hz h0 h1
  have L31 : ∀ z : Node, z.length + (l + (e + 1) + 1) = k + 1 →
      (((fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) z).length : ℤ) ≤
        m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂ := by
    intro z hz
    have hj : k + 1 - z.length = l + 1 + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) (l := l + 1) hf2 he1 he2 (by omega) (by omega) h1
      (fun z hz => h2 z (by omega))
  have L32 : ∀ z : Node, z.length + (l + 1 + (e + 1) + 1) = k + 1 →
      (((fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) z).length : ℤ) ≤
        m3Psi f e (l + 2 + (e + 1)) φ₂ φ₃ := by
    intro z hz
    have hj : k + 1 - z.length = l + 2 + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) (l := l + 2) hf2 he1 he2 (by omega) (by omega)
      (fun z hz => h2 z (by omega)) (fun z hz => h3 z (by omega))
  -- 段 2 の部分木 1 個
  have hA : ∀ a : Node, a.length + (l + (e + 1) + (e + 1)) = k + 1 →
      (((fun a => g2Stg (k + 1) f (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)
        (k + 1 - a.length) a) a).length : ℤ) ≤
        m3Psi f e (l + (e + 1) + (e + 1)) (m3Psi f e (l + (e + 1)) φ₀ φ₁)
          (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂) := by
    intro a ha
    have hj : k + 1 - a.length = l + (e + 1) + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) (l := l + (e + 1)) hf2 he1 he2 (by omega) ha L30 L31
  have hB : ∀ a : Node, a.length + (l + (e + 1) + (e + 1) + 1) = k + 1 →
      (((fun a => g2Stg (k + 1) f (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z)
        (k + 1 - a.length) a) a).length : ℤ) ≤
        m3Psi f e (l + 1 + (e + 1) + (e + 1)) (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂)
          (m3Psi f e (l + 2 + (e + 1)) φ₂ φ₃) := by
    intro a ha
    have hj : k + 1 - a.length = l + 1 + (e + 1) + (e + 1) := by omega
    simp only [hj]
    exact length_g2Stg (h := k + 1) (l := l + 1 + (e + 1)) hf2 he1 he2 (by omega) (by omega)
      (fun z hz => L31 z (by omega)) (fun z hz => L32 z (by omega))
  -- 段 1
  have hlen := length_stratG_le (Fin := fun a => g2Stg (k + 1) f
    (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) (k + 1 - a.length) a)
    (by omega) hS hf2
  have hroot' := length_rootP_depth k f [] (e + 1) hf2 (le_of_lt he2)
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hkD : k = l + (e + 1) + (e + 1) + e := by omega
  rw [hkD] at hSL hSR
  have hL := length_onSp_two' (h := k + 1) (D := e) (y := [false]) (by omega) hA hB hSL
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hR' := length_onSp_two' (h := k + 1) (D := e) (y := [true]) (by omega) hA hB hSR
    (by simp only [List.length_cons, List.length_nil]; omega)
  rw [← hkD] at hL hR'
  have hsz : ((f : ℕ) : ℤ) = (((f + 1) / 2 : ℕ) : ℤ) + ((f / 2 : ℕ) : ℤ) := by
    exact_mod_cast hs.symm
  generalize (stratG (k + 1) f fun a => g2Stg (k + 1) f
    (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) (k + 1 - a.length) a).length
    = T at hlen ⊢
  have hlen' : (T : ℤ) + 2 * f ≤ 2 * 2 ^ (k + 1) + ((rootP k f []).length : ℤ) +
      ((onSp (fun a => g2Stg (k + 1) f
        (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) (k + 1 - a.length) a) k
        ((f + 1) / 2) [false]).length : ℤ) +
      ((onSp (fun a => g2Stg (k + 1) f
        (fun z => g2Stg (k + 1) f (finW (k + 1) p g) (k + 1 - z.length) z) (k + 1 - a.length) a) k
        (f / 2) [true]).length : ℤ) := by exact_mod_cast hlen
  have hroot'' : ((rootP k f []).length : ℤ) ≤ 2 * f * (e + 1) := by exact_mod_cast hroot'
  unfold m3Phi
  generalize m3Psi f e (l + (e + 1) + (e + 1)) (m3Psi f e (l + (e + 1)) φ₀ φ₁)
    (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂) = A at hL hR' ⊢
  generalize m3Psi f e (l + 1 + (e + 1) + (e + 1)) (m3Psi f e (l + 1 + (e + 1)) φ₁ φ₂)
    (m3Psi f e (l + 2 + (e + 1)) φ₂ φ₃) = B at hL hR' ⊢
  rw [show (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e by ring]
  rw [hsz] at hlen' hroot'' ⊢
  linarith

end SpookyTree
