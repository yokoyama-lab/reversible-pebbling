/-
# 窓の一般の m・剰余 r：帯の中の極限を仮定したときの収束の判定

`WindowGenRCriterion.lean`（極限の式の代数）と `WindowM34Outside.lean`（一般の m の帯の外の収束と，
剰余ごとの非収束の一般形）をつなぐ．

* **`Ttree_window_genr_tendsto_iff_of_mid`**: 仮定 `GenrMid m`（すべての `r ∈ [1, m−1]`，`γ ∈ [1,2]` で
  `T(T_{mH+r}, p(H))/2^{mH+r} → 2(m+1) − 2σ_{m,r}(γ)`．紙の定理 genr の帯の中の部分で，m ≥ 5・r ≥ 2 は紙のまま）
  の下で，`c > 0` なら `T(T_h, ⌊c·2^{h/m}⌋₊)/2^h` が収束 ⇔ `c ≤ 2^{−(m−1)/m}` または `c ≥ 2^{(m−1)/m}`．
  γ ≤ 1 と γ ≥ 2 の極限は仮定しない（`Ttree_genmr_tendsto_low`・`_high` で Lean 済み）．
* `genrLim_one_eq`: `r = 1` では `genrLim m 1 c = genm1Lim m (c·2^{1/m})`（Lean 済みの h ≡ 1 の極限と同じ式）．
* `genrMid_one`: `r = 1` の帯の中の極限（m ≥ 3）は `GenrMid` の形で Lean 済み．
-/
import SpookyTree.WindowGenRCriterion
import SpookyTree.WindowM34Outside

open Filter Topology

namespace SpookyTree

/-- 仮定: 剰余 `r = 1, …, m − 1` の帯の中の極限が `2(m+1) − 2σ_{m,r}(γ)`． -/
def GenrMid (m : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r < m → ∀ (p : ℕ → ℕ) (γ : ℝ), 1 ≤ γ → γ ≤ 2 →
    Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ) →
    Tendsto (fun H : ℕ => (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ))

/-- **収束の判定（帯の中の極限を仮定）.** -/
theorem Ttree_window_genr_tendsto_iff_of_mid {m : ℕ} (hm : 2 ≤ m) (hmid : GenrMid m)
    {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) ∨ (2 : ℝ) ^ (((m : ℝ) - 1) / m) ≤ c) := by
  constructor
  · intro hL
    by_contra hb
    push Not at hb
    obtain ⟨r, hr1, hr, h1, h2⟩ := genr_band hm hc0 hb.1 hb.2
    exact genm_not_tendsto_r hm (fun γ => 2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ)
      (fun p γ g1 g2 hp => hmid r hr1 hr p γ g1 g2 hp)
      (fun γ g1 g2 => genr_gap hr1 hr g1 g2) h1 h2 hL
  · intro hc
    refine ⟨_, Ttree_window_genm_tendsto_outside hm ?_ hc0 hc⟩
    intro r hr1 hr q hq
    have := hmid r hr1 hr q 2 (by norm_num) le_rfl hq
    rwa [genrLim_seam_two (by omega) hr] at this

/-- `r = 1` では `L_1(c)` は h ≡ 1 の極限の式 `genm1Lim` と一致する． -/
theorem genrLim_one_eq {m : ℕ} (hm : 1 ≤ m) (c : ℝ) :
    genrLim m 1 c = genm1Lim m (c * (2 : ℝ) ^ ((1 : ℝ) / m)) := by
  unfold genrLim genm1Lim
  simp only [Nat.cast_one]
  split_ifs with h1 h2
  · rw [rpow_one_div_pow hm]
  · rw [genrSigma_r1 hm (not_le.mp h1).le h2]
    ring
  · rfl

/-- `r = 1`（m ≥ 3）の帯の中の極限は Lean 済み（`Ttree_genm1_tendsto`）．`GenrMid` の `r = 1` の部分． -/
theorem genrMid_one {m : ℕ} (hm : 3 ≤ m) (p : ℕ → ℕ) (γ : ℝ) (h1 : 1 ≤ γ) (h2 : γ ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - 2 * genrSigma m 1 γ)) := by
  have e : 2 * ((m : ℝ) + 1) - 2 * genrSigma m 1 γ = 2 * m + (2 - γ) ^ m := by
    rw [genrSigma_r1 (by omega) h1 h2]
    ring
  rw [e]
  exact Ttree_genm1_tendsto hm h1 h2 hp

end SpookyTree
