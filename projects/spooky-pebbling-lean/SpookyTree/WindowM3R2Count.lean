/-
# 定理 L3 の組合せ部分（`h = 3H + 2`，紙の r = 2）: 段 2 の区域の頭打ちの和 `V*_2 ≤ W_3`

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 2 節（r = 2．補題 L2 と ν を入れた双対）。
`WindowM3LowerCount.lean`（r = 1）の組み立てを r = 2 に広げたもの。違いは 3 つ:
* 深さ: `D` = 深さ `2H + 2` の頂点（`S_x` は `s = 2^H − 1` 頂点），`R` = 深さ `H + 2` の頂点（`N_R = 4X`），
  `U` = 深さ `< 2H + 2` の頂点（`4X² − 1` 個）。
* 区域ごとの上界: r = 1 の 2 本（`s·n`，`μ₁q + μ₂n`）に，頭打ち `q·q`（紙の φ の `k ≥ 2q` の枝）を足した 3 本。
  `sβ + Σ_u min(k_u s, q) ≤ q(β + #{u : k_u ≥ 1}) ≤ q²`。
* **補題 L2（偶奇）** `openBelow_even`・`m3r2_parity`: `#{y ∈ P : j_y が奇数} ≤ ρ`（`ρ` = `P` の点を持つ `R_w` の数）。
  `y` の下の深さ `H + 2` の頂点 `w` のうち，`y` と `w` の間（両端を除く）に `P` の点が無いもの（`openBelow`）の数は偶数
  （子ごとに 1 + 1，0，または再帰で偶数）。そのうち `P` の点を持たないものがちょうど `J_y`（`j_y` 個），
  持つものは `y` ごとに別の `R_w`（`y` から下って最初の `P` の点が `y`）。

**主張（`m3r2_zone_sum_le`）.** `μ₁ + μ₂ = s`，`q = μ₁ + 2μ₂`，`Xs + ν ≤ μC + μS`，`μ₁q + 2μ₂X ≤ μC + 2μS`，
`μ₁q + 3μ₂X ≤ μC + 3μS + ν`，`q² ≤ μC + 4μS`，`|K_y| ≤ q` なら
  `Σ_y Σ_{u∈K_y} min(|Z'_{y,u}|, q) ≤ (2^{2H+2} − 1) + (s + μC)|P| + μS·2^{H+2}`。
紙の双対（`μ_C = 2f₂ − f₄`，`μ_S = (f₄ − f₂)/2`，`ν`）は j = 1, 2, 3, 4 の制約をこの形で満たす（`WindowM3R2Lower.lean`）。
-/
import SpookyTree.WindowM3LowerCount

namespace SpookyTree

/-! ## 補題 L2（偶奇） -/

open Classical in
/-- `v` の真の子孫で長さ `L` の頂点 `w` のうち，`v` と `w` の間（両端を除く）に `Bl` の点が無いもの。 -/
noncomputable def openBelow (L : ℕ) (Bl : Node → Prop) (v : Node) : Finset Node :=
  (words L).filter (fun w => v <+: w ∧ w ≠ v ∧ ∀ u, v <+: u → u <+: w → u ≠ v → u ≠ w → ¬ Bl u)

open Classical in
theorem mem_openBelow {L : ℕ} {Bl : Node → Prop} {v w : Node} :
    w ∈ openBelow L Bl v ↔ w.length = L ∧ v <+: w ∧ w ≠ v ∧
      ∀ u, v <+: u → u <+: w → u ≠ v → u ≠ w → ¬ Bl u := by
  unfold openBelow; rw [Finset.mem_filter, mem_words]

/-- 真の接頭辞は真に短い。 -/
theorem prefix_ne_length_lt {v u : Node} (h : v <+: u) (hne : u ≠ v) : v.length < u.length :=
  lt_of_le_of_ne h.length_le (fun he => hne (h.eq_of_length he).symm)

/-- 子 `v ++ [b]` の下の部分（長さ `L` が子の長さに等しいとき）は `{v ++ [b]}`。 -/
theorem openBelow_filter_leaf {L : ℕ} {Bl : Node → Prop} {v : Node} (b : Bool)
    (hL : v.length + 1 = L) :
    (openBelow L Bl v).filter (fun w => v ++ [b] <+: w) = {v ++ [b]} := by
  ext w
  rw [Finset.mem_filter, mem_openBelow, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hwl, -, -, -⟩, hcw⟩
    exact (hcw.eq_of_length (by simp; omega)).symm
  · rintro rfl
    refine ⟨⟨by simp; omega, List.prefix_append _ _, by simp, ?_⟩, List.prefix_refl _⟩
    intro u hvu huw hne1 hne2
    exfalso
    have h1 := prefix_ne_length_lt hvu hne1
    have h2 : u.length < (v ++ [b]).length :=
      lt_of_le_of_ne huw.length_le (fun he => hne2 (huw.eq_of_length he))
    simp at h2
    omega

/-- 子 `c = v ++ [b]` が `Bl` の点で，`c` より下に長さ `L` の頂点があるなら，`c` の下の部分は空。 -/
theorem openBelow_filter_blocked {L : ℕ} {Bl : Node → Prop} {v : Node} (b : Bool)
    (hL : v.length + 1 < L) (hb : Bl (v ++ [b])) :
    (openBelow L Bl v).filter (fun w => v ++ [b] <+: w) = ∅ := by
  ext w
  rw [Finset.mem_filter, mem_openBelow]
  simp only [Finset.notMem_empty, iff_false, not_and]
  rintro ⟨hwl, hvw, -, hcond⟩ hcw
  refine hcond (v ++ [b]) (List.prefix_append _ _) hcw (by simp) ?_ hb
  intro he
  rw [← he] at hwl
  simp at hwl
  omega

/-- 子 `c = v ++ [b]` が `Bl` の点でないなら，`c` の下の部分は `openBelow L Bl c`。 -/
theorem openBelow_filter_open {L : ℕ} {Bl : Node → Prop} {v : Node} (b : Bool)
    (hL : v.length + 1 < L) (hb : ¬ Bl (v ++ [b])) :
    (openBelow L Bl v).filter (fun w => v ++ [b] <+: w) = openBelow L Bl (v ++ [b]) := by
  ext w
  rw [Finset.mem_filter, mem_openBelow, mem_openBelow]
  constructor
  · rintro ⟨⟨hwl, hvw, hwv, hcond⟩, hcw⟩
    refine ⟨hwl, hcw, ?_, ?_⟩
    · intro he; rw [he] at hwl; simp at hwl; omega
    · intro u hcu huw hne1 hne2
      have hvu : v <+: u := (List.prefix_append _ _).trans hcu
      have : v.length < u.length := by
        have := hcu.length_le; simp at this; omega
      exact hcond u hvu huw (fun he => by rw [he] at this; omega) hne2
  · rintro ⟨hwl, hcw, hwc, hcond⟩
    have hvw : v <+: w := (List.prefix_append _ _).trans hcw
    refine ⟨⟨hwl, hvw, ?_, ?_⟩, hcw⟩
    · intro he; rw [he] at hwl; omega
    · intro u hvu huw hne1 hne2
      have hlt := prefix_ne_length_lt hvu hne1
      have hcu : v ++ [b] <+: u :=
        List.prefix_of_prefix_length_le hcw huw (by simp; omega)
      by_cases hc : u = v ++ [b]
      · rw [hc]; exact hb
      · exact hcond u hcu huw hc hne2

/-- 真の子孫は 2 つの子のどちらか一方の下にある。 -/
theorem openBelow_card_split (L : ℕ) (Bl : Node → Prop) (v : Node) :
    (openBelow L Bl v).card = ((openBelow L Bl v).filter (fun w => v ++ [false] <+: w)).card +
      ((openBelow L Bl v).filter (fun w => v ++ [true] <+: w)).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := openBelow L Bl v)
    (fun w => v ++ [false] <+: w)]
  congr 1
  congr 1
  apply Finset.filter_congr
  intro w hw
  obtain ⟨-, hvw, hwv, -⟩ := mem_openBelow.mp hw
  obtain ⟨b, hb⟩ := prefix_child hvw hwv
  constructor
  · intro hn
    cases b with
    | false => exact absurd hb hn
    | true => exact hb
  · intro ht hf
    have := prefix_eq_of_length hf ht (by simp)
    simp at this

/-- **補題 L2 の核（偶奇）.** `|v| < L` なら `openBelow L Bl v` の大きさは偶数。 -/
theorem openBelow_even (L : ℕ) (Bl : Node → Prop) :
    ∀ k (v : Node), v.length + k + 1 = L → Even (openBelow L Bl v).card := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [openBelow_card_split, openBelow_filter_leaf false (by omega),
      openBelow_filter_leaf true (by omega)]
    simp
  | succ k ih =>
    intro v hv
    have part : ∀ b : Bool, Even ((openBelow L Bl v).filter (fun w => v ++ [b] <+: w)).card := by
      intro b
      by_cases hb : Bl (v ++ [b])
      · rw [openBelow_filter_blocked b (by omega) hb]; simp
      · rw [openBelow_filter_open b (by omega) hb]
        exact ih (v ++ [b]) (by simp; omega)
    rw [openBelow_card_split]
    exact (part false).add (part true)

/-- `openBelow` は `Bl` の 2 点で交わらない（`v` の真の子孫の `v'` が `Bl` の点なら間を塞ぐ）。 -/
theorem openBelow_disjoint {L : ℕ} {Bl : Node → Prop} {v v' : Node} (hv : Bl v) (hv' : Bl v')
    (hne : v ≠ v') : Disjoint (openBelow L Bl v) (openBelow L Bl v') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  obtain ⟨-, h1, h2, h3⟩ := mem_openBelow.mp hw
  obtain ⟨-, h1', h2', h3'⟩ := mem_openBelow.mp hw'
  rcases lt_trichotomy v.length v'.length with hl | hl | hl
  · exact h3 v' (List.prefix_of_prefix_length_le h1 h1' hl.le) h1'
      (Ne.symm hne) (Ne.symm h2') hv'
  · exact hne (prefix_eq_of_length h1 h1' hl)
  · exact h3' v (List.prefix_of_prefix_length_le h1' h1 hl.le) h1 hne (Ne.symm h2) hv

/-! ## 区域ごとの算術（r = 2） -/

/-- **段 1 の区域ごとの算術（r = 2）.** `G ≤ μ₁A + μ₂Kk`，`G ≤ s·Kk`，`G ≤ q·A`，`A + β ≤ q`，
`Kk + β ≤ n ≤ Xj + t` のもとで `sβ + G ≤ μC·min(j, 1) + μS·j + ν·(j mod 2) + s·t`。
`j = 0, 1` は `s·n`，`j = 2, 3` は `μ₁q + μ₂n`，`j ≥ 4` は `q²` で抑える。 -/
theorem m3r2_zone_arith {s q X μ₁ μ₂ μC μS ν β A Kk G n j t : ℕ}
    (hs : μ₁ + μ₂ = s) (hq : q = μ₁ + 2 * μ₂)
    (h1 : X * s + ν ≤ μC + μS) (h2 : μ₁ * q + 2 * μ₂ * X ≤ μC + 2 * μS)
    (h3 : μ₁ * q + 3 * μ₂ * X ≤ μC + 3 * μS + ν) (h4 : q * q ≤ μC + 4 * μS)
    (hGa : G ≤ μ₁ * A + μ₂ * Kk) (hGb : G ≤ s * Kk) (hGc : G ≤ q * A)
    (hAq : A + β ≤ q) (hKn : Kk + β ≤ n) (hn : n ≤ X * j + t) :
    s * β + G ≤ μC * min j 1 + μS * j + ν * (j % 2) + s * t := by
  have B1 : s * β + G ≤ s * (X * j + t) := by
    have e1 : s * (Kk + β) ≤ s * (X * j + t) := Nat.mul_le_mul_left _ (hKn.trans hn)
    have e2 : s * (Kk + β) = s * β + s * Kk := by ring
    omega
  have B2 : s * β + G ≤ μ₁ * q + μ₂ * X * j + s * t := by
    have e1 : μ₁ * (A + β) ≤ μ₁ * q := Nat.mul_le_mul_left _ hAq
    have e2 : μ₂ * (Kk + β) ≤ μ₂ * (X * j + t) := Nat.mul_le_mul_left _ (hKn.trans hn)
    have e3 : s * β = μ₁ * β + μ₂ * β := by rw [← hs]; ring
    have e4 : μ₁ * (A + β) = μ₁ * A + μ₁ * β := by ring
    have e5 : μ₂ * (Kk + β) = μ₂ * Kk + μ₂ * β := by ring
    have e6 : μ₂ * (X * j + t) = μ₂ * X * j + μ₂ * t := by ring
    have e7 : μ₂ * t ≤ s * t := Nat.mul_le_mul_right _ (by omega)
    omega
  have B3 : s * β + G ≤ q * q := by
    have e1 : s * β ≤ q * β := Nat.mul_le_mul_right _ (by omega)
    have e2 : q * (A + β) ≤ q * q := Nat.mul_le_mul_left _ hAq
    have e3 : q * (A + β) = q * A + q * β := by ring
    omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j) with rfl | rfl | rfl | rfl | hj
  · have g : μC * min 0 1 + μS * 0 + ν * (0 % 2) + s * t = s * t := by
      rw [show min 0 1 = 0 from rfl, show (0 : ℕ) % 2 = 0 from rfl]; ring
    have e : s * (X * 0 + t) = s * t := by ring
    omega
  · have g : μC * min 1 1 + μS * 1 + ν * (1 % 2) + s * t = μC + μS + ν + s * t := by
      rw [show min 1 1 = 1 from rfl, show (1 : ℕ) % 2 = 1 from rfl]; ring
    have e : s * (X * 1 + t) = X * s + s * t := by ring
    omega
  · have g : μC * min 2 1 + μS * 2 + ν * (2 % 2) + s * t = μC + 2 * μS + s * t := by
      rw [show min 2 1 = 1 from rfl, show (2 : ℕ) % 2 = 0 from rfl]; ring
    have e : μ₂ * X * 2 = 2 * μ₂ * X := by ring
    omega
  · have g : μC * min 3 1 + μS * 3 + ν * (3 % 2) + s * t = μC + 3 * μS + ν + s * t := by
      rw [show min 3 1 = 1 from rfl, show (3 : ℕ) % 2 = 1 from rfl]; ring
    have e : μ₂ * X * 3 = 3 * μ₂ * X := by ring
    omega
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 4 := ⟨j - 4, by omega⟩
    have hm : min (j' + 4) 1 = 1 := by omega
    rw [hm]
    have e : μS * (j' + 4) = 4 * μS + μS * j' := by ring
    omega

/-! ## 主補題 -/

open Classical in
/-- **定理 L3 の組合せ部分（`h = 3H + 2`）.** -/
theorem m3r2_zone_sum_le {ms : ℕ → Move} {H c : ℕ} (hH : 1 ≤ H) (f : Node → ℕ)
    (q μ₁ μ₂ μC μS ν : ℕ)
    (hs : μ₁ + μ₂ = 2 ^ H - 1) (hq : q = μ₁ + 2 * μ₂)
    (h1 : 2 ^ H * (2 ^ H - 1) + ν ≤ μC + μS)
    (h2 : μ₁ * q + 2 * μ₂ * 2 ^ H ≤ μC + 2 * μS)
    (h3 : μ₁ * q + 3 * μ₂ * 2 ^ H ≤ μC + 3 * μS + ν) (h4 : q * q ≤ μC + 4 * μS)
    (hK : ∀ y ∈ pebSet (3 * H + 2) ms c, (zoneK ms (3 * H + 2) c f y).card ≤ q) :
    ∑ y ∈ pebSet (3 * H + 2) ms c, ∑ u ∈ zoneK ms (3 * H + 2) c f y,
        min (childZone ms (childZone ms (nodes (3 * H + 2)) c y) (f y) u).card q
      ≤ (2 ^ (2 * H + 2) - 1) + (μ₁ + μ₂ + μC) * (pebSet (3 * H + 2) ms c).card
        + μS * 2 ^ (H + 2) := by
  -- 記法
  obtain ⟨h, hh⟩ : ∃ h, h = 3 * H + 2 := ⟨_, rfl⟩
  rw [← hh]
  rw [← hh] at hK
  obtain ⟨P, hP⟩ : ∃ P, P = pebSet h ms c := ⟨_, rfl⟩
  rw [← hP]
  rw [← hP] at hK
  have memP : ∀ y, y ∈ P ↔ y ≠ [] ∧ y.length < h ∧ st ms c y = .pebble := by
    intro y; rw [hP]; exact mem_pebSet
  obtain ⟨Z, hZ⟩ : ∃ Z : Node → Finset Node, ∀ y, Z y = childZone ms (nodes h) c y :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Node → Finset Node, ∀ y, K y = zoneK ms h c f y := ⟨_, fun _ => rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2 : Node → Node → Finset Node,
      ∀ y u, Z2 y u = childZone ms (childZone ms (nodes h) c y) (f y) u := ⟨_, fun _ _ => rfl⟩
  simp only [← hKdef, ← hZ2]
  simp only [← hKdef] at hK
  have memK : ∀ y x, x ∈ K y ↔ x ∈ Z y ∧ st ms (f y) x = .pebble := by
    intro y x; rw [hKdef, hZ, mem_zoneK]
  have hZ2Z : ∀ y u, Z2 y u ⊆ Z y := by
    intro y u; rw [hZ2, hZ]; exact childZone_subset
  have memZ2 : ∀ y u d, d ∈ Z2 y u ↔ d ∈ Z y ∧ u <+: d ∧ d ≠ u ∧
      ∀ w, u <+: w → w <+: d → w ≠ u → st ms (f y) w ≠ .pebble := by
    intro y u d; rw [hZ2, hZ, mem_childZone]
  have memZ : ∀ y d, d ∈ Z y ↔ d.length < h ∧ y <+: d ∧ d ≠ y ∧
      ∀ w, y <+: w → w <+: d → w ≠ y → st ms c w ≠ .pebble := by
    intro y d; rw [hZ, mem_childZone, mem_nodes]
  -- 区域は互いに素
  have hdisjZ : ∀ y ∈ P, ∀ y' ∈ P, y ≠ y' → Disjoint (Z y) (Z y') := by
    intro y hy y' hy' hne
    rw [hZ, hZ]
    exact childZone_disjoint ((memP y).mp hy).2.2 ((memP y').mp hy').2.2 hne
  have hdisjZ2 : ∀ y, ∀ u ∈ K y, ∀ u' ∈ K y, u ≠ u' → Disjoint (Z2 y u) (Z2 y u') := by
    intro y u hu u' hu' hne
    rw [hZ2, hZ2]
    exact childZone_disjoint ((memK y u).mp hu).2 ((memK y u').mp hu').2 hne
  -- 大きさ
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ H := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = 2 ^ H - 1 := ⟨_, rfl⟩
  have hs' : μ₁ + μ₂ = s := by omega
  rw [← hX] at h2 h3
  rw [← hsd, ← hX] at h1
  -- D（深さ 2H+2）、R（深さ H+2）
  obtain ⟨D, hD⟩ : ∃ D : Finset Node, D = words (2 * H + 2) := ⟨_, rfl⟩
  have memD : ∀ x, x ∈ D ↔ x.length = 2 * H + 2 := by intro x; rw [hD, mem_words]
  obtain ⟨R, hR⟩ : ∃ R : Finset Node, R = words (H + 2) := ⟨_, rfl⟩
  have memR : ∀ x, x ∈ R ↔ x.length = H + 2 := by intro x; rw [hR, mem_words]
  have hRcard : R.card = 2 ^ (H + 2) := by rw [hR, card_words]
  have hSx : ∀ x ∈ D, (subtree h x).card = s := by
    intro x hx
    rw [card_subtree, (memD x).mp hx, show h - (2 * H + 2) = H by omega, hsd]
  -- 汚れ
  obtain ⟨Pd, hPd⟩ : ∃ Pd : Node → Prop, ∀ x, Pd x ↔ ∃ z ∈ P, x <+: z := ⟨_, fun _ => Iff.rfl⟩
  have hPd_anc : ∀ y ∈ P, ∀ x, x <+: y → Pd x := fun y hy x hxy => (hPd x).mpr ⟨y, hy, hxy⟩
  -- 段 2 の分類
  obtain ⟨Dn, hDn⟩ : ∃ Dn : Finset Node, Dn = D.filter (fun x => ¬ Pd x) := ⟨_, rfl⟩
  obtain ⟨DP, hDP⟩ : ∃ DP : Finset Node, DP = D.filter (fun x => Pd x) := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : Node → Finset Node,
      ∀ y, Kd y = Dn.filter (fun x => ∃ z ∈ K y, x <+: z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Cl, hCl⟩ : ∃ Cl : Node → Finset Node,
      ∀ y, Cl y = Dn.filter (fun x => ¬ ∃ z ∈ K y, x <+: z) := ⟨_, fun _ => rfl⟩
  have memDn : ∀ x, x ∈ Dn ↔ x ∈ D ∧ ¬ Pd x := by intro x; rw [hDn, Finset.mem_filter]
  have memKd : ∀ y x, x ∈ Kd y ↔ (x ∈ D ∧ ¬ Pd x) ∧ ∃ z ∈ K y, x <+: z := by
    intro y x; rw [hKd, Finset.mem_filter, memDn]
  have memCl : ∀ y x, x ∈ Cl y ↔ (x ∈ D ∧ ¬ Pd x) ∧ ¬ ∃ z ∈ K y, x <+: z := by
    intro y x; rw [hCl, Finset.mem_filter, memDn]
  obtain ⟨a, ha⟩ : ∃ a : Node → Node → Node → ℕ,
      ∀ y u x, a y u x = ((Z2 y u).filter (fun d => x <+: d)).card := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Node → Node → Finset Node,
      ∀ y u, F y u = (Cl y).filter (fun x => a y u x ≠ 0) := ⟨_, fun _ _ => rfl⟩
  have hF_anc : ∀ y u x, x ∈ F y u → u ∈ K y →
      u <+: x ∧ u.length < x.length ∧ ∃ d ∈ Z2 y u, x <+: d := by
    intro y u x hx hu
    rw [hF, Finset.mem_filter, memCl] at hx
    obtain ⟨⟨-, hxK⟩, hax⟩ := hx
    rw [ha] at hax
    obtain ⟨d, hd⟩ := Finset.card_ne_zero.mp hax
    rw [Finset.mem_filter] at hd
    obtain ⟨hdZ, hxd⟩ := hd
    have hud := ((memZ2 y u d).mp hdZ).2.1
    by_cases hl : x.length ≤ u.length
    · exact absurd ⟨u, hu, List.prefix_of_prefix_length_le hxd hud hl⟩ hxK
    · exact ⟨List.prefix_of_prefix_length_le hud hxd (by omega), by omega, d, hdZ, hxd⟩
  have hsub_a : ∀ y x, ∑ u ∈ K y, a y u x ≤ ((Z y).filter (fun d => x <+: d)).card := by
    intro y x
    have he : ∑ u ∈ K y, a y u x = ∑ u ∈ K y, ((Z2 y u).filter (fun d => x <+: d)).card :=
      Finset.sum_congr rfl (fun u _ => ha y u x)
    rw [he]
    apply sum_card_le_of_disj
    · intro u hu u' hu' hne
      exact Finset.disjoint_filter_filter (hdisjZ2 y u hu u' hu' hne)
    · intro u _ d hd
      rw [Finset.mem_filter] at hd ⊢
      exact ⟨hZ2Z y u hd.1, hd.2⟩
  have hsum_Sx : ∀ x ∈ D, ∑ y ∈ P, ((Z y).filter (fun d => x <+: d)).card ≤ s := by
    intro x hx
    rw [← hSx x hx]
    apply sum_card_le_of_disj
    · intro y hy y' hy' hne
      exact Finset.disjoint_filter_filter (hdisjZ y hy y' hy' hne)
    · intro y _ d hd
      rw [Finset.mem_filter] at hd
      exact mem_subtree.mpr ⟨((memZ y d).mp hd.1).1, hd.2⟩
  -- (y, u) ごとの評価
  have hyu : ∀ y ∈ P, ∀ u ∈ K y, min (Z2 y u).card q ≤
      ((Z2 y u).filter (fun d => d.length < 2 * H + 2)).card + ∑ x ∈ DP, a y u x
      + ∑ x ∈ Kd y, a y u x + min ((F y u).card * s) q := by
    intro y _ u _
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z2 y u)
      (fun d => d.length < 2 * H + 2)
    have hN : ((Z2 y u).filter (fun d => ¬ d.length < 2 * H + 2)).card ≤ ∑ x ∈ D, a y u x := by
      have hsub : (Z2 y u).filter (fun d => ¬ d.length < 2 * H + 2) ⊆
          D.biUnion (fun x => (Z2 y u).filter (fun d => x <+: d)) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        refine Finset.mem_biUnion.mpr ⟨d.take (2 * H + 2), (memD _).mpr ?_,
          Finset.mem_filter.mpr ⟨hd.1, List.take_prefix _ _⟩⟩
        rw [List.length_take]
        omega
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
      exact Finset.sum_congr rfl (fun x _ => (ha y u x).symm)
    have hDsplit : ∑ x ∈ D, a y u x = ∑ x ∈ DP, a y u x + ∑ x ∈ Kd y, a y u x
        + ∑ x ∈ Cl y, a y u x := by
      rw [hDP, hKd, hCl, hDn, add_assoc,
        Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]
    have hCl_le : ∑ x ∈ Cl y, a y u x ≤ (F y u).card * s := by
      have h1 : ∑ x ∈ Cl y, a y u x = ∑ x ∈ F y u, a y u x := by
        rw [hF y u]; exact (Finset.sum_filter_ne_zero _).symm
      have h2 := Finset.sum_le_card_nsmul (F y u) (a y u) s (by
        intro x hx
        rw [hF, Finset.mem_filter, memCl] at hx
        rw [ha, ← hSx x hx.1.1.1]
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_filter] at hd
        exact mem_subtree.mpr ⟨((memZ y d).mp (hZ2Z y u hd.1)).1, hd.2⟩)
      rw [smul_eq_mul] at h2
      rw [h1]
      exact h2
    generalize (F y u).card * s = m at hCl_le ⊢
    omega
  -- y ごとの量
  obtain ⟨β, hβ⟩ : ∃ β : Node → ℕ, ∀ y, β y = (Kd y).card := ⟨_, fun _ => rfl⟩
  obtain ⟨Am, hAm⟩ : ∃ Am : Node → ℕ, ∀ y, Am y = ∑ u ∈ K y, min (F y u).card 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Kk, hKk⟩ : ∃ Kk : Node → ℕ, ∀ y, Kk y = ∑ u ∈ K y, (F y u).card := ⟨_, fun _ => rfl⟩
  obtain ⟨Gs, hGs⟩ : ∃ Gs : Node → ℕ, ∀ y, Gs y = ∑ u ∈ K y, min ((F y u).card * s) q :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Node → Finset Node, ∀ y, N y = Dn.filter (fun x => x ∈ Z y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : Finset Node, Rc = R.filter (fun w => ¬ Pd w) := ⟨_, rfl⟩
  obtain ⟨RP, hRP⟩ : ∃ RP : Finset Node, RP = R.filter (fun w => Pd w) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Node → Finset Node, ∀ y, J y = Rc.filter (fun w => w ∈ Z y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ Tt : Node → Finset Node,
      ∀ y, Tt y = (N y).filter (fun x => Pd (x.take (H + 2))) := ⟨_, fun _ => rfl⟩
  have memN : ∀ y x, x ∈ N y ↔ (x ∈ D ∧ ¬ Pd x) ∧ x ∈ Z y := by
    intro y x; rw [hN, Finset.mem_filter, memDn]
  -- (C1) A + β ≤ |K_y|
  have hC1 : ∀ y ∈ P, Am y + β y ≤ q := by
    intro y hy
    have hA1 : Am y ≤ ((K y).filter (fun u => u.length < 2 * H + 2)).card := by
      rw [hAm, Finset.card_filter]
      apply Finset.sum_le_sum
      intro u hu
      by_cases hk : (F y u).card = 0
      · rw [hk]; simp
      · obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hk
        have h1 := hF_anc y u x hx hu
        have hxD : x ∈ D := by
          rw [hF, Finset.mem_filter, memCl] at hx; exact hx.1.1.1
        rw [if_pos (by rw [(memD x).mp hxD] at h1; exact h1.2.1)]
        exact min_le_right _ _
    have hB1 : β y ≤ ((K y).filter (fun u => ¬ u.length < 2 * H + 2)).card := by
      rw [hβ]
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (2 * H + 2) (K y))
      intro x hx
      rw [memKd] at hx
      rw [Finset.mem_filter, ← hD]
      exact ⟨hx.1.1, hx.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K y)
      (fun u => u.length < 2 * H + 2)
    have := hK y hy
    omega
  -- (C2) Kk + β ≤ |N_y|
  have hC2 : ∀ y ∈ P, Kk y + β y ≤ (N y).card := by
    intro y hy
    have hFd : ((K y : Finset Node) : Set Node).PairwiseDisjoint (F y) := by
      intro u hu u' hu' hne
      show Disjoint (F y u) (F y u')
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨hux, -, d, hdZ, hxd⟩ := hF_anc y u x hx hu
      obtain ⟨hux', -, d', hdZ', hxd'⟩ := hF_anc y u' x hx' hu'
      have hpu := ((memK y u).mp hu).2
      have hpu' := ((memK y u').mp hu').2
      rcases lt_trichotomy u.length u'.length with hl | hl | hl
      · exact ((memZ2 y u d).mp hdZ).2.2.2 u' (List.prefix_of_prefix_length_le hux hux' hl.le)
          (hux'.trans hxd) (Ne.symm hne) hpu'
      · exact hne (prefix_eq_of_length hux hux' hl)
      · exact ((memZ2 y u' d').mp hdZ').2.2.2 u (List.prefix_of_prefix_length_le hux' hux hl.le)
          (hux.trans hxd') hne hpu
    have hFsub : (K y).biUnion (F y) ⊆ (N y).filter (fun x => ¬ ∃ z ∈ K y, x <+: z) := by
      intro x hx
      obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨-, -, d, hdZ, hxd⟩ := hF_anc y u x hxu hu
      rw [hF, Finset.mem_filter, memCl] at hxu
      rw [Finset.mem_filter, memN]
      refine ⟨⟨hxu.1.1, ?_⟩, hxu.1.2⟩
      rw [hZ]
      refine zone_mem_of_prefix ?_ hxd (fun hxy => hxu.1.1.2 (hPd_anc y hy x hxy))
      rw [← hZ]; exact hZ2Z y u hdZ
    have hKdsub : Kd y ⊆ (N y).filter (fun x => ∃ z ∈ K y, x <+: z) := by
      intro x hx
      rw [memKd] at hx
      obtain ⟨⟨hxD, hxP⟩, z, hzK, hxz⟩ := hx
      rw [Finset.mem_filter, memN]
      refine ⟨⟨⟨hxD, hxP⟩, ?_⟩, z, hzK, hxz⟩
      rw [hZ]
      refine zone_mem_of_prefix ?_ hxz (fun hxy => hxP (hPd_anc y hy x hxy))
      rw [← hZ]; exact ((memK y z).mp hzK).1
    have e1 := Finset.card_le_card hFsub
    rw [Finset.card_biUnion hFd] at e1
    have e2 := Finset.card_le_card hKdsub
    have e3 := Finset.card_filter_add_card_filter_not (s := N y) (fun x => ∃ z ∈ K y, x <+: z)
    rw [hKk, hβ]
    omega
  -- (C3) |N_y| ≤ X j_y + t_y
  have hC3 : ∀ y ∈ P, (N y).card ≤ X * (J y).card + (Tt y).card := by
    intro y hy
    have hsp := Finset.card_filter_add_card_filter_not (s := N y) (fun x => Pd (x.take (H + 2)))
    rw [← hTt] at hsp
    have hsub : (N y).filter (fun x => ¬ Pd (x.take (H + 2))) ⊆
        (J y).biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter, memN] at hx
      obtain ⟨⟨⟨hxD, -⟩, hxZ⟩, hw⟩ := hx
      have hxl := (memD x).mp hxD
      refine Finset.mem_biUnion.mpr ⟨x.take (H + 2), ?_,
        Finset.mem_filter.mpr ⟨hxD, List.take_prefix _ _⟩⟩
      rw [hJ, Finset.mem_filter, hRc, Finset.mem_filter, memR, List.length_take]
      refine ⟨⟨by omega, hw⟩, ?_⟩
      rw [hZ]
      refine zone_mem_of_prefix (d := x) ?_ (List.take_prefix _ _) ?_
      · rw [← hZ]; exact hxZ
      · intro hxy
        exact hw (hPd_anc y hy _ hxy)
    have e1 : ((N y).filter (fun x => ¬ Pd (x.take (H + 2)))).card ≤
        ∑ w ∈ J y, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ J y, (D.filter (fun x => w <+: x)).card ≤ (J y).card * X := by
      have := Finset.sum_le_card_nsmul (J y) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hJ, Finset.mem_filter, hRc, Finset.mem_filter, memR] at hw
        rw [hD, hX, show 2 * H + 2 = (H + 2) + H by ring]
        exact card_words_prefix_le hw.1.1)
      rwa [smul_eq_mul] at this
    have e3 : (J y).card * X = X * (J y).card := mul_comm _ _
    omega
  -- (G9) 頭打ちの部分の 3 本の上界
  have hGa : ∀ y, Gs y ≤ μ₁ * Am y + μ₂ * Kk y := by
    intro y
    rw [hGs, hAm, hKk, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    rw [← hs', hq]
    exact odd_min_le μ₁ μ₂ _
  have hGb : ∀ y, Gs y ≤ s * Kk y := by
    intro y
    rw [hGs, hKk, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    rw [mul_comm s]
    exact min_le_left _ _
  have hGc : ∀ y, Gs y ≤ q * Am y := by
    intro y
    rw [hGs, hAm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    by_cases hk : (F y u).card = 0
    · rw [hk]; simp
    · rw [show min (F y u).card 1 = 1 by omega, mul_one]
      exact min_le_right _ _
  -- y ごとの算術
  have hyb : ∀ y ∈ P, s * β y + Gs y ≤
      μC * min (J y).card 1 + μS * (J y).card + ν * ((J y).card % 2) + s * (Tt y).card := by
    intro y hy
    exact m3r2_zone_arith hs' hq h1 h2 h3 h4 (hGa y) (hGb y) (hGc y) (hC1 y hy) (hC2 y hy)
      (hC3 y hy)
  -- 大域の量
  -- (G1) Σ t_y ≤ X ρ
  have hG1 : ∑ y ∈ P, (Tt y).card ≤ X * RP.card := by
    have hT1 : ∑ y ∈ P, (Tt y).card ≤ (D.filter (fun x => Pd (x.take (H + 2)))).card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (Tt y) (Tt y')
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [hTt, Finset.mem_filter, memN] at hx hx'
        exact Finset.disjoint_left.mp (hdisjZ y hy y' hy' hne) hx.1.2 hx'.1.2
      · intro y _ x hx
        rw [hTt, Finset.mem_filter, memN] at hx
        exact Finset.mem_filter.mpr ⟨hx.1.1.1, hx.2⟩
    have hT2 : D.filter (fun x => Pd (x.take (H + 2))) ⊆
        RP.biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxl := (memD x).mp hx.1
      refine Finset.mem_biUnion.mpr ⟨x.take (H + 2), ?_,
        Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      rw [hRP, Finset.mem_filter, memR, List.length_take]
      exact ⟨by omega, hx.2⟩
    have e1 : (D.filter (fun x => Pd (x.take (H + 2)))).card ≤
        ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hT2).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card ≤ RP.card * X := by
      have := Finset.sum_le_card_nsmul RP (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hRP, Finset.mem_filter, memR] at hw
        rw [hD, hX, show 2 * H + 2 = (H + 2) + H by ring]
        exact card_words_prefix_le hw.1)
      rwa [smul_eq_mul] at this
    have e3 : RP.card * X = X * RP.card := mul_comm _ _
    omega
  -- (G2) Σ j_y + ρ ≤ 2^{H+2}
  have hJZ : ∀ y, J y ⊆ Z y := by
    intro y w hw; rw [hJ, Finset.mem_filter] at hw; exact hw.2
  have hG2 : ∑ y ∈ P, (J y).card + RP.card ≤ 2 ^ (H + 2) := by
    have h1 : ∑ y ∈ P, (J y).card ≤ Rc.card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (J y) (J y')
        exact Disjoint.mono (hJZ y) (hJZ y') (hdisjZ y hy y' hy' hne)
      · intro y _ w hw
        rw [hJ, Finset.mem_filter] at hw
        exact hw.1
    have h2 := Finset.card_filter_add_card_filter_not (s := R) (fun w => Pd w)
    rw [← hRP, ← hRc, hRcard] at h2
    omega
  -- (G3) #{j_y ≥ 1} ≤ |P ∩ 深さ < H + 2|
  have hG3 : ∑ y ∈ P, min (J y).card 1 ≤ (P.filter (fun y => y.length < H + 2)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro y hy
    by_cases hj : (J y).card = 0
    · rw [hj]; simp
    · obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hj
      rw [hJ, Finset.mem_filter, hRc, Finset.mem_filter, memR] at hw
      obtain ⟨-, hyw, hne, -⟩ := (memZ y w).mp hw.2
      have : y.length < w.length :=
        lt_of_le_of_ne hyw.length_le (fun he => hne (hyw.eq_of_length he).symm)
      rw [if_pos (by rw [hw.1.1] at this; exact this)]
      exact min_le_right _ _
  -- (G4) ρ ≤ |P ∩ 深さ ≥ H + 2|
  have hG4 : RP.card ≤ (P.filter (fun y => ¬ y.length < H + 2)).card := by
    refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (H + 2) P)
    intro w hw
    rw [hRP, Finset.mem_filter] at hw
    rw [Finset.mem_filter, ← hR]
    exact ⟨hw.1, (hPd w).mp hw.2⟩
  have hPsplit := Finset.card_filter_add_card_filter_not (s := P) (fun y => y.length < H + 2)
  -- (G5) P 汚れの x の数 ≤ |P|
  have hG5 : DP.card ≤ P.card := by
    refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (2 * H + 2) P).trans
      (Finset.card_filter_le _ _))
    intro x hx
    rw [hDP, Finset.mem_filter] at hx
    rw [Finset.mem_filter, ← hD]
    exact ⟨hx.1, (hPd x).mp hx.2⟩
  -- (G6) U の部分
  have hG6 : ∑ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 2)).card
      ≤ 2 ^ (2 * H + 2) - 1 := by
    have h1 : ∀ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 2)).card ≤
        ((Z y).filter (fun d => d.length < 2 * H + 2)).card := by
      intro y _
      apply sum_card_le_of_disj
      · intro u hu u' hu' hne
        exact Finset.disjoint_filter_filter (hdisjZ2 y u hu u' hu' hne)
      · intro u _ d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hZ2Z y u hd.1, hd.2⟩
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← card_nodes]
    apply sum_card_le_of_disj
    · intro y hy y' hy' hne
      exact Finset.disjoint_filter_filter (hdisjZ y hy y' hy' hne)
    · intro y _ d hd
      rw [Finset.mem_filter] at hd
      exact mem_nodes.mpr hd.2
  -- (G7) P 汚れの部分
  have hG7 : ∑ y ∈ P, ∑ u ∈ K y, ∑ x ∈ DP, a y u x ≤ DP.card * s := by
    have h1 : ∑ y ∈ P, ∑ u ∈ K y, ∑ x ∈ DP, a y u x =
        ∑ x ∈ DP, ∑ y ∈ P, ∑ u ∈ K y, a y u x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    rw [h1]
    have := Finset.sum_le_card_nsmul DP (fun x => ∑ y ∈ P, ∑ u ∈ K y, a y u x) s (by
      intro x hx
      rw [hDP, Finset.mem_filter] at hx
      exact (Finset.sum_le_sum (fun y _ => hsub_a y x)).trans (hsum_Sx x hx.1))
    rwa [smul_eq_mul] at this
  -- (G8) K 汚れの部分
  have hG8 : ∀ y ∈ P, ∑ u ∈ K y, ∑ x ∈ Kd y, a y u x ≤ s * β y := by
    intro y _
    rw [Finset.sum_comm, hβ, mul_comm]
    have := Finset.sum_le_card_nsmul (Kd y) (fun x => ∑ u ∈ K y, a y u x) s (by
      intro x hx
      rw [memKd] at hx
      refine (hsub_a y x).trans ?_
      rw [← hSx x hx.1.1]
      apply Finset.card_le_card
      intro d hd
      rw [Finset.mem_filter] at hd
      exact mem_subtree.mpr ⟨((memZ y d).mp hd.1).1, hd.2⟩)
    rwa [smul_eq_mul] at this
  -- (G10) 補題 L2（偶奇）: Σ_y (j_y mod 2) ≤ ρ
  obtain ⟨Bo, hBo⟩ : ∃ Bo : Node → Finset Node, ∀ y, Bo y = openBelow (H + 2) (· ∈ P) y :=
    ⟨_, fun _ => rfl⟩
  have hJBo : ∀ y ∈ P, J y = (Bo y).filter (fun w => ¬ Pd w) := by
    intro y hy
    have hy0 : y ≠ [] := ((memP y).mp hy).1
    ext w
    simp only [hJ, hRc, hBo, Finset.mem_filter, memR, mem_openBelow, memZ]
    constructor
    · rintro ⟨⟨hwl, hwc⟩, -, hyw, hwy, hst⟩
      refine ⟨⟨hwl, hyw, hwy, ?_⟩, hwc⟩
      intro u hyu huw hne1 _ huP
      exact hst u hyu huw hne1 ((memP u).mp huP).2.2
    · rintro ⟨⟨hwl, hyw, hwy, hcond⟩, hwc⟩
      refine ⟨⟨hwl, hwc⟩, by omega, hyw, hwy, ?_⟩
      intro u hyu huw hne1 hpeb
      have hu0 : u ≠ [] := by
        rintro rfl; exact hy0 (List.prefix_nil.mp hyu)
      have huP : u ∈ P := (memP u).mpr ⟨hu0, by have := huw.length_le; omega, hpeb⟩
      by_cases hue : u = w
      · subst hue; exact hwc ((hPd u).mpr ⟨u, huP, List.prefix_refl _⟩)
      · exact hcond u hyu huw hne1 hue huP
  have hpar : ∀ y ∈ P, (J y).card % 2 ≤ ((Bo y).filter (fun w => Pd w)).card := by
    intro y hy
    have hsp := Finset.card_filter_add_card_filter_not (s := Bo y) (fun w => Pd w)
    rw [← hJBo y hy] at hsp
    by_cases hyl : y.length < H + 2
    · have hev := openBelow_even (H + 2) (· ∈ P) (H + 2 - y.length - 1) y (by omega)
      rw [← hBo y] at hev
      obtain ⟨r, hr⟩ := hev
      omega
    · have hemp : J y = ∅ := by
        rw [hJBo y hy]
        apply Finset.eq_empty_of_forall_notMem
        intro w hw
        rw [Finset.mem_filter, hBo, mem_openBelow] at hw
        have := prefix_ne_length_lt hw.1.2.1 hw.1.2.2.1
        have := hw.1.1
        omega
      rw [hemp]; simp
  have hG10 : ∑ y ∈ P, (J y).card % 2 ≤ RP.card := by
    refine (Finset.sum_le_sum hpar).trans ?_
    apply sum_card_le_of_disj
    · intro y hy y' hy' hne
      show Disjoint ((Bo y).filter (fun w => Pd w)) ((Bo y').filter (fun w => Pd w))
      apply Finset.disjoint_filter_filter
      rw [hBo, hBo]
      exact openBelow_disjoint hy hy' hne
    · intro y _ w hw
      rw [Finset.mem_filter, hBo, mem_openBelow] at hw
      rw [hRP, Finset.mem_filter, memR]
      exact ⟨hw.1.1, hw.2⟩
  -- 合わせる
  have hstep1 : ∑ y ∈ P, ∑ u ∈ K y, min (Z2 y u).card q ≤
      ∑ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 2)).card
      + ∑ y ∈ P, ∑ u ∈ K y, ∑ x ∈ DP, a y u x
      + ∑ y ∈ P, (s * β y + Gs y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y hy
    have e1 := Finset.sum_le_sum (hyu y hy)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
    have e2 := hG8 y hy
    have e3 := hGs y
    omega
  have hstep2 : ∑ y ∈ P, (s * β y + Gs y) ≤
      μC * ∑ y ∈ P, min (J y).card 1 + μS * ∑ y ∈ P, (J y).card
        + ν * ∑ y ∈ P, (J y).card % 2 + s * ∑ y ∈ P, (Tt y).card := by
    refine (Finset.sum_le_sum hyb).trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
  -- 最後の算術
  have e1 : s * ∑ y ∈ P, (Tt y).card ≤ s * (X * RP.card) := Nat.mul_le_mul_left _ hG1
  have e1' : ν * ∑ y ∈ P, (J y).card % 2 ≤ ν * RP.card := Nat.mul_le_mul_left _ hG10
  have e2 : s * (X * RP.card) + ν * RP.card ≤ μC * RP.card + μS * RP.card := by
    have := Nat.mul_le_mul_right RP.card h1
    have e : (X * s + ν) * RP.card = s * (X * RP.card) + ν * RP.card := by ring
    have e' : (μC + μS) * RP.card = μC * RP.card + μS * RP.card := by ring
    omega
  have e3 : μC * ∑ y ∈ P, min (J y).card 1 + μC * RP.card ≤ μC * P.card := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have e4 : μS * ∑ y ∈ P, (J y).card + μS * RP.card ≤ μS * 2 ^ (H + 2) := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ hG2
  have e5 : DP.card * s ≤ P.card * s := Nat.mul_le_mul_right _ hG5
  have e6 : (μ₁ + μ₂ + μC) * P.card = P.card * s + μC * P.card := by rw [hs']; ring
  omega

end SpookyTree
