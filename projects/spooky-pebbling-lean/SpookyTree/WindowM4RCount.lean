/-
# 定理 L4r の組合せ部分（`h = 4H + r`，紙の r = 2, 3）: 段 3 の区域の頭打ちの和 `V*_3 ≤ W_r`

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4R_2026-11.md` の 2 節（補題 L2・補題 M4・段 2 と段 1 の双対）。
`WindowM4LowerCount.lean`（r = 1）の組み立てを一般の `r` に広げ，偶奇と 4 を法とする制約を入れたもの。違い:
* 深さ: `D` = 深さ `3H + r`（`S_x` は `s = 2^H − 1` 頂点），`Rb` = 深さ `2H + r`，`Yb` = 深さ `H + r`（`N_Y = 2^r X`）。
* 段 2（区域 `Z_y` の中）の双対は区域ごとに選ぶ（紙の D1・D2・D4・Dsat）。条件は `M4RDual`:
  `j ≥ 1` で `min(sXj, μ₁q + μ₂Xj, q²) ≤ λC + λS j + ν (j mod 2)`，`Xs + ν ≤ λC + λS`，`λS ≤ Xs`。
* **段 2 の偶奇**: `#{u ∈ K_y : j_u 奇数} ≤ ρ_y + τ°_y`（`τ°_y` = `P` 汚れの `R_w` で `y` の下の開いた部分にあるもの，
  `Σ_y τ°_y ≤ |P|`）。`openBelow (2H + r) (P ∪ K_y) u` の偶奇（`openBelow_even`）から。
* **段 1 の偶奇（補題 L2）と補題 M4**: `i_y + d_y = |openBelow (H + r) P y|`（`d_y` = 汚れた `Y_v` の数）。
  `i_y mod 2 ≤ d_y`，`#{y : i_y ≡ 2 (mod 4), i_y ≥ 6} ≤ #{y : i_y = 2} + #{y : d_y ≥ 1}`（`m4_count`）。

**主張（`m4r_zone_sum_le`）.** 段 3 の双対 `μ₁ + μ₂ = s`，`q = μ₁ + 2μ₂`，各 `i` に段 2 の双対 `(λC, λS, ν)`
（`M4RDual`，`ν ≤ NU`）があって `λC q + λS X i + κ[i = 2] ≤ μC min(i,1) + μS i + ν₁ (i mod 2) + κ[i ≡ 2 (4), i ≥ 6]`，
`X·Xs + ν₁ + κ ≤ μC + μS`，`|K_y| ≤ q`，`|K'_{y,u}| ≤ q` なら
  `Σ_{y,u,v} min(|Z''|, q) ≤ (2^{3H+r} − 1) + s|P| + s Σ_y |K_y| + sX|P| + μC|P| + μS·2^{H+r} + NU|P|`。
-/
import SpookyTree.WindowM4LowerCount
import SpookyTree.WindowM3R2Count

namespace SpookyTree

/-! ## `openBelow` の補題（偶奇と 4 を法とする分解） -/

theorem openBelow_eq_empty {L : ℕ} {Bl : Node → Prop} {v : Node} (hv : L ≤ v.length) :
    openBelow L Bl v = ∅ := by
  ext w
  rw [mem_openBelow]
  simp only [Finset.notMem_empty, iff_false, not_and]
  intro hwl hvw hwv
  exfalso
  have := prefix_ne_length_lt hvw hwv
  omega

/-- `openBelow` の大きさはいつも偶数。 -/
theorem openBelow_even' (L : ℕ) (Bl : Node → Prop) (v : Node) : Even (openBelow L Bl v).card := by
  by_cases hv : v.length < L
  · obtain ⟨k, hk⟩ : ∃ k, v.length + k + 1 = L := ⟨L - v.length - 1, by omega⟩
    exact openBelow_even L Bl k v hk
  · rw [openBelow_eq_empty (by omega)]; simp

/-- `|v| + 1 = L` なら `openBelow L Bl v` は `v` の 2 つの子。 -/
theorem openBelow_card_two {L : ℕ} {Bl : Node → Prop} {v : Node} (hL : v.length + 1 = L) :
    (openBelow L Bl v).card = 2 := by
  rw [openBelow_card_split, openBelow_filter_leaf false hL, openBelow_filter_leaf true hL]
  simp

/-- **補題 M4 の核.** `|v| + 2 ≤ L` で `|openBelow L Bl v| ≡ 2 (mod 4)` なら，`v` の真の子孫で深さ `L − 1` の
`Bl` の点 `y` があり，`v` と `y` の間（両端を除く）に `Bl` の点は無い。 -/
theorem openBelow_mod4 (L : ℕ) (Bl : Node → Prop) :
    ∀ k (v : Node), v.length + k + 2 = L → (openBelow L Bl v).card % 4 = 2 →
      ∃ y, Bl y ∧ y.length + 1 = L ∧ v <+: y ∧ y ≠ v ∧
        ∀ u, v <+: u → u <+: y → u ≠ v → u ≠ y → ¬ Bl u := by
  intro k
  induction k with
  | zero =>
    intro v hv hmod
    have part : ∀ b : Bool, ¬ Bl (v ++ [b]) →
        ((openBelow L Bl v).filter (fun w => v ++ [b] <+: w)).card = 2 := by
      intro b hb
      rw [openBelow_filter_open b (by omega) hb]
      exact openBelow_card_two (by simp; omega)
    obtain ⟨b, hb⟩ : ∃ b : Bool, Bl (v ++ [b]) := by
      by_contra hno
      push Not at hno
      rw [openBelow_card_split, part false (hno false), part true (hno true)] at hmod
      norm_num at hmod
    refine ⟨v ++ [b], hb, by simp; omega, List.prefix_append _ _, by simp, ?_⟩
    intro u hvu huy hne1 hne2
    exfalso
    have h1 := prefix_ne_length_lt hvu hne1
    have h2 : u.length < (v ++ [b]).length :=
      lt_of_le_of_ne huy.length_le (fun he => hne2 (huy.eq_of_length he))
    simp at h2
    omega
  | succ k ih =>
    intro v hv hmod
    have ev : ∀ b : Bool, Even ((openBelow L Bl v).filter (fun w => v ++ [b] <+: w)).card := by
      intro b
      by_cases hb : Bl (v ++ [b])
      · rw [openBelow_filter_blocked b (by omega) hb]; simp
      · rw [openBelow_filter_open b (by omega) hb]
        exact openBelow_even L Bl (k + 1) (v ++ [b]) (by simp; omega)
    have hsplit := openBelow_card_split L Bl v
    obtain ⟨b, hb⟩ : ∃ b : Bool,
        ((openBelow L Bl v).filter (fun w => v ++ [b] <+: w)).card % 4 = 2 := by
      obtain ⟨x, hx⟩ := ev false
      obtain ⟨y, hy⟩ := ev true
      by_contra hno
      push Not at hno
      have h0 := hno false
      have h1 := hno true
      omega
    have hopen : ¬ Bl (v ++ [b]) := by
      intro hbl
      rw [openBelow_filter_blocked b (by omega) hbl] at hb
      simp at hb
    rw [openBelow_filter_open b (by omega) hopen] at hb
    obtain ⟨y, hyB, hyl, hcy, hyc, hpath⟩ := ih (v ++ [b]) (by simp; omega) hb
    refine ⟨y, hyB, hyl, (List.prefix_append _ _).trans hcy, ?_, ?_⟩
    · intro he; rw [he] at hyl; omega
    · intro u hvu huy hne1 hne2
      have hlt := prefix_ne_length_lt hvu hne1
      have hcu : v ++ [b] <+: u := List.prefix_of_prefix_length_le hcy huy (by simp; omega)
      by_cases hc : u = v ++ [b]
      · rw [hc]; exact hopen
      · exact hpath u hcu huy hc hne2

/-- 最も近い `Bl` の真の祖先は 1 つ。 -/
theorem bl_anc_unique {Bl : Node → Prop} {y1 y2 z : Node} (h1 : Bl y1) (h2 : Bl y2)
    (hp1 : y1 <+: z) (hp2 : y2 <+: z) (hn1 : z ≠ y1) (hn2 : z ≠ y2)
    (hc1 : ∀ u, y1 <+: u → u <+: z → u ≠ y1 → u ≠ z → ¬ Bl u)
    (hc2 : ∀ u, y2 <+: u → u <+: z → u ≠ y2 → u ≠ z → ¬ Bl u) : y1 = y2 := by
  rcases lt_trichotomy y1.length y2.length with hl | hl | hl
  · exact absurd h2 (hc1 y2 (List.prefix_of_prefix_length_le hp1 hp2 hl.le) hp2
      (fun he => by rw [he] at hl; omega) (Ne.symm hn2))
  · exact prefix_eq_of_length hp1 hp2 hl
  · exact absurd h1 (hc2 y1 (List.prefix_of_prefix_length_le hp2 hp1 hl.le) hp1
      (fun he => by rw [he] at hl; omega) (Ne.symm hn1))

open Classical in
/-- **補題 M4（数え上げの形）.** `i_y + d_y = |openBelow L P y|`（`y ∈ P`）なら
`#{y : i_y ≡ 2 (mod 4), i_y ≥ 6} ≤ #{y : i_y = 2} + #{y : d_y ≥ 1}`。
`d_y = 0` の左辺の `y` に深さ `L − 1` の `P` の点 `y''` を単射で対応させる（`y''` は `i + d = 2`）。 -/
theorem m4_count {P : Finset Node} {L : ℕ} (i d : Node → ℕ)
    (hid : ∀ y ∈ P, i y + d y = (openBelow L (fun x => x ∈ P) y).card) :
    (P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).card ≤
      (P.filter (fun y => i y = 2)).card + (P.filter (fun y => 1 ≤ d y)).card := by
  have hex : ∀ y ∈ (P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).filter (fun y => d y = 0),
      ∃ z, z ∈ P ∧ z.length + 1 = L ∧ y <+: z ∧ z ≠ y ∧
        ∀ u, y <+: u → u <+: z → u ≠ y → u ≠ z → ¬ u ∈ P := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_filter] at hy
    obtain ⟨⟨hyP, hm, h6⟩, hd0⟩ := hy
    have hc := hid y hyP
    rw [hd0, add_zero] at hc
    have hlen : y.length + 2 ≤ L := by
      by_contra hl
      rcases (by omega : y.length + 1 = L ∨ L ≤ y.length) with h1 | h1
      · rw [openBelow_card_two h1] at hc; omega
      · rw [openBelow_eq_empty h1] at hc; simp at hc; omega
    obtain ⟨k, hk⟩ : ∃ k, y.length + k + 2 = L := ⟨L - y.length - 2, by omega⟩
    exact openBelow_mod4 L _ k y hk (by rw [← hc]; exact hm)
  choose! φ hφP hφl hφy hφne hφpath using hex
  have hmap : ∀ y ∈ (P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).filter (fun y => d y = 0),
      φ y ∈ P.filter (fun y => i y = 2) ∪
        (P.filter (fun y => 1 ≤ d y)).filter (fun y => ¬ (i y % 4 = 2 ∧ 6 ≤ i y)) := by
    intro y hy
    have hc := hid (φ y) (hφP y hy)
    rw [openBelow_card_two (hφl y hy)] at hc
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    by_cases hd : d (φ y) = 0
    · left; exact ⟨hφP y hy, by omega⟩
    · right; exact ⟨⟨hφP y hy, by omega⟩, by omega⟩
  have hinj : Set.InjOn φ ((P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).filter (fun y => d y = 0) :
      Set Node) := by
    intro y1 hy1 y2 hy2 heq
    have hy1' := Finset.mem_coe.mp hy1
    have hy2' := Finset.mem_coe.mp hy2
    have hP1 : y1 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hy1').1).1
    have hP2 : y2 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hy2').1).1
    have a2 : y2 <+: φ y1 := by rw [heq]; exact hφy y2 hy2'
    have b2 : φ y1 ≠ y2 := by rw [heq]; exact hφne y2 hy2'
    have c2 : ∀ u, y2 <+: u → u <+: φ y1 → u ≠ y2 → u ≠ φ y1 → ¬ u ∈ P := by
      rw [heq]; exact hφpath y2 hy2'
    exact bl_anc_unique (Bl := fun x => x ∈ P) hP1 hP2 (hφy y1 hy1') a2 (hφne y1 hy1') b2
      (hφpath y1 hy1') c2
  have e1 := Finset.card_le_card_of_injOn φ
    (fun y hy => Finset.mem_coe.mpr (hmap y (Finset.mem_coe.mp hy))) hinj
  have e2 := Finset.card_union_le (P.filter (fun y => i y = 2))
    ((P.filter (fun y => 1 ≤ d y)).filter (fun y => ¬ (i y % 4 = 2 ∧ 6 ≤ i y)))
  have e3 := Finset.card_filter_add_card_filter_not
    (s := P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)) (fun y => d y = 0)
  have e4 : ((P.filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).filter (fun y => ¬ d y = 0)).card ≤
      ((P.filter (fun y => 1 ≤ d y)).filter (fun y => i y % 4 = 2 ∧ 6 ≤ i y)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨⟨hy.1.1, by omega⟩, hy.1.2⟩
  have e5 := Finset.card_filter_add_card_filter_not (s := P.filter (fun y => 1 ≤ d y))
    (fun y => i y % 4 = 2 ∧ 6 ≤ i y)
  omega

/-! ## 区域ごとの算術 -/

/-- 段 2 の双対の条件（区域 `Z_y` ごと）。`j ≥ 1` の各列（`R_w` を `j` 個持つ `Z'`）と `ρ` の列，`λS ≤ Xs`。 -/
def M4RDual (s X q μ₁ μ₂ lC lS ν : ℕ) : Prop :=
  (∀ j, 1 ≤ j → min (min (s * (X * j)) (μ₁ * q + μ₂ * X * j)) (q * q) ≤ lC + lS * j + ν * (j % 2)) ∧
    X * s + ν ≤ lC + lS ∧ lS ≤ X * s

/-- **段 3 → 段 2 の区域ごとの算術.** `G ≤ μ₁A + μ₂Kk`，`G ≤ s·Kk`，`G ≤ q·A`，`A + β ≤ q`，
`Kk + β ≤ n ≤ Xj + t` と段 2 の双対から `sβ + G ≤ λC·min(j, 1) + λS·j + ν·(j mod 2) + s·t`。 -/
theorem m4r_u_arith {s q X μ₁ μ₂ lC lS ν β A Kk G n j t : ℕ}
    (hs : μ₁ + μ₂ = s) (hq : q = μ₁ + 2 * μ₂) (hD : M4RDual s X q μ₁ μ₂ lC lS ν)
    (hGa : G ≤ μ₁ * A + μ₂ * Kk) (hGb : G ≤ s * Kk) (hGc : G ≤ q * A)
    (hAq : A + β ≤ q) (hKn : Kk + β ≤ n) (hn : n ≤ X * j + t) :
    s * β + G ≤ lC * min j 1 + lS * j + ν * (j % 2) + s * t := by
  have B1 : s * β + G ≤ s * (X * j) + s * t := by
    have e1 : s * (Kk + β) ≤ s * (X * j + t) := Nat.mul_le_mul_left _ (hKn.trans hn)
    have e2 : s * (Kk + β) = s * β + s * Kk := by ring
    have e3 : s * (X * j + t) = s * (X * j) + s * t := by ring
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
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have e : s * (X * 0) = 0 := by ring
    have g : lC * min 0 1 + lS * 0 + ν * (0 % 2) + s * t = s * t := by
      rw [show min 0 1 = 0 from rfl, show (0 : ℕ) % 2 = 0 from rfl]; ring
    omega
  · have hm := hD.1 j hj
    have hmin : min j 1 = 1 := by omega
    rw [hmin, mul_one]
    have : s * β + G ≤ min (min (s * (X * j)) (μ₁ * q + μ₂ * X * j)) (q * q) + s * t := by
      rcases min_cases (min (s * (X * j)) (μ₁ * q + μ₂ * X * j)) (q * q) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        rcases min_cases (s * (X * j)) (μ₁ * q + μ₂ * X * j) with ⟨h2, -⟩ | ⟨h2, -⟩
        · rw [h2]; exact B1
        · rw [h2]; exact B2
      · rw [h1]; omega
    omega

open Classical in
/-- **定理 L4r の組合せ部分（`h = 4H + r`）.** -/
theorem m4r_zone_sum_le {ms : ℕ → Move} {H r c : ℕ} (hH : 1 ≤ H) (f : Node → ℕ) (g : Node → Node → ℕ)
    (q μ₁ μ₂ μC μS ν₁ κ NU : ℕ)
    (hs : μ₁ + μ₂ = 2 ^ H - 1) (hq : q = μ₁ + 2 * μ₂)
    (hdual : ∀ i, ∃ lC lS ν, M4RDual (2 ^ H - 1) (2 ^ H) q μ₁ μ₂ lC lS ν ∧ ν ≤ NU ∧
      lC * q + lS * 2 ^ H * i + κ * (if i = 2 then 1 else 0) ≤
        μC * min i 1 + μS * i + ν₁ * (i % 2) + κ * (if i % 4 = 2 ∧ 6 ≤ i then 1 else 0))
    (hρ0 : 2 ^ H * (2 ^ H * (2 ^ H - 1)) + ν₁ + κ ≤ μC + μS)
    (hK1 : ∀ y ∈ pebSet (4 * H + r) ms c, (zoneK ms (4 * H + r) c f y).card ≤ q)
    (hK2 : ∀ y ∈ pebSet (4 * H + r) ms c, ∀ u ∈ zoneK ms (4 * H + r) c f y,
      (zoneK2 ms (4 * H + r) c f g y u).card ≤ q) :
    ∑ y ∈ pebSet (4 * H + r) ms c, ∑ u ∈ zoneK ms (4 * H + r) c f y,
        ∑ v ∈ zoneK2 ms (4 * H + r) c f g y u,
          min (childZone ms (childZone ms (childZone ms (nodes (4 * H + r)) c y) (f y) u)
            (g y u) v).card q
      ≤ (2 ^ (3 * H + r) - 1) + (2 ^ H - 1) * (pebSet (4 * H + r) ms c).card
        + (2 ^ H - 1) * ∑ y ∈ pebSet (4 * H + r) ms c, (zoneK ms (4 * H + r) c f y).card
        + (2 ^ H - 1) * 2 ^ H * (pebSet (4 * H + r) ms c).card
        + μC * (pebSet (4 * H + r) ms c).card + μS * 2 ^ (H + r)
        + NU * (pebSet (4 * H + r) ms c).card := by
  -- 記法
  obtain ⟨h, hh⟩ : ∃ h, h = 4 * H + r := ⟨_, rfl⟩
  rw [← hh]
  rw [← hh] at hK1 hK2
  obtain ⟨Z3, hZ3⟩ : ∃ Z3 : Node → Node → Node → Finset Node,
      ∀ y u v, Z3 y u v = childZone ms (childZone ms (childZone ms (nodes h) c y) (f y) u) (g y u) v :=
    ⟨_, fun _ _ _ => rfl⟩
  simp only [← hZ3]
  obtain ⟨P, hP⟩ : ∃ P, P = pebSet h ms c := ⟨_, rfl⟩
  rw [← hP]
  rw [← hP] at hK1 hK2
  have memP : ∀ y, y ∈ P ↔ y ≠ [] ∧ y.length < h ∧ st ms c y = .pebble := by
    intro y; rw [hP]; exact mem_pebSet
  obtain ⟨Z, hZ⟩ : ∃ Z : Node → Finset Node, ∀ y, Z y = childZone ms (nodes h) c y :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K2 : Node → Node → Finset Node, ∀ y u, K2 y u = zoneK2 ms h c f g y u :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Node → Finset Node, ∀ y, K y = zoneK ms h c f y := ⟨_, fun _ => rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2 : Node → Node → Finset Node,
      ∀ y u, Z2 y u = childZone ms (childZone ms (nodes h) c y) (f y) u := ⟨_, fun _ _ => rfl⟩
  simp only [← hK2def, ← hKdef]
  simp only [← hK2def, ← hKdef] at hK1 hK2
  have memK : ∀ y x, x ∈ K y ↔ x ∈ Z y ∧ st ms (f y) x = .pebble := by
    intro y x; rw [hKdef, hZ, mem_zoneK]
  have memK2 : ∀ y u x, x ∈ K2 y u ↔ x ∈ Z2 y u ∧ st ms (g y u) x = .pebble := by
    intro y u x; rw [hK2def, hZ2, mem_zoneK2]
  have hZ2Z : ∀ y u, Z2 y u ⊆ Z y := by
    intro y u; rw [hZ2, hZ]; exact childZone_subset
  have hZ3Z2 : ∀ y u v, Z3 y u v ⊆ Z2 y u := by
    intro y u v; rw [hZ3, hZ2]; exact childZone_subset
  have hZ3Z : ∀ y u v, Z3 y u v ⊆ Z y := fun y u v => (hZ3Z2 y u v).trans (hZ2Z y u)
  have memZ : ∀ y d, d ∈ Z y ↔ d.length < h ∧ y <+: d ∧ d ≠ y ∧
      ∀ w, y <+: w → w <+: d → w ≠ y → st ms c w ≠ .pebble := by
    intro y d; rw [hZ, mem_childZone, mem_nodes]
  have memZ2 : ∀ y u d, d ∈ Z2 y u ↔ d ∈ Z y ∧ u <+: d ∧ d ≠ u ∧
      ∀ w, u <+: w → w <+: d → w ≠ u → st ms (f y) w ≠ .pebble := by
    intro y u d; rw [hZ2, hZ, mem_childZone]
  have memZ3 : ∀ y u v d, d ∈ Z3 y u v ↔ d ∈ Z2 y u ∧ v <+: d ∧ d ≠ v ∧
      ∀ w, v <+: w → w <+: d → w ≠ v → st ms (g y u) w ≠ .pebble := by
    intro y u v d; rw [hZ3, hZ2, mem_childZone]
  have hZ2c : ∀ y u, Z2 y u = childZone ms (Z y) (f y) u := by
    intro y u; rw [hZ2, hZ]
  -- 区域は互いに素
  have hdisjZ : ∀ y ∈ P, ∀ y' ∈ P, y ≠ y' → Disjoint (Z y) (Z y') := by
    intro y hy y' hy' hne
    rw [hZ, hZ]
    exact childZone_disjoint ((memP y).mp hy).2.2 ((memP y').mp hy').2.2 hne
  have hdisjZ2 : ∀ y, ∀ u ∈ K y, ∀ u' ∈ K y, u ≠ u' → Disjoint (Z2 y u) (Z2 y u') := by
    intro y u hu u' hu' hne
    rw [hZ2, hZ2]
    exact childZone_disjoint ((memK y u).mp hu).2 ((memK y u').mp hu').2 hne
  have hdisjZ3 : ∀ y u, ∀ v ∈ K2 y u, ∀ v' ∈ K2 y u, v ≠ v' → Disjoint (Z3 y u v) (Z3 y u v') := by
    intro y u v hv v' hv' hne
    rw [hZ3, hZ3]
    exact childZone_disjoint ((memK2 y u v).mp hv).2 ((memK2 y u v').mp hv').2 hne
  -- 大きさ
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ H := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s, s = 2 ^ H - 1 := ⟨_, rfl⟩
  rw [← hsd, ← hX]
  have hs' : μ₁ + μ₂ = s := by omega
  rw [← hsd, ← hX] at hdual hρ0
  -- D（深さ 3H+r）、Rb（深さ 2H+r）、Yb（深さ H+r）
  obtain ⟨D, hD⟩ : ∃ D : Finset Node, D = words (3 * H + r) := ⟨_, rfl⟩
  have memD : ∀ x, x ∈ D ↔ x.length = 3 * H + r := by intro x; rw [hD, mem_words]
  obtain ⟨Rb, hRb⟩ : ∃ Rb : Finset Node, Rb = words (2 * H + r) := ⟨_, rfl⟩
  have memRb : ∀ x, x ∈ Rb ↔ x.length = 2 * H + r := by intro x; rw [hRb, mem_words]
  obtain ⟨Yb, hYb⟩ : ∃ Yb : Finset Node, Yb = words (H + r) := ⟨_, rfl⟩
  have memYb : ∀ x, x ∈ Yb ↔ x.length = H + r := by intro x; rw [hYb, mem_words]
  have hYbcard : Yb.card = 2 ^ (H + r) := by rw [hYb, card_words]
  have hSx : ∀ x ∈ D, (subtree h x).card = s := by
    intro x hx
    rw [card_subtree, (memD x).mp hx, show h - (3 * H + r) = H by omega, hsd]
  -- R_w の中の S_x は X 個以下、Y_v の中の R_w は X 個以下
  have hDinR : ∀ w ∈ Rb, (D.filter (fun x => w <+: x)).card ≤ X := by
    intro w hw
    rw [hD, hX, show 3 * H + r = (2 * H + r) + H by ring]
    exact card_words_prefix_le ((memRb w).mp hw)
  have hRinY : ∀ w ∈ Yb, (Rb.filter (fun x => w <+: x)).card ≤ X := by
    intro w hw
    rw [hRb, hX, show 2 * H + r = (H + r) + H by ring]
    exact card_words_prefix_le ((memYb w).mp hw)
  -- 汚れ
  obtain ⟨Pd, hPd⟩ : ∃ Pd : Node → Prop, ∀ x, Pd x ↔ ∃ z ∈ P, x <+: z := ⟨_, fun _ => Iff.rfl⟩
  have hPd_anc : ∀ y ∈ P, ∀ x, x <+: y → Pd x := fun y hy x hxy => (hPd x).mpr ⟨y, hy, hxy⟩
  -- Z_y の点の祖先は（P 汚れでなければ）Z_y に入る
  have hinZ : ∀ y ∈ P, ∀ d x, d ∈ Z y → x <+: d → ¬ Pd x → x ∈ Z y := by
    intro y hy d x hd hxd hxP
    rw [hZ] at hd ⊢
    exact zone_mem_of_prefix hd hxd (fun hxy => hxP (hPd_anc y hy x hxy))
  -- Z'_{y,u} の点の祖先は（P・K₁ 汚れでなければ）Z'_{y,u} に入る
  have hinZ2 : ∀ y ∈ P, ∀ u ∈ K y, ∀ d x, d ∈ Z2 y u → x <+: d → ¬ Pd x →
      ¬ (∃ z ∈ K y, x <+: z) → x ∈ Z2 y u := by
    intro y hy u hu d x hd hxd hxP hxK
    have hxZ := hinZ y hy d x (hZ2Z y u hd) hxd hxP
    rw [hZ2c] at hd ⊢
    exact childZone_mem_of_prefix hd hxd (fun hxu => hxK ⟨u, hu, hxu⟩) hxZ
  -- 段 3 の分類
  obtain ⟨Dn, hDn⟩ : ∃ Dn : Finset Node, Dn = D.filter (fun x => ¬ Pd x) := ⟨_, rfl⟩
  obtain ⟨DP, hDP⟩ : ∃ DP : Finset Node, DP = D.filter (fun x => Pd x) := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1 : Node → Finset Node,
      ∀ y, D1 y = Dn.filter (fun x => ∃ z ∈ K y, x <+: z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Dn1, hDn1⟩ : ∃ Dn1 : Node → Finset Node,
      ∀ y, Dn1 y = Dn.filter (fun x => ¬ ∃ z ∈ K y, x <+: z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : Node → Node → Finset Node,
      ∀ y u, Kd y u = (Dn1 y).filter (fun x => ∃ z ∈ K2 y u, x <+: z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Cl, hCl⟩ : ∃ Cl : Node → Node → Finset Node,
      ∀ y u, Cl y u = (Dn1 y).filter (fun x => ¬ ∃ z ∈ K2 y u, x <+: z) := ⟨_, fun _ _ => rfl⟩
  have memDn : ∀ x, x ∈ Dn ↔ x ∈ D ∧ ¬ Pd x := by intro x; rw [hDn, Finset.mem_filter]
  have memDn1 : ∀ y x, x ∈ Dn1 y ↔ (x ∈ D ∧ ¬ Pd x) ∧ ¬ ∃ z ∈ K y, x <+: z := by
    intro y x; rw [hDn1, Finset.mem_filter, memDn]
  have memD1 : ∀ y x, x ∈ D1 y ↔ (x ∈ D ∧ ¬ Pd x) ∧ ∃ z ∈ K y, x <+: z := by
    intro y x; rw [hD1, Finset.mem_filter, memDn]
  have memKd : ∀ y u x, x ∈ Kd y u ↔ ((x ∈ D ∧ ¬ Pd x) ∧ ¬ ∃ z ∈ K y, x <+: z) ∧
      ∃ z ∈ K2 y u, x <+: z := by
    intro y u x; rw [hKd, Finset.mem_filter, memDn1]
  have memCl : ∀ y u x, x ∈ Cl y u ↔ ((x ∈ D ∧ ¬ Pd x) ∧ ¬ ∃ z ∈ K y, x <+: z) ∧
      ¬ ∃ z ∈ K2 y u, x <+: z := by
    intro y u x; rw [hCl, Finset.mem_filter, memDn1]
  -- a y u v x = |Z''_{y,u,v} ∩ S_x|
  obtain ⟨a, ha⟩ : ∃ a : Node → Node → Node → Node → ℕ,
      ∀ y u v x, a y u v x = ((Z3 y u v).filter (fun d => x <+: d)).card := ⟨_, fun _ _ _ _ => rfl⟩
  -- F y u v = きれいな x のうち Z''_{y,u,v} が届くもの
  obtain ⟨F, hF⟩ : ∃ F : Node → Node → Node → Finset Node,
      ∀ y u v, F y u v = (Cl y u).filter (fun x => a y u v x ≠ 0) := ⟨_, fun _ _ _ => rfl⟩
  have hF_anc : ∀ y u v x, x ∈ F y u v → v ∈ K2 y u →
      v <+: x ∧ v.length < x.length ∧ ∃ d ∈ Z3 y u v, x <+: d := by
    intro y u v x hx hv
    rw [hF, Finset.mem_filter, memCl] at hx
    obtain ⟨⟨-, hxK⟩, hax⟩ := hx
    rw [ha] at hax
    obtain ⟨d, hd⟩ := Finset.card_ne_zero.mp hax
    rw [Finset.mem_filter] at hd
    obtain ⟨hdZ, hxd⟩ := hd
    have hvd := ((memZ3 y u v d).mp hdZ).2.1
    by_cases hlen : x.length ≤ v.length
    · exact absurd ⟨v, hv, List.prefix_of_prefix_length_le hxd hvd hlen⟩ hxK
    · exact ⟨List.prefix_of_prefix_length_le hvd hxd (by omega), by omega, d, hdZ, hxd⟩
  -- S_x の中での和
  have hsub_a3 : ∀ y u x, ∑ v ∈ K2 y u, a y u v x ≤ ((Z2 y u).filter (fun d => x <+: d)).card := by
    intro y u x
    have he : ∑ v ∈ K2 y u, a y u v x = ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => x <+: d)).card :=
      Finset.sum_congr rfl (fun v _ => ha y u v x)
    rw [he]
    apply sum_card_le_of_disj
    · intro v hv v' hv' hne
      exact Finset.disjoint_filter_filter (hdisjZ3 y u v hv v' hv' hne)
    · intro v _ d hd
      rw [Finset.mem_filter] at hd ⊢
      exact ⟨hZ3Z2 y u v hd.1, hd.2⟩
  have hsub_a2 : ∀ y x, ∑ u ∈ K y, ((Z2 y u).filter (fun d => x <+: d)).card ≤
      ((Z y).filter (fun d => x <+: d)).card := by
    intro y x
    apply sum_card_le_of_disj
    · intro u hu u' hu' hne
      exact Finset.disjoint_filter_filter (hdisjZ2 y u hu u' hu' hne)
    · intro u _ d hd
      rw [Finset.mem_filter] at hd ⊢
      exact ⟨hZ2Z y u hd.1, hd.2⟩
  have hsub_a : ∀ y x, ∑ u ∈ K y, ∑ v ∈ K2 y u, a y u v x ≤ ((Z y).filter (fun d => x <+: d)).card :=
    fun y x => (Finset.sum_le_sum (fun u _ => hsub_a3 y u x)).trans (hsub_a2 y x)
  have hZy_Sx : ∀ y, ∀ x ∈ D, ((Z y).filter (fun d => x <+: d)).card ≤ s := by
    intro y x hx
    rw [← hSx x hx]
    apply Finset.card_le_card
    intro d hd
    rw [Finset.mem_filter] at hd
    exact mem_subtree.mpr ⟨((memZ y d).mp hd.1).1, hd.2⟩
  have hsum_Sx : ∀ x ∈ D, ∑ y ∈ P, ((Z y).filter (fun d => x <+: d)).card ≤ s := by
    intro x hx
    rw [← hSx x hx]
    apply sum_card_le_of_disj
    · intro y hy y' hy' hne
      exact Finset.disjoint_filter_filter (hdisjZ y hy y' hy' hne)
    · intro y _ d hd
      rw [Finset.mem_filter] at hd
      exact mem_subtree.mpr ⟨((memZ y d).mp hd.1).1, hd.2⟩
  -- (y, u, v) ごとの評価
  have hyuv : ∀ y u v, min (Z3 y u v).card q ≤
      ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card + ∑ x ∈ DP, a y u v x
      + ∑ x ∈ D1 y, a y u v x + ∑ x ∈ Kd y u, a y u v x + min ((F y u v).card * s) q := by
    intro y u v
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z3 y u v)
      (fun d => d.length < 3 * H + r)
    have hN : ((Z3 y u v).filter (fun d => ¬ d.length < 3 * H + r)).card ≤ ∑ x ∈ D, a y u v x := by
      have hsub : (Z3 y u v).filter (fun d => ¬ d.length < 3 * H + r) ⊆
          D.biUnion (fun x => (Z3 y u v).filter (fun d => x <+: d)) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        refine Finset.mem_biUnion.mpr ⟨d.take (3 * H + r), (memD _).mpr ?_,
          Finset.mem_filter.mpr ⟨hd.1, List.take_prefix _ _⟩⟩
        rw [List.length_take]
        omega
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
      exact Finset.sum_congr rfl (fun x _ => (ha y u v x).symm)
    have e1 : ∑ x ∈ D, a y u v x = ∑ x ∈ DP, a y u v x + ∑ x ∈ Dn, a y u v x := by
      rw [hDP, hDn, Finset.sum_filter_add_sum_filter_not]
    have e2 : ∑ x ∈ Dn, a y u v x = ∑ x ∈ D1 y, a y u v x + ∑ x ∈ Dn1 y, a y u v x := by
      rw [hD1, hDn1, Finset.sum_filter_add_sum_filter_not]
    have e3 : ∑ x ∈ Dn1 y, a y u v x = ∑ x ∈ Kd y u, a y u v x + ∑ x ∈ Cl y u, a y u v x := by
      rw [hKd, hCl, Finset.sum_filter_add_sum_filter_not]
    have hCl_le : ∑ x ∈ Cl y u, a y u v x ≤ (F y u v).card * s := by
      have h1 : ∑ x ∈ Cl y u, a y u v x = ∑ x ∈ F y u v, a y u v x := by
        rw [hF y u v]; exact (Finset.sum_filter_ne_zero _).symm
      have h2 := Finset.sum_le_card_nsmul (F y u v) (a y u v) s (by
        intro x hx
        rw [hF, Finset.mem_filter, memCl] at hx
        rw [ha, ← hSx x hx.1.1.1.1]
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_filter] at hd
        exact mem_subtree.mpr ⟨((memZ y d).mp (hZ3Z y u v hd.1)).1, hd.2⟩)
      rw [smul_eq_mul] at h2
      rw [h1]
      exact h2
    generalize (F y u v).card * s = m at hCl_le ⊢
    omega
  -- (y, u) ごとの量
  obtain ⟨β, hβ⟩ : ∃ β : Node → Node → ℕ, ∀ y u, β y u = (Kd y u).card := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Am, hAm⟩ : ∃ Am : Node → Node → ℕ, ∀ y u, Am y u = ∑ v ∈ K2 y u, min (F y u v).card 1 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Kk, hKk⟩ : ∃ Kk : Node → Node → ℕ, ∀ y u, Kk y u = ∑ v ∈ K2 y u, (F y u v).card :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Node → Node → Finset Node, ∀ y u, N y u = (Dn1 y).filter (fun x => x ∈ Z2 y u) :=
    ⟨_, fun _ _ => rfl⟩
  have memN : ∀ y u x, x ∈ N y u ↔ ((x ∈ D ∧ ¬ Pd x) ∧ ¬ ∃ z ∈ K y, x <+: z) ∧ x ∈ Z2 y u := by
    intro y u x; rw [hN, Finset.mem_filter, memDn1]
  obtain ⟨Rc, hRc⟩ : ∃ Rc : Node → Finset Node,
      ∀ y, Rc y = Rb.filter (fun w => ¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z) := ⟨_, fun _ => rfl⟩
  have memRc : ∀ y w, w ∈ Rc y ↔ w ∈ Rb ∧ ¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z := by
    intro y w; rw [hRc, Finset.mem_filter]
  obtain ⟨J, hJ⟩ : ∃ J : Node → Node → Finset Node, ∀ y u, J y u = (Rc y).filter (fun w => w ∈ Z2 y u) :=
    ⟨_, fun _ _ => rfl⟩
  have memJ : ∀ y u w, w ∈ J y u ↔ (w ∈ Rb ∧ ¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z) ∧ w ∈ Z2 y u := by
    intro y u w; rw [hJ, Finset.mem_filter, memRc]
  obtain ⟨Tt, hTt⟩ : ∃ Tt : Node → Node → Finset Node,
      ∀ y u, Tt y u = (N y u).filter (fun x => Pd (x.take (2 * H + r)) ∨
        ∃ z ∈ K y, x.take (2 * H + r) <+: z) := ⟨_, fun _ _ => rfl⟩
  -- (C0) A ≤ Kk
  have hC0 : ∀ y u, Am y u ≤ Kk y u := by
    intro y u; rw [hAm, hKk]
    exact Finset.sum_le_sum (fun v _ => min_le_left _ _)
  -- (C1) A + β ≤ |K'_{y,u}|
  have hC1 : ∀ y ∈ P, ∀ u ∈ K y, Am y u + β y u ≤ q := by
    intro y hy u hu
    have hA1 : Am y u ≤ ((K2 y u).filter (fun v => v.length < 3 * H + r)).card := by
      rw [hAm, Finset.card_filter]
      apply Finset.sum_le_sum
      intro v hv
      by_cases hk : (F y u v).card = 0
      · rw [hk]; simp
      · obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hk
        have h1 := hF_anc y u v x hx hv
        have hxD : x ∈ D := by
          rw [hF, Finset.mem_filter, memCl] at hx; exact hx.1.1.1.1
        rw [if_pos (by rw [(memD x).mp hxD] at h1; exact h1.2.1)]
        exact min_le_right _ _
    have hB1 : β y u ≤ ((K2 y u).filter (fun v => ¬ v.length < 3 * H + r)).card := by
      rw [hβ]
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (3 * H + r) (K2 y u))
      intro x hx
      rw [memKd] at hx
      rw [Finset.mem_filter, ← hD]
      exact ⟨hx.1.1.1, hx.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K2 y u)
      (fun v => v.length < 3 * H + r)
    have := hK2 y hy u hu
    omega
  -- (C2) Kk + β ≤ |N_{y,u}|
  have hC2 : ∀ y ∈ P, ∀ u ∈ K y, Kk y u + β y u ≤ (N y u).card := by
    intro y hy u hu
    have hFd : ((K2 y u : Finset Node) : Set Node).PairwiseDisjoint (F y u) := by
      intro v hv v' hv' hne
      show Disjoint (F y u v) (F y u v')
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨hvx, -, d, hdZ, hxd⟩ := hF_anc y u v x hx hv
      obtain ⟨hvx', -, d', hdZ', hxd'⟩ := hF_anc y u v' x hx' hv'
      have hpv := ((memK2 y u v).mp hv).2
      have hpv' := ((memK2 y u v').mp hv').2
      rcases lt_trichotomy v.length v'.length with hlv | hlv | hlv
      · exact ((memZ3 y u v d).mp hdZ).2.2.2 v' (List.prefix_of_prefix_length_le hvx hvx' hlv.le)
          (hvx'.trans hxd) (Ne.symm hne) hpv'
      · exact hne (prefix_eq_of_length hvx hvx' hlv)
      · exact ((memZ3 y u v' d').mp hdZ').2.2.2 v (List.prefix_of_prefix_length_le hvx' hvx hlv.le)
          (hvx.trans hxd') hne hpv
    have hFsub : (K2 y u).biUnion (F y u) ⊆ (N y u).filter (fun x => ¬ ∃ z ∈ K2 y u, x <+: z) := by
      intro x hx
      obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨-, -, d, hdZ, hxd⟩ := hF_anc y u v x hxv hv
      rw [hF, Finset.mem_filter, memCl] at hxv
      rw [Finset.mem_filter, memN]
      refine ⟨⟨hxv.1.1, ?_⟩, hxv.1.2⟩
      exact hinZ2 y hy u hu d x (hZ3Z2 y u v hdZ) hxd hxv.1.1.1.2 hxv.1.1.2
    have hKdsub : Kd y u ⊆ (N y u).filter (fun x => ∃ z ∈ K2 y u, x <+: z) := by
      intro x hx
      rw [memKd] at hx
      obtain ⟨⟨⟨hxD, hxP⟩, hxK⟩, z, hzK, hxz⟩ := hx
      rw [Finset.mem_filter, memN]
      refine ⟨⟨⟨⟨hxD, hxP⟩, hxK⟩, ?_⟩, z, hzK, hxz⟩
      exact hinZ2 y hy u hu z x ((memK2 y u z).mp hzK).1 hxz hxP hxK
    have e1 := Finset.card_le_card hFsub
    rw [Finset.card_biUnion hFd] at e1
    have e2 := Finset.card_le_card hKdsub
    have e3 := Finset.card_filter_add_card_filter_not (s := N y u) (fun x => ∃ z ∈ K2 y u, x <+: z)
    rw [hKk, hβ]
    omega
  -- (C3) |N_{y,u}| ≤ X j + t
  have hC3 : ∀ y ∈ P, ∀ u ∈ K y, (N y u).card ≤ X * (J y u).card + (Tt y u).card := by
    intro y hy u hu
    have hsp := Finset.card_filter_add_card_filter_not (s := N y u)
      (fun x => Pd (x.take (2 * H + r)) ∨ ∃ z ∈ K y, x.take (2 * H + r) <+: z)
    rw [← hTt] at hsp
    have hsub : (N y u).filter (fun x => ¬ (Pd (x.take (2 * H + r)) ∨
        ∃ z ∈ K y, x.take (2 * H + r) <+: z)) ⊆
        (J y u).biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter, memN] at hx
      obtain ⟨⟨⟨⟨hxD, -⟩, -⟩, hxZ⟩, hw⟩ := hx
      rw [not_or] at hw
      have hxl := (memD x).mp hxD
      refine Finset.mem_biUnion.mpr ⟨x.take (2 * H + r), ?_,
        Finset.mem_filter.mpr ⟨hxD, List.take_prefix _ _⟩⟩
      rw [memJ, memRb, List.length_take]
      refine ⟨⟨by omega, hw.1, hw.2⟩, ?_⟩
      exact hinZ2 y hy u hu x _ hxZ (List.take_prefix _ _) hw.1 hw.2
    have e1 : ((N y u).filter (fun x => ¬ (Pd (x.take (2 * H + r)) ∨
        ∃ z ∈ K y, x.take (2 * H + r) <+: z))).card ≤
        ∑ w ∈ J y u, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ J y u, (D.filter (fun x => w <+: x)).card ≤ (J y u).card * X := by
      have := Finset.sum_le_card_nsmul (J y u) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        exact hDinR w ((memJ y u w).mp hw).1.1)
      rwa [smul_eq_mul] at this
    have e3 : (J y u).card * X = X * (J y u).card := mul_comm _ _
    omega
  -- y ごとの量
  obtain ⟨RK, hRK⟩ : ∃ RK : Node → Finset Node,
      ∀ y, RK y = Rb.filter (fun w => ¬ Pd w ∧ ∃ z ∈ K y, w <+: z) := ⟨_, fun _ => rfl⟩
  have memRK : ∀ y w, w ∈ RK y ↔ w ∈ Rb ∧ ¬ Pd w ∧ ∃ z ∈ K y, w <+: z := by
    intro y w; rw [hRK, Finset.mem_filter]
  obtain ⟨A2, hA2⟩ : ∃ A2 : Node → ℕ, ∀ y, A2 y = ∑ u ∈ K y, min (J y u).card 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨Kk2, hKk2⟩ : ∃ Kk2 : Node → ℕ, ∀ y, Kk2 y = ∑ u ∈ K y, (J y u).card := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Node → Finset Node,
      ∀ y, M y = (Rb.filter (fun w => ¬ Pd w)).filter (fun w => w ∈ Z y) := ⟨_, fun _ => rfl⟩
  have memM : ∀ y w, w ∈ M y ↔ (w ∈ Rb ∧ ¬ Pd w) ∧ w ∈ Z y := by
    intro y w; rw [hM, Finset.mem_filter, Finset.mem_filter]
  obtain ⟨Tau, hTau⟩ : ∃ Tau : Node → Finset Node,
      ∀ y, Tau y = (Dn.filter (fun x => x ∈ Z y)).filter (fun x => Pd (x.take (2 * H + r))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Ib, hIb⟩ : ∃ Ib : Node → Finset Node,
      ∀ y, Ib y = (Yb.filter (fun w => ¬ Pd w)).filter (fun w => w ∈ Z y) := ⟨_, fun _ => rfl⟩
  have memIb : ∀ y w, w ∈ Ib y ↔ (w ∈ Yb ∧ ¬ Pd w) ∧ w ∈ Z y := by
    intro y w; rw [hIb, Finset.mem_filter, Finset.mem_filter]
  obtain ⟨Tt', hTt'⟩ : ∃ Tt' : Node → Finset Node,
      ∀ y, Tt' y = (M y).filter (fun w => Pd (w.take (H + r))) := ⟨_, fun _ => rfl⟩
  have hJZ2 : ∀ y u, J y u ⊆ Z2 y u := by
    intro y u w hw; exact ((memJ y u w).mp hw).2
  -- (T) Σ_u t ≤ X ρ + τ
  have hT : ∀ y ∈ P, ∑ u ∈ K y, (Tt y u).card ≤ X * (RK y).card + (Tau y).card := by
    intro y hy
    obtain ⟨Q, hQ⟩ : ∃ Q : Finset Node, Q = (Dn.filter (fun x => x ∈ Z y)).filter
        (fun x => Pd (x.take (2 * H + r)) ∨ ∃ z ∈ K y, x.take (2 * H + r) <+: z) := ⟨_, rfl⟩
    have e1 : ∑ u ∈ K y, (Tt y u).card ≤ Q.card := by
      apply sum_card_le_of_disj
      · intro u hu u' hu' hne
        show Disjoint (Tt y u) (Tt y u')
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [hTt, Finset.mem_filter, memN] at hx hx'
        exact Finset.disjoint_left.mp (hdisjZ2 y u hu u' hu' hne) hx.1.2 hx'.1.2
      · intro u _ x hx
        rw [hTt, Finset.mem_filter, memN] at hx
        rw [hQ, Finset.mem_filter, Finset.mem_filter, memDn]
        exact ⟨⟨hx.1.1.1, hZ2Z y u hx.1.2⟩, hx.2⟩
    have e2 : Q ⊆ Tau y ∪ D.filter (fun x => x.take (2 * H + r) ∈ RK y) := by
      intro x hx
      rw [hQ, Finset.mem_filter, Finset.mem_filter, memDn] at hx
      obtain ⟨⟨⟨hxD, hxP⟩, hxZ⟩, hw⟩ := hx
      rw [Finset.mem_union]
      by_cases hPw : Pd (x.take (2 * H + r))
      · left
        rw [hTau, Finset.mem_filter, Finset.mem_filter, memDn]
        exact ⟨⟨⟨hxD, hxP⟩, hxZ⟩, hPw⟩
      · right
        have hxl := (memD x).mp hxD
        rw [Finset.mem_filter, memRK, memRb, List.length_take]
        exact ⟨hxD, by omega, hPw, hw.resolve_left hPw⟩
    have e3 : (D.filter (fun x => x.take (2 * H + r) ∈ RK y)).card ≤ X * (RK y).card := by
      have hsub : D.filter (fun x => x.take (2 * H + r) ∈ RK y) ⊆
          (RK y).biUnion (fun w => D.filter (fun x => w <+: x)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_biUnion.mpr ⟨_, hx.2, Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      have := Finset.sum_le_card_nsmul (RK y) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        exact hDinR w ((memRK y w).mp hw).1)
      rw [smul_eq_mul] at this
      have h1 : (D.filter (fun x => x.take (2 * H + r) ∈ RK y)).card ≤
          ∑ w ∈ RK y, (D.filter (fun x => w <+: x)).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have e : (RK y).card * X = X * (RK y).card := mul_comm _ _
      omega
    have e4 := (Finset.card_le_card e2).trans (Finset.card_union_le _ _)
    omega
  -- (S1) A2 + ρ ≤ |K_y|
  have hS1 : ∀ y ∈ P, A2 y + (RK y).card ≤ q := by
    intro y hy
    have hA1 : A2 y ≤ ((K y).filter (fun u => u.length < 2 * H + r)).card := by
      rw [hA2, Finset.card_filter]
      apply Finset.sum_le_sum
      intro u hu
      by_cases hk : (J y u).card = 0
      · rw [hk]; simp
      · obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hk
        obtain ⟨⟨hwR, -, -⟩, hwZ⟩ := (memJ y u w).mp hw
        obtain ⟨-, huw, hwu, -⟩ := (memZ2 y u w).mp hwZ
        have : u.length < w.length :=
          lt_of_le_of_ne huw.length_le (fun he => hwu (huw.eq_of_length he).symm)
        rw [if_pos (by rw [(memRb w).mp hwR] at this; exact this)]
        exact min_le_right _ _
    have hB1 : (RK y).card ≤ ((K y).filter (fun u => ¬ u.length < 2 * H + r)).card := by
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (2 * H + r) (K y))
      intro w hw
      rw [memRK] at hw
      rw [Finset.mem_filter, ← hRb]
      exact ⟨hw.1, hw.2.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K y) (fun u => u.length < 2 * H + r)
    have := hK1 y hy
    omega
  -- (S2) Kk2 + ρ ≤ |M_y|
  have hS2 : ∀ y ∈ P, Kk2 y + (RK y).card ≤ (M y).card := by
    intro y hy
    have hJd : ((K y : Finset Node) : Set Node).PairwiseDisjoint (J y) := by
      intro u hu u' hu' hne
      exact Disjoint.mono (hJZ2 y u) (hJZ2 y u') (hdisjZ2 y u hu u' hu' hne)
    have hJsub : (K y).biUnion (J y) ⊆ (M y).filter (fun w => ¬ ∃ z ∈ K y, w <+: z) := by
      intro w hw
      obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨⟨hwR, hwP, hwK⟩, hwZ⟩ := (memJ y u w).mp hwu
      rw [Finset.mem_filter, memM]
      exact ⟨⟨⟨hwR, hwP⟩, hZ2Z y u hwZ⟩, hwK⟩
    have hRKsub : RK y ⊆ (M y).filter (fun w => ∃ z ∈ K y, w <+: z) := by
      intro w hw
      obtain ⟨hwR, hwP, z, hzK, hwz⟩ := (memRK y w).mp hw
      rw [Finset.mem_filter, memM]
      exact ⟨⟨⟨hwR, hwP⟩, hinZ y hy z w ((memK y z).mp hzK).1 hwz hwP⟩, z, hzK, hwz⟩
    have e1 := Finset.card_le_card hJsub
    rw [Finset.card_biUnion hJd] at e1
    have e2 := Finset.card_le_card hRKsub
    have e3 := Finset.card_filter_add_card_filter_not (s := M y) (fun w => ∃ z ∈ K y, w <+: z)
    rw [hKk2]
    omega
  -- (S3) |M_y| ≤ X i + t'
  have hS3 : ∀ y ∈ P, (M y).card ≤ X * (Ib y).card + (Tt' y).card := by
    intro y hy
    have hsp := Finset.card_filter_add_card_filter_not (s := M y) (fun w => Pd (w.take (H + r)))
    rw [← hTt'] at hsp
    have hsub : (M y).filter (fun w => ¬ Pd (w.take (H + r))) ⊆
        (Ib y).biUnion (fun v => Rb.filter (fun w => v <+: w)) := by
      intro w hw
      rw [Finset.mem_filter, memM] at hw
      obtain ⟨⟨⟨hwR, -⟩, hwZ⟩, hv⟩ := hw
      have hwl := (memRb w).mp hwR
      refine Finset.mem_biUnion.mpr ⟨w.take (H + r), ?_, Finset.mem_filter.mpr ⟨hwR, List.take_prefix _ _⟩⟩
      rw [memIb, memYb, List.length_take]
      exact ⟨⟨by omega, hv⟩, hinZ y hy w _ hwZ (List.take_prefix _ _) hv⟩
    have e1 : ((M y).filter (fun w => ¬ Pd (w.take (H + r)))).card ≤
        ∑ v ∈ Ib y, (Rb.filter (fun w => v <+: w)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have e2 : ∑ v ∈ Ib y, (Rb.filter (fun w => v <+: w)).card ≤ (Ib y).card * X := by
      have := Finset.sum_le_card_nsmul (Ib y) (fun v => (Rb.filter (fun w => v <+: w)).card) X (by
        intro v hv
        exact hRinY v ((memIb y v).mp hv).1.1)
      rwa [smul_eq_mul] at this
    have e3 : (Ib y).card * X = X * (Ib y).card := mul_comm _ _
    omega
  -- y ごとの算術（段 2 → 段 1）
  have hA2K : ∀ y, A2 y ≤ Kk2 y := by
    intro y; rw [hA2, hKk2]
    exact Finset.sum_le_sum (fun u _ => min_le_left _ _)
  -- 大域の量
  -- (G1) Σ t'_y ≤ X ρ₀
  obtain ⟨YP, hYP⟩ : ∃ YP : Finset Node, YP = Yb.filter (fun w => Pd w) := ⟨_, rfl⟩
  obtain ⟨Yc, hYc⟩ : ∃ Yc : Finset Node, Yc = Yb.filter (fun w => ¬ Pd w) := ⟨_, rfl⟩
  have hG1 : ∑ y ∈ P, (Tt' y).card ≤ X * YP.card := by
    have hT1 : ∑ y ∈ P, (Tt' y).card ≤ (Rb.filter (fun w => Pd (w.take (H + r)))).card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (Tt' y) (Tt' y')
        rw [Finset.disjoint_left]
        intro w hw hw'
        rw [hTt', Finset.mem_filter, memM] at hw hw'
        exact Finset.disjoint_left.mp (hdisjZ y hy y' hy' hne) hw.1.2 hw'.1.2
      · intro y _ w hw
        rw [hTt', Finset.mem_filter, memM] at hw
        exact Finset.mem_filter.mpr ⟨hw.1.1.1, hw.2⟩
    have hT2 : Rb.filter (fun w => Pd (w.take (H + r))) ⊆
        YP.biUnion (fun v => Rb.filter (fun w => v <+: w)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hwl := (memRb w).mp hw.1
      refine Finset.mem_biUnion.mpr ⟨w.take (H + r), ?_,
        Finset.mem_filter.mpr ⟨hw.1, List.take_prefix _ _⟩⟩
      rw [hYP, Finset.mem_filter, memYb, List.length_take]
      exact ⟨by omega, hw.2⟩
    have e1 : (Rb.filter (fun w => Pd (w.take (H + r)))).card ≤
        ∑ v ∈ YP, (Rb.filter (fun w => v <+: w)).card :=
      (Finset.card_le_card hT2).trans Finset.card_biUnion_le
    have e2 : ∑ v ∈ YP, (Rb.filter (fun w => v <+: w)).card ≤ YP.card * X := by
      have := Finset.sum_le_card_nsmul YP (fun v => (Rb.filter (fun w => v <+: w)).card) X (by
        intro v hv
        rw [hYP, Finset.mem_filter] at hv
        exact hRinY v hv.1)
      rwa [smul_eq_mul] at this
    have e3 : YP.card * X = X * YP.card := mul_comm _ _
    omega
  -- (G2) Σ i_y + ρ₀ ≤ 2^{H+1}
  have hIZ : ∀ y, Ib y ⊆ Z y := by
    intro y w hw; exact ((memIb y w).mp hw).2
  have hG2 : ∑ y ∈ P, (Ib y).card + YP.card ≤ 2 ^ (H + r) := by
    have h1 : ∑ y ∈ P, (Ib y).card ≤ Yc.card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (Ib y) (Ib y')
        exact Disjoint.mono (hIZ y) (hIZ y') (hdisjZ y hy y' hy' hne)
      · intro y _ w hw
        rw [memIb] at hw
        rw [hYc, Finset.mem_filter]
        exact hw.1
    have h2 := Finset.card_filter_add_card_filter_not (s := Yb) (fun w => Pd w)
    rw [← hYP, ← hYc, hYbcard] at h2
    omega
  -- (G3) #{i_y ≥ 1} ≤ |P ∩ 深さ ≤ H|
  have hG3 : ∑ y ∈ P, min (Ib y).card 1 ≤ (P.filter (fun y => y.length < H + r)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro y hy
    by_cases hj : (Ib y).card = 0
    · rw [hj]; simp
    · obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hj
      rw [memIb, memYb] at hw
      obtain ⟨-, hyw, hne, -⟩ := (memZ y w).mp hw.2
      have : y.length < w.length :=
        lt_of_le_of_ne hyw.length_le (fun he => hne (hyw.eq_of_length he).symm)
      rw [if_pos (by rw [hw.1.1] at this; exact this)]
      exact min_le_right _ _
  -- (G4) ρ₀ ≤ |P ∩ 深さ ≥ H+1|
  have hG4 : YP.card ≤ (P.filter (fun y => ¬ y.length < H + r)).card := by
    refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (H + r) P)
    intro w hw
    rw [hYP, Finset.mem_filter] at hw
    rw [Finset.mem_filter, ← hYb]
    exact ⟨hw.1, (hPd w).mp hw.2⟩
  have hPsplit := Finset.card_filter_add_card_filter_not (s := P) (fun y => y.length < H + r)
  -- (G5) P 汚れの x の数 ≤ |P|
  have hG5 : DP.card ≤ P.card := by
    refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (3 * H + r) P).trans
      (Finset.card_filter_le _ _))
    intro x hx
    rw [hDP, Finset.mem_filter] at hx
    rw [Finset.mem_filter, ← hD]
    exact ⟨hx.1, (hPd x).mp hx.2⟩
  -- (G5') Σ τ_y ≤ X |P|
  have hG5' : ∑ y ∈ P, (Tau y).card ≤ X * P.card := by
    have hT1 : ∑ y ∈ P, (Tau y).card ≤ (D.filter (fun x => Pd (x.take (2 * H + r)))).card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (Tau y) (Tau y')
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [hTau, Finset.mem_filter, Finset.mem_filter] at hx hx'
        exact Finset.disjoint_left.mp (hdisjZ y hy y' hy' hne) hx.1.2 hx'.1.2
      · intro y _ x hx
        rw [hTau, Finset.mem_filter, Finset.mem_filter, memDn] at hx
        exact Finset.mem_filter.mpr ⟨hx.1.1.1, hx.2⟩
    obtain ⟨RP, hRP⟩ : ∃ RP : Finset Node, RP = Rb.filter (fun w => Pd w) := ⟨_, rfl⟩
    have hT2 : D.filter (fun x => Pd (x.take (2 * H + r))) ⊆
        RP.biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxl := (memD x).mp hx.1
      refine Finset.mem_biUnion.mpr ⟨x.take (2 * H + r), ?_,
        Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      rw [hRP, Finset.mem_filter, memRb, List.length_take]
      exact ⟨by omega, hx.2⟩
    have e1 : (D.filter (fun x => Pd (x.take (2 * H + r)))).card ≤
        ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hT2).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card ≤ RP.card * X := by
      have := Finset.sum_le_card_nsmul RP (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hRP, Finset.mem_filter] at hw
        exact hDinR w hw.1)
      rwa [smul_eq_mul] at this
    have e3 : RP.card ≤ P.card := by
      refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (2 * H + r) P).trans
        (Finset.card_filter_le _ _))
      intro w hw
      rw [hRP, Finset.mem_filter] at hw
      rw [Finset.mem_filter, ← hRb]
      exact ⟨hw.1, (hPd w).mp hw.2⟩
    have e4 : RP.card * X ≤ X * P.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ e3
    omega
  -- (G6) U の部分
  have hG6 : ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u,
      ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card ≤ 2 ^ (3 * H + r) - 1 := by
    have h1 : ∀ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u,
        ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card ≤
        ((Z y).filter (fun d => d.length < 3 * H + r)).card := by
      intro y _
      have h1u : ∀ u ∈ K y, ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card ≤
          ((Z2 y u).filter (fun d => d.length < 3 * H + r)).card := by
        intro u _
        apply sum_card_le_of_disj
        · intro v hv v' hv' hne
          exact Finset.disjoint_filter_filter (hdisjZ3 y u v hv v' hv' hne)
        · intro v _ d hd
          rw [Finset.mem_filter] at hd ⊢
          exact ⟨hZ3Z2 y u v hd.1, hd.2⟩
      refine (Finset.sum_le_sum h1u).trans ?_
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
  have hG7 : ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x ≤ DP.card * s := by
    have h1 : ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x =
        ∑ x ∈ DP, ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, a y u v x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    rw [h1]
    have := Finset.sum_le_card_nsmul DP (fun x => ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, a y u v x) s (by
      intro x hx
      rw [hDP, Finset.mem_filter] at hx
      exact (Finset.sum_le_sum (fun y _ => hsub_a y x)).trans (hsum_Sx x hx.1))
    rwa [smul_eq_mul] at this
  -- (G7') K₁ 汚れの部分
  have hG7' : ∀ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ D1 y, a y u v x ≤ s * (K y).card := by
    intro y _
    have h1 : ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ D1 y, a y u v x =
        ∑ x ∈ D1 y, ∑ u ∈ K y, ∑ v ∈ K2 y u, a y u v x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    rw [h1]
    have h2 := Finset.sum_le_card_nsmul (D1 y) (fun x => ∑ u ∈ K y, ∑ v ∈ K2 y u, a y u v x) s (by
      intro x hx
      rw [memD1] at hx
      exact (hsub_a y x).trans (hZy_Sx y x hx.1.1))
    rw [smul_eq_mul] at h2
    have h3 : (D1 y).card ≤ (K y).card := by
      refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (3 * H + r) (K y)).trans
        (Finset.card_filter_le _ _))
      intro x hx
      rw [memD1] at hx
      rw [Finset.mem_filter, ← hD]
      exact ⟨hx.1.1, hx.2⟩
    have h4 : (D1 y).card * s ≤ s * (K y).card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h3
    omega
  -- (G8) K₂ 汚れの部分
  have hG8 : ∀ y u, ∑ v ∈ K2 y u, ∑ x ∈ Kd y u, a y u v x ≤ s * β y u := by
    intro y u
    rw [Finset.sum_comm, hβ, mul_comm]
    have := Finset.sum_le_card_nsmul (Kd y u) (fun x => ∑ v ∈ K2 y u, a y u v x) s (by
      intro x hx
      rw [memKd] at hx
      refine (hsub_a3 y u x).trans ?_
      rw [← hSx x hx.1.1.1]
      apply Finset.card_le_card
      intro d hd
      rw [Finset.mem_filter] at hd
      exact mem_subtree.mpr ⟨((memZ y d).mp (hZ2Z y u hd.1)).1, hd.2⟩)
    rwa [smul_eq_mul] at this
  -- (G9) 頭打ちの部分
  have hG9 : ∀ y u, ∑ v ∈ K2 y u, min ((F y u v).card * s) q ≤ μ₁ * Am y u + μ₂ * Kk y u := by
    intro y u
    rw [hAm, hKk, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    rw [← hs', hq]
    exact odd_min_le μ₁ μ₂ _
  -- (G9') 頭打ちの部分の残りの 2 本
  have hG9b : ∀ y u, ∑ v ∈ K2 y u, min ((F y u v).card * s) q ≤ s * Kk y u := by
    intro y u
    rw [hKk, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [mul_comm s]
    exact min_le_left _ _
  have hG9c : ∀ y u, ∑ v ∈ K2 y u, min ((F y u v).card * s) q ≤ q * Am y u := by
    intro y u
    rw [hAm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rcases Nat.eq_zero_or_pos (F y u v).card with h0 | h0
    · rw [h0]; simp
    · rw [show min (F y u v).card 1 = 1 by omega, mul_one]; exact min_le_right _ _
  -- (y, u) ごとの和
  have hyu_tot : ∀ y u, ∑ v ∈ K2 y u, min (Z3 y u v).card q ≤
      ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card
      + ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x + ∑ v ∈ K2 y u, ∑ x ∈ D1 y, a y u v x
      + (s * β y u + ∑ v ∈ K2 y u, min ((F y u v).card * s) q) := by
    intro y u
    have e1 := Finset.sum_le_sum (fun v (_ : v ∈ K2 y u) => hyuv y u v)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at e1
    have e2 := hG8 y u
    omega
  -- 補助: 区域の祖先，区域の点は P でない
  have hne_nil : ∀ x : Node, 1 ≤ x.length → x ≠ [] := by
    intro x hx he; rw [he] at hx; simp at hx
  have hZanc : ∀ y d x, d ∈ Z y → y <+: x → x <+: d → x ≠ y → x ∈ Z y := by
    intro y d x hd hyx hxd hxy
    obtain ⟨hdl, -, -, hpath⟩ := (memZ y d).mp hd
    exact (memZ y x).mpr ⟨lt_of_le_of_lt hxd.length_le hdl, hyx, hxy,
      fun w h1 h2 h3 => hpath w h1 (h2.trans hxd) h3⟩
  have hZnP : ∀ y d, d ∈ Z y → d ∉ P := by
    intro y d hd hdP
    obtain ⟨-, hyd, hdy, hpath⟩ := (memZ y d).mp hd
    exact hpath d hyd (List.prefix_refl _) hdy ((memP d).mp hdP).2.2
  have hnotP_st : ∀ x : Node, x ≠ [] → x.length < h → x ∉ P → st ms c x ≠ .pebble := by
    intro x hx hxl hxP hst
    exact hxP ((memP x).mpr ⟨hx, hxl, hst⟩)
  have hPdself : ∀ x, ¬ Pd x → x ∉ P :=
    fun x hx hxP => hx ((hPd x).mpr ⟨x, hxP, List.prefix_refl _⟩)
  -- 段 2 の偶奇（区域 Z_y の中で補題 L2）
  obtain ⟨OB2, hOB2⟩ : ∃ OB2 : Node → Node → Finset Node,
      ∀ y u, OB2 y u = openBelow (2 * H + r) (fun x => x ∈ P ∨ x ∈ K y) u := ⟨_, fun _ _ => rfl⟩
  have hJOB : ∀ y ∈ P, ∀ u ∈ K y,
      J y u = (OB2 y u).filter (fun w => ¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z) := by
    intro y hy u hu
    have huZ : u ∈ Z y := ((memK y u).mp hu).1
    obtain ⟨-, hyu, huy, -⟩ := (memZ y u).mp huZ
    have l1 := prefix_ne_length_lt hyu huy
    ext w
    rw [memJ, Finset.mem_filter, hOB2, mem_openBelow, memRb]
    constructor
    · rintro ⟨⟨hwl, hwP, hwK⟩, hwZ⟩
      obtain ⟨hwZy, huw, hwu, hpath2⟩ := (memZ2 y u w).mp hwZ
      refine ⟨⟨hwl, huw, hwu, ?_⟩, hwP, hwK⟩
      intro x hux hxw hxu _ hx
      have hlt := prefix_ne_length_lt hux hxu
      have hxy : x ≠ y := by intro he; rw [he] at hlt; omega
      have hxZ := hZanc y w x hwZy (hyu.trans hux) hxw hxy
      rcases hx with hxP | hxK
      · exact hZnP y x hxZ hxP
      · exact hpath2 x hux hxw hxu ((memK y x).mp hxK).2
    · rintro ⟨⟨hwl, huw, hwu, hcond⟩, hwP, hwK⟩
      have l2 := prefix_ne_length_lt huw hwu
      have hwlh : w.length < h := by omega
      have hwy : w ≠ y := by intro he; rw [he] at l2; omega
      have hwZy : w ∈ Z y := by
        refine (memZ y w).mpr ⟨hwlh, hyu.trans huw, hwy, ?_⟩
        intro x hyx hxw hxy
        by_cases hxl : x.length ≤ u.length
        · have hxu : x <+: u := List.prefix_of_prefix_length_le hxw huw hxl
          exact ((memZ y u).mp huZ).2.2.2 x hyx hxu hxy
        · have hux : u <+: x := List.prefix_of_prefix_length_le huw hxw (by omega)
          have hxlh : x.length < h := lt_of_le_of_lt hxw.length_le hwlh
          by_cases hxw' : x = w
          · rw [hxw']
            exact hnotP_st w (hne_nil w (by omega)) hwlh (hPdself w hwP)
          · exact hnotP_st x (hne_nil x (by omega)) hxlh
              (fun hxP => hcond x hux hxw (fun he => by rw [he] at hxl; omega) hxw' (Or.inl hxP))
      refine ⟨⟨hwl, hwP, hwK⟩, (memZ2 y u w).mpr ⟨hwZy, huw, hwu, ?_⟩⟩
      intro x hux hxw hxu hst
      by_cases hxw' : x = w
      · rw [hxw'] at hst
        exact hwK ⟨w, (memK y w).mpr ⟨hwZy, hst⟩, List.prefix_refl _⟩
      · have hlt := prefix_ne_length_lt hux hxu
        have hxZ : x ∈ Z y := hZanc y w x hwZy (hyu.trans hux) hxw
          (fun he => by rw [he] at hlt; omega)
        exact hcond x hux hxw hxu hxw' (Or.inr ((memK y x).mpr ⟨hxZ, hst⟩))
  obtain ⟨To, hTo⟩ : ∃ To : Node → Finset Node,
      ∀ y, To y = Rb.filter (fun w => Pd w ∧ ∃ u ∈ K y, w ∈ OB2 y u) := ⟨_, fun _ => rfl⟩
  have hpar2 : ∀ y ∈ P, ∑ u ∈ K y, (J y u).card % 2 ≤ (RK y).card + (To y).card := by
    intro y hy
    obtain ⟨Ro, hRo⟩ : ∃ Ro : Node → Finset Node,
        ∀ u, Ro u = (OB2 y u).filter (fun w => ¬ (¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z)) :=
      ⟨_, fun _ => rfl⟩
    have e1 : ∀ u ∈ K y, (J y u).card % 2 ≤ (Ro u).card := by
      intro u hu
      have hsp := Finset.card_filter_add_card_filter_not (s := OB2 y u)
        (fun w => ¬ Pd w ∧ ¬ ∃ z ∈ K y, w <+: z)
      rw [← hJOB y hy u hu, ← hRo] at hsp
      have hev : Even (OB2 y u).card := by rw [hOB2]; exact openBelow_even' _ _ _
      obtain ⟨k, hk⟩ := hev
      omega
    have e2 : ∑ u ∈ K y, (Ro u).card ≤ (RK y ∪ To y).card := by
      apply sum_card_le_of_disj
      · intro u hu u' hu' hne
        show Disjoint (Ro u) (Ro u')
        have hd : Disjoint (OB2 y u) (OB2 y u') := by
          rw [hOB2, hOB2]
          exact openBelow_disjoint (L := 2 * H + r) (Bl := fun x => x ∈ P ∨ x ∈ K y)
            (Or.inr (Finset.mem_coe.mp hu)) (Or.inr (Finset.mem_coe.mp hu')) hne
        rw [hRo, hRo]
        exact Finset.disjoint_filter_filter hd
      · intro u hu w hw
        rw [hRo, Finset.mem_filter] at hw
        obtain ⟨hwO, hwc⟩ := hw
        have hwl : w.length = 2 * H + r := by
          have := hwO; rw [hOB2, mem_openBelow] at this; exact this.1
        rw [Finset.mem_union]
        by_cases hwP : Pd w
        · right; rw [hTo, Finset.mem_filter]; exact ⟨(memRb w).mpr hwl, hwP, u, hu, hwO⟩
        · left; rw [memRK]
          refine ⟨(memRb w).mpr hwl, hwP, ?_⟩
          by_contra hK; exact hwc ⟨hwP, hK⟩
    have e3 := Finset.card_union_le (RK y) (To y)
    have e4 := Finset.sum_le_sum e1
    omega
  have hTo_path : ∀ y ∈ P, ∀ w ∈ To y, y <+: w ∧ w ≠ y ∧
      ∀ x, y <+: x → x <+: w → x ≠ y → x ≠ w → ¬ x ∈ P := by
    intro y hy w hw
    rw [hTo, Finset.mem_filter] at hw
    obtain ⟨-, -, u, hu, hwO⟩ := hw
    rw [hOB2, mem_openBelow] at hwO
    obtain ⟨-, huw, hwu, hcond⟩ := hwO
    have huZ : u ∈ Z y := ((memK y u).mp hu).1
    obtain ⟨-, hyu, huy, -⟩ := (memZ y u).mp huZ
    have l1 := prefix_ne_length_lt hyu huy
    have l2 := prefix_ne_length_lt huw hwu
    refine ⟨hyu.trans huw, fun he => by rw [he] at l2; omega, ?_⟩
    intro x hyx hxw hxy hxw' hxP
    by_cases hxl : x.length ≤ u.length
    · have hxu : x <+: u := List.prefix_of_prefix_length_le hxw huw hxl
      exact hZnP y x (hZanc y u x huZ hyx hxu hxy) hxP
    · have hux : u <+: x := List.prefix_of_prefix_length_le huw hxw (by omega)
      exact hcond x hux hxw (fun he => by rw [he] at hxl; omega) hxw' (Or.inl hxP)
  have hTo_sum : ∑ y ∈ P, (To y).card ≤ P.card := by
    obtain ⟨RP, hRP⟩ : ∃ RP : Finset Node, RP = Rb.filter (fun w => Pd w) := ⟨_, rfl⟩
    have e1 : ∑ y ∈ P, (To y).card ≤ RP.card := by
      apply sum_card_le_of_disj
      · intro y hy y' hy' hne
        show Disjoint (To y) (To y')
        rw [Finset.disjoint_left]
        intro w hw hw'
        obtain ⟨h1, h2, h3⟩ := hTo_path y (Finset.mem_coe.mp hy) w hw
        obtain ⟨h1', h2', h3'⟩ := hTo_path y' (Finset.mem_coe.mp hy') w hw'
        exact hne (bl_anc_unique (Bl := fun x => x ∈ P) (Finset.mem_coe.mp hy)
          (Finset.mem_coe.mp hy') h1 h1' h2 h2' h3 h3')
      · intro y _ w hw
        rw [hTo, Finset.mem_filter] at hw
        rw [hRP, Finset.mem_filter]
        exact ⟨hw.1, hw.2.1⟩
    have e3 : RP.card ≤ P.card := by
      refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (2 * H + r) P).trans
        (Finset.card_filter_le _ _))
      intro w hw
      rw [hRP, Finset.mem_filter] at hw
      rw [Finset.mem_filter, ← hRb]
      exact ⟨hw.1, (hPd w).mp hw.2⟩
    omega
  -- 段 1 の偶奇（補題 L2）と補題 M4
  obtain ⟨OB1, hOB1⟩ : ∃ OB1 : Node → Finset Node,
      ∀ y, OB1 y = openBelow (H + r) (fun x => x ∈ P) y := ⟨_, fun _ => rfl⟩
  have hIbOB : ∀ y ∈ P, Ib y = (OB1 y).filter (fun w => ¬ Pd w) := by
    intro y hy
    ext w
    rw [memIb, Finset.mem_filter, hOB1, mem_openBelow, memYb]
    constructor
    · rintro ⟨⟨hwl, hwP⟩, hwZ⟩
      obtain ⟨-, hyw, hwy, -⟩ := (memZ y w).mp hwZ
      refine ⟨⟨hwl, hyw, hwy, ?_⟩, hwP⟩
      intro x hyx hxw hxy _ hxP
      exact hZnP y x (hZanc y w x hwZ hyx hxw hxy) hxP
    · rintro ⟨⟨hwl, hyw, hwy, hcond⟩, hwP⟩
      have hwlh : w.length < h := by omega
      refine ⟨⟨hwl, hwP⟩, (memZ y w).mpr ⟨hwlh, hyw, hwy, ?_⟩⟩
      intro x hyx hxw hxy
      have hlt := prefix_ne_length_lt hyx hxy
      have hxlh : x.length < h := lt_of_le_of_lt hxw.length_le hwlh
      by_cases hxw' : x = w
      · rw [hxw']; exact hnotP_st w (hne_nil w (by omega)) hwlh (hPdself w hwP)
      · exact hnotP_st x (hne_nil x (by omega)) hxlh (hcond x hyx hxw hxy hxw')
  obtain ⟨dd, hdd⟩ : ∃ dd : Node → ℕ, ∀ y, dd y = ((OB1 y).filter (fun w => Pd w)).card :=
    ⟨_, fun _ => rfl⟩
  have hid : ∀ y ∈ P, (Ib y).card + dd y = (openBelow (H + r) (fun x => x ∈ P) y).card := by
    intro y hy
    rw [hIbOB y hy, hdd, ← hOB1]
    have := Finset.card_filter_add_card_filter_not (s := OB1 y) (fun w => Pd w)
    omega
  have hL2 : ∀ y ∈ P, (Ib y).card % 2 ≤ dd y := by
    intro y hy
    obtain ⟨k, hk⟩ := openBelow_even' (H + r) (fun x => x ∈ P) y
    have := hid y hy
    omega
  have hdsum : ∑ y ∈ P, dd y ≤ YP.card := by
    rw [Finset.sum_congr rfl (fun y _ => hdd y)]
    apply sum_card_le_of_disj
    · intro y hy y' hy' hne
      show Disjoint ((OB1 y).filter (fun w => Pd w)) ((OB1 y').filter (fun w => Pd w))
      apply Finset.disjoint_filter_filter
      rw [hOB1, hOB1]
      exact openBelow_disjoint (Bl := fun x => x ∈ P) (Finset.mem_coe.mp hy)
        (Finset.mem_coe.mp hy') hne
    · intro y _ w hw
      rw [Finset.mem_filter, hOB1, mem_openBelow] at hw
      rw [hYP, Finset.mem_filter, memYb]
      exact ⟨hw.1.1, hw.2⟩
  have hM4 := m4_count (P := P) (L := H + r) (fun y => (Ib y).card) dd hid
  have hDd : (P.filter (fun y => 1 ≤ dd y)).card ≤ ∑ y ∈ P, dd y := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro y _
    split_ifs with h1 <;> omega
  have hL2sum : ∑ y ∈ P, (Ib y).card % 2 ≤ ∑ y ∈ P, dd y := Finset.sum_le_sum hL2
  -- y ごと
  have hy_tot : ∀ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, min (Z3 y u v).card q
      + κ * (if (Ib y).card = 2 then 1 else 0) ≤
      ∑ u ∈ K y, ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card
      + ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x + s * (K y).card
      + s * (Tau y).card + (X * s) * (Tt' y).card + NU * (To y).card
      + (μC * min (Ib y).card 1 + μS * (Ib y).card + ν₁ * ((Ib y).card % 2)
        + κ * (if (Ib y).card % 4 = 2 ∧ 6 ≤ (Ib y).card then 1 else 0)) := by
    intro y hy
    obtain ⟨lC, lS, ν, hD, hνN, hfin⟩ := hdual (Ib y).card
    have hρ' := hD.2.1
    have hlS := hD.2.2
    have e1 : ∀ u ∈ K y, ∑ v ∈ K2 y u, min (Z3 y u v).card q ≤
        ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + r)).card
        + ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x + ∑ v ∈ K2 y u, ∑ x ∈ D1 y, a y u v x
        + (lC * min (J y u).card 1 + lS * (J y u).card + ν * ((J y u).card % 2)
          + s * (Tt y u).card) := by
      intro u hu
      have h1 := hyu_tot y u
      have h2 := m4r_u_arith hs' hq hD (hG9 y u) (hG9b y u) (hG9c y u) (hC1 y hy u hu)
        (hC2 y hy u hu) (hC3 y hy u hu)
      omega
    have e2 := Finset.sum_le_sum e1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at e2
    have e3 : ∑ u ∈ K y, (lC * min (J y u).card 1 + lS * (J y u).card + ν * ((J y u).card % 2)
        + s * (Tt y u).card) = lC * A2 y + lS * Kk2 y + ν * ∑ u ∈ K y, (J y u).card % 2
          + s * ∑ u ∈ K y, (Tt y u).card := by
      rw [hA2, hKk2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e4 := hG7' y hy
    have e5 : s * ∑ u ∈ K y, (Tt y u).card ≤ s * (X * (RK y).card + (Tau y).card) :=
      Nat.mul_le_mul_left _ (hT y hy)
    have e6 : s * (X * (RK y).card + (Tau y).card) = (X * s) * (RK y).card + s * (Tau y).card := by
      ring
    have e7 : ν * ∑ u ∈ K y, (J y u).card % 2 ≤ ν * ((RK y).card + (To y).card) :=
      Nat.mul_le_mul_left _ (hpar2 y hy)
    have e8 : ν * ((RK y).card + (To y).card) = ν * (RK y).card + ν * (To y).card := by ring
    have e9 : (X * s + ν) * (RK y).card ≤ (lC + lS) * (RK y).card := Nat.mul_le_mul_right _ hρ'
    have e10 : lC * (A2 y + (RK y).card) ≤ lC * q := Nat.mul_le_mul_left _ (hS1 y hy)
    have e11 : lS * (Kk2 y + (RK y).card) ≤ lS * (X * (Ib y).card + (Tt' y).card) :=
      Nat.mul_le_mul_left _ ((hS2 y hy).trans (hS3 y hy))
    have e12 : lS * (Tt' y).card ≤ (X * s) * (Tt' y).card := Nat.mul_le_mul_right _ hlS
    have e13 : ν * (To y).card ≤ NU * (To y).card := Nat.mul_le_mul_right _ hνN
    have r1 : (X * s + ν) * (RK y).card = X * s * (RK y).card + ν * (RK y).card := by ring
    have r2 : (lC + lS) * (RK y).card = lC * (RK y).card + lS * (RK y).card := by ring
    have r3 : lC * (A2 y + (RK y).card) = lC * A2 y + lC * (RK y).card := by ring
    have r4 : lS * (Kk2 y + (RK y).card) = lS * Kk2 y + lS * (RK y).card := by ring
    have r5 : lS * (X * (Ib y).card + (Tt' y).card) = lS * X * (Ib y).card + lS * (Tt' y).card := by
      ring
    omega
  -- 全体
  have htot := Finset.sum_le_sum hy_tot
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at htot
  rw [← Finset.card_filter, ← Finset.card_filter] at htot
  -- 最後の算術
  have f1 : (X * s) * ∑ y ∈ P, (Tt' y).card ≤ (X * s) * (X * YP.card) := Nat.mul_le_mul_left _ hG1
  have f2 : (X * s) * (X * YP.card) = (X * (X * s)) * YP.card := by ring
  have f3 : μC * ∑ y ∈ P, min (Ib y).card 1 + μC * YP.card ≤ μC * P.card := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have f4 : μS * ∑ y ∈ P, (Ib y).card + μS * YP.card ≤ μS * 2 ^ (H + r) := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ hG2
  have f5 : DP.card * s ≤ s * P.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hG5
  have f6 : s * ∑ y ∈ P, (Tau y).card ≤ s * (X * P.card) := Nat.mul_le_mul_left _ hG5'
  have f7 : s * (X * P.card) = s * X * P.card := by ring
  have f8 : ν₁ * ∑ y ∈ P, (Ib y).card % 2 ≤ ν₁ * YP.card :=
    Nat.mul_le_mul_left _ (hL2sum.trans hdsum)
  have f9 : κ * (P.filter (fun y => (Ib y).card % 4 = 2 ∧ 6 ≤ (Ib y).card)).card ≤
      κ * ((P.filter (fun y => (Ib y).card = 2)).card + YP.card) :=
    Nat.mul_le_mul_left _ (by have := hDd.trans hdsum; omega)
  have f10 : κ * ((P.filter (fun y => (Ib y).card = 2)).card + YP.card) =
      κ * (P.filter (fun y => (Ib y).card = 2)).card + κ * YP.card := by ring
  have f11 : (X * (X * s) + ν₁ + κ) * YP.card ≤ (μC + μS) * YP.card := Nat.mul_le_mul_right _ hρ0
  have f12 : (X * (X * s) + ν₁ + κ) * YP.card = X * (X * s) * YP.card + ν₁ * YP.card + κ * YP.card := by
    ring
  have f13 : (μC + μS) * YP.card = μC * YP.card + μS * YP.card := by ring
  have f14 : NU * ∑ y ∈ P, (To y).card ≤ NU * P.card := Nat.mul_le_mul_left _ hTo_sum
  omega

end SpookyTree
