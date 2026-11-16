/-
# 定理 L3 の組合せ部分（`h = 3H + 1`）: 段 2 の区域の頭打ちの和 `V*_2 ≤ W_3`

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 2 節（r = 1）。ここは手順を使わない
（時刻 `c` の盤面と、区域ごとの時刻 `f y` の盤面だけの話）。

**主張（`m3_zone_sum_le`）.** 高さ `h = 3H + 1`、`P = pebSet h ms c`、`Z_y = childZone (nodes h) c y`、
`K_y = zoneK ms h c f y`（`Z_y` のうち時刻 `f y` にペブル）、`Z'_{y,u} = childZone Z_y (f y) u` について、
`|K_y| ≤ q`、`μ₁ + μ₂ = s = 2^H − 1`、`q = μ₁ + 2μ₂`、`μC + μS = 2^H·s`、`μ₁q + 2μ₂·2^H ≤ μC + 2μS`、
`μ₂·2^H ≤ μS` なら
  `Σ_y Σ_{u∈K_y} min(|Z'_{y,u}|, q) ≤ (2^{2H+1} − 1) + (s + μC)|P| + μS·2^{H+1}`。
紙の `W_3 = |U| + (p−1)s + μ_C(p−1) + μ_S N_R`（`N_R = 2X`）は `|P| ≤ p − 1` と紙の双対
`μ_C = 2Xs − f_2`、`μ_S = f_2 − Xs` を入れたもの（`WindowM3Lower.lean`）。

**証明の形（紙 2.1・2.2 節を頂点の数え方に直したもの。LP の双対は使わず、乗数で直接まとめる）.**
`D` = 深さ `2H+1` の頂点（`S_x` は `s` 頂点）、`U` = 深さ `≤ 2H` の頂点、`R` = 深さ `H+1` の頂点（`R_w` は
`S_x` を `X = 2^H` 個含む）。`x` が P 汚れ ⇔ `S_x` に `P` の点がある。
* 段 2（`y` ごと）: `x ∈ D` が P 汚れでなく `S_x` に `K_y` の点があれば K 汚れ（`β_y` 個）、どちらでもなければ
  きれい。`k_u` = `Z'_{y,u}` が届くきれいな `x` の数。
  `min(|Z'|, q) ≤ |Z' ∩ U| + Σ_{x P 汚れ} |Z' ∩ S_x| + Σ_{x K 汚れ} |Z' ∩ S_x| + min(k_u s, q)`、
  `min(k s, q) ≤ μ₁ min(k, 1) + μ₂ k`（`odd_min_le`）。
  `Σ_u min(k_u, 1) + β_y ≤ |K_y| ≤ q`、`Σ_u k_u + β_y ≤ n_y`（`n_y` = `Z_y` に入る P 汚れでない `x` の数）。
* 段 1: `j_y` = `Z_y` に入る、`P` の点を持たない `R_w` の数、`t_y` = `Z_y` に入る P 汚れでない `x` のうち
  `R_w` が `P` の点を持つもの。`n_y ≤ X j_y + t_y`。
* `y` ごとの算術（`m3_zone_arith`）: `sβ + μ₁A + μ₂K ≤ μC min(j, 1) + μS j + s t`（`j = 0, 1` は `s n` で、
  `j ≥ 2` は `μ₁ q + μ₂ n` で抑える）。
* 足す: `Σ t_y ≤ Xρ`、`Σ j_y + ρ ≤ 2X`、`#{j_y ≥ 1} + ρ ≤ |P|`（`ρ` = `P` の点を持つ `R_w` の数）、
  `#{P 汚れの x} ≤ |P|`、`sX = μC + μS`。
-/
import SpookyTree.WindowM3LowerRefined

namespace SpookyTree

/-! ## 道具 -/

/-- 互いに素な族が `T` に入れば、大きさの和は `|T|` 以下。 -/
theorem sum_card_le_of_disj {ι : Type*} [DecidableEq ι] {s : Finset ι} {F : ι → Finset Node}
    {T : Finset Node} (hd : (s : Set ι).PairwiseDisjoint F) (hsub : ∀ i ∈ s, F i ⊆ T) :
    ∑ i ∈ s, (F i).card ≤ T.card := by
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- 長さ `L` の `w` の下の、長さ `L + M` の頂点は `2^M` 個以下。 -/
theorem card_words_prefix_le {w : Node} {L M : ℕ} (hw : w.length = L) :
    ((words (L + M)).filter (fun x => w <+: x)).card ≤ 2 ^ M := by
  have hsub : (words (L + M)).filter (fun x => w <+: x) ⊆ (words M).image (fun t => w ++ t) := by
    intro x hx
    rw [Finset.mem_filter, mem_words] at hx
    obtain ⟨hxl, t, rfl⟩ := hx
    refine Finset.mem_image.mpr ⟨t, mem_words.mpr ?_, rfl⟩
    simp at hxl; omega
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq (card_words M)))

open Classical in
/-- 長さ `L` の頂点のうち、`S` の点を下に持つものの数は、`S` の長さ `≥ L` の点の数以下（`take L` の像）。 -/
theorem card_words_dirty_le (L : ℕ) (S : Finset Node) :
    ((words L).filter (fun x => ∃ z ∈ S, x <+: z)).card ≤ (S.filter (fun z => ¬ z.length < L)).card := by
  have hsub : (words L).filter (fun x => ∃ z ∈ S, x <+: z) ⊆
      (S.filter (fun z => ¬ z.length < L)).image (List.take L) := by
    intro x hx
    rw [Finset.mem_filter, mem_words] at hx
    obtain ⟨hxl, z, hzS, hxz⟩ := hx
    refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, ?_⟩, ?_⟩
    · have := hxz.length_le; omega
    · have := List.prefix_iff_eq_take.mp hxz
      rw [hxl] at this
      exact this.symm
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- 区域 `Z_y` の点 `d` の祖先 `x` で、`y` の祖先（`y` 自身を含む）でないものは `Z_y` に入る。 -/
theorem zone_mem_of_prefix {ms : ℕ → Move} {h c : ℕ} {y d x : Node}
    (hd : d ∈ childZone ms (nodes h) c y) (hxd : x <+: d) (hxy : ¬ x <+: y) :
    x ∈ childZone ms (nodes h) c y := by
  obtain ⟨hdn, hyd, -, hpath⟩ := mem_childZone.mp hd
  have hyx : y.length < x.length := by
    by_contra hl
    exact hxy (List.prefix_of_prefix_length_le hxd hyd (by omega))
  have hyx' : y <+: x := List.prefix_of_prefix_length_le hyd hxd hyx.le
  refine mem_childZone.mpr ⟨mem_nodes.mpr (lt_of_le_of_lt hxd.length_le (mem_nodes.mp hdn)), hyx', ?_,
    fun w h1 h2 h3 => hpath w h1 (h2.trans hxd) h3⟩
  intro he; rw [he] at hyx; omega

/-! ## `y` ごとの算術 -/

/-- **段 1 の区域ごとの算術.** `A ≤ Kk`、`A + β ≤ q`、`Kk + β ≤ n ≤ X j + t` のもとで
`sβ + μ₁A + μ₂Kk ≤ μC·min(j, 1) + μS·j + s·t`。 -/
theorem m3_zone_arith {s q X μ₁ μ₂ μC μS β A Kk n j t : ℕ}
    (hs : μ₁ + μ₂ = s) (hCS : μC + μS = X * s)
    (h2 : μ₁ * q + 2 * μ₂ * X ≤ μC + 2 * μS) (h3 : μ₂ * X ≤ μS)
    (hA : A ≤ Kk) (hAq : A + β ≤ q) (hKn : Kk + β ≤ n) (hn : n ≤ X * j + t) :
    s * β + μ₁ * A + μ₂ * Kk ≤ μC * min j 1 + μS * j + s * t := by
  -- 2 通りの上界
  have opt1 : s * β + μ₁ * A + μ₂ * Kk ≤ s * (X * j + t) := by
    have e1 : μ₁ * A ≤ μ₁ * Kk := Nat.mul_le_mul_left _ hA
    have e2 : s * (Kk + β) ≤ s * (X * j + t) := Nat.mul_le_mul_left _ (hKn.trans hn)
    have e3 : s * (Kk + β) = s * β + μ₁ * Kk + μ₂ * Kk := by rw [← hs]; ring
    omega
  have opt2 : s * β + μ₁ * A + μ₂ * Kk ≤ μ₁ * q + μ₂ * (X * j + t) := by
    have e1 : μ₁ * (A + β) ≤ μ₁ * q := Nat.mul_le_mul_left _ hAq
    have e2 : μ₂ * (Kk + β) ≤ μ₂ * (X * j + t) := Nat.mul_le_mul_left _ (hKn.trans hn)
    have e3 : s * β + μ₁ * A + μ₂ * Kk = μ₁ * (A + β) + μ₂ * (Kk + β) := by rw [← hs]; ring
    omega
  rcases Nat.lt_or_ge j 2 with hj | hj
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simpa using opt1
    · have e : s * (X * 1 + t) = X * s + s * t := by ring
      rw [min_self, mul_one, mul_one]
      omega
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    have hm : min (j' + 2) 1 = 1 := by omega
    rw [hm]
    have e1 : μ₂ * X * j' ≤ μS * j' := Nat.mul_le_mul_right _ h3
    have e2 : μ₂ * t ≤ s * t := Nat.mul_le_mul_right _ (by omega)
    have e3 : μ₂ * (X * (j' + 2) + t) = 2 * μ₂ * X + μ₂ * X * j' + μ₂ * t := by ring
    have e4 : μS * (j' + 2) = 2 * μS + μS * j' := by ring
    omega

/-! ## 主補題 -/

open Classical in
/-- **定理 L3 の組合せ部分（`h = 3H + 1`）.** -/
theorem m3_zone_sum_le {ms : ℕ → Move} {H c : ℕ} (f : Node → ℕ) (q μ₁ μ₂ μC μS : ℕ)
    (hs : μ₁ + μ₂ = 2 ^ H - 1) (hq : q = μ₁ + 2 * μ₂)
    (hCS : μC + μS = 2 ^ H * (2 ^ H - 1))
    (h2 : μ₁ * q + 2 * μ₂ * 2 ^ H ≤ μC + 2 * μS) (h3 : μ₂ * 2 ^ H ≤ μS)
    (hK : ∀ y ∈ pebSet (3 * H + 1) ms c, (zoneK ms (3 * H + 1) c f y).card ≤ q) :
    ∑ y ∈ pebSet (3 * H + 1) ms c, ∑ u ∈ zoneK ms (3 * H + 1) c f y,
        min (childZone ms (childZone ms (nodes (3 * H + 1)) c y) (f y) u).card q
      ≤ (2 ^ (2 * H + 1) - 1) + (μ₁ + μ₂ + μC) * (pebSet (3 * H + 1) ms c).card
        + μS * 2 ^ (H + 1) := by
  -- 記法
  obtain ⟨h, hh⟩ : ∃ h, h = 3 * H + 1 := ⟨_, rfl⟩
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
  rw [← hsd, ← hX] at hCS
  -- D（深さ 2H+1）、R（深さ H+1）
  obtain ⟨D, hD⟩ : ∃ D : Finset Node, D = words (2 * H + 1) := ⟨_, rfl⟩
  have memD : ∀ x, x ∈ D ↔ x.length = 2 * H + 1 := by intro x; rw [hD, mem_words]
  obtain ⟨R, hR⟩ : ∃ R : Finset Node, R = words (H + 1) := ⟨_, rfl⟩
  have memR : ∀ x, x ∈ R ↔ x.length = H + 1 := by intro x; rw [hR, mem_words]
  have hRcard : R.card = 2 ^ (H + 1) := by rw [hR, card_words]
  have hSx : ∀ x ∈ D, (subtree h x).card = s := by
    intro x hx
    rw [card_subtree, (memD x).mp hx, show h - (2 * H + 1) = H by omega, hsd]
  -- 汚れ
  obtain ⟨Pd, hPd⟩ : ∃ Pd : Node → Prop, ∀ x, Pd x ↔ ∃ z ∈ P, x <+: z := ⟨_, fun _ => Iff.rfl⟩
  -- y の祖先は P 汚れ
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
  -- a y u x = |Z'_{y,u} ∩ S_x|
  obtain ⟨a, ha⟩ : ∃ a : Node → Node → Node → ℕ,
      ∀ y u x, a y u x = ((Z2 y u).filter (fun d => x <+: d)).card := ⟨_, fun _ _ _ => rfl⟩
  -- F y u = きれいな x のうち Z'_{y,u} が届くもの
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
  -- S_x の中での和
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
      ((Z2 y u).filter (fun d => d.length < 2 * H + 1)).card + ∑ x ∈ DP, a y u x
      + ∑ x ∈ Kd y, a y u x + min ((F y u).card * s) q := by
    intro y _ u _
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z2 y u)
      (fun d => d.length < 2 * H + 1)
    have hN : ((Z2 y u).filter (fun d => ¬ d.length < 2 * H + 1)).card ≤ ∑ x ∈ D, a y u x := by
      have hsub : (Z2 y u).filter (fun d => ¬ d.length < 2 * H + 1) ⊆
          D.biUnion (fun x => (Z2 y u).filter (fun d => x <+: d)) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        refine Finset.mem_biUnion.mpr ⟨d.take (2 * H + 1), (memD _).mpr ?_,
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
  obtain ⟨N, hN⟩ : ∃ N : Node → Finset Node, ∀ y, N y = Dn.filter (fun x => x ∈ Z y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : Finset Node, Rc = R.filter (fun w => ¬ Pd w) := ⟨_, rfl⟩
  obtain ⟨RP, hRP⟩ : ∃ RP : Finset Node, RP = R.filter (fun w => Pd w) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Node → Finset Node, ∀ y, J y = Rc.filter (fun w => w ∈ Z y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ Tt : Node → Finset Node,
      ∀ y, Tt y = (N y).filter (fun x => Pd (x.take (H + 1))) := ⟨_, fun _ => rfl⟩
  have memN : ∀ y x, x ∈ N y ↔ (x ∈ D ∧ ¬ Pd x) ∧ x ∈ Z y := by
    intro y x; rw [hN, Finset.mem_filter, memDn]
  -- (C0) A ≤ Kk
  have hC0 : ∀ y, Am y ≤ Kk y := by
    intro y; rw [hAm, hKk]
    exact Finset.sum_le_sum (fun u _ => min_le_left _ _)
  -- (C1) A + β ≤ |K_y|
  have hC1 : ∀ y ∈ P, Am y + β y ≤ q := by
    intro y hy
    have hA1 : Am y ≤ ((K y).filter (fun u => u.length < 2 * H + 1)).card := by
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
    have hB1 : β y ≤ ((K y).filter (fun u => ¬ u.length < 2 * H + 1)).card := by
      rw [hβ]
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (2 * H + 1) (K y))
      intro x hx
      rw [memKd] at hx
      rw [Finset.mem_filter, ← hD]
      exact ⟨hx.1.1, hx.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K y)
      (fun u => u.length < 2 * H + 1)
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
    -- きれいな x と K 汚れの x は N_y の互いに素な部分集合
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
    have hsp := Finset.card_filter_add_card_filter_not (s := N y) (fun x => Pd (x.take (H + 1)))
    rw [← hTt] at hsp
    have hsub : (N y).filter (fun x => ¬ Pd (x.take (H + 1))) ⊆
        (J y).biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter, memN] at hx
      obtain ⟨⟨⟨hxD, -⟩, hxZ⟩, hw⟩ := hx
      have hxl := (memD x).mp hxD
      refine Finset.mem_biUnion.mpr ⟨x.take (H + 1), ?_, Finset.mem_filter.mpr ⟨hxD, List.take_prefix _ _⟩⟩
      rw [hJ, Finset.mem_filter, hRc, Finset.mem_filter, memR, List.length_take]
      refine ⟨⟨by omega, hw⟩, ?_⟩
      rw [hZ]
      refine zone_mem_of_prefix (d := x) ?_ (List.take_prefix _ _) ?_
      · rw [← hZ]; exact hxZ
      · intro hxy
        exact hw (hPd_anc y hy _ hxy)
    have e1 : ((N y).filter (fun x => ¬ Pd (x.take (H + 1)))).card ≤
        ∑ w ∈ J y, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ J y, (D.filter (fun x => w <+: x)).card ≤ (J y).card * X := by
      have := Finset.sum_le_card_nsmul (J y) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hJ, Finset.mem_filter, hRc, Finset.mem_filter, memR] at hw
        rw [hD, hX, show 2 * H + 1 = (H + 1) + H by ring]
        exact card_words_prefix_le hw.1.1)
      rwa [smul_eq_mul] at this
    have e3 : (J y).card * X = X * (J y).card := mul_comm _ _
    omega
  -- y ごとの算術
  have hyb : ∀ y ∈ P, s * β y + μ₁ * Am y + μ₂ * Kk y ≤
      μC * min (J y).card 1 + μS * (J y).card + s * (Tt y).card := by
    intro y hy
    exact m3_zone_arith hs' hCS h2 h3 (hC0 y) ((hC1 y hy)) (hC2 y hy) (hC3 y hy)
  -- 大域の量
  -- (G1) Σ t_y ≤ X ρ
  have hG1 : ∑ y ∈ P, (Tt y).card ≤ X * RP.card := by
    have hT1 : ∑ y ∈ P, (Tt y).card ≤ (D.filter (fun x => Pd (x.take (H + 1)))).card := by
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
    have hT2 : D.filter (fun x => Pd (x.take (H + 1))) ⊆
        RP.biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxl := (memD x).mp hx.1
      refine Finset.mem_biUnion.mpr ⟨x.take (H + 1), ?_,
        Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      rw [hRP, Finset.mem_filter, memR, List.length_take]
      exact ⟨by omega, hx.2⟩
    have e1 : (D.filter (fun x => Pd (x.take (H + 1)))).card ≤
        ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hT2).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card ≤ RP.card * X := by
      have := Finset.sum_le_card_nsmul RP (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hRP, Finset.mem_filter, memR] at hw
        rw [hD, hX, show 2 * H + 1 = (H + 1) + H by ring]
        exact card_words_prefix_le hw.1)
      rwa [smul_eq_mul] at this
    have e3 : RP.card * X = X * RP.card := mul_comm _ _
    omega
  -- (G2) Σ j_y + ρ ≤ 2^{H+1}
  have hJZ : ∀ y, J y ⊆ Z y := by
    intro y w hw; rw [hJ, Finset.mem_filter] at hw; exact hw.2
  have hG2 : ∑ y ∈ P, (J y).card + RP.card ≤ 2 ^ (H + 1) := by
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
  -- (G3) #{j_y ≥ 1} ≤ |P ∩ 深さ ≤ H|
  have hG3 : ∑ y ∈ P, min (J y).card 1 ≤ (P.filter (fun y => y.length < H + 1)).card := by
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
  -- (G4) ρ ≤ |P ∩ 深さ ≥ H+1|
  have hG4 : RP.card ≤ (P.filter (fun y => ¬ y.length < H + 1)).card := by
    refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (H + 1) P)
    intro w hw
    rw [hRP, Finset.mem_filter] at hw
    rw [Finset.mem_filter, ← hR]
    exact ⟨hw.1, (hPd w).mp hw.2⟩
  have hPsplit := Finset.card_filter_add_card_filter_not (s := P) (fun y => y.length < H + 1)
  -- (G5) P 汚れの x の数 ≤ |P|
  have hG5 : DP.card ≤ P.card := by
    refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (2 * H + 1) P).trans
      (Finset.card_filter_le _ _))
    intro x hx
    rw [hDP, Finset.mem_filter] at hx
    rw [Finset.mem_filter, ← hD]
    exact ⟨hx.1, (hPd x).mp hx.2⟩
  -- (G6) U の部分
  have hG6 : ∑ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 1)).card
      ≤ 2 ^ (2 * H + 1) - 1 := by
    have h1 : ∀ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 1)).card ≤
        ((Z y).filter (fun d => d.length < 2 * H + 1)).card := by
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
  -- (G9) 頭打ちの部分
  have hG9 : ∀ y ∈ P, ∑ u ∈ K y, min ((F y u).card * s) q ≤ μ₁ * Am y + μ₂ * Kk y := by
    intro y _
    rw [hAm, hKk, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    rw [← hs', hq]
    exact odd_min_le μ₁ μ₂ _
  -- 合わせる
  have hstep1 : ∑ y ∈ P, ∑ u ∈ K y, min (Z2 y u).card q ≤
      ∑ y ∈ P, ∑ u ∈ K y, ((Z2 y u).filter (fun d => d.length < 2 * H + 1)).card
      + ∑ y ∈ P, ∑ u ∈ K y, ∑ x ∈ DP, a y u x
      + ∑ y ∈ P, (s * β y + (μ₁ * Am y + μ₂ * Kk y)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y hy
    have e1 := Finset.sum_le_sum (hyu y hy)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
    have e2 := hG8 y hy
    have e3 := hG9 y hy
    omega
  have hstep2 : ∑ y ∈ P, (s * β y + (μ₁ * Am y + μ₂ * Kk y)) ≤
      μC * ∑ y ∈ P, min (J y).card 1 + μS * ∑ y ∈ P, (J y).card + s * ∑ y ∈ P, (Tt y).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y hy
    have := hyb y hy
    omega
  -- 最後の算術
  have e1 : s * ∑ y ∈ P, (Tt y).card ≤ s * (X * RP.card) := Nat.mul_le_mul_left _ hG1
  have e2 : s * (X * RP.card) = μC * RP.card + μS * RP.card := by
    rw [← mul_assoc, mul_comm s X, hCS.symm]; ring
  have e3 : μC * ∑ y ∈ P, min (J y).card 1 + μC * RP.card ≤ μC * P.card := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have e4 : μS * ∑ y ∈ P, (J y).card + μS * RP.card ≤ μS * 2 ^ (H + 1) := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ hG2
  have e5 : DP.card * s ≤ P.card * s := Nat.mul_le_mul_right _ hG5
  have e6 : (μ₁ + μ₂ + μC) * P.card = P.card * s + μC * P.card := by rw [hs']; ring
  omega

end SpookyTree
