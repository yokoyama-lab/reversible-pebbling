/-
# 付記 A の組合せ部分: 段 1 の区域の頭打ちの和 `V` の上界（`h = 2H + 1`）

紙は `notes/spooky-pebbling/tree-gap/CRITIC_WINDOW_UB_2026-11-01.md` の付記 A と、その検算
`CHECK_APPENDIX_A_2026-11-01.md` の 1〜2 節。ここは手順を使わない（ある時刻 `c` の盤面だけの話）。

**主張（`odd_zone_sum_le`）.** 高さ `h = 2H + 1` の完全二分木、時刻 `c` の盤面の根以外のペブルの集合 `P`
（`pebSet`）、`y ∈ P` の区域 `Z_y = childZone ms (nodes h) c y`（`y` の真の子孫で、`y` から下る道
〔`y` を除き自身を含む〕に時刻 `c` のペブルが無いもの）について、`μ₁ + μ₂ = 2^H − 1`、`q = μ₁ + 2μ₂` なら
  `Σ_{y∈P} min(|Z_y|, q) ≤ (2^{H+1} − 1) + μ₁·|P| + μ₂·2^{H+1}`。
付記 A の `W = (N − 1) + (2s − q)(p − 1) + (q − s)N`（`N = 2^{H+1}`、`s = 2^H − 1`）は
`μ₁ = 2s − q`、`μ₂ = q − s`（`s ≤ q ≤ 2s` で非負）、`|P| ≤ p − 1` の場合（LP の双対解）。

**証明の形（付記 A の (a)〜(h) を頂点ごとの数え方に直したもの）.**
`U` = 深さ `≤ H` の頂点（`2^{H+1} − 1` 個）、`D` = 深さ `H + 1` の頂点（`2^{H+1}` 個）、`S_x` = `x ∈ D` の部分木（`s` 頂点）。
`x ∈ D` は `S_x ∩ P ≠ ∅` なら汚れている（`D_d`）、そうでなければきれい（`D_c`）。`a(y, x) = |Z_y ∩ S_x|`、
`F_y = {x ∈ D_c : a(y, x) ≠ 0}`、`k_y = |F_y|`。
* 各 `y`: `min(|Z_y|, q) ≤ |Z_y ∩ U| + min(k_y·s, q) + Σ_{x∈D_d} a(y, x)`（`a(y, x) ≤ s`）。
* `min(k·s, q) ≤ μ₁·min(k, 1) + μ₂·k`（`k = 1` で `s = μ₁ + μ₂`、`k ≥ 2` で `q = μ₁ + 2μ₂`。双対の 2 本の等式）。
* `k_y ≠ 0` なら `y` は深さ `≤ H`（`y` が深ければ `x` が `y` の祖先になり `x` は汚れる）。
* きれいな `x` は高々 1 つの `y` の `F_y` に入る（`S_x` に `P` が無いので、`S_x` の頂点の最も近い `P` の祖先は 1 つ）。
* 汚れた `x` の数 `≤ |P ∖ U|`（`x ↦` その下の `P` の頂点、の逆を `take (H+1)` で取る）。
* 汚れた `x` について `Σ_y a(y, x) ≤ s`（区域は互いに素）。
合わせて `μ₁(|P ∩ U| + |D_d|) + μ₂(Σ k_y + |D_d|) ≤ μ₁|P| + μ₂·2^{H+1}`。
付記 A と違い、「根の子 ∈ P」も `H ≥ 1` も使わない。
-/
import SpookyTree.WindowLower

namespace SpookyTree

/-- 時刻 `c` の盤面の、根以外のペブルの集合（紙の `P = K_0 ∖ {根}`）。 -/
def pebSet (h : ℕ) (ms : ℕ → Move) (c : ℕ) : Finset Node :=
  ((nodes h).filter (fun x => st ms c x = .pebble)).erase []

theorem mem_pebSet {h : ℕ} {ms : ℕ → Move} {c : ℕ} {y : Node} :
    y ∈ pebSet h ms c ↔ y ≠ [] ∧ y.length < h ∧ st ms c y = .pebble := by
  unfold pebSet
  rw [Finset.mem_erase, Finset.mem_filter, mem_nodes]

/-- `min(k·s, q) ≤ μ₁·min(k, 1) + μ₂·k`（`s = μ₁ + μ₂`、`q = μ₁ + 2μ₂`）。双対の 2 本の等式。 -/
theorem odd_min_le (μ₁ μ₂ k : ℕ) :
    min (k * (μ₁ + μ₂)) (μ₁ + 2 * μ₂) ≤ μ₁ * min k 1 + μ₂ * k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp
    · simp only [one_mul, mul_one, min_self]
      omega
  · have h1 : min k 1 = 1 := by omega
    rw [h1, mul_one]
    have : μ₂ * 2 ≤ μ₂ * k := Nat.mul_le_mul_left _ hk
    have := min_le_right (k * (μ₁ + μ₂)) (μ₁ + 2 * μ₂)
    omega

open Classical in
/-- **付記 A の (A1)（LP 双対の形）.** `h = 2H + 1`、`μ₁ + μ₂ = 2^H − 1`、`q = μ₁ + 2μ₂` なら、
時刻 `c` の盤面の根以外のペブル `y` の区域 `Z_y` について
`Σ_y min(|Z_y|, q) ≤ (2^{H+1} − 1) + μ₁·|P| + μ₂·2^{H+1}`。 -/
theorem odd_zone_sum_le {ms : ℕ → Move} {H c : ℕ} (μ₁ μ₂ q : ℕ)
    (hs : μ₁ + μ₂ = 2 ^ H - 1) (hq : q = μ₁ + 2 * μ₂) :
    ∑ y ∈ pebSet (2 * H + 1) ms c, min (childZone ms (nodes (2 * H + 1)) c y).card q
      ≤ (2 ^ (H + 1) - 1) + μ₁ * (pebSet (2 * H + 1) ms c).card + μ₂ * 2 ^ (H + 1) := by
  -- 記法
  obtain ⟨h, hh⟩ : ∃ h, h = 2 * H + 1 := ⟨_, rfl⟩
  rw [← hh]
  obtain ⟨P, hP⟩ : ∃ P, P = pebSet h ms c := ⟨_, rfl⟩
  rw [← hP]
  have memP : ∀ y, y ∈ P ↔ y ≠ [] ∧ y.length < h ∧ st ms c y = .pebble := by
    intro y; rw [hP]; exact mem_pebSet
  obtain ⟨Z, hZ⟩ : ∃ Z : Node → Finset Node, ∀ y, Z y = childZone ms (nodes h) c y :=
    ⟨_, fun _ => rfl⟩
  simp only [← hZ]
  have memZ : ∀ y d, d ∈ Z y ↔ d.length < h ∧ y <+: d ∧ d ≠ y ∧
      ∀ w, y <+: w → w <+: d → w ≠ y → st ms c w ≠ .pebble := by
    intro y d; rw [hZ, mem_childZone, mem_nodes]
  -- 区域は互いに素
  have hdisjZ : ∀ y ∈ P, ∀ y' ∈ P, y ≠ y' → Disjoint (Z y) (Z y') := by
    intro y hy y' hy' hne
    rw [hZ, hZ]
    exact childZone_disjoint ((memP y).mp hy).2.2 ((memP y').mp hy').2.2 hne
  obtain ⟨s, hsd⟩ : ∃ s, s = 2 ^ H - 1 := ⟨_, rfl⟩
  have hs' : s = μ₁ + μ₂ := by omega
  -- 深さ H + 1 の頂点 D（2^{H+1} 個）
  obtain ⟨D, hD⟩ : ∃ D : Finset Node, D = words (H + 1) := ⟨_, rfl⟩
  have memD : ∀ x, x ∈ D ↔ x.length = H + 1 := by intro x; rw [hD, mem_words]
  have hDcard : D.card = 2 ^ (H + 1) := by rw [hD, card_words]
  -- a y x = |Z_y ∩ S_x|
  obtain ⟨a, ha⟩ : ∃ a : Node → Node → ℕ, ∀ y x, a y x = ((Z y).filter (fun d => x <+: d)).card :=
    ⟨_, fun _ _ => rfl⟩
  have hsubS : ∀ (y x : Node), (Z y).filter (fun d => x <+: d) ⊆ subtree h x := by
    intro y x d hd
    rw [Finset.mem_filter] at hd
    exact mem_subtree.mpr ⟨((memZ y d).mp hd.1).1, hd.2⟩
  have hcardS : ∀ x ∈ D, (subtree h x).card = s := by
    intro x hx
    rw [card_subtree, (memD x).mp hx, show h - (H + 1) = H by omega, hsd]
  have ha_le : ∀ y, ∀ x ∈ D, a y x ≤ s := by
    intro y x hx
    rw [ha, ← hcardS x hx]
    exact Finset.card_le_card (hsubS y x)
  -- 汚れた x（S_x ∩ P ≠ ∅）ときれいな x
  obtain ⟨Dd, hDd⟩ : ∃ Dd : Finset Node, Dd = D.filter (fun x => ∃ z ∈ P, x <+: z) := ⟨_, rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : Finset Node, Dc = D.filter (fun x => ¬ ∃ z ∈ P, x <+: z) := ⟨_, rfl⟩
  have hDcd : Dd.card + Dc.card = 2 ^ (H + 1) := by
    rw [hDd, hDc, Finset.card_filter_add_card_filter_not, hDcard]
  have hDd_D : ∀ x ∈ Dd, x ∈ D := by
    intro x hx; rw [hDd] at hx; exact (Finset.mem_filter.mp hx).1
  -- F y = きれいな x のうち Z_y が届くもの
  obtain ⟨F, hF⟩ : ∃ F : Node → Finset Node, ∀ y, F y = Dc.filter (fun x => a y x ≠ 0) :=
    ⟨_, fun _ => rfl⟩
  have hF_D : ∀ y, ∀ x ∈ F y, x ∈ D := by
    intro y x hx
    rw [hF] at hx
    have := (Finset.mem_filter.mp hx).1
    rw [hDc] at this
    exact (Finset.mem_filter.mp this).1
  -- きれいな x に Z_y が届けば、y は x の祖先で深さ H 以下
  have hF_anc : ∀ y ∈ P, ∀ x ∈ F y, y <+: x ∧ y.length < H + 1 ∧ ∃ d ∈ Z y, x <+: d := by
    intro y hy x hx
    rw [hF, Finset.mem_filter, hDc, Finset.mem_filter] at hx
    obtain ⟨⟨hxD, hxc⟩, hax⟩ := hx
    rw [ha] at hax
    obtain ⟨d, hd⟩ := Finset.card_ne_zero.mp hax
    rw [Finset.mem_filter] at hd
    obtain ⟨hdZ, hxd⟩ := hd
    have hyd := ((memZ y d).mp hdZ).2.1
    have hxl := (memD x).mp hxD
    by_cases hl : x.length ≤ y.length
    · exact absurd ⟨y, hy, List.prefix_of_prefix_length_le hxd hyd hl⟩ hxc
    · exact ⟨List.prefix_of_prefix_length_le hyd hxd (by omega), by omega, d, hdZ, hxd⟩
  -- きれいな x は高々 1 つの y に数えられる
  have hF_disj : (P : Set Node).PairwiseDisjoint F := by
    intro y hy y' hy' hne
    show Disjoint (F y) (F y')
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨hyx, -, d, hdZ, hxd⟩ := hF_anc y hy x hx
    obtain ⟨hyx', -, d', hdZ', hxd'⟩ := hF_anc y' hy' x hx'
    have hpy := ((memP y).mp hy).2.2
    have hpy' := ((memP y').mp hy').2.2
    rcases lt_trichotomy y.length y'.length with hl | hl | hl
    · exact ((memZ y d).mp hdZ).2.2.2 y' (List.prefix_of_prefix_length_le hyx hyx' hl.le)
        (hyx'.trans hxd) (Ne.symm hne) hpy'
    · exact hne (prefix_eq_of_length hyx hyx' hl)
    · exact ((memZ y' d').mp hdZ').2.2.2 y (List.prefix_of_prefix_length_le hyx' hyx hl.le)
        (hyx.trans hxd') hne hpy
  have hsumF : ∑ y ∈ P, (F y).card ≤ Dc.card := by
    rw [← Finset.card_biUnion hF_disj]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨y, -, hxy⟩ := Finset.mem_biUnion.mp hx
    rw [hF] at hxy
    exact (Finset.mem_filter.mp hxy).1
  -- 汚れた x の下の区域の合計は s 以下
  have hsum_a : ∀ x ∈ D, ∑ y ∈ P, a y x ≤ s := by
    intro x hx
    have hdisj : (P : Set Node).PairwiseDisjoint (fun y => (Z y).filter (fun d => x <+: d)) := by
      intro y hy y' hy' hne
      exact Finset.disjoint_filter_filter (hdisjZ y hy y' hy' hne)
    have he : ∑ y ∈ P, a y x = (P.biUnion (fun y => (Z y).filter (fun d => x <+: d))).card := by
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_congr rfl (fun y _ => ha y x)
    rw [he, ← hcardS x hx]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨y, -, hdy⟩ := Finset.mem_biUnion.mp hd
    exact hsubS y x hdy
  -- 汚れた x の数 ≤ |P ∖ U|
  have hDd_le : Dd.card ≤ (P.filter (fun y => ¬ y.length < H + 1)).card := by
    have hsub : Dd ⊆ (P.filter (fun y => ¬ y.length < H + 1)).image (List.take (H + 1)) := by
      intro x hx
      rw [hDd, Finset.mem_filter] at hx
      obtain ⟨hxD, z, hzP, hxz⟩ := hx
      have hxl := (memD x).mp hxD
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzP, ?_⟩, ?_⟩
      · have := hxz.length_le; omega
      · have := List.prefix_iff_eq_take.mp hxz
        rw [hxl] at this
        exact this.symm
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- k_y ≠ 0 の y は深さ H 以下
  have hk_le : ∑ y ∈ P, min (F y).card 1 ≤ (P.filter (fun y => y.length < H + 1)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro y hy
    by_cases hk : (F y).card = 0
    · rw [hk]; simp
    · obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hk
      rw [if_pos (hF_anc y hy x hx).2.1]
      exact min_le_right _ _
  have hPsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun y => y.length < H + 1)
  -- 頂点 y ごとの評価
  have hy_bound : ∀ y ∈ P, min (Z y).card q ≤ ((Z y).filter (fun d => d.length < H + 1)).card
      + min ((F y).card * s) q + ∑ x ∈ Dd, a y x := by
    intro y _
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z y)
      (fun d => d.length < H + 1)
    have hN : ((Z y).filter (fun d => ¬ d.length < H + 1)).card ≤ ∑ x ∈ D, a y x := by
      have hsub : (Z y).filter (fun d => ¬ d.length < H + 1) ⊆
          D.biUnion (fun x => (Z y).filter (fun d => x <+: d)) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        refine Finset.mem_biUnion.mpr ⟨d.take (H + 1), (memD _).mpr ?_,
          Finset.mem_filter.mpr ⟨hd.1, List.take_prefix _ _⟩⟩
        rw [List.length_take]
        omega
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
      exact Finset.sum_congr rfl (fun x _ => (ha y x).symm)
    have hDsplit : ∑ x ∈ D, a y x = ∑ x ∈ Dd, a y x + ∑ x ∈ Dc, a y x := by
      rw [hDd, hDc, Finset.sum_filter_add_sum_filter_not]
    have hDc_le : ∑ x ∈ Dc, a y x ≤ (F y).card * s := by
      have h1 : ∑ x ∈ Dc, a y x = ∑ x ∈ F y, a y x := by
        rw [hF y]; exact (Finset.sum_filter_ne_zero _).symm
      have h2 := Finset.sum_le_card_nsmul (F y) (a y) s (fun x hx => ha_le y x (hF_D y x hx))
      rw [smul_eq_mul] at h2
      rw [h1]
      exact h2
    generalize (F y).card * s = m at hDc_le ⊢
    omega
  have hsum1 : ∑ y ∈ P, min (Z y).card q ≤
      ∑ y ∈ P, ((Z y).filter (fun d => d.length < H + 1)).card
      + ∑ y ∈ P, min ((F y).card * s) q + ∑ y ∈ P, ∑ x ∈ Dd, a y x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hy_bound
  -- U の部分
  have hU : ∑ y ∈ P, ((Z y).filter (fun d => d.length < H + 1)).card ≤ 2 ^ (H + 1) - 1 := by
    have hdisj : (P : Set Node).PairwiseDisjoint
        (fun y => (Z y).filter (fun d => d.length < H + 1)) := by
      intro y hy y' hy' hne
      exact Finset.disjoint_filter_filter (hdisjZ y hy y' hy' hne)
    rw [← Finset.card_biUnion hdisj, ← card_nodes]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨y, -, hdy⟩ := Finset.mem_biUnion.mp hd
    exact mem_nodes.mpr (Finset.mem_filter.mp hdy).2
  -- 頭打ちの部分（双対）
  have hmin : ∑ y ∈ P, min ((F y).card * s) q
      ≤ μ₁ * ∑ y ∈ P, min (F y).card 1 + μ₂ * ∑ y ∈ P, (F y).card := by
    have h1 : ∀ y ∈ P, min ((F y).card * s) q ≤ μ₁ * min (F y).card 1 + μ₂ * (F y).card := by
      intro y _
      rw [hs', hq]
      exact odd_min_le μ₁ μ₂ _
    refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- 汚れた x の部分
  have hR : ∑ y ∈ P, ∑ x ∈ Dd, a y x ≤ Dd.card * s := by
    rw [Finset.sum_comm]
    have := Finset.sum_le_card_nsmul Dd (fun x => ∑ y ∈ P, a y x) s
      (fun x hx => hsum_a x (hDd_D x hx))
    rwa [smul_eq_mul] at this
  -- 合わせる
  rw [hs'] at hR
  have e1 := Nat.mul_le_mul_left μ₁ hk_le
  have e2 := Nat.mul_le_mul_left μ₁ hDd_le
  have e3 := Nat.mul_le_mul_left μ₂ hsumF
  have e4 : μ₁ * ((P.filter (fun y => y.length < H + 1)).card +
      (P.filter (fun y => ¬ y.length < H + 1)).card) = μ₁ * P.card := by rw [hPsplit]
  have e5 : μ₂ * (Dd.card + Dc.card) = μ₂ * 2 ^ (H + 1) := by rw [hDcd]
  nlinarith

end SpookyTree
