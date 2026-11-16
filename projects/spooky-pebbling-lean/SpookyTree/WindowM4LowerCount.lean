/-
# 定理 L4 の組合せ部分（`h = 4H + 1`）: 段 3 の区域の頭打ちの和 `V*_3 ≤ W_4`

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4_2026-11.md` の 2 節（r = 1）。手順は使わない
（時刻 `c` の盤面、区域ごとの時刻 `f y`、`g y u` の盤面だけの話）。

**主張（`m4_zone_sum_le`）.** 高さ `h = 4H + 1`、`P = pebSet h ms c`、`Z_y`、`K_y = zoneK`、`Z'_{y,u}`、
`K'_{y,u} = zoneK2`、`Z''_{y,u,v} = childZone Z'_{y,u} (g y u) v` について、`|K_y| ≤ q`、`|K'_{y,u}| ≤ q`、
段 3 の双対 `μ₁ + μ₂ = s = 2^H − 1`、`q = μ₁ + 2μ₂`、段 2 の双対 `λC + λS = X s`、`μ₁ q + 2μ₂ X ≤ λC + 2λS`、
`μ₂ X ≤ λS`、段 1 の双対 `μC + μS = X·X s`、`λC q + 2λS X ≤ μC + 2μS`、`λS X ≤ μS` なら
  `Σ_{y,u,v} min(|Z''|, q) ≤ (2^{3H+1} − 1) + s|P| + s Σ_y |K_y| + sX|P| + μC|P| + μS·2^{H+1}`。
紙の `W_4 = |U| + (p−1)s + (p−1)q s + (p−1)X s + μ_C(p−1) + 2Xμ_S` は `|P| ≤ p − 1`、`|K_y| ≤ q` を入れたもの。

**証明の形（紙 2.1〜2.3 節を頂点の数え方に直したもの。`WindowM3LowerCount.lean` を 1 段伸ばした）.**
`D` = 深さ `3H+1`（`S_x` は `s` 頂点）、`Rb` = 深さ `2H+1`（`R_w` は `S_x` を `X` 個）、`Yb` = 深さ `H+1`
（`Y_v` は `R_w` を `X` 個、全部で `2X` 個）。`x` が P 汚れ ⇔ `x` の下に `P` の点、K₁ 汚れ（`y` ごと）⇔ `K_y` の点、
K₂ 汚れ（`(y, u)` ごと）⇔ `K'_{y,u}` の点。
* 段 3（`(y,u,v)` ごと）: `min(|Z''|, q) ≤ |Z'' ∩ U| + Σ_{P 汚れ} + Σ_{K₁ 汚れ} + Σ_{K₂ 汚れ} + min(k s, q)`。
* 段 3 → 段 2（`(y,u)` ごと）: `m3_zone_arith` で `sβ + μ₁A + μ₂K ≤ λC min(j,1) + λS j + s t`
  （`j` = `Z'_{y,u}` に入るきれいな `R_w`〔P・K₁ 汚れでない〕の数）。
* 段 2 → 段 1（`y` ごと）: `Σ_u t ≤ Xρ_y + τ_y`、`m3_zone_arith`（`s` を `Xs` に）で
  `Xsρ + λC A + λS K ≤ μC min(i,1) + μS i + Xs t'`（`i` = `Z_y` に入る P 汚れでない `Y_v` の数）。
* 段 1: `Σ t' ≤ Xρ₀`、`Σ i + ρ₀ ≤ 2X`、`#{i ≥ 1} + ρ₀ ≤ |P|`、`Σ τ ≤ X|P|`、`X·Xs = μC + μS`。
-/
import SpookyTree.WindowM3LowerCount
import SpookyTree.WindowM4LowerRefined

namespace SpookyTree

/-- 区域 `Z'` の点 `d` の祖先 `x` で、`u` の祖先でなく `Z` に入るものは `Z' = childZone Z f u` に入る。 -/
theorem childZone_mem_of_prefix {ms : ℕ → Move} {Z : Finset Node} {f : ℕ} {u d x : Node}
    (hd : d ∈ childZone ms Z f u) (hxd : x <+: d) (hxu : ¬ x <+: u) (hxZ : x ∈ Z) :
    x ∈ childZone ms Z f u := by
  obtain ⟨-, hud, -, hpath⟩ := mem_childZone.mp hd
  have hux : u.length < x.length := by
    by_contra hl
    exact hxu (List.prefix_of_prefix_length_le hxd hud (by omega))
  have hux' : u <+: x := List.prefix_of_prefix_length_le hud hxd hux.le
  refine mem_childZone.mpr ⟨hxZ, hux', ?_, fun w h1 h2 h3 => hpath w h1 (h2.trans hxd) h3⟩
  intro he; rw [he] at hux; omega

open Classical in
/-- **定理 L4 の組合せ部分（`h = 4H + 1`）.** -/
theorem m4_zone_sum_le {ms : ℕ → Move} {H c : ℕ} (f : Node → ℕ) (g : Node → Node → ℕ)
    (q μ₁ μ₂ lC lS μC μS : ℕ)
    (hs : μ₁ + μ₂ = 2 ^ H - 1) (hq : q = μ₁ + 2 * μ₂)
    (hl : lC + lS = 2 ^ H * (2 ^ H - 1))
    (h2 : μ₁ * q + 2 * μ₂ * 2 ^ H ≤ lC + 2 * lS) (h3 : μ₂ * 2 ^ H ≤ lS)
    (hCS : μC + μS = 2 ^ H * (2 ^ H * (2 ^ H - 1)))
    (h2' : lC * q + 2 * lS * 2 ^ H ≤ μC + 2 * μS) (h3' : lS * 2 ^ H ≤ μS)
    (hK1 : ∀ y ∈ pebSet (4 * H + 1) ms c, (zoneK ms (4 * H + 1) c f y).card ≤ q)
    (hK2 : ∀ y ∈ pebSet (4 * H + 1) ms c, ∀ u ∈ zoneK ms (4 * H + 1) c f y,
      (zoneK2 ms (4 * H + 1) c f g y u).card ≤ q) :
    ∑ y ∈ pebSet (4 * H + 1) ms c, ∑ u ∈ zoneK ms (4 * H + 1) c f y,
        ∑ v ∈ zoneK2 ms (4 * H + 1) c f g y u,
          min (childZone ms (childZone ms (childZone ms (nodes (4 * H + 1)) c y) (f y) u)
            (g y u) v).card q
      ≤ (2 ^ (3 * H + 1) - 1) + (2 ^ H - 1) * (pebSet (4 * H + 1) ms c).card
        + (2 ^ H - 1) * ∑ y ∈ pebSet (4 * H + 1) ms c, (zoneK ms (4 * H + 1) c f y).card
        + (2 ^ H - 1) * 2 ^ H * (pebSet (4 * H + 1) ms c).card
        + μC * (pebSet (4 * H + 1) ms c).card + μS * 2 ^ (H + 1) := by
  -- 記法
  obtain ⟨h, hh⟩ : ∃ h, h = 4 * H + 1 := ⟨_, rfl⟩
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
  rw [← hX] at h2 h3 h2' h3'
  rw [← hsd, ← hX] at hl hCS
  -- D（深さ 3H+1）、Rb（深さ 2H+1）、Yb（深さ H+1）
  obtain ⟨D, hD⟩ : ∃ D : Finset Node, D = words (3 * H + 1) := ⟨_, rfl⟩
  have memD : ∀ x, x ∈ D ↔ x.length = 3 * H + 1 := by intro x; rw [hD, mem_words]
  obtain ⟨Rb, hRb⟩ : ∃ Rb : Finset Node, Rb = words (2 * H + 1) := ⟨_, rfl⟩
  have memRb : ∀ x, x ∈ Rb ↔ x.length = 2 * H + 1 := by intro x; rw [hRb, mem_words]
  obtain ⟨Yb, hYb⟩ : ∃ Yb : Finset Node, Yb = words (H + 1) := ⟨_, rfl⟩
  have memYb : ∀ x, x ∈ Yb ↔ x.length = H + 1 := by intro x; rw [hYb, mem_words]
  have hYbcard : Yb.card = 2 ^ (H + 1) := by rw [hYb, card_words]
  have hSx : ∀ x ∈ D, (subtree h x).card = s := by
    intro x hx
    rw [card_subtree, (memD x).mp hx, show h - (3 * H + 1) = H by omega, hsd]
  -- R_w の中の S_x は X 個以下、Y_v の中の R_w は X 個以下
  have hDinR : ∀ w ∈ Rb, (D.filter (fun x => w <+: x)).card ≤ X := by
    intro w hw
    rw [hD, hX, show 3 * H + 1 = (2 * H + 1) + H by ring]
    exact card_words_prefix_le ((memRb w).mp hw)
  have hRinY : ∀ w ∈ Yb, (Rb.filter (fun x => w <+: x)).card ≤ X := by
    intro w hw
    rw [hRb, hX, show 2 * H + 1 = (H + 1) + H by ring]
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
      ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card + ∑ x ∈ DP, a y u v x
      + ∑ x ∈ D1 y, a y u v x + ∑ x ∈ Kd y u, a y u v x + min ((F y u v).card * s) q := by
    intro y u v
    have hsplit := Finset.card_filter_add_card_filter_not (s := Z3 y u v)
      (fun d => d.length < 3 * H + 1)
    have hN : ((Z3 y u v).filter (fun d => ¬ d.length < 3 * H + 1)).card ≤ ∑ x ∈ D, a y u v x := by
      have hsub : (Z3 y u v).filter (fun d => ¬ d.length < 3 * H + 1) ⊆
          D.biUnion (fun x => (Z3 y u v).filter (fun d => x <+: d)) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        refine Finset.mem_biUnion.mpr ⟨d.take (3 * H + 1), (memD _).mpr ?_,
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
      ∀ y u, Tt y u = (N y u).filter (fun x => Pd (x.take (2 * H + 1)) ∨
        ∃ z ∈ K y, x.take (2 * H + 1) <+: z) := ⟨_, fun _ _ => rfl⟩
  -- (C0) A ≤ Kk
  have hC0 : ∀ y u, Am y u ≤ Kk y u := by
    intro y u; rw [hAm, hKk]
    exact Finset.sum_le_sum (fun v _ => min_le_left _ _)
  -- (C1) A + β ≤ |K'_{y,u}|
  have hC1 : ∀ y ∈ P, ∀ u ∈ K y, Am y u + β y u ≤ q := by
    intro y hy u hu
    have hA1 : Am y u ≤ ((K2 y u).filter (fun v => v.length < 3 * H + 1)).card := by
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
    have hB1 : β y u ≤ ((K2 y u).filter (fun v => ¬ v.length < 3 * H + 1)).card := by
      rw [hβ]
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (3 * H + 1) (K2 y u))
      intro x hx
      rw [memKd] at hx
      rw [Finset.mem_filter, ← hD]
      exact ⟨hx.1.1.1, hx.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K2 y u)
      (fun v => v.length < 3 * H + 1)
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
      (fun x => Pd (x.take (2 * H + 1)) ∨ ∃ z ∈ K y, x.take (2 * H + 1) <+: z)
    rw [← hTt] at hsp
    have hsub : (N y u).filter (fun x => ¬ (Pd (x.take (2 * H + 1)) ∨
        ∃ z ∈ K y, x.take (2 * H + 1) <+: z)) ⊆
        (J y u).biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter, memN] at hx
      obtain ⟨⟨⟨⟨hxD, -⟩, -⟩, hxZ⟩, hw⟩ := hx
      rw [not_or] at hw
      have hxl := (memD x).mp hxD
      refine Finset.mem_biUnion.mpr ⟨x.take (2 * H + 1), ?_,
        Finset.mem_filter.mpr ⟨hxD, List.take_prefix _ _⟩⟩
      rw [memJ, memRb, List.length_take]
      refine ⟨⟨by omega, hw.1, hw.2⟩, ?_⟩
      exact hinZ2 y hy u hu x _ hxZ (List.take_prefix _ _) hw.1 hw.2
    have e1 : ((N y u).filter (fun x => ¬ (Pd (x.take (2 * H + 1)) ∨
        ∃ z ∈ K y, x.take (2 * H + 1) <+: z))).card ≤
        ∑ w ∈ J y u, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ J y u, (D.filter (fun x => w <+: x)).card ≤ (J y u).card * X := by
      have := Finset.sum_le_card_nsmul (J y u) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        exact hDinR w ((memJ y u w).mp hw).1.1)
      rwa [smul_eq_mul] at this
    have e3 : (J y u).card * X = X * (J y u).card := mul_comm _ _
    omega
  -- (y, u) ごとの算術（段 3 → 段 2）
  have hyub : ∀ y ∈ P, ∀ u ∈ K y, s * β y u + μ₁ * Am y u + μ₂ * Kk y u ≤
      lC * min (J y u).card 1 + lS * (J y u).card + s * (Tt y u).card := by
    intro y hy u hu
    exact m3_zone_arith hs' hl h2 h3 (hC0 y u) (hC1 y hy u hu) (hC2 y hy u hu) (hC3 y hy u hu)
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
      ∀ y, Tau y = (Dn.filter (fun x => x ∈ Z y)).filter (fun x => Pd (x.take (2 * H + 1))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Ib, hIb⟩ : ∃ Ib : Node → Finset Node,
      ∀ y, Ib y = (Yb.filter (fun w => ¬ Pd w)).filter (fun w => w ∈ Z y) := ⟨_, fun _ => rfl⟩
  have memIb : ∀ y w, w ∈ Ib y ↔ (w ∈ Yb ∧ ¬ Pd w) ∧ w ∈ Z y := by
    intro y w; rw [hIb, Finset.mem_filter, Finset.mem_filter]
  obtain ⟨Tt', hTt'⟩ : ∃ Tt' : Node → Finset Node,
      ∀ y, Tt' y = (M y).filter (fun w => Pd (w.take (H + 1))) := ⟨_, fun _ => rfl⟩
  have hJZ2 : ∀ y u, J y u ⊆ Z2 y u := by
    intro y u w hw; exact ((memJ y u w).mp hw).2
  -- (T) Σ_u t ≤ X ρ + τ
  have hT : ∀ y ∈ P, ∑ u ∈ K y, (Tt y u).card ≤ X * (RK y).card + (Tau y).card := by
    intro y hy
    obtain ⟨Q, hQ⟩ : ∃ Q : Finset Node, Q = (Dn.filter (fun x => x ∈ Z y)).filter
        (fun x => Pd (x.take (2 * H + 1)) ∨ ∃ z ∈ K y, x.take (2 * H + 1) <+: z) := ⟨_, rfl⟩
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
    have e2 : Q ⊆ Tau y ∪ D.filter (fun x => x.take (2 * H + 1) ∈ RK y) := by
      intro x hx
      rw [hQ, Finset.mem_filter, Finset.mem_filter, memDn] at hx
      obtain ⟨⟨⟨hxD, hxP⟩, hxZ⟩, hw⟩ := hx
      rw [Finset.mem_union]
      by_cases hPw : Pd (x.take (2 * H + 1))
      · left
        rw [hTau, Finset.mem_filter, Finset.mem_filter, memDn]
        exact ⟨⟨⟨hxD, hxP⟩, hxZ⟩, hPw⟩
      · right
        have hxl := (memD x).mp hxD
        rw [Finset.mem_filter, memRK, memRb, List.length_take]
        exact ⟨hxD, by omega, hPw, hw.resolve_left hPw⟩
    have e3 : (D.filter (fun x => x.take (2 * H + 1) ∈ RK y)).card ≤ X * (RK y).card := by
      have hsub : D.filter (fun x => x.take (2 * H + 1) ∈ RK y) ⊆
          (RK y).biUnion (fun w => D.filter (fun x => w <+: x)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_biUnion.mpr ⟨_, hx.2, Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      have := Finset.sum_le_card_nsmul (RK y) (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        exact hDinR w ((memRK y w).mp hw).1)
      rw [smul_eq_mul] at this
      have h1 : (D.filter (fun x => x.take (2 * H + 1) ∈ RK y)).card ≤
          ∑ w ∈ RK y, (D.filter (fun x => w <+: x)).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have e : (RK y).card * X = X * (RK y).card := mul_comm _ _
      omega
    have e4 := (Finset.card_le_card e2).trans (Finset.card_union_le _ _)
    omega
  -- (S1) A2 + ρ ≤ |K_y|
  have hS1 : ∀ y ∈ P, A2 y + (RK y).card ≤ q := by
    intro y hy
    have hA1 : A2 y ≤ ((K y).filter (fun u => u.length < 2 * H + 1)).card := by
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
    have hB1 : (RK y).card ≤ ((K y).filter (fun u => ¬ u.length < 2 * H + 1)).card := by
      refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (2 * H + 1) (K y))
      intro w hw
      rw [memRK] at hw
      rw [Finset.mem_filter, ← hRb]
      exact ⟨hw.1, hw.2.2⟩
    have hsp := Finset.card_filter_add_card_filter_not (s := K y) (fun u => u.length < 2 * H + 1)
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
    have hsp := Finset.card_filter_add_card_filter_not (s := M y) (fun w => Pd (w.take (H + 1)))
    rw [← hTt'] at hsp
    have hsub : (M y).filter (fun w => ¬ Pd (w.take (H + 1))) ⊆
        (Ib y).biUnion (fun v => Rb.filter (fun w => v <+: w)) := by
      intro w hw
      rw [Finset.mem_filter, memM] at hw
      obtain ⟨⟨⟨hwR, -⟩, hwZ⟩, hv⟩ := hw
      have hwl := (memRb w).mp hwR
      refine Finset.mem_biUnion.mpr ⟨w.take (H + 1), ?_, Finset.mem_filter.mpr ⟨hwR, List.take_prefix _ _⟩⟩
      rw [memIb, memYb, List.length_take]
      exact ⟨⟨by omega, hv⟩, hinZ y hy w _ hwZ (List.take_prefix _ _) hv⟩
    have e1 : ((M y).filter (fun w => ¬ Pd (w.take (H + 1)))).card ≤
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
  have hyb : ∀ y ∈ P, (X * s) * (RK y).card + lC * A2 y + lS * Kk2 y ≤
      μC * min (Ib y).card 1 + μS * (Ib y).card + (X * s) * (Tt' y).card := by
    intro y hy
    exact m3_zone_arith hl hCS h2' h3' (hA2K y) (hS1 y hy) (hS2 y hy) (hS3 y hy)
  -- 大域の量
  -- (G1) Σ t'_y ≤ X ρ₀
  obtain ⟨YP, hYP⟩ : ∃ YP : Finset Node, YP = Yb.filter (fun w => Pd w) := ⟨_, rfl⟩
  obtain ⟨Yc, hYc⟩ : ∃ Yc : Finset Node, Yc = Yb.filter (fun w => ¬ Pd w) := ⟨_, rfl⟩
  have hG1 : ∑ y ∈ P, (Tt' y).card ≤ X * YP.card := by
    have hT1 : ∑ y ∈ P, (Tt' y).card ≤ (Rb.filter (fun w => Pd (w.take (H + 1)))).card := by
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
    have hT2 : Rb.filter (fun w => Pd (w.take (H + 1))) ⊆
        YP.biUnion (fun v => Rb.filter (fun w => v <+: w)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hwl := (memRb w).mp hw.1
      refine Finset.mem_biUnion.mpr ⟨w.take (H + 1), ?_,
        Finset.mem_filter.mpr ⟨hw.1, List.take_prefix _ _⟩⟩
      rw [hYP, Finset.mem_filter, memYb, List.length_take]
      exact ⟨by omega, hw.2⟩
    have e1 : (Rb.filter (fun w => Pd (w.take (H + 1)))).card ≤
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
  have hG2 : ∑ y ∈ P, (Ib y).card + YP.card ≤ 2 ^ (H + 1) := by
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
  have hG3 : ∑ y ∈ P, min (Ib y).card 1 ≤ (P.filter (fun y => y.length < H + 1)).card := by
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
  have hG4 : YP.card ≤ (P.filter (fun y => ¬ y.length < H + 1)).card := by
    refine le_trans (Finset.card_le_card ?_) (card_words_dirty_le (H + 1) P)
    intro w hw
    rw [hYP, Finset.mem_filter] at hw
    rw [Finset.mem_filter, ← hYb]
    exact ⟨hw.1, (hPd w).mp hw.2⟩
  have hPsplit := Finset.card_filter_add_card_filter_not (s := P) (fun y => y.length < H + 1)
  -- (G5) P 汚れの x の数 ≤ |P|
  have hG5 : DP.card ≤ P.card := by
    refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (3 * H + 1) P).trans
      (Finset.card_filter_le _ _))
    intro x hx
    rw [hDP, Finset.mem_filter] at hx
    rw [Finset.mem_filter, ← hD]
    exact ⟨hx.1, (hPd x).mp hx.2⟩
  -- (G5') Σ τ_y ≤ X |P|
  have hG5' : ∑ y ∈ P, (Tau y).card ≤ X * P.card := by
    have hT1 : ∑ y ∈ P, (Tau y).card ≤ (D.filter (fun x => Pd (x.take (2 * H + 1)))).card := by
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
    have hT2 : D.filter (fun x => Pd (x.take (2 * H + 1))) ⊆
        RP.biUnion (fun w => D.filter (fun x => w <+: x)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxl := (memD x).mp hx.1
      refine Finset.mem_biUnion.mpr ⟨x.take (2 * H + 1), ?_,
        Finset.mem_filter.mpr ⟨hx.1, List.take_prefix _ _⟩⟩
      rw [hRP, Finset.mem_filter, memRb, List.length_take]
      exact ⟨by omega, hx.2⟩
    have e1 : (D.filter (fun x => Pd (x.take (2 * H + 1)))).card ≤
        ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card :=
      (Finset.card_le_card hT2).trans Finset.card_biUnion_le
    have e2 : ∑ w ∈ RP, (D.filter (fun x => w <+: x)).card ≤ RP.card * X := by
      have := Finset.sum_le_card_nsmul RP (fun w => (D.filter (fun x => w <+: x)).card) X (by
        intro w hw
        rw [hRP, Finset.mem_filter] at hw
        exact hDinR w hw.1)
      rwa [smul_eq_mul] at this
    have e3 : RP.card ≤ P.card := by
      refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (2 * H + 1) P).trans
        (Finset.card_filter_le _ _))
      intro w hw
      rw [hRP, Finset.mem_filter] at hw
      rw [Finset.mem_filter, ← hRb]
      exact ⟨hw.1, (hPd w).mp hw.2⟩
    have e4 : RP.card * X ≤ X * P.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ e3
    omega
  -- (G6) U の部分
  have hG6 : ∑ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u,
      ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card ≤ 2 ^ (3 * H + 1) - 1 := by
    have h1 : ∀ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u,
        ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card ≤
        ((Z y).filter (fun d => d.length < 3 * H + 1)).card := by
      intro y _
      have h1u : ∀ u ∈ K y, ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card ≤
          ((Z2 y u).filter (fun d => d.length < 3 * H + 1)).card := by
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
      refine le_trans (Finset.card_le_card ?_) ((card_words_dirty_le (3 * H + 1) (K y)).trans
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
  -- 合わせる: (y, u) ごと
  have hyu_tot : ∀ y ∈ P, ∀ u ∈ K y, ∑ v ∈ K2 y u, min (Z3 y u v).card q ≤
      ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card
      + ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x + ∑ v ∈ K2 y u, ∑ x ∈ D1 y, a y u v x
      + (lC * min (J y u).card 1 + lS * (J y u).card + s * (Tt y u).card) := by
    intro y hy u hu
    have e1 := Finset.sum_le_sum (fun v (_ : v ∈ K2 y u) => hyuv y u v)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at e1
    have e2 := hG8 y u
    have e3 := hG9 y u
    have e4 := hyub y hy u hu
    omega
  -- y ごと
  have hy_tot : ∀ y ∈ P, ∑ u ∈ K y, ∑ v ∈ K2 y u, min (Z3 y u v).card q ≤
      ∑ u ∈ K y, ∑ v ∈ K2 y u, ((Z3 y u v).filter (fun d => d.length < 3 * H + 1)).card
      + ∑ u ∈ K y, ∑ v ∈ K2 y u, ∑ x ∈ DP, a y u v x + s * (K y).card
      + (μC * min (Ib y).card 1 + μS * (Ib y).card + (X * s) * (Tt' y).card + s * (Tau y).card) := by
    intro y hy
    have e1 := Finset.sum_le_sum (fun u hu => hyu_tot y hy u hu)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at e1
    have e2 : ∑ u ∈ K y, (lC * min (J y u).card 1 + lS * (J y u).card + s * (Tt y u).card) =
        lC * A2 y + lS * Kk2 y + s * ∑ u ∈ K y, (Tt y u).card := by
      rw [hA2, hKk2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    have e3 := hG7' y hy
    have e4 : s * ∑ u ∈ K y, (Tt y u).card ≤ s * (X * (RK y).card + (Tau y).card) :=
      Nat.mul_le_mul_left _ (hT y hy)
    have e5 : s * (X * (RK y).card + (Tau y).card) = (X * s) * (RK y).card + s * (Tau y).card := by
      ring
    have e6 := hyb y hy
    omega
  -- 全体
  have htot := Finset.sum_le_sum hy_tot
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at htot
  have e1 : ∑ y ∈ P, (μC * min (Ib y).card 1 + μS * (Ib y).card + (X * s) * (Tt' y).card +
      s * (Tau y).card) = μC * ∑ y ∈ P, min (Ib y).card 1 + μS * ∑ y ∈ P, (Ib y).card +
      (X * s) * ∑ y ∈ P, (Tt' y).card + s * ∑ y ∈ P, (Tau y).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e2 : ∑ y ∈ P, s * (K y).card = s * ∑ y ∈ P, (K y).card := by rw [Finset.mul_sum]
  -- 最後の算術
  have f1 : (X * s) * ∑ y ∈ P, (Tt' y).card ≤ (X * s) * (X * YP.card) := Nat.mul_le_mul_left _ hG1
  have f2 : (X * s) * (X * YP.card) = μC * YP.card + μS * YP.card := by
    rw [show (X * s) * (X * YP.card) = (X * (X * s)) * YP.card by ring, ← hCS]; ring
  have f3 : μC * ∑ y ∈ P, min (Ib y).card 1 + μC * YP.card ≤ μC * P.card := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have f4 : μS * ∑ y ∈ P, (Ib y).card + μS * YP.card ≤ μS * 2 ^ (H + 1) := by
    rw [← mul_add]; exact Nat.mul_le_mul_left _ hG2
  have f5 : DP.card * s ≤ s * P.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hG5
  have f6 : s * ∑ y ∈ P, (Tau y).card ≤ s * (X * P.card) := Nat.mul_le_mul_left _ hG5'
  have f7 : s * (X * P.card) = s * X * P.card := by ring
  omega

end SpookyTree
