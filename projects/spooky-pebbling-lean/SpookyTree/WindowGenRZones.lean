/-
# 定理 genr の還元: 切断点から区域の族を作り，`ZoneFamily.Hyp` の各欄を示す

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_ALL_2026-11.md` 2.8 節（追記 2・3 で直した版），
`WINDOW_GENM_R1_2026-11.md` 1.1〜1.4 節（区域の入れ子，基底，Junk），`paper/app_window_res.tex` の "Setting"・"Reduction"．
前の煉瓦は `WindowGenRReduction`（`ZoneFamily`，`ZoneFamily.Hyp`，`top_bound`）と
`WindowGenRLemmaT`（`inZ`，`freeI`，`freeD`，`isoSet`，`fullM`，`zNodes`，`dirty`）．

## 設定（静的な切断点の構造）
`CutData`: 高さ `hgt = (top + 1) H + r` の完全二分木，`X = 2^H`，段は下から `L = 0, …, top`
（`top = m − 1`）．段 `L` のブロックの根の深さは `β L = hgt − L H`（`β 1 = h − H`，`β top = H + r`）．
各段 `L ≥ 1` の区域 `y` の数え済みの点の候補 `Kf L y`（戦略では区域の根が空になる直前の盤面のペブル）．
* 最上段 `top` の区域は根 `[]` の 1 つ（`Ys top = E top = {[]}`）．
* 段 `L + 1` の区域 `y` の数え済み `KZ (L+1) y = {x ∈ Kf (L+1) y : inZ (E (L+1)) y x}`，
  段 `L` の根 `Ys L = ⋃_y KZ (L+1) y`，前の段までの点 `E L = E (L+1) ∪ Ys L`（`lv` で上から作る）．
* 値 `Val 0 x = min(|Z_x|, Q)`（最下段の区域の頂点数を `Q` で頭打ち．紙の `min(|Z''|, q)`），
  `Val (L+1) y = Σ_{x ∈ KZ} Val L x`（紙の (0) は定義から等号）．
* `Uc L y = |Z_y ∩ U|`（`U` = 深さ `< β 1`），部分ブロック `t`，`τ`（前の段の点を含むブロック `W` の中の部分ブロック），
  基底の `J1`（前の段の点を含む段 1 のブロックの頂点），none の点（汚れた段 1 のブロック `Dset` と子の区域の満ブロック数 `kk`）．

## 示すこと
* `toFamily_hyp`: 仮定 `Ok`（`H ≥ 1`，`1 ≤ γ ≤ 2`，`Q ≤ γX`，区域ごとに `|K_Z| ≤ Q`，切断点は木の頂点）の下で
  `ZoneFamily.Hyp` の**全欄**（`hYE`，`hKZ`，`hchild`，`hbud`，`hVal`，`hU`，`hM`，`hb`，`hbase`）．
  (b) は紙 2.8 (b)（批判 S1 で直した場合分け）を `fullM` の分解で示す（`sum_t_le`）．
* `tau_sum_le`: `Σ_{Z} τ_Z ≤ X |E_L|`（紙の総和の段落・検算 F1），`J1_sum_le`: `Σ J1 ≤ X |E_1|`．
* `card_E_le`: `|E_L| ≤ Σ_{j ≤ top − L} Q^j`．
* `val_top_le`: 最上段の値
  `Val ≤ 2^{β 1} + X|E_1| + Σ_{L=2}^{top} (1 + 3 C_L) X^L |E_L| + X^{top+1} 2^r σ_{top+1,r}(γ)`
  （`top_bound` に上の 3 つを入れた形）．
-/
import SpookyTree.WindowGenRReduction

open Finset

namespace SpookyTree
namespace GenRZones

open GenRSigma GenRDual GenRLemmaT GenRReduction

/-! ## 1. 道の道具 -/

theorem inZ_lt {E : Finset Node} {y u : Node} (h : inZ E y u) : y.length < u.length :=
  prefix_ne_length_lt h.1 h.2.1

/-- 子の区域は親の区域に入る（`x ∈ Z_y`，`E ⊆ E'`）． -/
theorem inZ_trans {E E' : Finset Node} (hEE : E ⊆ E') {y x u : Node}
    (hx : inZ E y x) (hu : inZ E' x u) : inZ E y u := by
  obtain ⟨hyx, hxy, hcx⟩ := hx
  obtain ⟨hxu, hux, hcu⟩ := hu
  have hlx := prefix_ne_length_lt hyx hxy
  have hlu := prefix_ne_length_lt hxu hux
  refine ⟨hyx.trans hxu, fun he => by rw [he] at hlu; omega, ?_⟩
  intro e he hye heu hey
  rcases le_or_gt e.length x.length with hl | hl
  · exact hcx e he hye (List.prefix_of_prefix_length_le heu hxu hl) hey
  · exact hcu e (hEE he) (List.prefix_of_prefix_length_le hxu heu hl.le) heu
      (fun h => by rw [h] at hl; omega)

theorem prefix_take_of {x w : Node} {β : ℕ} (hx : x <+: w) (hl : x.length ≤ β) :
    x <+: w.take β := by
  refine List.prefix_of_prefix_length_le hx (List.take_prefix _ _) ?_
  rw [List.length_take]
  have := hx.length_le
  omega

theorem take_prefix_of {x w : Node} {β : ℕ} (hx : x <+: w) (hl : β ≤ x.length) :
    w.take β <+: x := by
  refine List.prefix_of_prefix_length_le (List.take_prefix _ _) hx ?_
  rw [List.length_take]
  omega

theorem length_take_of {w : Node} {β : ℕ} (hl : β ≤ w.length) : (w.take β).length = β := by
  rw [List.length_take]; omega

/-- 長さ `β + H` の語の集合で，各語の長さ `β` の接頭辞が `D`（長さ `β` の語の集合）にあれば `|S| ≤ 2^H |D|`． -/
theorem card_le_pow_of_take {β H : ℕ} {S D : Finset Node}
    (hD : ∀ W ∈ D, W.length = β) (hS : ∀ w ∈ S, w.length = β + H ∧ w.take β ∈ D) :
    S.card ≤ 2 ^ H * D.card := by
  classical
  have hsub : S ⊆ D.biUnion (fun W => (words (β + H)).filter (fun x => W <+: x)) := by
    intro w hw
    obtain ⟨hl, hW⟩ := hS w hw
    exact mem_biUnion.mpr ⟨_, hW, mem_filter.mpr ⟨mem_words.mpr hl, List.take_prefix _ _⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have h1 : ∑ W ∈ D, ((words (β + H)).filter (fun x => W <+: x)).card ≤ ∑ _W ∈ D, 2 ^ H :=
    sum_le_sum fun W hW => card_words_prefix_le (hD W hW)
  rw [sum_const, smul_eq_mul, mul_comm] at h1
  exact h1

/-- 互いに素な族の和の濃度． -/
theorem sum_card_eq_card_biUnion {α β : Type*} [DecidableEq β] {s : Finset α} {f : α → Finset β}
    (h : ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → Disjoint (f x) (f x')) :
    ∑ x ∈ s, (f x).card = (s.biUnion f).card := by
  classical
  rw [card_biUnion]
  intro x hx x' hx' hne
  exact h x (mem_coe.mp hx) x' (mem_coe.mp hx') hne

/-! ## 2. 1 つの区域（抽象的な形）

`E`: 前の段までの点（区域の根 `y ∈ E`），`Y`: この段の数え済みの点の全体（子の区域の根），
`KZa = {x ∈ Y : x ∈ Z_y}`，子の区域の前の段の点は `E ∪ Y`．ブロックの深さは `β`（この段）と `β + H`（子の段）． -/

section zone
open Classical

variable {β H hgt : ℕ} {E Y : Finset Node} {y : Node}

/-- 区域の数え済みの点（`Y` のうち区域 `Z_y` にあるもの）． -/
noncomputable def KZa (E Y : Finset Node) (y : Node) : Finset Node := Y.filter (inZ E y)

theorem mem_KZa {x : Node} : x ∈ KZa E Y y ↔ x ∈ Y ∧ inZ E y x := by
  unfold KZa; exact mem_filter

/-- 子の区域の満ブロック（子の段のブロック `β + H`）． -/
noncomputable def Fz (β H hgt : ℕ) (E Y : Finset Node) (x : Node) : Finset Node :=
  fullM (β + H) hgt x (E ∪ Y)

/-- 根が `E ∪ Y` の異なる点の区域の満ブロックは交わらない（`β + H < hgt`）． -/
theorem Fz_disj (hβ : β + H < hgt) {x x' : Node} (hx : x ∈ E ∪ Y) (hx' : x' ∈ E ∪ Y)
    (hne : x ≠ x') : Disjoint (Fz β H hgt E Y x) (Fz β H hgt E Y x') := by
  rw [disjoint_left]
  intro w h1 h2
  unfold Fz at h1 h2
  obtain ⟨hl, h1⟩ := mem_fullM.mp h1
  obtain ⟨-, h2⟩ := mem_fullM.mp h2
  exact ZoneFamily.inZ_disj hx hx' hne (h1 w (List.prefix_refl _) (by omega))
    (h2 w (List.prefix_refl _) (by omega))

/-- 自由なブロック `W`（`E` を含まない）の上下の点は `Z_y` にある． -/
theorem inZ_of_free {x W u : Node} (hxZ : inZ E y x)
    (hW : W ∈ openBelow β (cutBl (KZa E Y y) E) x) (hWE : ¬ meets E W)
    (hxu : x <+: u) (hux : u ≠ x) (hcmp : u <+: W ∨ W <+: u) : inZ E y u := by
  obtain ⟨hyx, hxy, hcx⟩ := hxZ
  obtain ⟨-, -, -, hopen⟩ := mem_openBelow.mp hW
  have hlx := prefix_ne_length_lt hyx hxy
  have hlu := prefix_ne_length_lt hxu hux
  refine ⟨hyx.trans hxu, fun he => by rw [he] at hlu; omega, ?_⟩
  intro e he hye heu hey
  rcases le_or_gt e.length x.length with hl | hl
  · exact hcx e he hye (List.prefix_of_prefix_length_le heu hxu hl) hey
  · have hxe : x <+: e := List.prefix_of_prefix_length_le hxu heu hl.le
    have hex : e ≠ x := fun h => by rw [h] at hl; omega
    have hcomp : e <+: W ∨ W <+: e := by
      rcases hcmp with h | h
      · exact Or.inl (heu.trans h)
      · rcases le_total e.length W.length with h2 | h2
        · exact Or.inl (List.prefix_of_prefix_length_le heu h h2)
        · exact Or.inr (List.prefix_of_prefix_length_le h heu h2)
    rcases hcomp with h | h
    · by_cases heW : e = W
      · subst heW; exact hWE ⟨e, he, List.prefix_refl _⟩
      · exact hopen e hxe h hex heW (Or.inr he)
    · exact hWE ⟨e, he, h⟩

/-- きれいな自由なブロックの延長（長さ `β + H`）は子の区域の満ブロック． -/
theorem ext_mem_Fz {x W w : Node} (hx : x ∈ KZa E Y y)
    (hW : W ∈ freeI β (KZa E Y y) E x) (hWw : W <+: w) (hwl : w.length = β + H) :
    w ∈ Fz β H hgt E Y x := by
  have hxZ := (mem_KZa.mp hx).2
  obtain ⟨hWf, hWK, hWE⟩ := mem_freeI.mp hW
  have hWf' : W ∈ openBelow β (cutBl (KZa E Y y) E) x := hWf
  obtain ⟨hWl, hxW, hWx, hopen⟩ := mem_openBelow.mp hWf'
  have hxl : x.length < β := by have := prefix_ne_length_lt hxW hWx; omega
  unfold Fz
  rw [mem_fullM]
  refine ⟨hwl, fun z hwz _ => ?_⟩
  have hWz : W <+: z := hWw.trans hwz
  have hxz : x <+: z := hxW.trans hWz
  have hzl : β ≤ z.length := by have := hWz.length_le; omega
  refine ⟨hxz, fun he => by rw [he] at hzl; omega, ?_⟩
  intro e he hxe hez hex
  have hcomp : (e <+: W ∧ e ≠ W) ∨ W <+: e := by
    rcases le_total e.length W.length with h2 | h2
    · by_cases heW : e = W
      · exact Or.inr (by rw [heW])
      · exact Or.inl ⟨List.prefix_of_prefix_length_le hez hWz h2, heW⟩
    · exact Or.inr (List.prefix_of_prefix_length_le hWz hez h2)
  rcases mem_union.mp he with heE | heY
  · rcases hcomp with ⟨h, hne⟩ | h
    · exact hopen e hxe h hex hne (Or.inr heE)
    · exact hWE ⟨e, heE, h⟩
  · have heZ : inZ E y e := inZ_of_free hxZ hWf' hWE hxe hex
      (by rcases hcomp with ⟨h, -⟩ | h; exact Or.inl h; exact Or.inr h)
    have heK : e ∈ KZa E Y y := mem_KZa.mpr ⟨heY, heZ⟩
    rcases hcomp with ⟨h, hne⟩ | h
    · exact hopen e hxe h hex hne (Or.inl heK)
    · exact hWK ⟨e, heK, h⟩

/-- **`M = Xj + t` の下側**: `2^H · |きれいな自由なブロック| ≤ |子の区域の満ブロック|`． -/
theorem pow_mul_freeI_le {x : Node} (hx : x ∈ KZa E Y y) :
    2 ^ H * (freeI β (KZa E Y y) E x).card ≤ (Fz β H hgt E Y x).card := by
  have hsub : ((freeI β (KZa E Y y) E x) ×ˢ words H).image (fun p => p.1 ++ p.2) ⊆
      Fz β H hgt E Y x := by
    intro w hw
    obtain ⟨⟨W, s⟩, hp, rfl⟩ := mem_image.mp hw
    obtain ⟨hW, hs⟩ := mem_product.mp hp
    have hWl : W.length = β := (mem_openBelow.mp (mem_freeI.mp hW).1).1
    exact ext_mem_Fz hx hW (List.prefix_append _ _) (by
      rw [List.length_append, hWl, mem_words.mp hs])
  have hinj : Set.InjOn (fun p : Node × Node => p.1 ++ p.2)
      ((freeI β (KZa E Y y) E x) ×ˢ words H : Finset (Node × Node)) := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
    have ha := (mem_openBelow.mp (mem_freeI.mp (mem_product.mp hab).1).1).1
    have ha' := (mem_openBelow.mp (mem_freeI.mp (mem_product.mp hab').1).1).1
    obtain ⟨h1, h2⟩ := List.append_inj he (by rw [ha, ha'])
    exact Prod.ext h1 h2
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, card_product, card_words, mul_comm] at this
  exact this

/-- 前の段の点を含むブロック `W` の部分ブロック（紙の τ の分）． -/
noncomputable def REz (β H hgt : ℕ) (E Y : Finset Node) (x : Node) : Finset Node :=
  (Fz β H hgt E Y x).filter (fun w => meets E (w.take β))

/-- きれいな自由なブロックの部分ブロック． -/
noncomputable def Az (β H hgt : ℕ) (E Y : Finset Node) (y x : Node) : Finset Node :=
  (Fz β H hgt E Y x).filter (fun w => x.length < β ∧ w.take β ∈ freeI β (KZa E Y y) E x)

/-- 残り（汚れたブロックの部分ブロック）． -/
noncomputable def RNz (β H hgt : ℕ) (E Y : Finset Node) (y x : Node) : Finset Node :=
  (Fz β H hgt E Y x).filter (fun w => ¬ meets E (w.take β) ∧
    ¬ (x.length < β ∧ w.take β ∈ freeI β (KZa E Y y) E x))

theorem Fz_card_le (x : Node) : (Fz β H hgt E Y x).card ≤
    (Az β H hgt E Y y x).card + (RNz β H hgt E Y y x).card + (REz β H hgt E Y x).card := by
  have hsub : Fz β H hgt E Y x ⊆ (Az β H hgt E Y y x ∪ RNz β H hgt E Y y x) ∪ REz β H hgt E Y x := by
    intro w hw
    simp only [mem_union, Az, RNz, REz, mem_filter]
    by_cases h1 : meets E (w.take β)
    · exact Or.inr ⟨hw, h1⟩
    · by_cases h2 : x.length < β ∧ w.take β ∈ freeI β (KZa E Y y) E x
      · exact Or.inl (Or.inl ⟨hw, h2⟩)
      · exact Or.inl (Or.inr ⟨hw, h1, h2⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))

theorem Az_card_le (x : Node) :
    (Az β H hgt E Y y x).card ≤ 2 ^ H * jIdx β (KZa E Y y) E x := by
  unfold jIdx
  split_ifs with hxl
  · refine card_le_pow_of_take (β := β) (fun W hW => (mem_openBelow.mp (mem_freeI.mp hW).1).1) ?_
    intro w hw
    obtain ⟨hwF, -, hW⟩ := mem_filter.mp hw
    exact ⟨(mem_fullM.mp hwF).1, hW⟩
  · have h0 : Az β H hgt E Y y x = ∅ := by
      unfold Az
      rw [filter_eq_empty_iff]
      intro w _ h
      exact hxl h.1
    rw [h0, card_empty]
    exact Nat.zero_le _

/-- 汚れた自由なブロックと孤立した汚れたブロック． -/
noncomputable def Dall (β : ℕ) (E Y : Finset Node) (y : Node) : Finset Node :=
  (zNodes β (KZa E Y y)).biUnion (freeD β (KZa E Y y) E) ∪ isoSet β y (KZa E Y y) E

/-- **紙 2.8 (b) の場合分け**: 残りの部分ブロックの親ブロック `W` は汚れた自由なブロックか孤立した汚れたブロック． -/
theorem RNz_take (hβ : β + H < hgt) (hyE : y ∈ E) {x w : Node} (hx : x ∈ KZa E Y y)
    (hw : w ∈ RNz β H hgt E Y y x) : w.take β ∈ Dall β E Y y := by
  obtain ⟨hwF, hWE, hnot⟩ := mem_filter.mp hw
  have hxZ := (mem_KZa.mp hx).2
  unfold Fz at hwF
  obtain ⟨hwl, hfull⟩ := mem_fullM.mp hwF
  have hxw : inZ (E ∪ Y) x w := hfull w (List.prefix_refl _) (by omega)
  have hWl : (w.take β).length = β := length_take_of (by omega)
  unfold Dall
  rw [mem_union, mem_biUnion]
  rcases lt_or_ge x.length β with hxl | hxl
  · -- 節点 x の汚れた自由なブロック
    left
    refine ⟨x, mem_zNodes.mpr ⟨hx, hxl⟩, ?_⟩
    have hxW : x <+: w.take β := prefix_take_of hxw.1 hxl.le
    have hWf : w.take β ∈ free β (KZa E Y y) E x := by
      rw [free_eq, mem_openBelow]
      refine ⟨hWl, hxW, fun he => by rw [he] at hWl; omega, ?_⟩
      intro u hxu huW hux _ hB
      have huE : u ∈ E ∪ Y := by
        rcases hB with h | h
        · exact mem_union.mpr (Or.inr (mem_KZa.mp h).1)
        · exact mem_union.mpr (Or.inl h)
      exact hxw.2.2 u huE hxu (huW.trans (List.take_prefix _ _)) hux
    refine mem_freeD.mpr ⟨hWf, ?_⟩
    by_contra hK
    exact hnot ⟨hxl, mem_freeI.mpr ⟨hWf, hK, hWE⟩⟩
  · -- 深い点 x: W ∋ x
    have hWx : w.take β <+: x := take_prefix_of hxw.1 hxl
    have hWK : meets (KZa E Y y) (w.take β) := ⟨x, hx, hWx⟩
    obtain ⟨hyx, hxy, hcx⟩ := hxZ
    have hyW : y.length < (w.take β).length := by
      by_contra hle
      push Not at hle
      exact hWE ⟨y, hyE, List.prefix_of_prefix_length_le hWx hyx hle⟩
    have hpath : pathZ E y (w.take β) := by
      refine ⟨List.prefix_of_prefix_length_le hyx hWx hyW.le, fun he => by rw [he] at hyW; omega, ?_⟩
      intro e he hye heW hey _
      exact hcx e he hye (heW.trans hWx) hey
    by_cases hv : ∃ v ∈ zNodes β (KZa E Y y), w.take β ∈ free β (KZa E Y y) E v
    · obtain ⟨v, hv, hWv⟩ := hv
      exact Or.inl ⟨v, hv, mem_freeD.mpr ⟨hWv, hWK⟩⟩
    · push Not at hv
      exact Or.inr (mem_isoSet.mpr ⟨hWl, hWK, hv, hpath⟩)

theorem Dall_card_le : (Dall β E Y y).card ≤
    (isoSet β y (KZa E Y y) E).card + ∑ v ∈ zNodes β (KZa E Y y), dirty β (KZa E Y y) E v := by
  unfold Dall
  refine (card_union_le _ _).trans ?_
  have h1 := card_biUnion_le (s := zNodes β (KZa E Y y)) (t := freeD β (KZa E Y y) E)
  have h2 : ∑ v ∈ zNodes β (KZa E Y y), (freeD β (KZa E Y y) E v).card ≤
      ∑ v ∈ zNodes β (KZa E Y y), dirty β (KZa E Y y) E v :=
    sum_le_sum fun v _ => by unfold dirty; omega
  omega

/-- **紙 2.8 (b)**: `Σ_x t_x ≤ X(λ + Σ(d + d°)) + τ_Z`（`t_x = M(Z'_x) − X j_x`，`τ_Z = Σ_x |REz x|`）． -/
theorem sum_t_le (hβ : β + H < hgt) (hyE : y ∈ E) :
    ∑ x ∈ KZa E Y y, ((Fz β H hgt E Y x).card - 2 ^ H * jIdx β (KZa E Y y) E x) ≤
      2 ^ H * ((isoSet β y (KZa E Y y) E).card +
        ∑ v ∈ zNodes β (KZa E Y y), dirty β (KZa E Y y) E v) +
      ∑ x ∈ KZa E Y y, (REz β H hgt E Y x).card := by
  have hpt : ∀ x ∈ KZa E Y y, (Fz β H hgt E Y x).card - 2 ^ H * jIdx β (KZa E Y y) E x ≤
      (RNz β H hgt E Y y x).card + (REz β H hgt E Y x).card := by
    intro x _
    have := Fz_card_le (β := β) (H := H) (hgt := hgt) (E := E) (Y := Y) (y := y) x
    have := Az_card_le (β := β) (H := H) (hgt := hgt) (E := E) (Y := Y) (y := y) x
    omega
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  refine Nat.add_le_add_right ?_ _
  have hYsub : ∀ x ∈ KZa E Y y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr (mem_KZa.mp hx).1)
  rw [sum_card_eq_card_biUnion (f := RNz β H hgt E Y y) (fun x hx x' hx' hne =>
    disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _)
      (Fz_disj hβ (hYsub x hx) (hYsub x' hx') hne)))]
  refine (card_le_pow_of_take (β := β) (H := H) (D := Dall β E Y y) ?_ ?_).trans
    (Nat.mul_le_mul_left _ Dall_card_le)
  · intro W hW
    unfold Dall at hW
    rcases mem_union.mp hW with h | h
    · obtain ⟨v, -, hv⟩ := mem_biUnion.mp h
      exact (mem_openBelow.mp (mem_freeD.mp hv).1).1
    · exact (mem_isoSet.mp h).1
  · intro w hw
    obtain ⟨x, hx, hwx⟩ := mem_biUnion.mp hw
    refine ⟨?_, RNz_take hβ hyE hx hwx⟩
    have hwF := (mem_filter.mp hwx).1
    unfold Fz at hwF
    exact (mem_fullM.mp hwF).1

/-- **`M = Xj + t`**: `t_x := |Fz x| − X j_x` で等号． -/
theorem Fz_eq (x : Node) (hx : x ∈ KZa E Y y) :
    (Fz β H hgt E Y x).card = 2 ^ H * jIdx β (KZa E Y y) E x +
      ((Fz β H hgt E Y x).card - 2 ^ H * jIdx β (KZa E Y y) E x) := by
  have : 2 ^ H * jIdx β (KZa E Y y) E x ≤ (Fz β H hgt E Y x).card := by
    unfold jIdx
    split_ifs
    · exact pow_mul_freeI_le hx
    · rw [mul_zero]; exact Nat.zero_le _
  omega

/-- 区域の和を `Y` の和に直す（根が `E` の異なる点の区域の数え済みの点は交わらない）． -/
theorem sum_zones_le {S : Finset Node} (hS : ∀ y ∈ S, y ∈ E) (f : Node → ℕ) :
    ∑ y ∈ S, ∑ x ∈ KZa E Y y, f x ≤ ∑ x ∈ Y, f x := by
  rw [← sum_biUnion]
  · refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
    intro x hx
    obtain ⟨y, -, hxy⟩ := mem_biUnion.mp hx
    exact (mem_KZa.mp hxy).1
  · intro y1 h1 y2 h2 hne
    show Disjoint (KZa E Y y1) (KZa E Y y2)
    rw [disjoint_left]
    intro x hx1 hx2
    exact ZoneFamily.inZ_disj (hS y1 (mem_coe.mp h1)) (hS y2 (mem_coe.mp h2)) hne
      (mem_KZa.mp hx1).2 (mem_KZa.mp hx2).2

/-- **紙の総和の段落（検算 F1）**: 全区域の τ の和は `X |E|` 以下． -/
theorem tau_sum_abs (hβ : β + H < hgt) {S : Finset Node} (hS : ∀ y ∈ S, y ∈ E) :
    ∑ y ∈ S, ∑ x ∈ KZa E Y y, (REz β H hgt E Y x).card ≤ 2 ^ H * E.card := by
  refine (sum_zones_le hS _).trans ?_
  have hYsub : ∀ x ∈ Y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr hx)
  rw [sum_card_eq_card_biUnion (f := REz β H hgt E Y) (fun x hx x' hx' hne =>
    disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _)
      (Fz_disj hβ (hYsub x hx) (hYsub x' hx') hne)))]
  refine (card_le_pow_of_take (β := β) (H := H)
    (D := (words β).filter (fun W => ∃ z ∈ E, W <+: z)) ?_ ?_).trans ?_
  · intro W hW; exact mem_words.mp (mem_filter.mp hW).1
  · intro w hw
    obtain ⟨x, -, hwx⟩ := mem_biUnion.mp hw
    obtain ⟨hwF, hm⟩ := mem_filter.mp hwx
    unfold Fz at hwF
    have hl := (mem_fullM.mp hwF).1
    exact ⟨hl, mem_filter.mpr ⟨mem_words.mpr (length_take_of (by omega)), hm⟩⟩
  · exact Nat.mul_le_mul_left _ ((card_words_dirty_le β E).trans (card_filter_le _ _))

/-- `U` の部分: 子の区域は親の区域の互いに素な部分集合． -/
theorem sum_sub_zone_le (P : Node → Prop) [DecidablePred P] :
    ∑ x ∈ KZa E Y y, (((nodes hgt).filter (inZ (E ∪ Y) x)).filter P).card ≤
      (((nodes hgt).filter (inZ E y)).filter P).card := by
  have hYsub : ∀ x ∈ KZa E Y y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr (mem_KZa.mp hx).1)
  rw [sum_card_eq_card_biUnion]
  · refine card_le_card ?_
    intro u hu
    obtain ⟨x, hx, hux⟩ := mem_biUnion.mp hu
    obtain ⟨hu1, hP⟩ := mem_filter.mp hux
    obtain ⟨hn, hZ⟩ := mem_filter.mp hu1
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hn, inZ_trans subset_union_left (mem_KZa.mp hx).2 hZ⟩, hP⟩
  · intro x hx x' hx' hne
    rw [disjoint_left]
    intro u h1 h2
    exact ZoneFamily.inZ_disj (hYsub x hx) (hYsub x' hx') hne
      (mem_filter.mp (mem_filter.mp h1).1).2 (mem_filter.mp (mem_filter.mp h2).1).2

end zone

/-! ## 3. 基底（段 1 の区域と最下段の区域．紙 2.8 基底，R1 1.4 基底）

段 1 のブロックの深さ `β`，`β + H = hgt`（ブロックの頂点数 `2^H − 1 = s`）．最下段の区域 `Z''_x`（`x ∈ KZa`）
の頂点を `U` の部分（深さ `< β`），前の段の点を含むブロック（Junk），`Z''_x` にすべて入るブロック（`kz x` 個），
区域 `Z_y` にすべて入り `K_Z` の点を含むブロック（`Dz`，紙の汚れ）に分ける． -/

section base
open Classical

variable {β H hgt : ℕ} {E Y : Finset Node} {y : Node}

/-- 最下段の区域． -/
noncomputable def Z0 (hgt : ℕ) (E Y : Finset Node) (x : Node) : Finset Node :=
  (nodes hgt).filter (inZ (E ∪ Y) x)

/-- 最下段の区域にすべて入る段 1 のブロックの数． -/
noncomputable def kz (β hgt : ℕ) (E Y : Finset Node) (x : Node) : ℕ :=
  (fullM β hgt x (E ∪ Y)).card

/-- 前の段の点を含むブロックの頂点（Junk）． -/
noncomputable def P2z (β hgt : ℕ) (E Y : Finset Node) (x : Node) : Finset Node :=
  (Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ meets E (u.take β))

/-- 区域 `Z_y` にすべて入り，数え済みの点を含むブロック（汚れ）． -/
noncomputable def Dz (β hgt : ℕ) (E Y : Finset Node) (y : Node) : Finset Node :=
  (fullM β hgt y E).filter (meets (KZa E Y y))

theorem fullM_sub_parent {x : Node} (hx : x ∈ KZa E Y y) :
    fullM β hgt x (E ∪ Y) ⊆ fullM β hgt y E := by
  intro w hw
  obtain ⟨hl, h⟩ := mem_fullM.mp hw
  exact mem_fullM.mpr ⟨hl, fun z hwz hz =>
    inZ_trans subset_union_left (mem_KZa.mp hx).2 (h z hwz hz)⟩

/-- 区域の分け方（紙: `U` の部分，汚れた部分，満ブロック）． -/
theorem Z0_cover (hβ : β + H = hgt) (hyE : y ∈ E) {x u : Node} (hx : x ∈ KZa E Y y)
    (hu : u ∈ Z0 hgt E Y x) :
    u.length < β ∨ (β ≤ u.length ∧ meets E (u.take β)) ∨
      (β ≤ u.length ∧ u.take β ∈ fullM β hgt x (E ∪ Y)) ∨
      (β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y) := by
  obtain ⟨hun, huZ⟩ := mem_filter.mp hu
  rw [mem_nodes] at hun
  have hxZ := (mem_KZa.mp hx).2
  rcases lt_or_ge u.length β with hl | hl
  · exact Or.inl hl
  right
  set W := u.take β with hWdef
  have hWu : W <+: u := List.take_prefix _ _
  have hWl : W.length = β := length_take_of hl
  by_cases hWE : meets E W
  · exact Or.inl ⟨hl, hWE⟩
  right
  by_cases hWF : W ∈ fullM β hgt x (E ∪ Y)
  · exact Or.inl ⟨hl, hWF⟩
  right
  refine ⟨hl, mem_filter.mpr ⟨?_, ?_⟩⟩
  · -- W は Z_y にすべて入る
    have hyu : inZ E y u := inZ_trans subset_union_left hxZ huZ
    obtain ⟨hyu1, hyu2, hyu3⟩ := hyu
    have hyW : y.length < W.length := by
      by_contra hle
      push Not at hle
      exact hWE ⟨y, hyE, List.prefix_of_prefix_length_le hWu hyu1 hle⟩
    have hyW' : y <+: W := List.prefix_of_prefix_length_le hyu1 hWu hyW.le
    refine mem_fullM.mpr ⟨hWl, fun z hWz _ => ⟨hyW'.trans hWz, ?_, ?_⟩⟩
    · intro he
      have := hWz.length_le
      rw [he] at this
      omega
    · intro e he hye hez hey
      rcases le_or_gt W.length e.length with h2 | h2
      · exact hWE ⟨e, he, List.prefix_of_prefix_length_le hWz hez h2⟩
      · exact hyu3 e he hye ((List.prefix_of_prefix_length_le hez hWz h2.le).trans hWu) hey
  · -- W は数え済みの点を含む
    rcases le_or_gt β x.length with hxl | hxl
    · exact ⟨x, hx, take_prefix_of huZ.1 hxl⟩
    · by_contra hK
      apply hWF
      have hxW : x <+: W := prefix_take_of huZ.1 hxl.le
      -- W が Z_y にすべて入ることは上と同じ
      have hyu : inZ E y u := inZ_trans subset_union_left hxZ huZ
      have hfullY : ∀ z, W <+: z → z.length < hgt → inZ E y z := by
        obtain ⟨hyu1, hyu2, hyu3⟩ := hyu
        have hyW : y.length < W.length := by
          by_contra hle
          push Not at hle
          exact hWE ⟨y, hyE, List.prefix_of_prefix_length_le hWu hyu1 hle⟩
        have hyW' : y <+: W := List.prefix_of_prefix_length_le hyu1 hWu hyW.le
        intro z hWz _
        refine ⟨hyW'.trans hWz, ?_, ?_⟩
        · intro he
          have := hWz.length_le
          rw [he] at this
          omega
        · intro e he hye hez hey
          rcases le_or_gt W.length e.length with h2 | h2
          · exact hWE ⟨e, he, List.prefix_of_prefix_length_le hWz hez h2⟩
          · exact hyu3 e he hye ((List.prefix_of_prefix_length_le hez hWz h2.le).trans hWu) hey
      refine mem_fullM.mpr ⟨hWl, fun z hWz hz => ⟨hxW.trans hWz, ?_, ?_⟩⟩
      · intro he
        have := hWz.length_le
        rw [he] at this
        omega
      · intro e he hxe hez hex
        rcases le_or_gt W.length e.length with h2 | h2
        · have hWe : W <+: e := List.prefix_of_prefix_length_le hWz hez h2
          rcases mem_union.mp he with heE | heY
          · exact hWE ⟨e, heE, hWe⟩
          · have hel : e.length < hgt := lt_of_le_of_lt hez.length_le hz
            exact hK ⟨e, mem_KZa.mpr ⟨heY, hfullY e hWe hel⟩, hWe⟩
        · exact huZ.2.2 e he hxe ((List.prefix_of_prefix_length_le hez hWz h2.le).trans hWu) hex

/-- 長さ `β` の語 `W` の下の木の頂点は `2^H − 1` 個． -/
theorem card_sub_blocks (hβ : β + H = hgt) {B : Finset Node} (hB : ∀ W ∈ B, W.length = β)
    {S : Finset Node} (hS : ∀ u ∈ S, u.length < hgt ∧ β ≤ u.length ∧ u.take β ∈ B) :
    S.card ≤ B.card * (2 ^ H - 1) := by
  have hsub : S ⊆ B.biUnion (subtree hgt) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hS u hu
    exact mem_biUnion.mpr ⟨_, h3, mem_subtree.mpr ⟨h1, List.take_prefix _ _⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have : ∀ W ∈ B, (subtree hgt W).card = 2 ^ H - 1 := by
    intro W hW
    rw [card_subtree, hB W hW, show hgt - β = H by omega]
  rw [sum_congr rfl this, sum_const, smul_eq_mul]

theorem Z0_disj {x x' : Node} (hx : x ∈ E ∪ Y) (hx' : x' ∈ E ∪ Y) (hne : x ≠ x')
    (P : Node → Prop) [DecidablePred P] :
    Disjoint ((Z0 hgt E Y x).filter P) ((Z0 hgt E Y x').filter P) := by
  rw [disjoint_left]
  intro u h1 h2
  exact ZoneFamily.inZ_disj hx hx' hne (mem_filter.mp (mem_filter.mp h1).1).2
    (mem_filter.mp (mem_filter.mp h2).1).2

/-- 満ブロックのある点は浅い（`β < hgt`）． -/
theorem kz_pos_shallow (hβ : β < hgt) {x : Node} (hk : 1 ≤ kz β hgt E Y x) : x.length < β := by
  unfold kz at hk
  obtain ⟨w, hw⟩ := card_pos.mp hk
  obtain ⟨hl, h⟩ := mem_fullM.mp hw
  have := inZ_lt (h w (List.prefix_refl _) (by omega))
  omega

/-- [行 Z]: `|Dz| + #{x : kz ≥ 1} ≤ |K_Z|`（紙 R1 1.4 基底の `#{Z'' : k ≥ 1} + β_Z ≤ |K_Z|`）． -/
theorem base_rowZ (hβ : β < hgt) :
    (Dz β hgt E Y y).card + ((KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x)).card ≤
      (KZa E Y y).card := by
  have h1 : (Dz β hgt E Y y).card ≤ ((KZa E Y y).filter (fun x => ¬ x.length < β)).card :=
    card_le_of_meets fun w hw => ⟨(mem_fullM.mp (mem_filter.mp hw).1).1, (mem_filter.mp hw).2⟩
  have h2 : ((KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x)).card ≤
      ((KZa E Y y).filter (fun x => x.length < β)).card :=
    card_le_card fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,
      kz_pos_shallow hβ (mem_filter.mp hx).2⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := KZa E Y y) (fun x => x.length < β)
  omega

/-- [行 N]: `|Dz| + Σ kz ≤ M_1(Z_y)`（紙の `Σk + β_Z ≤ M_1(Z)`）． -/
theorem base_rowN (hβ : β < hgt) (hlen : ∀ z ∈ Y, z.length < hgt) :
    (Dz β hgt E Y y).card + ∑ x ∈ (KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x),
      kz β hgt E Y x ≤ (fullM β hgt y E).card := by
  have hYsub : ∀ x ∈ KZa E Y y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr (mem_KZa.mp hx).1)
  have hs : ∑ x ∈ (KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x), kz β hgt E Y x ≤
      ∑ x ∈ KZa E Y y, kz β hgt E Y x :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _
  have hdisj : ∀ x ∈ KZa E Y y, ∀ x' ∈ KZa E Y y, x ≠ x' →
      Disjoint (fullM β hgt x (E ∪ Y)) (fullM β hgt x' (E ∪ Y)) := by
    intro x hx x' hx' hne
    rw [disjoint_left]
    intro w h1 h2
    obtain ⟨hl, h1⟩ := mem_fullM.mp h1
    obtain ⟨-, h2⟩ := mem_fullM.mp h2
    exact ZoneFamily.inZ_disj (hYsub x hx) (hYsub x' hx') hne
      (h1 w (List.prefix_refl _) (by omega)) (h2 w (List.prefix_refl _) (by omega))
  have he : ∑ x ∈ KZa E Y y, kz β hgt E Y x =
      ((KZa E Y y).biUnion (fun x => fullM β hgt x (E ∪ Y))).card :=
    sum_card_eq_card_biUnion hdisj
  have hD : Disjoint (Dz β hgt E Y y) ((KZa E Y y).biUnion (fun x => fullM β hgt x (E ∪ Y))) := by
    rw [disjoint_left]
    intro w hwD hwB
    obtain ⟨x, hx, hwx⟩ := mem_biUnion.mp hwB
    obtain ⟨z, hz, hwz⟩ := (mem_filter.mp hwD).2
    have hzY := (mem_KZa.mp hz).1
    have hzZ := (mem_fullM.mp hwx).2 z hwz (hlen z hzY)
    exact hzZ.2.2 z (mem_union.mpr (Or.inr hzY)) hzZ.1 (List.prefix_refl _) hzZ.2.1
  have hsub : Dz β hgt E Y y ∪ (KZa E Y y).biUnion (fun x => fullM β hgt x (E ∪ Y)) ⊆
      fullM β hgt y E := by
    intro w hw
    rcases mem_union.mp hw with h | h
    · exact (mem_filter.mp h).1
    · obtain ⟨x, hx, hwx⟩ := mem_biUnion.mp h
      exact fullM_sub_parent hx hwx
  have := card_le_card hsub
  rw [card_union_of_disjoint hD] at this
  omega

/-- 1 つの最下段の区域: `|Z''_x| ≤ |U 部分| + |Junk| + |汚れ| + kz·(2^H − 1)`． -/
theorem Z0_card_le (hβ : β + H = hgt) (hyE : y ∈ E) {x : Node} (hx : x ∈ KZa E Y y) :
    (Z0 hgt E Y x).card ≤ ((Z0 hgt E Y x).filter (fun u => u.length < β)).card +
      (P2z β hgt E Y x).card +
      ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card +
      kz β hgt E Y x * (2 ^ H - 1) := by
  have hsub : Z0 hgt E Y x ⊆ (((Z0 hgt E Y x).filter (fun u => u.length < β) ∪ P2z β hgt E Y x) ∪
      (Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)) ∪
      (Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ fullM β hgt x (E ∪ Y)) := by
    intro u hu
    simp only [mem_union, P2z, mem_filter]
    rcases Z0_cover hβ hyE hx hu with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hu, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hu, h⟩))
    · exact Or.inr ⟨hu, h⟩
    · exact Or.inl (Or.inr ⟨hu, h⟩)
  have h4 : ((Z0 hgt E Y x).filter
      (fun u => β ≤ u.length ∧ u.take β ∈ fullM β hgt x (E ∪ Y))).card ≤
      kz β hgt E Y x * (2 ^ H - 1) :=
    card_sub_blocks hβ (fun W hW => (mem_fullM.mp hW).1) fun u hu => by
      obtain ⟨hu1, h1, h2⟩ := mem_filter.mp hu
      exact ⟨mem_nodes.mp (mem_filter.mp hu1).1, h1, h2⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have a := card_union_le (((Z0 hgt E Y x).filter (fun u => u.length < β) ∪ P2z β hgt E Y x))
    ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y))
  have b := card_union_le ((Z0 hgt E Y x).filter (fun u => u.length < β)) (P2z β hgt E Y x)
  omega

/-- 汚れの和: `Σ_x |Z''_x ∩ 汚れ| ≤ |Dz| (2^H − 1)`． -/
theorem sum_dirty_le (hβ : β + H = hgt) :
    ∑ x ∈ KZa E Y y,
      ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card ≤
      (Dz β hgt E Y y).card * (2 ^ H - 1) := by
  have hYsub : ∀ x ∈ KZa E Y y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr (mem_KZa.mp hx).1)
  rw [sum_card_eq_card_biUnion (fun x hx x' hx' hne => Z0_disj (hYsub x hx) (hYsub x' hx') hne _)]
  refine card_sub_blocks hβ (fun W hW => (mem_fullM.mp (mem_filter.mp hW).1).1) ?_
  intro u hu
  obtain ⟨x, -, hux⟩ := mem_biUnion.mp hu
  obtain ⟨hu1, h1, h2⟩ := mem_filter.mp hux
  exact ⟨mem_nodes.mp (mem_filter.mp hu1).1, h1, h2⟩

/-- **基底の値の評価**（紙 2.8 基底: `min(ks, q) ≤ X v_1(k)`，汚れ `s ≤ X`）． -/
theorem base_value (hβ : β + H = hgt) (hyE : y ∈ E) {γ : ℝ} (hγ : 0 ≤ γ) {Q : ℕ}
    (hQ : (Q : ℝ) ≤ γ * 2 ^ H) :
    ∑ x ∈ KZa E Y y, min ((Z0 hgt E Y x).card : ℝ) Q ≤
      ((((nodes hgt).filter (inZ E y)).filter (fun u => u.length < β)).card : ℝ) +
      ∑ x ∈ KZa E Y y, ((P2z β hgt E Y x).card : ℝ) +
      (2 ^ H : ℝ) * ((Dz β hgt E Y y).card +
        ∑ x ∈ (KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x), min (kz β hgt E Y x : ℝ) γ) := by
  have hX1 : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
  have hpow : ((2 ^ H - 1 : ℕ) : ℝ) ≤ 2 ^ H := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; linarith
  -- 各点
  have hpt : ∀ x ∈ KZa E Y y, min ((Z0 hgt E Y x).card : ℝ) Q ≤
      (((Z0 hgt E Y x).filter (fun u => u.length < β)).card : ℝ) + (P2z β hgt E Y x).card +
      ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card +
      (2 ^ H : ℝ) * min (kz β hgt E Y x : ℝ) γ := by
    intro x hx
    have hc : ((Z0 hgt E Y x).card : ℝ) ≤
        (((Z0 hgt E Y x).filter (fun u => u.length < β)).card : ℝ) + (P2z β hgt E Y x).card +
        ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card +
        (kz β hgt E Y x : ℝ) * ((2 ^ H - 1 : ℕ) : ℝ) := by
      exact_mod_cast Z0_card_le hβ hyE hx
    have hk0 : (0 : ℝ) ≤ kz β hgt E Y x := Nat.cast_nonneg _
    have hkm : (kz β hgt E Y x : ℝ) * ((2 ^ H - 1 : ℕ) : ℝ) ≤ 2 ^ H * kz β hgt E Y x := by
      nlinarith
    have hmin : min ((kz β hgt E Y x : ℝ) * ((2 ^ H - 1 : ℕ) : ℝ)) (Q : ℝ) ≤
        2 ^ H * min (kz β hgt E Y x : ℝ) γ := by
      rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 ^ H)]
      exact min_le_min hkm (by linarith)
    have hP : (0 : ℝ) ≤ (((Z0 hgt E Y x).filter (fun u => u.length < β)).card : ℝ) +
        (P2z β hgt E Y x).card +
        ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card := by
      positivity
    rcases le_total ((kz β hgt E Y x : ℝ) * ((2 ^ H - 1 : ℕ) : ℝ)) (Q : ℝ) with h | h
    · rw [min_eq_left h] at hmin
      have := min_le_left ((Z0 hgt E Y x).card : ℝ) (Q : ℝ)
      linarith
    · rw [min_eq_right h] at hmin
      have := min_le_right ((Z0 hgt E Y x).card : ℝ) (Q : ℝ)
      linarith
  refine (sum_le_sum hpt).trans ?_
  simp only [sum_add_distrib]
  -- U の部分
  have hU : ∑ x ∈ KZa E Y y, (((Z0 hgt E Y x).filter (fun u => u.length < β)).card : ℝ) ≤
      ((((nodes hgt).filter (inZ E y)).filter (fun u => u.length < β)).card : ℝ) := by
    have h := sum_sub_zone_le (hgt := hgt) (E := E) (Y := Y) (y := y)
      (fun u : Node => u.length < β)
    unfold Z0
    exact_mod_cast h
  -- 汚れ
  have hD : ∑ x ∈ KZa E Y y,
      (((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card : ℝ) ≤
      (2 ^ H : ℝ) * (Dz β hgt E Y y).card := by
    have h : (∑ x ∈ KZa E Y y,
        ((Z0 hgt E Y x).filter (fun u => β ≤ u.length ∧ u.take β ∈ Dz β hgt E Y y)).card : ℝ) ≤
        ((Dz β hgt E Y y).card : ℝ) * ((2 ^ H - 1 : ℕ) : ℝ) := by
      exact_mod_cast sum_dirty_le hβ
    have h0 : (0 : ℝ) ≤ (Dz β hgt E Y y).card := Nat.cast_nonneg _
    nlinarith
  -- 満ブロック: kz = 0 の項は 0
  have hK : ∑ x ∈ KZa E Y y, (2 ^ H : ℝ) * min (kz β hgt E Y x : ℝ) γ =
      (2 ^ H : ℝ) * ∑ x ∈ (KZa E Y y).filter (fun x => 1 ≤ kz β hgt E Y x),
        min (kz β hgt E Y x : ℝ) γ := by
    rw [← mul_sum, sum_filter]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · have : kz β hgt E Y x = 0 := by omega
      rw [this, Nat.cast_zero]
      exact min_eq_left hγ
  rw [hK]
  nlinarith

/-- Junk の和: 全区域で `Σ_x |Junk(x)| ≤ X |E|`． -/
theorem J_sum_abs (hβ : β + H = hgt) {S : Finset Node} (hS : ∀ y ∈ S, y ∈ E) :
    ∑ y ∈ S, ∑ x ∈ KZa E Y y, (P2z β hgt E Y x).card ≤ 2 ^ H * E.card := by
  refine (sum_zones_le hS _).trans ?_
  have hYsub : ∀ x ∈ Y, x ∈ E ∪ Y := fun x hx => mem_union.mpr (Or.inr hx)
  rw [sum_card_eq_card_biUnion (f := P2z β hgt E Y) (fun x hx x' hx' hne =>
    Z0_disj (hYsub x hx) (hYsub x' hx') hne _)]
  have h := card_sub_blocks (S := Y.biUnion (P2z β hgt E Y)) hβ
    (B := (words β).filter (fun W => ∃ z ∈ E, W <+: z))
    (fun W hW => mem_words.mp (mem_filter.mp hW).1) (by
      intro u hu
      obtain ⟨x, -, hux⟩ := mem_biUnion.mp hu
      obtain ⟨hu1, h1, h2⟩ := mem_filter.mp hux
      exact ⟨mem_nodes.mp (mem_filter.mp hu1).1, h1,
        mem_filter.mpr ⟨mem_words.mpr (length_take_of h1), h2⟩⟩)
  have h2 := (card_words_dirty_le β E).trans (card_filter_le _ _)
  have h3 : ((words β).filter (fun W => ∃ z ∈ E, W <+: z)).card * (2 ^ H - 1) ≤
      2 ^ H * E.card := by
    rw [mul_comm (2 ^ H)]; exact Nat.mul_le_mul h2 (Nat.sub_le _ _)
  exact h.trans h3

end base

/-! ## 4. 戦略の切断点から作る区域の族 -/

/-- 静的な切断点の構造（紙 2.8 の単位．`hgt = (top + 1) H + r`，`X = 2^H`，段 `0..top`）． -/
structure CutData where
  H : ℕ
  r : ℕ
  top : ℕ
  γ : ℝ
  Q : ℕ
  /-- 段 `L` の区域 `y` の数え済みの点の候補． -/
  Kf : ℕ → Node → Finset Node

namespace CutData

variable (D : CutData)

def X : ℕ := 2 ^ D.H
def hgt : ℕ := (D.top + 1) * D.H + D.r
def β (L : ℕ) : ℕ := D.hgt - L * D.H

open Classical in
/-- 上から `d` 段目（段 `top − d`）の区域の根と前の段までの点． -/
noncomputable def lv : ℕ → Finset Node × Finset Node
  | 0 => ({[]}, {[]})
  | d + 1 =>
    ((lv d).1.biUnion (fun y => (D.Kf (D.top - d) y).filter (inZ (lv d).2 y)),
      (lv d).2 ∪ (lv d).1.biUnion (fun y => (D.Kf (D.top - d) y).filter (inZ (lv d).2 y)))

noncomputable def Ys (L : ℕ) : Finset Node := if L ≤ D.top then (D.lv (D.top - L)).1 else ∅
noncomputable def E (L : ℕ) : Finset Node := if L ≤ D.top then (D.lv (D.top - L)).2 else {[]}

open Classical in
noncomputable def KZ : ℕ → Node → Finset Node
  | 0, _ => ∅
  | L + 1, y => (D.Kf (L + 1) y).filter (inZ (D.E (L + 1)) y)

open Classical in
noncomputable def Zs (L : ℕ) (y : Node) : Finset Node := (nodes D.hgt).filter (inZ (D.E L) y)

noncomputable def Val : ℕ → Node → ℝ
  | 0, x => min ((D.Zs 0 x).card : ℝ) D.Q
  | L + 1, y => ∑ x ∈ D.KZ (L + 1) y, Val L x

open Classical in
noncomputable def Uc (L : ℕ) (y : Node) : ℝ := ((D.Zs L y).filter (fun u => u.length < D.β 1)).card

open Classical in
/-- 点 `x` を含む段 `L` の区域の根． -/
noncomputable def par (L : ℕ) (x : Node) : Node :=
  if h : ∃ y ∈ D.Ys L, inZ (D.E L) y x then h.choose else []

noncomputable def t : ℕ → Node → ℕ
  | 0, _ => 0
  | L + 1, x => (fullM (D.β L) D.hgt x (D.E L)).card -
      D.X * jIdx (D.β (L + 1)) (D.KZ (L + 1) (D.par (L + 1) x)) (D.E (L + 1)) x

open Classical in
noncomputable def RE : ℕ → Node → Finset Node
  | L + 2, x => (fullM (D.β (L + 1)) D.hgt x (D.E (L + 1))).filter
      (fun w => meets (D.E (L + 2)) (w.take (D.β (L + 2))))
  | _, _ => ∅

noncomputable def τ (L : ℕ) (y : Node) : ℕ := ∑ x ∈ D.KZ L y, (D.RE L x).card

noncomputable def kk (x : Node) : ℕ := (fullM (D.β 1) D.hgt x (D.E 0)).card

open Classical in
noncomputable def Dset (y : Node) : Finset Node :=
  (fullM (D.β 1) D.hgt y (D.E 1)).filter (meets (D.KZ 1 y))

open Classical in
noncomputable def P2 (x : Node) : Finset Node :=
  (D.Zs 0 x).filter (fun u => D.β 1 ≤ u.length ∧ meets (D.E 1) (u.take (D.β 1)))

noncomputable def J1 (y : Node) : ℝ := ∑ x ∈ D.KZ 1 y, ((D.P2 x).card : ℝ)

open Classical in
noncomputable def sB (y : Node) : Finset (Option Node) :=
  insertNone ((D.KZ 1 y).filter (fun x => 1 ≤ D.kk x))

noncomputable def xB (y : Node) : Option Node → ℝ
  | none => (D.Dset y).card
  | some _ => 1

noncomputable def tB : Option Node → NoneCol
  | none => .dirty
  | some x => .clean (D.kk x)

/-- 切断点から作った区域の族． -/
noncomputable def toFamily : ZoneFamily where
  X := D.X
  γ := D.γ
  r := D.r
  hgt := D.hgt
  β := D.β
  E := D.E
  Ys := D.Ys
  KZ := D.KZ
  Val := D.Val
  Uc := D.Uc
  t := D.t
  τ := D.τ
  J1 := D.J1
  ι := Option Node
  sB := D.sB
  xB := D.xB
  tB := fun _ => D.tB

/-- 仮定（戦略から来るもの）． -/
structure Ok : Prop where
  hH : 1 ≤ D.H
  h1 : 1 ≤ D.γ
  h2 : D.γ ≤ 2
  hQ : (D.Q : ℝ) ≤ D.γ * D.X
  /-- 区域の数え済みの点は `Q` 個以下（中の段は `p − 2`，最上段は `p − 1`）． -/
  hbud : ∀ L, ∀ y ∈ D.Ys L, (D.KZ L y).card ≤ D.Q
  /-- 切断点は木の頂点． -/
  hlen : ∀ L y, ∀ x ∈ D.Kf L y, x.length < D.hgt

/-! ### 段の構造 -/

theorem lv_sub (d : ℕ) : (D.lv d).1 ⊆ (D.lv d).2 := by
  cases d with
  | zero => simp [lv]
  | succ d => intro x hx; simp only [lv] at hx ⊢; exact mem_union.mpr (Or.inr hx)

theorem Ys_top : D.Ys D.top = {[]} := by simp [Ys, lv]
theorem E_top : D.E D.top = {[]} := by simp [E, lv]

theorem Ys_empty {L : ℕ} (hL : D.top < L) : D.Ys L = ∅ := by
  unfold Ys; rw [if_neg (by omega)]

theorem Ys_sub_E (L : ℕ) : D.Ys L ⊆ D.E L := by
  unfold Ys E
  split_ifs
  · exact D.lv_sub _
  · exact empty_subset _

open Classical in
theorem Ys_succ {L : ℕ} (hL : L < D.top) :
    D.Ys L = (D.Ys (L + 1)).biUnion (D.KZ (L + 1)) ∧ D.E L = D.E (L + 1) ∪ D.Ys L := by
  obtain ⟨d, hd1, hd2⟩ : ∃ d, D.top - L = d + 1 ∧ D.top - (L + 1) = d := ⟨_, by omega, rfl⟩
  have hd3 : D.top - d = L + 1 := by omega
  have h1 : D.Ys L = (D.lv (d + 1)).1 := by unfold Ys; rw [if_pos hL.le, hd1]
  have h2 : D.E L = (D.lv (d + 1)).2 := by unfold E; rw [if_pos hL.le, hd1]
  have h3 : D.Ys (L + 1) = (D.lv d).1 := by unfold Ys; rw [if_pos (by omega), hd2]
  have h4 : D.E (L + 1) = (D.lv d).2 := by unfold E; rw [if_pos (by omega), hd2]
  have hK : D.KZ (L + 1) = fun y => (D.Kf (L + 1) y).filter (inZ (D.lv d).2 y) := by
    funext y
    show (D.Kf (L + 1) y).filter (inZ (D.E (L + 1)) y) = _
    rw [h4]
  rw [h1, h2, h3, h4, hK]
  constructor <;> simp only [lv, hd3]

theorem Ys_pos {L : ℕ} {y : Node} (hy : y ∈ D.Ys L) : L ≤ D.top := by
  by_contra h
  rw [D.Ys_empty (by omega)] at hy
  exact absurd hy (notMem_empty _)

/-- 数え済みの点は段の点の全体から区域の点を取ったもの． -/
theorem KZ_eq {L : ℕ} (hL : L < D.top) {y : Node} (hy : y ∈ D.Ys (L + 1)) :
    D.KZ (L + 1) y = KZa (D.E (L + 1)) (D.Ys L) y := by
  classical
  ext x
  rw [mem_KZa, (D.Ys_succ hL).1, mem_biUnion]
  constructor
  · intro hx
    exact ⟨⟨y, hy, hx⟩, by unfold KZ at hx; exact (mem_filter.mp hx).2⟩
  · rintro ⟨⟨y', hy', hx'⟩, hZ⟩
    have hZ' : inZ (D.E (L + 1)) y' x := by unfold KZ at hx'; exact (mem_filter.mp hx').2
    have : y' = y := by
      by_contra hne
      exact ZoneFamily.inZ_disj (D.Ys_sub_E _ hy') (D.Ys_sub_E _ hy) hne hZ' hZ
    rw [← this]
    exact hx'

theorem par_eq {L : ℕ} {y x : Node} (hy : y ∈ D.Ys L) (hx : inZ (D.E L) y x) : D.par L x = y := by
  classical
  unfold par
  have hex : ∃ y ∈ D.Ys L, inZ (D.E L) y x := ⟨y, hy, hx⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  by_contra hne
  exact ZoneFamily.inZ_disj (D.Ys_sub_E _ h1) (D.Ys_sub_E _ hy) hne h2 hx

/-! ### 深さ -/

theorem β_succ {L : ℕ} (hL : L + 1 ≤ D.top + 1) : D.β L = D.β (L + 1) + D.H := by
  have h1 : (L + 1) * D.H ≤ D.hgt := by
    unfold hgt; exact (Nat.mul_le_mul_right _ hL).trans (Nat.le_add_right _ _)
  unfold β
  rw [Nat.succ_mul] at h1 ⊢
  omega

theorem β_lt (hH : 1 ≤ D.H) {L : ℕ} (hL : 1 ≤ L) : D.β L < D.hgt := by
  have h1 : 1 ≤ L * D.H := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : D.H ≤ D.hgt := by
    unfold hgt
    have : D.H ≤ (D.top + 1) * D.H := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold β
  omega

theorem β_top : D.β D.top = D.H + D.r := by
  unfold β hgt
  rw [Nat.succ_mul]
  omega

theorem β_one_add : D.β 1 + D.H = D.hgt := by
  have : D.H ≤ D.hgt := by
    unfold hgt
    have : D.H ≤ (D.top + 1) * D.H := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold β; omega

/-! ### `ZoneFamily.Hyp` の各欄 -/

variable {D}

theorem hyp_hYE : ∀ L, ∀ y ∈ D.Ys L, y ∈ D.E L := fun L _ hy => D.Ys_sub_E L hy

theorem hyp_hKZ : ∀ L, ∀ y ∈ D.Ys L, ∀ x ∈ D.KZ L y, inZ (D.E L) y x := by
  classical
  intro L y _ x hx
  cases L with
  | zero => simp [KZ] at hx
  | succ L => unfold KZ at hx; exact (mem_filter.mp hx).2

theorem hyp_hchild : ∀ L, ∀ y ∈ D.Ys (L + 2), D.KZ (L + 2) y ⊆ D.Ys (L + 1) := by
  intro L y hy x hx
  have hL := D.Ys_pos hy
  rw [(D.Ys_succ (L := L + 1) (by omega)).1]
  exact mem_biUnion.mpr ⟨y, hy, hx⟩

theorem KZ_card_le (hD : D.Ok) (L : ℕ) {y : Node} (hy : y ∈ D.Ys L) : (D.KZ L y).card ≤ D.Q :=
  hD.hbud L y hy

theorem hyp_hbud (hD : D.Ok) : ∀ L, ∀ y ∈ D.Ys (L + 2),
    ((D.KZ (L + 2) y).card : ℝ) ≤ D.γ * D.X := by
  intro L y hy
  have : ((D.KZ (L + 2) y).card : ℝ) ≤ D.Q := by exact_mod_cast KZ_card_le hD (L + 2) hy
  linarith [hD.hQ]

theorem hyp_hVal : ∀ L, ∀ y ∈ D.Ys (L + 2), D.Val (L + 2) y ≤ ∑ x ∈ D.KZ (L + 2) y, D.Val (L + 1) x :=
  fun _ _ _ => le_of_eq rfl

theorem hyp_hU : ∀ L, ∀ y ∈ D.Ys (L + 2), ∑ x ∈ D.KZ (L + 2) y, D.Uc (L + 1) x ≤ D.Uc (L + 2) y := by
  classical
  intro L y hy
  have hL := D.Ys_pos hy
  rw [D.KZ_eq (L := L + 1) (by omega) hy]
  have hE := (D.Ys_succ (L := L + 1) (by omega)).2
  unfold Uc Zs
  rw [hE]
  exact_mod_cast sum_sub_zone_le (hgt := D.hgt) (E := D.E (L + 2))
    (Y := D.Ys (L + 1)) (y := y) (fun u : Node => u.length < D.β 1)

/-- 段 `L + 1` の区域の満ブロックは抽象の `Fz`． -/
theorem Mz_eq_Fz {L : ℕ} (hL : L + 2 ≤ D.top) (x : Node) :
    fullM (D.β (L + 1)) D.hgt x (D.E (L + 1)) =
      Fz (D.β (L + 2)) D.H D.hgt (D.E (L + 2)) (D.Ys (L + 1)) x := by
  unfold Fz
  rw [← (D.Ys_succ (L := L + 1) (by omega)).2, ← D.β_succ (by omega)]

theorem hyp_hM : ∀ L, ∀ y ∈ D.Ys (L + 2), ∀ x ∈ D.KZ (L + 2) y,
    D.toFamily.Mz (L + 1) x = D.X * jIdx (D.β (L + 2)) (D.KZ (L + 2) y) (D.E (L + 2)) x +
      D.t (L + 2) x := by
  intro L y hy x hx
  have hL := D.Ys_pos hy
  have hxZ : inZ (D.E (L + 2)) y x := hyp_hKZ (L + 2) y hy x hx
  have hpar := D.par_eq hy hxZ
  show (fullM (D.β (L + 1)) D.hgt x (D.E (L + 1))).card =
    D.X * jIdx (D.β (L + 2)) (D.KZ (L + 2) y) (D.E (L + 2)) x +
      ((fullM (D.β (L + 1)) D.hgt x (D.E (L + 1))).card -
        D.X * jIdx (D.β (L + 2)) (D.KZ (L + 2) (D.par (L + 2) x)) (D.E (L + 2)) x)
  rw [hpar, D.Mz_eq_Fz hL, D.KZ_eq (L := L + 1) (by omega) hy]
  rw [D.KZ_eq (L := L + 1) (by omega) hy] at hx
  exact Fz_eq x hx

open Classical in
theorem tau_eq {L : ℕ} {y : Node} (hy : y ∈ D.Ys (L + 2)) :
    D.τ (L + 2) y = ∑ x ∈ KZa (D.E (L + 2)) (D.Ys (L + 1)) y,
      (REz (D.β (L + 2)) D.H D.hgt (D.E (L + 2)) (D.Ys (L + 1)) x).card := by
  have hL := D.Ys_pos hy
  unfold τ
  rw [D.KZ_eq (L := L + 1) (by omega) hy]
  refine sum_congr rfl fun x _ => ?_
  show ((fullM (D.β (L + 1)) D.hgt x (D.E (L + 1))).filter
    (fun w => meets (D.E (L + 2)) (w.take (D.β (L + 2))))).card = _
  rw [D.Mz_eq_Fz hL]
  rfl

theorem hyp_hb (hD : D.Ok) : ∀ L, ∀ y ∈ D.Ys (L + 2), ∑ x ∈ D.KZ (L + 2) y, D.t (L + 2) x ≤
    D.X * ((isoSet (D.β (L + 2)) y (D.KZ (L + 2) y) (D.E (L + 2))).card +
      ∑ v ∈ zNodes (D.β (L + 2)) (D.KZ (L + 2) y),
        dirty (D.β (L + 2)) (D.KZ (L + 2) y) (D.E (L + 2)) v) + D.τ (L + 2) y := by
  classical
  intro L y hy
  have hL := D.Ys_pos hy
  have hK := D.KZ_eq (L := L + 1) (by omega) hy
  have ht : ∀ x ∈ D.KZ (L + 2) y, D.t (L + 2) x =
      (Fz (D.β (L + 2)) D.H D.hgt (D.E (L + 2)) (D.Ys (L + 1)) x).card -
        2 ^ D.H * jIdx (D.β (L + 2)) (KZa (D.E (L + 2)) (D.Ys (L + 1)) y) (D.E (L + 2)) x := by
    intro x hx
    have hpar := D.par_eq hy (hyp_hKZ (L + 2) y hy x hx)
    show (fullM (D.β (L + 1)) D.hgt x (D.E (L + 1))).card -
      D.X * jIdx (D.β (L + 2)) (D.KZ (L + 2) (D.par (L + 2) x)) (D.E (L + 2)) x = _
    rw [hpar, D.Mz_eq_Fz hL, hK]
    rfl
  have hτ := D.tau_eq hy
  rw [sum_congr rfl ht, hτ, hK]
  exact sum_t_le (by rw [← D.β_succ (by omega)]; exact D.β_lt hD.hH (by omega))
    (D.Ys_sub_E _ hy)

/-- 基底の欄の値の部分を抽象の形に直すための等式． -/
theorem hyp_hbase (hD : D.Ok) : ∀ y ∈ D.Ys 1,
    (∀ i ∈ D.sB y, 0 ≤ D.xB y i) ∧ (∀ i ∈ D.sB y, (D.tB i).Valid) ∧
    ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).rowZ ≤ D.γ * D.X ∧
    ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).rowN ≤
      D.toFamily.Mz 1 y ∧
    D.Val 1 y ≤ D.Uc 1 y + D.J1 y +
      D.X * ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).obj := by
  classical
  intro y hy
  have hL := D.Ys_pos hy
  have hK := D.KZ_eq (L := 0) (by omega) hy
  have hE : D.E 0 = D.E 1 ∪ D.Ys 0 := (D.Ys_succ (L := 0) (by omega)).2
  have hβ : D.β 1 + D.H = D.hgt := D.β_one_add
  have hβlt : D.β 1 < D.hgt := D.β_lt hD.hH le_rfl
  have hyE : y ∈ D.E 1 := D.Ys_sub_E 1 hy
  have hlen : ∀ z ∈ D.Ys 0, z.length < D.hgt := by
    intro z hz
    rw [(D.Ys_succ (L := 0) (by omega)).1] at hz
    obtain ⟨y', -, hz⟩ := mem_biUnion.mp hz
    unfold KZ at hz
    exact hD.hlen _ _ z (mem_filter.mp hz).1
  have hkk : ∀ x, D.kk x = kz (D.β 1) D.hgt (D.E 1) (D.Ys 0) x := by
    intro x; unfold kk kz; rw [hE]
  have hDs : D.Dset y = Dz (D.β 1) D.hgt (D.E 1) (D.Ys 0) y := by
    unfold Dset Dz; rw [hK]
  -- 和を展開
  have hsZ : ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).rowZ =
      (D.Dset y).card + ((D.KZ 1 y).filter (fun x => 1 ≤ D.kk x)).card := by
    unfold sB
    rw [sum_insertNone]
    simp [xB, tB, NoneCol.col]
  have hsN : ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).rowN =
      (D.Dset y).card + ∑ x ∈ (D.KZ 1 y).filter (fun x => 1 ≤ D.kk x), (D.kk x : ℝ) := by
    unfold sB
    rw [sum_insertNone]
    simp [xB, tB, NoneCol.col]
  have hsO : ∑ i ∈ D.sB y, D.xB y i * ((D.tB i).col (fun j : ℕ => U D.γ D.r 0 j)).obj =
      (D.Dset y).card + ∑ x ∈ (D.KZ 1 y).filter (fun x => 1 ≤ D.kk x), min (D.kk x : ℝ) D.γ := by
    unfold sB
    rw [sum_insertNone]
    simp [xB, tB, NoneCol.col, U]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    cases i with
    | none => exact Nat.cast_nonneg _
    | some _ => exact zero_le_one
  · intro i hi
    cases i with
    | none => trivial
    | some x =>
      unfold sB at hi
      rw [mem_insertNone] at hi
      exact (mem_filter.mp (hi x rfl)).2
  · rw [hsZ]
    have h := base_rowZ (y := y) (E := D.E 1) (Y := D.Ys 0) hβlt
    have h2 : ((D.KZ 1 y).card : ℝ) ≤ D.Q := by exact_mod_cast KZ_card_le hD 1 hy
    have h3 : ((D.Dset y).card : ℝ) + ((D.KZ 1 y).filter (fun x => 1 ≤ D.kk x)).card ≤
        (D.KZ 1 y).card := by
      rw [hDs, hK]; simp only [hkk]; exact_mod_cast h
    linarith [hD.hQ]
  · rw [hsN]
    have h := base_rowN (y := y) (E := D.E 1) (Y := D.Ys 0) hβlt hlen
    show _ ≤ ((fullM (D.β 1) D.hgt y (D.E 1)).card : ℝ)
    rw [hDs, hK]; simp only [hkk]; exact_mod_cast h
  · rw [hsO]
    have h := base_value (y := y) (E := D.E 1) (Y := D.Ys 0) hβ hyE
      (le_trans zero_le_one hD.h1) (Q := D.Q)
      (by have := hD.hQ; unfold X at this; push_cast at this; exact this)
    have hZ0 : ∀ x, D.Zs 0 x = Z0 D.hgt (D.E 1) (D.Ys 0) x := by
      intro x; unfold Zs Z0; rw [hE]
    have hP2 : ∀ x, D.P2 x = P2z (D.β 1) D.hgt (D.E 1) (D.Ys 0) x := by
      intro x; unfold P2 P2z; rw [hZ0]
    have hV : D.Val 1 y = ∑ x ∈ KZa (D.E 1) (D.Ys 0) y,
        min ((Z0 D.hgt (D.E 1) (D.Ys 0) x).card : ℝ) D.Q := by
      show ∑ x ∈ D.KZ 1 y, min ((D.Zs 0 x).card : ℝ) D.Q = _
      rw [hK]; exact sum_congr rfl fun x _ => by rw [hZ0]
    have hJ : D.J1 y = ∑ x ∈ KZa (D.E 1) (D.Ys 0) y,
        ((P2z (D.β 1) D.hgt (D.E 1) (D.Ys 0) x).card : ℝ) := by
      unfold J1; rw [hK]; exact sum_congr rfl fun x _ => by rw [hP2]
    have hUc : D.Uc 1 y = ((((nodes D.hgt).filter (inZ (D.E 1) y)).filter
        (fun u => u.length < D.β 1)).card : ℝ) := rfl
    have hXc : ((D.X : ℕ) : ℝ) = 2 ^ D.H := by unfold X; push_cast; rfl
    rw [hV, hJ, hUc, hXc, hDs, hK]
    simp only [hkk]
    exact h

/-! ### 族の仮定・τ と Junk の和・`|E_L|` -/

theorem toFamily_hyp (hD : D.Ok) : D.toFamily.Hyp where
  hX := Nat.one_le_two_pow
  h1 := hD.h1
  h2 := hD.h2
  hYE := hyp_hYE
  hKZ := hyp_hKZ
  hchild := hyp_hchild
  hbud := hyp_hbud hD
  hVal := hyp_hVal
  hU := hyp_hU
  hM := hyp_hM
  hb := hyp_hb hD
  hbase := hyp_hbase hD

/-- **`Σ_Z τ_Z ≤ X |E_L|`**（紙の総和の段落・検算 F1．`junkLevel_le`・`top_bound` の仮定 `hτ`）． -/
theorem tau_sum_le (hD : D.Ok) (L : ℕ) : ∑ z ∈ D.Ys L, D.τ L z ≤ D.X * (D.E L).card := by
  classical
  rcases Nat.lt_or_ge D.top L with hL | hL
  · rw [D.Ys_empty hL, sum_empty]; exact Nat.zero_le _
  match L, hL with
  | 0, _ => simp [τ, KZ]
  | 1, _ => simp [τ, KZ, RE]
  | L + 2, hL =>
    rw [sum_congr rfl fun y hy => D.tau_eq hy]
    exact tau_sum_abs (β := D.β (L + 2)) (H := D.H) (hgt := D.hgt) (Y := D.Ys (L + 1))
      (by rw [← D.β_succ (by omega)]; exact D.β_lt hD.hH (by omega)) (fun y hy => D.Ys_sub_E _ hy)

theorem J1_eq {y : Node} (hy : y ∈ D.Ys 1) :
    D.J1 y = ∑ x ∈ KZa (D.E 1) (D.Ys 0) y, ((P2z (D.β 1) D.hgt (D.E 1) (D.Ys 0) x).card : ℝ) := by
  classical
  have hL := D.Ys_pos hy
  have hK := D.KZ_eq (L := 0) (by omega) hy
  have hE : D.E 0 = D.E 1 ∪ D.Ys 0 := (D.Ys_succ (L := 0) (by omega)).2
  unfold J1
  rw [hK]
  refine sum_congr rfl fun x _ => ?_
  unfold P2 P2z Zs Z0
  rw [hE]

/-- **基底の Junk の和** `Σ_y J1 ≤ X |E_1|`（紙 R1 1.4 (J) の基底の項）． -/
theorem J1_sum_le (_hD : D.Ok) : ∑ y ∈ D.Ys 1, D.J1 y ≤ (D.X : ℝ) * (D.E 1).card := by
  classical
  rcases Nat.lt_or_ge D.top 1 with hL | hL
  · rw [D.Ys_empty hL, sum_empty]; positivity
  rw [sum_congr rfl fun y hy => J1_eq hy]
  have h := J_sum_abs (β := D.β 1) (H := D.H) (hgt := D.hgt) (E := D.E 1) (Y := D.Ys 0)
    D.β_one_add (S := D.Ys 1) (fun y hy => D.Ys_sub_E _ hy)
  have h' : (∑ y ∈ D.Ys 1, ∑ x ∈ KZa (D.E 1) (D.Ys 0) y,
      ((P2z (D.β 1) D.hgt (D.E 1) (D.Ys 0) x).card : ℝ)) ≤ ((2 ^ D.H * (D.E 1).card : ℕ) : ℝ) := by
    exact_mod_cast h
  have hX : ((D.X : ℕ) : ℝ) = 2 ^ D.H := by unfold X; push_cast; rfl
  rw [hX]
  push_cast at h'
  exact h'

/-- **`|E_L|` の上界**: 段 `top − d` で `|Ys| ≤ Q^d`，`|E| ≤ Σ_{j ≤ d} Q^j`． -/
theorem card_lv_le (hD : D.Ok) : ∀ d, d ≤ D.top →
    (D.Ys (D.top - d)).card ≤ D.Q ^ d ∧
      (D.E (D.top - d)).card ≤ ∑ j ∈ range (d + 1), D.Q ^ j := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, D.Ys_top, D.E_top]
    simp
  | succ d ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨L, hL⟩ : ∃ L, L = D.top - (d + 1) := ⟨_, rfl⟩
    rw [← hL]
    have hL1 : L + 1 = D.top - d := by omega
    rw [← hL1] at h1 h2
    obtain ⟨hY, hE⟩ := D.Ys_succ (L := L) (by omega)
    have hYc : (D.Ys L).card ≤ D.Q ^ (d + 1) := by
      rw [hY]
      refine card_biUnion_le.trans ?_
      calc ∑ y ∈ D.Ys (L + 1), (D.KZ (L + 1) y).card ≤ ∑ _y ∈ D.Ys (L + 1), D.Q :=
            sum_le_sum fun y hy => KZ_card_le hD _ hy
        _ = (D.Ys (L + 1)).card * D.Q := by rw [sum_const, smul_eq_mul]
        _ ≤ D.Q ^ d * D.Q := Nat.mul_le_mul_right _ h1
        _ = D.Q ^ (d + 1) := by rw [pow_succ]
    refine ⟨hYc, ?_⟩
    rw [hE, sum_range_succ _ (d + 1)]
    exact (card_union_le _ _).trans (Nat.add_le_add h2 hYc)

theorem card_E_le (hD : D.Ok) {L : ℕ} (hL : L ≤ D.top) :
    (D.E L).card ≤ ∑ j ∈ range (D.top - L + 1), D.Q ^ j := by
  have := (card_lv_le hD (D.top - L) (by omega)).2
  rwa [show D.top - (D.top - L) = L by omega] at this

/-! ### 最上段: `top_bound` に入れた形 -/

open Classical in
/-- **最上段の値の上界**（`top = T + 1 = m − 1`．紙 2.8 の総和の段落の，`O(X^{m−1})` に丸める前の形）:
`Val(Z_top) ≤ 2^{β 1} + X|E_1| + Σ_{L=2}^{T+1} (X^L + 3 C_L X^L) |E_L| + X^{T+2} 2^r σ_{T+2,r}(γ)`． -/
theorem val_top_le (hD : D.Ok) {T : ℕ} (hT : D.top = T + 1) :
    D.Val (T + 1) [] ≤ (2 : ℝ) ^ D.β 1 + (D.X : ℝ) * (D.E 1).card +
      ∑ L ∈ Icc 2 (T + 1), (D.X : ℝ) ^ L * (D.E L).card +
      ∑ L ∈ Icc 2 (T + 1), 3 * CL D.r L * (D.X : ℝ) ^ L * (D.E L).card +
      (D.X : ℝ) ^ (T + 2) * (2 ^ D.r * genrSigma (T + 2) D.r D.γ) := by
  have hF := toFamily_hyp hD
  have hy0 : ([] : Node) ∈ D.toFamily.Ys (T + 1) := by
    show [] ∈ D.Ys (T + 1); rw [← hT, D.Ys_top]; exact mem_singleton_self _
  have hMtop : (D.toFamily.Mz (T + 1) [] : ℝ) ≤ 2 ^ D.toFamily.r * D.toFamily.X := by
    show ((fullM (D.β (T + 1)) D.hgt [] (D.E (T + 1))).card : ℝ) ≤ 2 ^ D.r * ((D.X : ℕ) : ℝ)
    have h1 : (fullM (D.β (T + 1)) D.hgt [] (D.E (T + 1))).card ≤ 2 ^ D.H * 2 ^ D.r := by
      have hb : D.β (T + 1) = D.H + D.r := by rw [← hT]; exact D.β_top
      unfold fullM
      refine (card_filter_le _ _).trans (le_of_eq ?_)
      rw [card_words, hb, pow_add]
    have h2 : ((fullM (D.β (T + 1)) D.hgt [] (D.E (T + 1))).card : ℝ) ≤ ((2 ^ D.H * 2 ^ D.r : ℕ) : ℝ) := by
      exact_mod_cast h1
    unfold X
    push_cast at h2 ⊢
    linarith
  have hJ : ∀ y ∈ D.toFamily.Ys 1, 0 ≤ D.toFamily.J1 y := by
    intro y _
    show 0 ≤ D.J1 y
    unfold J1
    positivity
  have hτ : ∀ L, ∑ z ∈ D.toFamily.Ys L, D.toFamily.τ L z ≤ D.toFamily.X * (D.toFamily.E L).card :=
    tau_sum_le hD
  have h := ZoneFamily.top_bound hF hJ hτ T [] hy0 hMtop
  -- U の部分と Junk の基底
  have hUc : D.Uc (T + 1) [] ≤ (2 : ℝ) ^ D.β 1 := by
    unfold Uc
    have hsub : (D.Zs (T + 1) []).filter (fun u => u.length < D.β 1) ⊆ nodes (D.β 1) := by
      intro u hu; exact mem_nodes.mpr (mem_filter.mp hu).2
    have h1 := (card_le_card hsub).trans (le_of_eq (card_nodes (D.β 1)))
    have h2 : 2 ^ D.β 1 - 1 ≤ 2 ^ D.β 1 := Nat.sub_le _ _
    exact_mod_cast h1.trans h2
  have hJ1 := J1_sum_le hD
  change D.Val (T + 1) [] ≤ D.Uc (T + 1) [] +
      (∑ y ∈ D.Ys 1, D.J1 y + ∑ L ∈ Icc 2 (T + 1), (D.X : ℝ) ^ L * (D.E L).card) +
      ∑ L ∈ Icc 2 (T + 1), 3 * CL D.r L * (D.X : ℝ) ^ L * (D.E L).card +
      (D.X : ℝ) ^ (T + 2) * (2 ^ D.r * genrSigma (T + 2) D.r D.γ) at h
  linarith

end CutData

end GenRZones
end SpookyTree
