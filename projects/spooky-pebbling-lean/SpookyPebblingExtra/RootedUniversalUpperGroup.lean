/-
# 定理 U: 区域と群分け（紙の補題 1）

紙 `UNIVERSAL_UB_2026-11.md` の 1・2 節。区域（頂 `z` から下に連結な頂点の集合）`Zone` と、
区域の群分け `Grp`（頂の集合 `T` と各頂の群 `g a`）を定義し、子の数が `d` 以下の木で
閾値 `S ≥ 1` の群分けが存在することを示す（`grp_exists`）。

**紙との違い（証明の組み立てだけ）.** 紙は後行順に余り `R(v)` を積んで閾値で群を閉じる。ここでは
同じ結論（群の大きさ `≤ 1 + d(S−1)`、頂の数 `≤ ⌊(|Z|−1)/S⌋ + d`、群の穴は他の頂か区域の外）を、
区域の大きさについての強い帰納法で示す: 区域の中の部分木が `S` 以上の頂点のうち部分木が最小の `v`
を選ぶと、その子の部分木はどれも `S` 未満なので `|Z ∩ T_v| ≤ 1 + d(S−1)`。`v` の部分木を群にして
切り取り、残りの区域に帰納法を使う。そのような `v` が無ければ、根の子を頂にする（紙の `B`）。
紙の後行順の貪欲と同じ群分けになるとは主張しない（定理 U に要るのは補題 1 の (a)〜(d) だけ）。
-/
import SpookyPebblingExtra.RootedUniversalUpperBasic

namespace Spooky
namespace RootedTree
namespace UUB

open Finset Classical

variable {t : RootedTree}

/-- 区域: `z ∈ Z`、頂点は `n` 未満で `z` の子孫、`z` 以外の頂点の親は `Z` にある。 -/
def Zone (t : RootedTree) (Z : Finset ℕ) (z : ℕ) : Prop :=
  z ∈ Z ∧ (∀ v ∈ Z, v < t.n) ∧ (∀ v ∈ Z, t.Anc z v) ∧
    (∀ v ∈ Z, v ≠ z → ∃ p ∈ Z, t.par v = some p)

/-- `v` の子（`n` 未満）の集合。 -/
def chs (t : RootedTree) (v : ℕ) : Finset ℕ := (range t.n).filter (fun u => t.par u = some v)

/-- 区域 `Z` の中の `v` の子孫（`v` を含む）。 -/
noncomputable def ZD (t : RootedTree) (Z : Finset ℕ) (v : ℕ) : Finset ℕ := Z.filter (fun x => t.Anc v x)

/-- 群分け（紙の補題 1 の結論）。`T` が頂の集合、`g a` が頂 `a` の群。 -/
structure Grp (t : RootedTree) (d S : ℕ) (Z : Finset ℕ) (z : ℕ) (T : Finset ℕ)
    (g : ℕ → Finset ℕ) : Prop where
  sub : T ⊆ Z.erase z
  zone : ∀ a ∈ T, Zone t (g a) a
  gsub : ∀ a ∈ T, g a ⊆ Z.erase z
  disj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (g a) (g b)
  cover : ∀ v ∈ Z.erase z, ∃ a ∈ T, v ∈ g a
  size : ∀ a ∈ T, (g a).card ≤ 1 + d * (S - 1)
  count : T.card ≤ (Z.card - 1) / S + d
  hole : ∀ a ∈ T, ∀ v ∈ g a, ∀ u, u < t.n → t.par u = some v → u ∈ g a ∨ u ∈ T ∨ u ∉ Z
  topch : ∀ u, u < t.n → t.par u = some z → u ∈ Z → u ∈ T

/-! ## 区域の性質 -/

theorem Zone.mem {Z : Finset ℕ} {z : ℕ} (h : Zone t Z z) : z ∈ Z := h.1
theorem Zone.lt {Z : Finset ℕ} {z : ℕ} (h : Zone t Z z) : ∀ v ∈ Z, v < t.n := h.2.1
theorem Zone.anc {Z : Finset ℕ} {z : ℕ} (h : Zone t Z z) : ∀ v ∈ Z, t.Anc z v := h.2.2.1
theorem Zone.up {Z : Finset ℕ} {z : ℕ} (h : Zone t Z z) :
    ∀ v ∈ Z, v ≠ z → ∃ p ∈ Z, t.par v = some p := h.2.2.2

theorem Zone.card_pos {Z : Finset ℕ} {z : ℕ} (h : Zone t Z z) : 1 ≤ Z.card :=
  Finset.card_pos.mpr ⟨z, h.mem⟩

/-- 区域の頂は区域の頂点の子でない。 -/
theorem Zone.top_not_child (ht : t.isTree = true) {Z : Finset ℕ} {z v : ℕ} (hZ : Zone t Z z)
    (hv : v ∈ Z) (hp : t.par z = some v) : False := by
  have hzn := hZ.lt z hZ.mem
  have h1 : v = z := anc_antisymm ht hzn (anc_of_par hp) (hZ.anc v hv)
  subst h1
  exact par_ne ht hzn hp rfl

/-- 区域の頂点 `x` と頂 `z` の間にある頂点は区域にある。 -/
theorem Zone.between (ht : t.isTree = true) {Z : Finset ℕ} {z : ℕ} (hZ : Zone t Z z) {b x : ℕ}
    (hx : x ∈ Z) (hbx : t.Anc b x) (hzb : t.Anc z b) : b ∈ Z := by
  obtain ⟨k, hk⟩ := hbx
  induction k generalizing x with
  | zero =>
    have : some x = some b := hk
    rw [← Option.some.inj this]; exact hx
  | succ k ih =>
    by_cases hxz : x = z
    · subst hxz
      have hb : b = x := anc_antisymm ht (hZ.lt x hx) ⟨k + 1, hk⟩ hzb
      rw [hb]; exact hx
    · obtain ⟨p, hpZ, hp⟩ := hZ.up x hx hxz
      have hk' : t.up k (some p) = some b := by
        have : t.up (k + 1) (some x) = t.up k (t.par x) := rfl
        rw [this, hp] at hk; exact hk
      exact ih hpZ hk'

theorem mem_ZD {Z : Finset ℕ} {v x : ℕ} : x ∈ ZD t Z v ↔ x ∈ Z ∧ t.Anc v x := mem_filter

theorem ZD_subset (Z : Finset ℕ) (v : ℕ) : ZD t Z v ⊆ Z := filter_subset _ _

theorem zone_ZD (ht : t.isTree = true) {Z : Finset ℕ} {z v : ℕ} (hZ : Zone t Z z) (hv : v ∈ Z) :
    Zone t (ZD t Z v) v := by
  refine ⟨mem_ZD.mpr ⟨hv, Anc.refl v⟩, fun x hx => hZ.lt x (mem_ZD.mp hx).1,
    fun x hx => (mem_ZD.mp hx).2, ?_⟩
  intro x hx hxv
  obtain ⟨hxZ, hvx⟩ := mem_ZD.mp hx
  have hxz : x ≠ z := by
    rintro rfl
    exact hxv (anc_antisymm ht (hZ.lt x hxZ) hvx (hZ.anc v hv)).symm
  obtain ⟨p, hpZ, hp⟩ := hZ.up x hxZ hxz
  refine ⟨p, mem_ZD.mpr ⟨hpZ, ?_⟩, hp⟩
  rcases anc_cases hvx with h | ⟨d', hd', hvd'⟩
  · exact absurd h.symm hxv
  · rw [hp] at hd'; cases hd'; exact hvd'

theorem ZD_sub_erase (ht : t.isTree = true) {Z : Finset ℕ} {z v : ℕ} (hZ : Zone t Z z) (hv : v ∈ Z)
    (hvz : v ≠ z) : ZD t Z v ⊆ Z.erase z := by
  intro x hx
  obtain ⟨hxZ, hvx⟩ := mem_ZD.mp hx
  refine mem_erase.mpr ⟨?_, hxZ⟩
  rintro rfl
  exact hvz (anc_antisymm ht (hZ.lt x hxZ) hvx (hZ.anc v hv))

theorem zone_diff (ht : t.isTree = true) {Z : Finset ℕ} {z v : ℕ} (hZ : Zone t Z z) (hv : v ∈ Z)
    (hvz : v ≠ z) : Zone t (Z.filter (fun x => ¬ t.Anc v x)) z := by
  refine ⟨mem_filter.mpr ⟨hZ.mem, ?_⟩, fun x hx => hZ.lt x (mem_filter.mp hx).1,
    fun x hx => hZ.anc x (mem_filter.mp hx).1, ?_⟩
  · intro hvz'
    exact hvz (anc_antisymm ht (hZ.lt z hZ.mem) hvz' (hZ.anc v hv))
  · intro x hx hxz
    obtain ⟨hxZ, hnx⟩ := mem_filter.mp hx
    obtain ⟨p, hpZ, hp⟩ := hZ.up x hxZ hxz
    refine ⟨p, mem_filter.mpr ⟨hpZ, fun hvp => hnx (Anc.trans hvp (anc_of_par hp))⟩, hp⟩

/-- 兄弟の子孫は交わらない。 -/
theorem ZD_disj_siblings (ht : t.isTree = true) {Z : Finset ℕ} {y a b : ℕ} (ha : a < t.n)
    (hb : b < t.n) (hpa : t.par a = some y) (hpb : t.par b = some y) (hab : a ≠ b) :
    Disjoint (ZD t Z a) (ZD t Z b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨_, hax⟩ := mem_ZD.mp hxa
  obtain ⟨_, hbx⟩ := mem_ZD.mp hxb
  have key : ∀ {a b : ℕ}, a < t.n → b < t.n → t.par a = some y → t.par b = some y → a ≠ b →
      t.Anc a b → False := by
    intro a b ha hb hpa hpb hab h
    rcases anc_cases h with h1 | ⟨d', hd', had'⟩
    · exact hab h1
    · rw [hpb] at hd'; cases hd'
      have hyn : y < t.n := (parOk_some ((isTree_spec ht).2 a ha).1 hpa).1
      have : a = y := anc_antisymm ht hyn had' (anc_of_par hpa)
      exact par_ne ht ha hpa this
  rcases anc_total hax hbx with h | h
  · exact key ha hb hpa hpb hab h
  · exact key hb ha hpb hpa (Ne.symm hab) h

/-- 区域の中の部分木の大きさ: 子の部分木（区域の中）がどれも `S − 1` 以下なら `≤ 1 + d(S−1)`。 -/
theorem card_ZD_le (ht : t.isTree = true) {d S : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    {Z : Finset ℕ} {z v : ℕ} (hZ : Zone t Z z) (hv : v ∈ Z)
    (hS : ∀ c, c < t.n → t.par c = some v → c ∈ Z → (ZD t Z c).card ≤ S - 1) :
    (ZD t Z v).card ≤ 1 + d * (S - 1) := by
  set C := (chs t v).filter (· ∈ Z) with hC
  have hsub : ZD t Z v ⊆ insert v (C.biUnion (ZD t Z)) := by
    intro x hx
    obtain ⟨hxZ, hvx⟩ := mem_ZD.mp hx
    by_cases hxv : x = v
    · rw [hxv]; exact mem_insert_self _ _
    · obtain ⟨b, hbn, hpb, hbx⟩ := anc_child ht (hZ.lt x hxZ) hvx hxv
      have hbZ : b ∈ Z := hZ.between ht hxZ hbx (Anc.trans (hZ.anc v hv) (anc_of_par hpb))
      refine mem_insert_of_mem (mem_biUnion.mpr ⟨b, ?_, mem_ZD.mpr ⟨hxZ, hbx⟩⟩)
      rw [hC, mem_filter]
      exact ⟨mem_filter.mpr ⟨mem_range.mpr hbn, hpb⟩, hbZ⟩
  have hCd : C.card ≤ d := le_trans (card_filter_le _ _) (hd v (hZ.lt v hv))
  have hsum : ∑ c ∈ C, (ZD t Z c).card ≤ C.card * (S - 1) := by
    have := Finset.sum_le_card_nsmul C (fun c => (ZD t Z c).card) (S - 1) (by
      intro c hc
      rw [hC, mem_filter] at hc
      obtain ⟨hc1, hcZ⟩ := hc
      obtain ⟨hcn, hpc⟩ := mem_filter.mp hc1
      exact hS c (mem_range.mp hcn) hpc hcZ)
    simpa using this
  calc (ZD t Z v).card ≤ (insert v (C.biUnion (ZD t Z))).card := card_le_card hsub
    _ ≤ (C.biUnion (ZD t Z)).card + 1 := card_insert_le _ _
    _ ≤ ∑ c ∈ C, (ZD t Z c).card + 1 := Nat.add_le_add_right card_biUnion_le _
    _ ≤ C.card * (S - 1) + 1 := Nat.add_le_add_right hsum _
    _ ≤ 1 + d * (S - 1) := by
        have := Nat.mul_le_mul_right (S - 1) hCd
        omega

/-! ## 群分けの存在（補題 1） -/

/-- **補題 1（群分け）.** 子の数が `d` 以下の木の区域 `Z`（頂 `z`）と `S ≥ 1` について群分けがある。 -/
theorem grp_exists (ht : t.isTree = true) {d S : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (hS : 1 ≤ S) (Z : Finset ℕ) : ∀ z, Zone t Z z → ∃ T g, Grp t d S Z z T g := by
  induction Z using Finset.strongInduction with
  | H Z ih =>
  intro z hZ
  by_cases hA : ∃ v ∈ Z.erase z, S ≤ (ZD t Z v).card
  · -- 部分木が S 以上の頂点のうち、部分木が最小のもの
    set Cand := (Z.erase z).filter (fun v => S ≤ (ZD t Z v).card) with hCand
    have hne : Cand.Nonempty := by
      obtain ⟨v, hv, hvS⟩ := hA
      exact ⟨v, mem_filter.mpr ⟨hv, hvS⟩⟩
    obtain ⟨v, hvC, hmin⟩ := Cand.exists_min_image (fun v => (ZD t Z v).card) hne
    obtain ⟨hvE, hvS⟩ := mem_filter.mp hvC
    obtain ⟨hvz, hvZ⟩ := mem_erase.mp hvE
    have hvn := hZ.lt v hvZ
    -- 子の部分木は S 未満
    have hchS : ∀ c, c < t.n → t.par c = some v → c ∈ Z → (ZD t Z c).card ≤ S - 1 := by
      intro c hcn hpc hcZ
      by_contra hcon
      have hcS : S ≤ (ZD t Z c).card := by omega
      have hcz : c ≠ z := by
        rintro rfl
        exact hZ.top_not_child ht hvZ hpc
      have hcC : c ∈ Cand := mem_filter.mpr ⟨mem_erase.mpr ⟨hcz, hcZ⟩, hcS⟩
      have h1 := hmin c hcC
      have hlt : (ZD t Z c).card < (ZD t Z v).card := by
        apply card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨v, mem_ZD.mpr ⟨hvZ, Anc.refl v⟩, ?_⟩
          intro hv'
          have hcv : t.Anc c v := (mem_ZD.mp hv').2
          have : v = c := anc_antisymm ht hcn (anc_of_par hpc) hcv
          exact par_ne ht hcn hpc this.symm
        · intro x hx
          obtain ⟨hxZ, hcx⟩ := mem_ZD.mp hx
          exact mem_ZD.mpr ⟨hxZ, Anc.trans (anc_of_par hpc) hcx⟩
      omega
    have hsize : (ZD t Z v).card ≤ 1 + d * (S - 1) := card_ZD_le ht hd hZ hvZ hchS
    set Z' := Z.filter (fun x => ¬ t.Anc v x) with hZ'
    have hZ'z : Zone t Z' z := zone_diff ht hZ hvZ hvz
    have hvZ' : v ∉ Z' := fun h => (mem_filter.mp h).2 (Anc.refl v)
    have hss : Z' ⊂ Z := by
      rw [Finset.ssubset_iff_of_subset (filter_subset _ _)]
      exact ⟨v, hvZ, hvZ'⟩
    have hcardZ : Z'.card + (ZD t Z v).card = Z.card := by
      rw [hZ', ZD, add_comm]
      exact card_filter_add_card_filter_not _
    obtain ⟨T', g', hG⟩ := ih Z' hss z hZ'z
    have hvT' : v ∉ T' := fun h => hvZ' (mem_of_mem_erase (hG.sub h))
    have hgv : (if v = v then ZD t Z v else g' v) = ZD t Z v := if_pos rfl
    have hga : ∀ a ∈ T', (if a = v then ZD t Z v else g' a) = g' a := by
      intro a ha
      exact if_neg (fun h => hvT' (by rw [← h]; exact ha))
    -- `Z'` の頂点の子で `v` の子孫になるのは `v` だけ
    have hchild_v : ∀ x ∈ Z', ∀ u, t.par u = some x → t.Anc v u → u = v := by
      intro x hx u hpu hvu
      rcases anc_cases hvu with h | ⟨d', hd', hvd'⟩
      · exact h.symm
      · rw [hpu] at hd'; cases hd'
        exact absurd hvd' (mem_filter.mp hx).2
    have hZ'sub : Z' ⊆ Z := filter_subset _ _
    refine ⟨insert v T', fun a => if a = v then ZD t Z v else g' a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- sub
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hvE
      · exact erase_subset_erase z hZ'sub (hG.sub ha)
    · -- zone
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · simp only [hgv]; exact zone_ZD ht hZ hvZ
      · simp only [hga a ha]; exact hG.zone a ha
    · -- gsub
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · simp only [hgv]; exact ZD_sub_erase ht hZ hvZ hvz
      · simp only [hga a ha]; exact (hG.gsub a ha).trans (erase_subset_erase z hZ'sub)
    · -- disj
      have hdv : ∀ a ∈ T', Disjoint (ZD t Z v) (g' a) := by
        intro a ha
        rw [Finset.disjoint_left]
        intro x hx hx'
        have := mem_of_mem_erase (hG.gsub a ha hx')
        exact (mem_filter.mp this).2 (mem_ZD.mp hx).2
      intro a ha b hb hab
      rcases mem_insert.mp ha with hav | ha'
      · subst hav
        rcases mem_insert.mp hb with hbv | hb'
        · exact absurd hbv.symm hab
        · simp only [hgv, hga b hb']; exact hdv b hb'
      · rcases mem_insert.mp hb with hbv | hb'
        · subst hbv
          simp only [hgv, hga a ha']; exact (hdv a ha').symm
        · simp only [hga a ha', hga b hb']; exact hG.disj a ha' b hb' hab
    · -- cover
      intro x hx
      obtain ⟨hxz, hxZ⟩ := mem_erase.mp hx
      by_cases hvx : t.Anc v x
      · exact ⟨v, mem_insert_self _ _, by simp only [hgv]; exact mem_ZD.mpr ⟨hxZ, hvx⟩⟩
      · obtain ⟨a, ha, hxa⟩ := hG.cover x (mem_erase.mpr ⟨hxz, mem_filter.mpr ⟨hxZ, hvx⟩⟩)
        exact ⟨a, mem_insert_of_mem ha, by simp only [hga a ha]; exact hxa⟩
    · -- size
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · simp only [hgv]; exact hsize
      · simp only [hga a ha]; exact hG.size a ha
    · -- count
      rw [card_insert_of_notMem hvT']
      have h1 := hG.count
      have h2 := hZ'z.card_pos
      have h3 : (Z'.card - 1) / S + 1 ≤ (Z.card - 1) / S := by
        have : (Z'.card - 1) / S + 1 = (Z'.card - 1 + S) / S := by
          rw [Nat.add_div_right _ (by omega)]
        rw [this]
        exact Nat.div_le_div_right (by omega)
      omega
    · -- hole
      intro a ha x hx u hun hpu
      rcases mem_insert.mp ha with rfl | ha
      · simp only [hgv] at hx ⊢
        obtain ⟨hxZ, hax⟩ := mem_ZD.mp hx
        by_cases huZ : u ∈ Z
        · exact Or.inl (mem_ZD.mpr ⟨huZ, Anc.trans hax (anc_of_par hpu)⟩)
        · exact Or.inr (Or.inr huZ)
      · simp only [hga a ha] at hx ⊢
        have hxZ' : x ∈ Z' := mem_of_mem_erase (hG.gsub a ha hx)
        rcases hG.hole a ha x hx u hun hpu with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (mem_insert_of_mem h))
        · by_cases huZ : u ∈ Z
          · have hvu : t.Anc v u := by
              by_contra hn
              exact h (mem_filter.mpr ⟨huZ, hn⟩)
            rw [hchild_v x hxZ' u hpu hvu]
            exact Or.inr (Or.inl (mem_insert_self _ _))
          · exact Or.inr (Or.inr huZ)
    · -- topch
      intro u hun hpu huZ
      by_cases hvu : t.Anc v u
      · rw [hchild_v z (mem_filter.mpr ⟨hZ.mem, fun h =>
            hvz (anc_antisymm ht (hZ.lt z hZ.mem) h (hZ.anc v hvZ))⟩) u hpu hvu]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (hG.topch u hun hpu (mem_filter.mpr ⟨huZ, hvu⟩))
  · -- どの頂点の部分木も S 未満: 根の子を頂にする
    push Not at hA
    set T := (chs t z).filter (· ∈ Z) with hT
    have hmemT : ∀ {a}, a ∈ T ↔ a < t.n ∧ t.par a = some z ∧ a ∈ Z := by
      intro a
      rw [hT, mem_filter, chs, mem_filter, mem_range, and_assoc]
    have hTz : ∀ a ∈ T, a ≠ z := by
      intro a ha
      obtain ⟨han, hpa, _⟩ := hmemT.mp ha
      exact par_ne ht han hpa
    refine ⟨T, ZD t Z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact mem_erase.mpr ⟨hTz a ha, (hmemT.mp ha).2.2⟩
    · intro a ha
      exact zone_ZD ht hZ (hmemT.mp ha).2.2
    · intro a ha
      exact ZD_sub_erase ht hZ (hmemT.mp ha).2.2 (hTz a ha)
    · intro a ha b hb hab
      obtain ⟨han, hpa, _⟩ := hmemT.mp ha
      obtain ⟨hbn, hpb, _⟩ := hmemT.mp hb
      exact ZD_disj_siblings ht han hbn hpa hpb hab
    · intro x hx
      obtain ⟨hxz, hxZ⟩ := mem_erase.mp hx
      obtain ⟨b, hbn, hpb, hbx⟩ := anc_child ht (hZ.lt x hxZ) (hZ.anc x hxZ) hxz
      have hbZ : b ∈ Z := hZ.between ht hxZ hbx (anc_of_par hpb)
      exact ⟨b, hmemT.mpr ⟨hbn, hpb, hbZ⟩, mem_ZD.mpr ⟨hxZ, hbx⟩⟩
    · intro a ha
      obtain ⟨han, hpa, haZ⟩ := hmemT.mp ha
      have h1 := hA a (mem_erase.mpr ⟨hTz a ha, haZ⟩)
      have hd1 : 1 ≤ d := by
        have := hd z (hZ.lt z hZ.mem)
        have hpos : 0 < (chs t z).card :=
          card_pos.mpr ⟨a, mem_filter.mpr ⟨mem_range.mpr han, hpa⟩⟩
        omega
      have : S - 1 ≤ d * (S - 1) := Nat.le_mul_of_pos_left _ hd1
      omega
    · have : T.card ≤ d := le_trans (card_filter_le _ _) (hd z (hZ.lt z hZ.mem))
      exact le_trans this (Nat.le_add_left _ _)
    · intro a ha x hx u hun hpu
      obtain ⟨_, hax⟩ := mem_ZD.mp hx
      by_cases huZ : u ∈ Z
      · exact Or.inl (mem_ZD.mpr ⟨huZ, Anc.trans hax (anc_of_par hpu)⟩)
      · exact Or.inr (Or.inr huZ)
    · intro u hun hpu huZ
      exact hmemT.mpr ⟨hun, hpu, huZ⟩

/-- 群の大きさの和は `|Z| − 1` 以下（群は互いに素で `Z ∖ {z}` に入る）。 -/
theorem Grp.sum_card_le {d S : ℕ} {Z : Finset ℕ} {z : ℕ} {T : Finset ℕ} {g : ℕ → Finset ℕ}
    (hG : Grp t d S Z z T g) (hz : z ∈ Z) {U : Finset ℕ} (hU : U ⊆ T) :
    ∑ a ∈ U, (g a).card ≤ Z.card - 1 := by
  have hdis : (U : Set ℕ).PairwiseDisjoint g := by
    intro a ha b hb hab
    exact hG.disj a (hU ha) b (hU hb) hab
  rw [← card_biUnion hdis]
  have hsub : U.biUnion g ⊆ Z.erase z := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_biUnion.mp hx
    exact hG.gsub a (hU ha) hxa
  have := card_le_card hsub
  rw [card_erase_of_mem hz] at this
  exact this

end UUB
end RootedTree
end Spooky
