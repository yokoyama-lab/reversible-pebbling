/-
# 窓・一般の m・h ≡ 1 (mod m) の下界: ブロックと段ごとの数え上げ（木の形を使わない部分）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 1 節（定理 L_{m,1}）。
紙は「区域の値 Val(Z) ≤ |Z ∩ U| + Junk(Z) + Φ_k(M_k(Z))」と汚れたブロックの全体の数え上げ（E_m）を分けるが，
ここでは区域ごとに閉じた形の 1 歩だけを示す（`count_step`）:

  `Z` の頂点の集合 `K`（`|K| ≤ Q`）と `K` の点 `u` ごとの互いに素な子 `C u ⊆ Z`（`u` の真の子孫）があり，
  `Z` にすべて入る深さ `Dp` の部分木で `K` の点を含まないものは，ある `C u` にすべて入る（紙の事実 F）とする。
  `M_c(u)` を `C u` にすべて入る深さ `Dp + L` の部分木の数，`M_p` を `Z` にすべて入る深さ `Dp` の部分木の数とすると，
    `X σ M_p + Σ_u Ψ(M_c(u)) ≤ min(X σ M_p, λ_C Q + λ_S M_p) + σ Σ_u M_c(u)`（`X = 2^L`）。
  仮定は `Ψ(0) = 0`，傾き `Ψ(M + t) ≤ Ψ(M) + σ t`，`j ≥ 1` で `Ψ(X j) ≤ λ_C + λ_S j`，`X σ ≤ λ_C + λ_S`。

`σ M − Ψ(M)` を区域の「節約」と読むと，親の節約は子の節約の和以下という形（紙の補題 S の (e)〜(g) と双対 D1・D2 にあたる）。
汚れた（`K` の点を含む）親のブロックは `X σ` を払う（紙の `a_{k−1}ρ_Z`）。紙の Junk・E_m・U はここには現れない。
-/
import SpookyTree.WindowM3LowerCount

namespace SpookyTree

/-! ## ブロック -/

open Classical in
/-- `Z` にすべて入る（高さ `h` の木の中の）部分木の，深さ `D` の根。 -/
noncomputable def fullRoots (h D : ℕ) (Z : Finset Node) : Finset Node :=
  (words D).filter (fun b => subtree h b ⊆ Z)

/-- `Z` にすべて入る深さ `D` の部分木の数（紙の `M_k(Z)`）。 -/
noncomputable def fullM (h D : ℕ) (Z : Finset Node) : ℕ := (fullRoots h D Z).card

open Classical in
theorem mem_fullRoots {h D : ℕ} {Z : Finset Node} {b : Node} :
    b ∈ fullRoots h D Z ↔ b.length = D ∧ subtree h b ⊆ Z := by
  unfold fullRoots; rw [Finset.mem_filter, mem_words]

theorem self_mem_subtree {h : ℕ} {b : Node} (hb : b.length < h) : b ∈ subtree h b :=
  mem_subtree.mpr ⟨hb, List.prefix_refl b⟩

/-- 木全体では深さ `D` の頂点はすべて根。 -/
theorem fullM_nodes (h D : ℕ) : fullM h D (nodes h) = 2 ^ D := by
  unfold fullM
  have : fullRoots h D (nodes h) = words D := by
    ext b
    rw [mem_fullRoots, mem_words]
    constructor
    · exact fun hb => hb.1
    · intro hb
      exact ⟨hb, fun z hz => mem_nodes.mpr (mem_subtree.mp hz).1⟩
  rw [this, card_words]

theorem fullM_empty {h D : ℕ} (hD : D < h) : fullM h D ∅ = 0 := by
  unfold fullM
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  obtain ⟨hbl, hbs⟩ := mem_fullRoots.mp hb
  have := hbs (self_mem_subtree (by omega))
  simp at this

/-- 深さ `D + L` の部分木は深さ `D` の部分木 1 個に `2^L` 個ずつ入る。 -/
theorem fullM_mul_le (h D L : ℕ) (Z : Finset Node) :
    2 ^ L * fullM h D Z ≤ fullM h (D + L) Z := by
  unfold fullM
  have hsub : ((fullRoots h D Z) ×ˢ (words L)).image (fun x => x.1 ++ x.2) ⊆
      fullRoots h (D + L) Z := by
    intro x hx
    obtain ⟨⟨b, w⟩, hbw, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product] at hbw
    obtain ⟨hb, hw⟩ := hbw
    rw [mem_fullRoots] at hb ⊢
    rw [mem_words] at hw
    refine ⟨by simp [hb.1, hw], ?_⟩
    intro z hz
    apply hb.2
    rw [mem_subtree] at hz ⊢
    exact ⟨hz.1, (List.prefix_append b w).trans hz.2⟩
  have hinj : Set.InjOn (fun x : Node × Node => x.1 ++ x.2)
      (((fullRoots h D Z) ×ˢ (words L) : Finset (Node × Node)) : Set (Node × Node)) := by
    rintro ⟨b, w⟩ hbw ⟨b', w'⟩ hbw' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_fullRoots, mem_words] at hbw hbw'
    simp only at heq
    have hl : b.length = b'.length := by rw [hbw.1.1, hbw'.1.1]
    obtain ⟨h1, h2⟩ := List.append_inj heq hl
    rw [h1, h2]
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_words] at this
  rw [mul_comm]
  exact this

/-- `Z` にすべて入る深さ `D` の部分木は互いに素なので，大きさ `2^{h−D} − 1` の和は `|Z|` 以下。 -/
theorem fullM_mul_card_le {h D : ℕ} (Z : Finset Node) :
    (2 ^ (h - D) - 1) * fullM h D Z ≤ Z.card := by
  unfold fullM
  have hd : ((fullRoots h D Z : Finset Node) : Set Node).PairwiseDisjoint (fun b => subtree h b) := by
    intro b hb b' hb' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz hz'
    have e1 := (mem_fullRoots.mp (Finset.mem_coe.mp hb)).1
    have e2 := (mem_fullRoots.mp (Finset.mem_coe.mp hb')).1
    exact hne (prefix_eq_of_length (mem_subtree.mp hz).2 (mem_subtree.mp hz').2 (by rw [e1, e2]))
  have hs := sum_card_le_of_disj hd (fun b hb => (mem_fullRoots.mp hb).2)
  have he : ∀ b ∈ fullRoots h D Z, (subtree h b).card = 2 ^ (h - D) - 1 := by
    intro b hb
    rw [card_subtree, (mem_fullRoots.mp hb).1]
  rw [Finset.sum_congr rfl he, Finset.sum_const, smul_eq_mul] at hs
  rw [mul_comm]
  exact hs

/-! ## 段ごとの数え上げ -/

open Classical in
/-- **段ごとの数え上げ（節約の 1 歩）.** -/
theorem count_step {h Dp L Q σc lC lS : ℕ} {Ψc : ℕ → ℕ} (hDph : Dp < h)
    (Z K : Finset Node) (C : Node → Finset Node)
    (hCsub : ∀ u ∈ K, C u ⊆ Z)
    (hCdisj : (K : Set Node).PairwiseDisjoint C)
    (hCdesc : ∀ u ∈ K, ∀ v ∈ C u, u.length < v.length)
    (hF : ∀ b ∈ fullRoots h Dp Z, (∀ x ∈ K, ¬ b <+: x) → ∃ u ∈ K, subtree h b ⊆ C u)
    (hK : K.card ≤ Q)
    (hΨ0 : Ψc 0 = 0) (hslope : ∀ M t, Ψc (M + t) ≤ Ψc M + σc * t)
    (hg : ∀ j, 1 ≤ j → Ψc (2 ^ L * j) ≤ lC + lS * j)
    (hσ : 2 ^ L * σc ≤ lC + lS) :
    2 ^ L * σc * fullM h Dp Z + ∑ u ∈ K, Ψc (fullM h (Dp + L) (C u)) ≤
      min (2 ^ L * σc * fullM h Dp Z) (lC * Q + lS * fullM h Dp Z) +
        σc * ∑ u ∈ K, fullM h (Dp + L) (C u) := by
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ L := ⟨_, rfl⟩
  rw [← hX] at hg hσ ⊢
  -- Ψ(M) ≤ σ M
  have hle : ∀ M, Ψc M ≤ σc * M := by
    intro M
    have := hslope 0 M
    rw [Nat.zero_add, hΨ0] at this
    omega
  -- (1) u ごとの傾き
  have h1 : ∀ u ∈ K, X * σc * fullM h Dp (C u) + Ψc (fullM h (Dp + L) (C u)) ≤
      σc * fullM h (Dp + L) (C u) + Ψc (X * fullM h Dp (C u)) := by
    intro u _
    have hm := fullM_mul_le h Dp L (C u)
    rw [← hX] at hm
    obtain ⟨t, ht⟩ : ∃ t, fullM h (Dp + L) (C u) = X * fullM h Dp (C u) + t :=
      ⟨_, (Nat.add_sub_cancel' hm).symm⟩
    rw [ht]
    have hs := hslope (X * fullM h Dp (C u)) t
    have e : σc * (X * fullM h Dp (C u) + t) = X * σc * fullM h Dp (C u) + σc * t := by ring
    omega
  have h1s := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1s
  -- (2) 子にすべて入る親のブロック
  have hdisjF : (K : Set Node).PairwiseDisjoint (fun u => fullRoots h Dp (C u)) := by
    intro u hu u' hu' hne
    have hd := hCdisj hu hu' hne
    simp only [Function.onFun] at hd ⊢
    rw [Finset.disjoint_left] at hd ⊢
    intro b hb hb'
    have hbb : b ∈ subtree h b := self_mem_subtree (by rw [(mem_fullRoots.mp hb).1]; exact hDph)
    exact hd ((mem_fullRoots.mp hb).2 hbb) ((mem_fullRoots.mp hb').2 hbb)
  obtain ⟨B, hB⟩ : ∃ B : Finset Node, B = K.biUnion (fun u => fullRoots h Dp (C u)) := ⟨_, rfl⟩
  have hBcard : B.card = ∑ u ∈ K, fullM h Dp (C u) := by
    rw [hB, Finset.card_biUnion hdisjF]; rfl
  have hBsub : B ⊆ fullRoots h Dp Z := by
    intro b hb
    rw [hB, Finset.mem_biUnion] at hb
    obtain ⟨u, hu, hb⟩ := hb
    obtain ⟨h1, h2⟩ := mem_fullRoots.mp hb
    exact mem_fullRoots.mpr ⟨h1, h2.trans (hCsub u hu)⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset Node, R = fullRoots h Dp Z \ B := ⟨_, rfl⟩
  have hRB : R.card + B.card = fullM h Dp Z := by
    rw [hR]; exact Finset.card_sdiff_add_card_eq_card hBsub
  -- (3) 汚れた親のブロックと，子にブロックを持つ K の点は別
  have hRK : ∀ b ∈ R, ∃ x ∈ K, b <+: x := by
    intro b hb
    rw [hR, Finset.mem_sdiff] at hb
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hsub⟩ := hF b hb.1 hcon
    exact hb.2 (by
      rw [hB, Finset.mem_biUnion]
      exact ⟨u, hu, mem_fullRoots.mpr ⟨(mem_fullRoots.mp hb.1).1, hsub⟩⟩)
  choose! κ hκK hκb using hRK
  have hRlen : ∀ b ∈ R, b.length = Dp := by
    intro b hb
    rw [hR, Finset.mem_sdiff] at hb
    exact (mem_fullRoots.mp hb.1).1
  obtain ⟨A, hA⟩ : ∃ A : Finset Node, A = K.filter (fun u => 1 ≤ fullM h Dp (C u)) := ⟨_, rfl⟩
  have hAR : A.card + R.card ≤ K.card := by
    have hinj : Set.InjOn κ (R : Set Node) := by
      intro b hb b' hb' he
      have l1 := hRlen b (Finset.mem_coe.mp hb)
      have l2 := hRlen b' (Finset.mem_coe.mp hb')
      have p1 := hκb b (Finset.mem_coe.mp hb)
      have p2 := hκb b' (Finset.mem_coe.mp hb')
      rw [he] at p1
      exact prefix_eq_of_length p1 p2 (by rw [l1, l2])
    have hdisj : Disjoint A (R.image κ) := by
      rw [Finset.disjoint_left]
      intro u huA huR
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp huR
      rw [hA, Finset.mem_filter] at huA
      obtain ⟨hu, hj⟩ := huA
      have hne : (fullRoots h Dp (C (κ b))).Nonempty := by
        rw [← Finset.card_pos]; unfold fullM at hj; omega
      obtain ⟨b', hb'⟩ := hne
      obtain ⟨l', hs'⟩ := mem_fullRoots.mp hb'
      have hlt := hCdesc (κ b) hu b' (hs' (self_mem_subtree (by omega)))
      have l1 := hRlen b hb
      have := (hκb b hb).length_le
      omega
    have hsub : A ∪ R.image κ ⊆ K := by
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [hA] at hx; exact (Finset.mem_filter.mp hx).1
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        exact hκK b hb
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at this
    exact this
  -- (4) 子の値の和
  have hD1 : ∑ u ∈ K, Ψc (X * fullM h Dp (C u)) ≤ X * σc * ∑ u ∈ K, fullM h Dp (C u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    have := hle (X * fullM h Dp (C u))
    calc Ψc (X * fullM h Dp (C u)) ≤ σc * (X * fullM h Dp (C u)) := this
      _ = X * σc * fullM h Dp (C u) := by ring
  have hD2 : ∑ u ∈ K, Ψc (X * fullM h Dp (C u)) ≤ lC * A.card + lS * ∑ u ∈ K, fullM h Dp (C u) := by
    rw [← Finset.sum_filter_add_sum_filter_not K (fun u => 1 ≤ fullM h Dp (C u))
      (fun u => Ψc (X * fullM h Dp (C u)))]
    have hz : ∑ u ∈ K.filter (fun u => ¬ 1 ≤ fullM h Dp (C u)), Ψc (X * fullM h Dp (C u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have : fullM h Dp (C u) = 0 := by
        have := (Finset.mem_filter.mp hu).2; omega
      rw [this, mul_zero, hΨ0]
    rw [hz, add_zero, ← hA]
    have hA1 : ∑ u ∈ A, Ψc (X * fullM h Dp (C u)) ≤ ∑ u ∈ A, (lC + lS * fullM h Dp (C u)) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [hA, Finset.mem_filter] at hu
      exact hg _ hu.2
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hA1
    have hAsub : A ⊆ K := by rw [hA]; exact Finset.filter_subset _ _
    have hsum := Finset.sum_le_sum_of_subset (f := fun u => fullM h Dp (C u)) hAsub
    have := Nat.mul_le_mul_left lS hsum
    linarith [mul_comm A.card lC]
  -- (5) まとめ
  rw [← min_add_add_right]
  apply le_min
  · have hs : ∑ u ∈ K, Ψc (fullM h (Dp + L) (C u)) ≤ σc * ∑ u ∈ K, fullM h (Dp + L) (C u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun u _ => hle _)
    omega
  · rw [← hRB] at ⊢
    rw [← hBcard] at h1s hD1 hD2
    have e1 : X * σc * (R.card + B.card) = X * σc * R.card + X * σc * B.card := by ring
    have e2 : lS * (R.card + B.card) = lS * R.card + lS * B.card := by ring
    have e3 : lC * (A.card + R.card) ≤ lC * Q := Nat.mul_le_mul_left _ (hAR.trans hK)
    have e4 : X * σc * R.card ≤ (lC + lS) * R.card := Nat.mul_le_mul_right _ hσ
    have e5 : (lC + lS) * R.card = lC * R.card + lS * R.card := by ring
    have e6 : lC * (A.card + R.card) = lC * A.card + lC * R.card := by ring
    omega

/-! ## 事実 F（区域の形で） -/

/-- **事実 F.** 時刻 `f` に `y` とその子がペブル，`Z` は `y` の真の子孫で `y` からの道について閉じる。
`Z` にすべて入る部分木 `subtree h b`（`b ≠ y`）が `y` 以外の `f` のペブルを含まないなら，ある `u ∈ Z`（`u ≠ y`，
`f` でペブル）の子区域にすべて入る。 -/
theorem zone_factF {h : ℕ} {ms : ℕ → Move} {Z : Finset Node} {y : Node} {f : ℕ} {b : Node}
    (hyf : st ms f y = .pebble) (hkid : ∀ bb : Bool, st ms f (y ++ [bb]) = .pebble)
    (hyZ : ∀ d ∈ Z, y <+: d)
    (hclosed : ∀ d ∈ Z, ∀ w, y <+: w → w <+: d → w ≠ y → w ∈ Z)
    (hbh : b.length < h) (hbZ : subtree h b ⊆ Z) (hby : b ≠ y)
    (hclean : ∀ x ∈ Z, x ≠ y → st ms f x = .pebble → ¬ b <+: x) :
    ∃ u ∈ Z, u ≠ y ∧ st ms f u = .pebble ∧ subtree h b ⊆ childZone ms Z f u := by
  have hbZ' : b ∈ Z := hbZ (self_mem_subtree hbh)
  have hdf : st ms f b ≠ .pebble := fun hp => hclean b hbZ' hby hp (List.prefix_refl b)
  obtain ⟨u, huZ, huy, hup, hbu⟩ :=
    cover_zone hyf (fun bb _ => hkid bb) (hyZ b hbZ') hbZ' hdf (hclosed b hbZ')
  refine ⟨u, huZ, huy, hup, ?_⟩
  obtain ⟨-, hub, hbne, hpath⟩ := mem_childZone.mp hbu
  have hyu : y <+: u := hyZ u huZ
  intro v hv
  obtain ⟨hvl, hbv⟩ := mem_subtree.mp hv
  refine mem_childZone.mpr ⟨hbZ hv, hub.trans hbv, ?_, ?_⟩
  · intro hvu
    rw [hvu] at hbv
    exact hbne (hbv.eq_of_length (le_antisymm hbv.length_le hub.length_le))
  · intro w hw1 hw2 hw3
    rcases le_total w.length b.length with hl | hl
    · exact hpath w hw1 (List.prefix_of_prefix_length_le hw2 hbv hl) hw3
    · have hbw : b <+: w := List.prefix_of_prefix_length_le hbv hw2 hl
      have hwZ : w ∈ Z := hbZ (mem_subtree.mpr ⟨lt_of_le_of_lt hw2.length_le hvl, hbw⟩)
      have hwy : w ≠ y := by
        intro he
        rw [he] at hw1
        exact huy (hw1.eq_of_length (le_antisymm hw1.length_le hyu.length_le))
      exact fun hp => hclean w hwZ hwy hp hbw

end SpookyTree
