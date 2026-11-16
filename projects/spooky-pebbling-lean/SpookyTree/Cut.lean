/-
# 切断の補題（上限を使って、置き直しの数を下から抑える）

`x` を置く手を `τ` とする。`τ` の直後、`x` と `x` の 2 つの子はペブルなので、`x` から深さ `L ≥ 2` 以上下にある
ペブル（「妨害」）は `cap − 3` 個以下。深さ `L` の子孫 `a`（`2^L` 個）のうち、部分木 `T(a)` に妨害を含むものは
`cap − 3` 個以下なので、少なくとも `2^L − (cap − 3)` 個の `a` は `T(a)` がペブルなし。そのような `a` は
（補題 F により）いずれペブルになり、`τ` 後の最初の置く手を `τ_a` とすると、補題 R により `T(a)` の全頂点が
`(τ, τ_a]` で置かれ、さらに帰納法により `τ_a` 後に `T(a)` の真の子孫への置く手が `g(k − L)` 回以上ある。
-/
import SpookyTree.Count

namespace SpookyTree

/-- 下界の関数。`L = M + 2`、`b` = 妨害の上限。 -/
def gfun (M b : ℕ) (k : ℕ) : ℕ :=
  if k ≤ M + 2 then 0 else (2 ^ (M + 2) - b) * (2 ^ (k - (M + 2)) - 1 + gfun M b (k - (M + 2)))
termination_by k
decreasing_by omega

/-- 時刻 `τ` より後、`x` の真の子孫に打つ置く手の添字。 -/
def plSet (ms : ℕ → Move) (T τ : ℕ) (x : Node) : Finset ℕ :=
  (Finset.range T).filter (fun i => τ < i ∧ IsPlace (ms i) ∧ x <+: (ms i).v ∧ (ms i).v ≠ x)

variable {h cap T : ℕ} {ms : ℕ → Move}

/-- 置く手の後はその頂点はペブル。 -/
theorem st_after_place {t : ℕ} (hp : IsPlace (ms t)) : st ms (t + 1) (ms t).v = .pebble := by
  rw [st_succ_eq]; rcases hp with h | h <;> rw [h] <;> rfl

/-- 置く手の直前、その頂点は揃っている。 -/
theorem ready_of_place (hV : Valid h cap T ms) {t : ℕ} (ht : t < T) (hp : IsPlace (ms t)) :
    Ready h (st ms t) (ms t).v := by
  have hL := hV.legal t ht
  unfold Legal at hL
  rcases hp with hop | hop <;> rw [hop] at hL <;> simp only at hL <;> exact hL.2.2

theorem place_len (hV : Valid h cap T ms) {t : ℕ} (ht : t < T) : (ms t).v.length < h :=
  (hV.legal t ht).1

/-- 妨害の数え上げ: 深さ `L` の子孫のうち、部分木にペブルがあるものは `cap − 3` 個以下。 -/
theorem blocked_card (hV : Valid h cap T ms) {τ : ℕ} (hτ : τ < T) (hp : IsPlace (ms τ))
    (L : ℕ) (hL : 2 ≤ L) (hint : (ms τ).v.length + 1 < h) :
    (((words L).image (fun w => (ms τ).v ++ w)).filter
      (fun a => ∃ z ∈ subtree h a, st ms (τ + 1) z = .pebble)).card ≤ cap - 3 := by
  set x := (ms τ).v with hx
  set S := st ms (τ + 1)
  have hready := ready_of_place hV hτ hp
  rw [← hx] at hready
  have hkid : S (x ++ [false]) = .pebble ∧ S (x ++ [true]) = .pebble := by
    rcases hready with hleaf | ⟨h0, h1⟩
    · omega
    · constructor
      · rw [show S = st ms (τ + 1) from rfl, st_succ_ne (by rw [← hx]; simp)]; exact h0
      · rw [show S = st ms (τ + 1) from rfl, st_succ_ne (by rw [← hx]; simp)]; exact h1
  have hxp : S x = .pebble := st_after_place hp
  set Pb := (nodes h).filter (fun l => S l = .pebble)
  have hPb : Pb.card ≤ cap := hV.cap_le (τ + 1) (by omega)
  set Pdeep := Pb.filter (fun z => x.length + L ≤ z.length)
  -- 塞がれた a は深いペブルの切り詰めの像に入る
  have hsub : (((words L).image (fun w => x ++ w)).filter
      (fun a => ∃ z ∈ subtree h a, S z = .pebble)) ⊆ Pdeep.image (fun z => z.take (x.length + L)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_image, mem_words] at ha
    obtain ⟨⟨w, hw, rfl⟩, z, hz, hzp⟩ := ha
    obtain ⟨hzl, hpre⟩ := mem_subtree.mp hz
    have hlen : x.length + L ≤ z.length := by
      have := hpre.length_le; simp [hw] at this; omega
    refine Finset.mem_image.mpr ⟨z, ?_, ?_⟩
    · simp only [Pdeep, Pb, Finset.mem_filter, mem_nodes]; exact ⟨⟨hzl, hzp⟩, hlen⟩
    · rw [List.prefix_iff_eq_take.mp hpre]; simp [hw]
  -- 深いペブルは x とその子 2 つ以外
  have hdeep : Pdeep.card + 3 ≤ Pb.card := by
    have h3 : ({x, x ++ [false], x ++ [true]} : Finset Node) ⊆ Pb := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      simp only [Pb, Finset.mem_filter, mem_nodes]
      rcases hl with rfl | rfl | rfl
      · exact ⟨by omega, hxp⟩
      · exact ⟨by simp; omega, hkid.1⟩
      · exact ⟨by simp; omega, hkid.2⟩
    have hdisj : Disjoint Pdeep {x, x ++ [false], x ++ [true]} := by
      rw [Finset.disjoint_left]
      intro l hl hl2
      simp only [Pdeep, Finset.mem_filter] at hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl2
      rcases hl2 with rfl | rfl | rfl <;> simp at hl <;> omega
    have hcard3 : ({x, x ++ [false], x ++ [true]} : Finset Node).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor <;> intro heq <;> have := congrArg List.length heq <;> simp at this
    have := Finset.card_union_of_disjoint hdisj
    have hU : Pdeep ∪ {x, x ++ [false], x ++ [true]} ⊆ Pb :=
      Finset.union_subset (Finset.filter_subset _ _) h3
    have := Finset.card_le_card hU
    omega
  calc _ ≤ (Pdeep.image (fun z => z.take (x.length + L))).card := Finset.card_le_card hsub
    _ ≤ Pdeep.card := Finset.card_image_le
    _ ≤ cap - 3 := by omega

/-- 置く手の添字の最小を取る。 -/
def firstPlace (ms : ℕ → Move) (T τ : ℕ) (a : Node) : ℕ :=
  let P := (Finset.range T).filter (fun i => τ < i ∧ (ms i).v = a ∧ IsPlace (ms i))
  if hP : P.Nonempty then P.min' hP else 0

theorem firstPlace_spec {τ : ℕ} {a : Node}
    (hex : ∃ i, τ < i ∧ i < T ∧ (ms i).v = a ∧ IsPlace (ms i)) :
    τ < firstPlace ms T τ a ∧ firstPlace ms T τ a < T ∧ (ms (firstPlace ms T τ a)).v = a ∧
      IsPlace (ms (firstPlace ms T τ a)) := by
  obtain ⟨i, h1, h2, h3, h4⟩ := hex
  have hne : ((Finset.range T).filter (fun i => τ < i ∧ (ms i).v = a ∧ IsPlace (ms i))).Nonempty :=
    ⟨i, by simp [h1, h2, h3, h4]⟩
  unfold firstPlace
  simp only [dif_pos hne]
  have hm := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  exact ⟨hm.2.1, hm.1, hm.2.2.1, hm.2.2.2⟩

/-- **切断の補題.** `x` を置く手 `τ` の後、`x` の真の子孫への置く手は `gfun M (cap−3) (h − |x|)` 回以上。 -/
theorem cut (hV : Valid h cap T ms) (M : ℕ) :
    ∀ k τ, h - (ms τ).v.length = k → τ < T → IsPlace (ms τ) →
    gfun M (cap - 3) k ≤ (plSet ms T τ (ms τ).v).card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro τ hk hτ hp
  set L := M + 2 with hLdef
  unfold gfun
  split_ifs with hkL
  · exact Nat.zero_le _
  set x := (ms τ).v with hx
  have hxl : x.length < h := place_len hV hτ
  have hint : x.length + 1 < h := by omega
  set A := (words L).image (fun w => x ++ w) with hA
  set B := A.filter (fun a => ∃ z ∈ subtree h a, st ms (τ + 1) z = .pebble) with hB
  set U := A \ B with hU
  have hAcard : A.card = 2 ^ L := by
    rw [hA, Finset.card_image_of_injective _ (fun a b (hab : x ++ a = x ++ b) =>
      List.append_cancel_left hab), card_words]
  have hBcard : B.card ≤ cap - 3 := blocked_card hV hτ hp L (by omega) hint
  have hUcard : 2 ^ L - (cap - 3) ≤ U.card := by
    have h1 := Finset.card_sdiff_add_card_inter A B
    have hBA : B ⊆ A := Finset.filter_subset _ _
    rw [Finset.inter_eq_right.mpr hBA] at h1
    rw [← hAcard, hU]
    omega
  -- 各 a ∈ U について
  have hkid := ready_of_place hV hτ hp
  rw [← hx] at hkid
  have hkidS : ∀ bb : Bool, st ms (τ + 1) (x ++ [bb]) = .pebble := by
    intro bb
    rcases hkid with hleaf | ⟨h0, h1⟩
    · omega
    · rw [st_succ_ne (by rw [← hx]; simp)]; cases bb <;> assumption
  have hmemA : ∀ a ∈ A, ∃ w, w.length = L ∧ a = x ++ w := by
    intro a ha; simp only [hA, Finset.mem_image, mem_words] at ha
    obtain ⟨w, hw, rfl⟩ := ha; exact ⟨w, hw, rfl⟩
  have hex : ∀ a ∈ U, ∃ i, τ < i ∧ i < T ∧ (ms i).v = a ∧ IsPlace (ms i) := by
    intro a ha
    obtain ⟨haA, haB⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨w, hw, rfl⟩ := hmemA _ haA
    have hfree : ∀ z ∈ subtree h (x ++ w), st ms (τ + 1) z ≠ .pebble := by
      intro z hz hzp; exact haB (Finset.mem_filter.mpr ⟨haA, z, hz, hzp⟩)
    obtain ⟨b0, w', rfl⟩ : ∃ b0 w', w = b0 :: w' := by
      cases w with
      | nil => simp [hLdef] at hw
      | cons b0 w' => exact ⟨b0, w', rfl⟩
    have hal : (x ++ b0 :: w').length < h := by simp at hw ⊢; omega
    -- 子 x ++ [b0] は τ+1 でペブル。補題 F で a はいずれペブル
    have hcin : x ++ b0 :: w' ∈ subtree h (x ++ [b0]) :=
      mem_subtree.mpr ⟨hal, ⟨w', by simp⟩⟩
    obtain ⟨s', hs1, hs2, hs3⟩ := lemmaF hV _ (x ++ [b0]) rfl (by simp) (by simp; omega)
      (τ + 1) (by omega) (hkidS b0) _ hcin
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := lemmaR hV _ (x ++ b0 :: w') rfl hal (τ + 1) s' hs1 hs2 hfree hs3
      (x ++ b0 :: w') (mem_subtree.mpr ⟨hal, List.prefix_refl _⟩)
    exact ⟨i, by omega, by omega, hi3, hi4⟩
  -- a ごとの置く手の集合
  let W1 : Node → Finset ℕ := fun a =>
    (Finset.range T).filter (fun i => τ < i ∧ i ≤ firstPlace ms T τ a ∧ IsPlace (ms i) ∧ a <+: (ms i).v)
  let W : Node → Finset ℕ := fun a => W1 a ∪ plSet ms T (firstPlace ms T τ a) a
  have hWsub : U.biUnion W ⊆ plSet ms T τ x := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨haA, -⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨w, hw, rfl⟩ := hmemA _ haA
    obtain ⟨hτa1, -, -, -⟩ := firstPlace_spec (hex _ ha)
    simp only [plSet, W, W1, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hia ⊢
    rcases hia with ⟨hiT, h1, h2, h3, h4⟩ | ⟨hiT, h1, h2, h3, h4⟩
    · refine ⟨hiT, h1, h3, (List.prefix_append x w).trans h4, ?_⟩
      intro heq; have := h4.length_le; rw [heq, List.length_append] at this; omega
    · refine ⟨hiT, by omega, h2, (List.prefix_append x w).trans h3, ?_⟩
      intro heq; have := h3.length_le; rw [heq, List.length_append] at this; omega
  have hdisj : ∀ a ∈ U, ∀ a' ∈ U, a ≠ a' → Disjoint (W a) (W a') := by
    intro a ha a' ha' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨w, hw, rfl⟩ := hmemA _ (Finset.mem_sdiff.mp ha).1
    obtain ⟨w', hw', rfl⟩ := hmemA _ (Finset.mem_sdiff.mp ha').1
    have pre : ∀ (c : Node), i ∈ W c → c <+: (ms i).v := by
      intro c hc
      simp only [W, W1, plSet, Finset.mem_union, Finset.mem_filter] at hc
      rcases hc with ⟨-, -, -, -, h4⟩ | ⟨-, -, -, h4, -⟩ <;> exact h4
    exact hne (prefix_eq_of_length (pre _ hi) (pre _ hi') (by simp [hw, hw']))
  have hWcard : ∀ a ∈ U, 2 ^ (k - L) - 1 + gfun M (cap - 3) (k - L) ≤ (W a).card := by
    intro a ha
    obtain ⟨haA, haB⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨w, hw, rfl⟩ := hmemA _ haA
    obtain ⟨hτa1, hτa2, hτa3, hτa4⟩ := firstPlace_spec (hex _ ha)
    have hal : (x ++ w).length < h := by simp [hw]; omega
    have hfree : ∀ z ∈ subtree h (x ++ w), st ms (τ + 1) z ≠ .pebble := by
      intro z hz hzp; exact haB (Finset.mem_filter.mpr ⟨haA, z, hz, hzp⟩)
    have hapeb : st ms (firstPlace ms T τ (x ++ w) + 1) (x ++ w) = .pebble := by
      have := st_after_place hτa4; rw [hτa3] at this; exact this
    -- W1: T(a) の全頂点が (τ, τ_a] で置かれる
    have hW1 : 2 ^ (k - L) - 1 ≤ (W1 (x ++ w)).card := by
      have hsubimg : subtree h (x ++ w) ⊆ (W1 (x ++ w)).image (fun i => (ms i).v) := by
        intro z hz
        obtain ⟨i, hi1, hi2, hi3, hi4⟩ := lemmaR hV _ (x ++ w) rfl hal (τ + 1) (firstPlace ms T τ (x ++ w) + 1)
          (by omega) (by omega) hfree hapeb z hz
        refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
        simp only [W1, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, by omega, hi4, hi3 ▸ (mem_subtree.mp hz).2⟩
      have := Finset.card_le_card hsubimg
      have h2 := Finset.card_image_le (s := W1 (x ++ w)) (f := fun i => (ms i).v)
      have hexp : h - (x ++ w).length = k - L := by simp [hw]; omega
      rw [card_subtree, hexp] at this
      omega
    -- W2: 帰納法
    have hW2 : gfun M (cap - 3) (k - L) ≤ (plSet ms T (firstPlace ms T τ (x ++ w)) (x ++ w)).card := by
      have := ih (k - L) (by omega) (firstPlace ms T τ (x ++ w)) (by rw [hτa3]; simp [hw]; omega) hτa2 hτa4
      rw [hτa3] at this; exact this
    have hdj : Disjoint (W1 (x ++ w)) (plSet ms T (firstPlace ms T τ (x ++ w)) (x ++ w)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [W1, plSet, Finset.mem_filter] at hi hi'
      omega
    simp only [W]
    rw [Finset.card_union_of_disjoint hdj]
    omega
  calc (2 ^ L - (cap - 3)) * (2 ^ (k - L) - 1 + gfun M (cap - 3) (k - L))
      ≤ U.card * (2 ^ (k - L) - 1 + gfun M (cap - 3) (k - L)) := Nat.mul_le_mul_right _ hUcard
    _ = ∑ _a ∈ U, (2 ^ (k - L) - 1 + gfun M (cap - 3) (k - L)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ U, (W a).card := Finset.sum_le_sum hWcard
    _ = (U.biUnion W).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (plSet ms T τ x).card := Finset.card_le_card hWsub

end SpookyTree
