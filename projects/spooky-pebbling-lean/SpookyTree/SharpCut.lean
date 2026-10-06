/-
# 鋭い下界の本体: ペブルの個数についての帰納法

`Cut.lean` の切断の補題は、深さ `L` を固定して「部分木にペブルの無い深さ `L` の子孫」だけを数えるので、
ペブルのある部分木の分（割合 `b / 2^L`）を丸ごと捨てる。ここでは捨てない。

`x` を置いた直後の配置 `S` について、`x` の子の子孫 `y`（高さ `j`）ごとに
  （`τ` より後に `T(y)` の頂点へ打つ置く手の数）`≥ Hb j (T(y) の中のペブル数)`
を、`j` についての帰納法で示す（`sharpB`）。
* `T(y)` にペブルが無ければ、`y` はいずれ置かれ（補題 F）、それまでに `T(y)` の全頂点が置かれ（補題 R）、
  `y` を置いた後にさらに `Fb j` 回（`sharpA` の帰納法の仮定）。
* ペブルがあれば、左右の子に分けて足す（`Hb_step`。相加相乗平均）。

これを `x` の 2 つの子に使うと `sharpA`: `x` を置いた後の真の子孫への置く手は `Fb k` 回以上。
ペブルの上限は「`x` の子 2 つの部分木のペブルは合わせて `cap − 1` 個以下」の形でだけ使う。
-/
import SpookyTree.Cut
import SpookyTree.UpperCore
import SpookyTree.SharpArith

namespace SpookyTree

/-- 時刻 `τ` より後に、`T(y)` の頂点（`y` 自身を含む）へ打つ置く手の添字。 -/
def plIn (ms : ℕ → Move) (T τ : ℕ) (y : Node) : Finset ℕ :=
  (Finset.range T).filter (fun i => τ < i ∧ IsPlace (ms i) ∧ y <+: (ms i).v)

variable {h cap T : ℕ} {ms : ℕ → Move}

theorem child_ne (y : Node) : y ++ [false] ≠ y ++ [true] := by simp

/-- 左右の子の部分木への置く手は交わらず、どちらも親の部分木への置く手。 -/
theorem plIn_children_card (τ : ℕ) (y : Node) :
    (plIn ms T τ (y ++ [false])).card + (plIn ms T τ (y ++ [true])).card
      ≤ (plIn ms T τ y).card := by
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro i hi
    simp only [plIn, Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ <;>
      exact ⟨a, b, c, (List.prefix_append y _).trans d⟩
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [plIn, Finset.mem_filter] at hi hi'
    exact child_ne y (prefix_eq_of_length hi.2.2.2 hi'.2.2.2 (by simp))

theorem plSet_children_card (τ : ℕ) (x : Node) :
    (plIn ms T τ (x ++ [false])).card + (plIn ms T τ (x ++ [true])).card
      ≤ (plSet ms T τ x).card := by
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro i hi
    simp only [plIn, plSet, Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · refine ⟨a, b, c, (List.prefix_append x _).trans d, ?_⟩
      intro heq; have := d.length_le; rw [heq, List.length_append] at this; simp at this
    · refine ⟨a, b, c, (List.prefix_append x _).trans d, ?_⟩
      intro heq; have := d.length_le; rw [heq, List.length_append] at this; simp at this
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [plIn, Finset.mem_filter] at hi hi'
    exact child_ne x (prefix_eq_of_length hi.2.2.2 hi'.2.2.2 (by simp))

/-! ## `pc` と `pcount`・`subtree` -/

theorem pc_le_pcount {c : Config} (k : ℕ) (y : Node) (hy : y.length + k = h) :
    pc k y c ≤ pcount h c := by
  rw [pc_eq_card]
  unfold pcount
  rw [← Finset.card_image_of_injective ((nodes k).filter (fun w => c (y ++ w) = Cell.pebble))
    (fun a b (hab : y ++ a = y ++ b) => List.append_cancel_left hab)]
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_image, Finset.mem_filter, mem_nodes] at hz ⊢
  obtain ⟨w, ⟨hw, hc⟩, rfl⟩ := hz
  exact ⟨by simp; omega, hc⟩

theorem free_of_pc_zero {c : Config} {j : ℕ} {y : Node} (hy : y.length + j = h)
    (h0 : pc j y c = 0) : ∀ z ∈ subtree h y, c z ≠ .pebble := by
  intro z hz hzp
  obtain ⟨hzl, w, rfl⟩ := mem_subtree.mp hz
  rw [pc_eq_card, Finset.card_eq_zero] at h0
  have hmem : w ∈ (nodes j).filter (fun w => c (y ++ w) = Cell.pebble) := by
    simp only [Finset.mem_filter, mem_nodes]
    exact ⟨by simp at hzl; omega, hzp⟩
  rw [h0] at hmem
  simp at hmem

theorem one_le_pc {c : Config} {j : ℕ} {y : Node} (hj : 1 ≤ j) (hy : c y = .pebble) :
    1 ≤ pc j y c := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [pc, hy, if_pos rfl]
  omega

theorem pc_children_le {c : Config} (j : ℕ) (y : Node) :
    pc j (y ++ [false]) c + pc j (y ++ [true]) c ≤ pc (j + 1) y c := by
  have e : pc (j + 1) y c
      = (if c y = Cell.pebble then 1 else 0) + pc j (y ++ [false]) c + pc j (y ++ [true]) c := rfl
  rw [e, Nat.add_assoc]
  exact Nat.le_add_left _ _

/-! ## ペブルの無い部分木: 全頂点の置き直しと、その後 -/

/-- `τ` の直後に `T(y)`（高さ `j`）にペブルが無く、`y` が後でペブルを持つなら、`τ` 後の最初の `y` の置く手 `τy` について、
`(τ, τy]` に `T(y)` の全頂点の置く手があり、それと `τy` より後の `y` の真の子孫への置く手は交わらない。 -/
theorem free_card (hV : Valid h cap T ms) {τ : ℕ} {y : Node} {j : ℕ}
    (hy : y.length + j = h) (hj : 1 ≤ j)
    (hfree : ∀ z ∈ subtree h y, st ms (τ + 1) z ≠ .pebble)
    (hlater : ∃ s', τ + 1 ≤ s' ∧ s' ≤ T ∧ st ms s' y = .pebble) :
    ∃ τy, τy < T ∧ (ms τy).v = y ∧ IsPlace (ms τy) ∧
      (2 ^ j - 1) + (plSet ms T τy y).card ≤ (plIn ms T τ y).card := by
  obtain ⟨s', hs1, hs2, hs3⟩ := hlater
  have hyl : y.length < h := by omega
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := lemmaR hV _ y rfl hyl (τ + 1) s' hs1 hs2 hfree hs3 y
    (mem_subtree.mpr ⟨hyl, List.prefix_refl _⟩)
  obtain ⟨hτa1, hτa2, hτa3, hτa4⟩ :=
    firstPlace_spec (T := T) (ms := ms) (τ := τ) (a := y) ⟨i, by omega, by omega, hi3, hi4⟩
  refine ⟨firstPlace ms T τ y, hτa2, hτa3, hτa4, ?_⟩
  have hypeb : st ms (firstPlace ms T τ y + 1) y = .pebble := by
    have := st_after_place hτa4
    rw [hτa3] at this
    exact this
  let W1 : Finset ℕ := (Finset.range T).filter
    (fun i => τ < i ∧ i ≤ firstPlace ms T τ y ∧ IsPlace (ms i) ∧ y <+: (ms i).v)
  have hW1 : 2 ^ j - 1 ≤ W1.card := by
    have hsubimg : subtree h y ⊆ W1.image (fun i => (ms i).v) := by
      intro z hz
      obtain ⟨i, hi1, hi2, hi3, hi4⟩ := lemmaR hV _ y rfl hyl (τ + 1)
        (firstPlace ms T τ y + 1) (by omega) (by omega) hfree hypeb z hz
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      simp only [W1, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, by omega, hi4, hi3 ▸ (mem_subtree.mp hz).2⟩
    have h1 := Finset.card_le_card hsubimg
    have h2 := Finset.card_image_le (s := W1) (f := fun i => (ms i).v)
    have hexp : h - y.length = j := by omega
    rw [card_subtree, hexp] at h1
    omega
  have hdj : Disjoint W1 (plSet ms T (firstPlace ms T τ y) y) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [W1, plSet, Finset.mem_filter] at hi hi'
    omega
  have hsub : W1 ∪ plSet ms T (firstPlace ms T τ y) y ⊆ plIn ms T τ y := by
    intro i hi
    simp only [W1, plSet, plIn, Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨a, b, _, d, e⟩ | ⟨a, b, d, e, _⟩
    · exact ⟨a, b, d, e⟩
    · exact ⟨a, by omega, d, e⟩
  have hfin := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdj] at hfin
  omega

/-! ## 帰納法 -/

/-- **部分木ごとの下界.** `c`（`τ` の直後にペブルを持つ、根でない頂点）の子孫 `y`（高さ `j`）について、
`τ` より後に `T(y)` の頂点へ打つ置く手は `Hb j (T(y) の中のペブル数)` 回以上。
`hA` は、`T(c)` の中の頂点を置く手についての `Fb` の下界（外側の帰納法の仮定）。 -/
theorem sharpB (hV : Valid h cap T ms) {Λ K : ℝ} (hΛ : 0 < Λ) (hK1 : 1 ≤ K) {τ : ℕ} (hτ : τ < T)
    {c : Node} (hc : c ≠ []) (hcl : c.length < h) (hcp : st ms (τ + 1) c = .pebble)
    (hA : ∀ j : ℕ, j + c.length ≤ h → ∀ τ' < T, IsPlace (ms τ') → (ms τ').v.length + j = h →
      Fb Λ K j ≤ ((plSet ms T τ' (ms τ').v).card : ℝ)) :
    ∀ (j : ℕ) (y : Node), 1 ≤ j → y.length + j = h → c <+: y →
      Hb Λ K j (pc j y (st ms (τ + 1))) ≤ ((plIn ms T τ y).card : ℝ) := by
  intro j
  induction j with
  | zero => intro y hj; omega
  | succ j ih =>
    intro y _ hy hcy
    have hyl : y.length < h := by omega
    have hcard0 : (0 : ℝ) ≤ ((plIn ms T τ y).card : ℝ) := Nat.cast_nonneg _
    by_cases hp0 : pc (j + 1) y (st ms (τ + 1)) = 0
    · -- ペブルなし: 全頂点の置き直しと、y を置いた後の Fb
      rw [hp0, Hb_zero]
      have hfree := free_of_pc_zero hy hp0
      have hlater := lemmaF hV _ c rfl hc hcl (τ + 1) (by omega) hcp y
        (mem_subtree.mpr ⟨hyl, hcy⟩)
      obtain ⟨τy, h2, h3, h4, h5⟩ := free_card hV hy (by omega) hfree hlater
      have hAj := hA (j + 1) (by have := hcy.length_le; omega) τy h2 h4 (by rw [h3]; exact hy)
      rw [h3] at hAj
      have e : ((2 ^ (j + 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) - 1 := by
        rw [Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        ring
      have h5' : ((2 ^ (j + 1) - 1 : ℕ) : ℝ) + ((plSet ms T τy y).card : ℝ)
          ≤ ((plIn ms T τ y).card : ℝ) := by exact_mod_cast h5
      rw [e] at h5'
      linarith
    · -- ペブルあり
      have hp1 : 1 ≤ pc (j + 1) y (st ms (τ + 1)) := Nat.one_le_iff_ne_zero.mpr hp0
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- 葉
        have hleaf := Hb_leaf (K := K) hΛ hK1 hp1
        exact le_trans hleaf hcard0
      · have ih0 := ih (y ++ [false]) hjpos (by simp; omega)
          (hcy.trans (List.prefix_append y _))
        have ih1 := ih (y ++ [true]) hjpos (by simp; omega)
          (hcy.trans (List.prefix_append y _))
        have hstep := Hb_step (K := K) hΛ hjpos hp1 (pc_children_le j y)
        have hcard := plIn_children_card (ms := ms) (T := T) τ y
        have hcard' : ((plIn ms T τ (y ++ [false])).card : ℝ)
            + ((plIn ms T τ (y ++ [true])).card : ℝ) ≤ ((plIn ms T τ y).card : ℝ) := by
          exact_mod_cast hcard
        linarith

/-- **鋭い切断の補題.** `x` を置く手 `τ` の後、`x` の真の子孫への置く手は `Fb k` 回以上（`k` は `x` の高さ）。
`Ψ` は `ψ(p)`（`p ≤ cap`）の上界、`Λ = Ψ + 2`、`K` は `cap · j · Λ ≤ 2^j` が成り立ち始める高さ。 -/
theorem sharpA (hV : Valid h cap T ms) {Λ K Ψ : ℝ} (hΛΨ : Λ = Ψ + 2) (hΨ0 : 0 ≤ Ψ) (hK1 : 1 ≤ K)
    (hΨ : ∀ p : ℕ, 1 ≤ p → p ≤ cap → psi p ≤ Ψ)
    (hK : ∀ j : ℕ, K < (j : ℝ) + 1 → j < h → (cap : ℝ) * j * Λ ≤ 2 ^ j) :
    ∀ k τ, (ms τ).v.length + k = h → τ < T → IsPlace (ms τ) →
      Fb Λ K k ≤ ((plSet ms T τ (ms τ).v).card : ℝ) := by
  have hΛ : 0 < Λ := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro τ hk hτ hp
  have hcard0 : (0 : ℝ) ≤ ((plSet ms T τ (ms τ).v).card : ℝ) := Nat.cast_nonneg _
  by_cases hsmall : (k : ℝ) ≤ K
  · exact le_trans (Fb_nonpos hΛ hsmall) hcard0
  · rw [not_le] at hsmall
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
      linarith
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj1 : 1 ≤ j := by omega
    -- x の子は τ の直後にペブル
    have hready := ready_of_place hV hτ hp
    have hkid : ∀ b : Bool, st ms (τ + 1) ((ms τ).v ++ [b]) = .pebble := by
      intro b
      rcases hready with hleaf | ⟨h0, h1⟩
      · omega
      · rw [st_succ_ne (by simp)]
        cases b <;> assumption
    have hxp : st ms (τ + 1) (ms τ).v = .pebble := st_after_place hp
    -- 帰納法の仮定を sharpB に渡す
    have hB : ∀ b : Bool, Hb Λ K j (pc j ((ms τ).v ++ [b]) (st ms (τ + 1)))
        ≤ ((plIn ms T τ ((ms τ).v ++ [b])).card : ℝ) := by
      intro b
      refine sharpB hV hΛ hK1 hτ (c := (ms τ).v ++ [b]) (by simp) (by simp; omega) (hkid b) ?_
        j ((ms τ).v ++ [b]) hj1 (by simp; omega) (List.prefix_refl _)
      intro j' hj' τ' hτ' hp' hl'
      exact ih j' (by simp at hj'; omega) τ' hl' hτ' hp'
    -- ペブル数: 子 2 つの部分木に合わせて cap - 1 個以下
    have hpc : pc (j + 1) (ms τ).v (st ms (τ + 1)) ≤ cap :=
      le_trans (pc_le_pcount (j + 1) (ms τ).v hk) (hV.cap_le (τ + 1) (by omega))
    have hpc' : pc (j + 1) (ms τ).v (st ms (τ + 1))
        = 1 + pc j ((ms τ).v ++ [false]) (st ms (τ + 1))
          + pc j ((ms τ).v ++ [true]) (st ms (τ + 1)) := by
      rw [pc, hxp, if_pos rfl]
    have hp0 : 1 ≤ pc j ((ms τ).v ++ [false]) (st ms (τ + 1)) := one_le_pc hj1 (hkid false)
    have hp1 : 1 ≤ pc j ((ms τ).v ++ [true]) (st ms (τ + 1)) := one_le_pc hj1 (hkid true)
    have hsumN : pc j ((ms τ).v ++ [false]) (st ms (τ + 1))
        + pc j ((ms τ).v ++ [true]) (st ms (τ + 1)) ≤ cap := by omega
    have hsumR : ((pc j ((ms τ).v ++ [false]) (st ms (τ + 1)) : ℕ) : ℝ)
        + ((pc j ((ms τ).v ++ [true]) (st ms (τ + 1)) : ℕ) : ℝ) ≤ (cap : ℝ) := by
      exact_mod_cast hsumN
    have hKj : K < (j : ℝ) + 1 := by push_cast at hsmall; exact hsmall
    have htop := Fb_top (K := K) hΛ hΛΨ (hΨ _ hp0 (by omega)) (hΨ _ hp1 (by omega)) hp0 hp1
      hsumR (hK j hKj (by omega))
    have hcard := plSet_children_card (ms := ms) (T := T) τ (ms τ).v
    have hcard' : ((plIn ms T τ ((ms τ).v ++ [false])).card : ℝ)
        + ((plIn ms T τ ((ms τ).v ++ [true])).card : ℝ)
        ≤ ((plSet ms T τ (ms τ).v).card : ℝ) := by exact_mod_cast hcard
    have hb0 := hB false
    have hb1 := hB true
    linarith

end SpookyTree
