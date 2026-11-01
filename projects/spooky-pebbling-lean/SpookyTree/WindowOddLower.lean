/-
# 付記 A: `m = 2`・`h` 奇数の窓の下界

紙は `notes/spooky-pebbling/tree-gap/CRITIC_WINDOW_UB_2026-11-01.md` の付記 A、その検算
`CHECK_APPENDIX_A_2026-11-01.md`（(A1)〜(A4)）、精密化した定理 A は `WINDOW_LB_2026-10-31.md` の 1 節。

* `window_lower_refined`（精密化した定理 A、すべての `h ≥ 1`・`cap`）: 根を最後に置いた直後の時刻 `c`
  （紙の `R` の直後）があって、`P = pebSet h ms c`（根以外のペブル）は `|P| + 1 ≤ cap`、かつ
    `6(2^h − 1) ≤ T + 1 + 4·cap + 2·Σ_{y∈P} min(|Z_y|, cap − 2)`
  （紙の `T ≥ 2(3n − 2p − V) − 1`）。`Z_y` は `WindowLower.lean` の段 1 の区域 `childZone`。
  既存の `zone_bound` を `K = 2` で使う: `K = 2` の項は `|Z| + (|Z| − (cap − 2))⁺ = 2|Z| − min(|Z|, cap − 2)`。
* `window_odd_lower`（付記 A の (A4) を整数で）: `h = 2H + 1`、`X = 2^H`、`X + 1 ≤ p ≤ 2X` なら
    `8X² + 2(2X − p)² + 4X ≤ T + 6p + 5`
  （紙の `T ≥ (4 + (2 − p/2^H)²)·2^h − 6p + 2^{H+2} − 5` を `2^h = 2X²` で書き直したもの）。
  `V ≤ W` は `WindowOddLowerCount.lean` の `odd_zone_sum_le` を `μ₁ = 2X − p`、`μ₂ = p − X − 1` で使う。
  `H ≥ 1` は仮定に要らない（`H = 0` では `p = 2` で自明に成り立つ）。
-/
import SpookyTree.WindowOddLowerCount

namespace SpookyTree

variable {h cap T : ℕ} {ms : ℕ → Move}

/-- **精密化した定理 A.** 段 1 の区域 `Z_y` を `cap − 2` で頭打ちした和を残した形。 -/
theorem window_lower_refined (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    ∃ c, (pebSet h ms c).card + 1 ≤ cap ∧
      6 * (2 ^ h - 1) ≤ T + 1 + 4 * cap +
        2 * ∑ y ∈ pebSet h ms c, min (childZone ms (nodes h) c y).card (cap - 2) := by
  -- 根がそれ以後ずっとペブルである最初の時刻 r + 1（r は根を最後に置く手）
  have hroot0 : ¬ (st ms 0 [] = .pebble) := by simp [st]
  obtain ⟨r, hrT, hr0, hr1⟩ := last_cross (P := fun t => st ms t [] = .pebble) T hroot0 hV.root
  have hroot : ∀ t, r + 1 ≤ t → t ≤ T → st ms t [] = .pebble := fun t h1 h2 => hr1 t (by omega) h2
  have hpeb : st ms (r + 1) [] = .pebble := hroot (r + 1) le_rfl (by omega)
  have hr0' : st ms r [] ≠ .pebble := hr0
  obtain ⟨hmv, hplace⟩ := place_of_change hr0' hpeb
  have hkid0 : ∀ b : Bool, 1 < h → st ms (r + 1) ([] ++ [b]) = .pebble := by
    intro b hh2
    have hready := ready_of_place hV hrT hplace
    rw [hmv] at hready
    rcases hready with hleaf | ⟨h0, h1⟩
    · simp at hleaf; omega
    · rw [st_succ_ne (t := r) (v := [] ++ [b]) (by rw [hmv]; simp)]
      cases b <;> assumption
  -- 段 0: 全頂点が r + 1 より前に置かれる（補題 R）
  obtain ⟨E1, hE1def⟩ : ∃ E1 : Finset ℕ,
      E1 = (Finset.range T).filter (fun i => i < r + 1 ∧ IsPlace (ms i)) := ⟨_, rfl⟩
  have hroot_len : ([] : Node).length < h := by simp; omega
  have hfree0 : ∀ z ∈ subtree h [], st ms 0 z ≠ .pebble := by intro z _; simp [st]
  have hE1 : 2 ^ h - 1 ≤ E1.card := by
    have hsub : nodes h ⊆ E1.image (fun i => (ms i).v) := by
      intro z hz
      obtain ⟨i, -, hi2, hi3, hi4⟩ :=
        lemmaR hV _ [] rfl hroot_len 0 (r + 1) (Nat.zero_le _) (by omega) hfree0 hpeb z
          (by rw [subtree_nil]; exact hz)
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      rw [hE1def, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi2, hi4⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := E1) (f := fun i => (ms i).v)
    rw [card_nodes] at h1
    omega
  -- 段 0 の数え済み K0 = P_{r+1}
  obtain ⟨K0, hK0⟩ : ∃ K0 : Finset Node, K0 = (nodes h).filter (fun x => st ms (r + 1) x = .pebble) :=
    ⟨_, rfl⟩
  have memK0 : ∀ x, x ∈ K0 ↔ x.length < h ∧ st ms (r + 1) x = .pebble := by
    intro x; rw [hK0, Finset.mem_filter, mem_nodes]
  have hK0card : K0.card ≤ cap := by
    have := hV.cap_le (r + 1) (by omega)
    unfold pcount at this; rw [hK0]; exact this
  have hrootK0 : [] ∈ K0 := (memK0 []).mpr ⟨hroot_len, hpeb⟩
  -- 段 1 の区域（zone_bound を K = 2 で）: |Z| + (|Z| − q) 以上の置く手
  have hzone : ∀ y ∈ K0.erase [], (childZone ms (nodes h) (r + 1) y).card +
      ((childZone ms (nodes h) (r + 1) y).card - (cap - 2))
      ≤ (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card := by
    intro y hy
    obtain ⟨hy0, hyK⟩ := Finset.mem_erase.mp hy
    have h2 := zone_bound hV hroot 2 _ y (r + 1) le_rfl (by omega) hy0 ((memK0 y).mp hyK).2
      (childZone_isZone (fun d hd => mem_nodes.mp hd) (fun d hd w _ hw2 _ =>
        mem_nodes.mpr (lt_of_le_of_lt hw2.length_le (mem_nodes.mp hd))))
    have hG0 : Gw (cap - 2) 0 = 0 := rfl
    have hG1 : Gw (cap - 2) 1 = 1 := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_one, hG0, hG1, mul_zero, mul_one,
      Nat.sub_zero] at h2
    exact h2
  -- 被覆: nodes ∖ K0 は段 1 の区域の和
  have hcov : 2 ^ h - 1 - K0.card ≤ ∑ y ∈ K0.erase [], (childZone ms (nodes h) (r + 1) y).card := by
    have hsub : nodes h \ K0 ⊆ (K0.erase []).biUnion (fun y => childZone ms (nodes h) (r + 1) y) := by
      intro d hd
      rw [Finset.mem_sdiff] at hd
      obtain ⟨hdZ, hdK⟩ := hd
      have hdl := mem_nodes.mp hdZ
      have hdf : st ms (r + 1) d ≠ .pebble := fun hp => hdK ((memK0 d).mpr ⟨hdl, hp⟩)
      have hd0 : d ≠ [] := by intro he; rw [he] at hdf; exact hdf hpeb
      have hh2 : 1 < h := by
        have : d.length ≠ 0 := by simpa using hd0
        omega
      obtain ⟨u, huZ, hu0, hup, hdu⟩ := cover_zone (Z := nodes h) hpeb (fun b _ => hkid0 b hh2)
        List.nil_prefix hdZ hdf
        (fun w _ hw2 _ => mem_nodes.mpr (lt_of_le_of_lt hw2.length_le hdl))
      refine Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨hu0, (memK0 u).mpr ⟨mem_nodes.mp huZ, hup⟩⟩, hdu⟩
    have hdisj : ((K0.erase []) : Set Node).PairwiseDisjoint
        (fun y => childZone ms (nodes h) (r + 1) y) := by
      intro u hu u' hu' hne
      exact childZone_disjoint ((memK0 u).mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu))).2
        ((memK0 u').mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu'))).2 hne
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at h1
    have h2 : K0 ⊆ nodes h := by rw [hK0]; exact Finset.filter_subset _ _
    have h3 := Finset.card_sdiff_add_card_eq_card h2
    rw [card_nodes] at h3
    omega
  -- 置く手の集合は互いに素
  have hle : E1.card + ∑ y ∈ K0.erase [], (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card
      ≤ nPlace ms T := by
    have hdisjB : ((K0.erase []) : Set Node).PairwiseDisjoint
        (fun y => plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)) := by
      intro u hu u' hu' hne
      have hd := childZone_disjoint (Z := nodes h)
        ((memK0 u).mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu))).2
        ((memK0 u').mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu'))).2 hne
      show Disjoint (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) u))
        (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) u'))
      rw [Finset.disjoint_left] at hd ⊢
      intro i hi hi'
      exact hd (mem_plAfter.mp hi).2.2.2 (mem_plAfter.mp hi').2.2.2
    have hdisjAB : Disjoint E1
        ((K0.erase []).biUnion (fun y => plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y))) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hE1def, Finset.mem_filter] at hiA
      obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hiB
      have := (mem_plAfter.mp hiu).2.1
      have := hiA.2.1
      omega
    have hsub : E1 ∪ (K0.erase []).biUnion
        (fun y => plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y))
        ⊆ (Finset.range T).filter (fun i => IsPlace (ms i)) := by
      intro i hi
      rw [Finset.mem_union] at hi
      rw [Finset.mem_filter]
      rcases hi with hi | hi
      · rw [hE1def, Finset.mem_filter] at hi
        exact ⟨hi.1, hi.2.2⟩
      · obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨h1, -, h3, -⟩ := mem_plAfter.mp hiu
        exact ⟨Finset.mem_range.mpr h1, h3⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_biUnion hdisjB] at this
    exact this
  -- 結論
  have hKP : pebSet h ms (r + 1) = K0.erase [] := by rw [hK0]; rfl
  refine ⟨r + 1, ?_, ?_⟩
  · rw [hKP, Finset.card_erase_of_mem hrootK0]
    have : 1 ≤ K0.card := Finset.card_pos.mpr ⟨_, hrootK0⟩
    omega
  · rw [hKP]
    have hsumZ := Finset.sum_le_sum hzone
    have hid : ∑ y ∈ K0.erase [], ((childZone ms (nodes h) (r + 1) y).card +
        ((childZone ms (nodes h) (r + 1) y).card - (cap - 2))) +
        ∑ y ∈ K0.erase [], min (childZone ms (nodes h) (r + 1) y).card (cap - 2) =
        2 * ∑ y ∈ K0.erase [], (childZone ms (nodes h) (r + 1) y).card := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      omega
    have hmv' := moves_eq hV hh
    omega

/-- **付記 A の (A4)（整数の形）.** `h = 2H + 1`、`X = 2^H`、`X + 1 ≤ p ≤ 2X` の妥当な手順の手数 `T` は
`8X² + 2(2X − p)² + 4X ≤ T + 6p + 5`、すなわち `T ≥ (4 + (2 − p/X)²)·2^h − 6p + 4X − 5`。 -/
theorem window_odd_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (2 * H + 1) p T ms)
    (hp1 : 2 ^ H + 1 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    8 * (2 ^ H) ^ 2 + 2 * (2 * 2 ^ H - p) ^ 2 + 4 * 2 ^ H ≤ T + 6 * p + 5 := by
  obtain ⟨c, hcard, hmain⟩ := window_lower_refined hV (by omega)
  have h2H1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  have h2h : 2 ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by ring
  rw [h2H1] at hp2
  obtain ⟨a, rfl⟩ : ∃ a, p = 2 ^ H + 1 + a := ⟨p - (2 ^ H + 1), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 1 := ⟨2 ^ H - 1 - a, by omega⟩
  have hW := odd_zone_sum_le (ms := ms) (H := H) (c := c) b a (2 ^ H + 1 + a - 2)
    (by omega) (by omega)
  rw [h2H1] at hW
  rw [h2h] at hmain
  have hsub : 2 * 2 ^ H - (2 ^ H + 1 + a) = b := by omega
  rw [hsub]
  generalize (pebSet (2 * H + 1) ms c).card = Pc at hcard hW
  generalize ∑ y ∈ pebSet (2 * H + 1) ms c,
    min (childZone ms (nodes (2 * H + 1)) c y).card (2 ^ H + 1 + a - 2) = V at hmain hW
  generalize 2 ^ H = X at *
  subst hb
  have hbP : b * Pc + b ≤ b * (2 * a + b + 2) := by
    have := Nat.mul_le_mul_left b (show Pc + 1 ≤ 2 * a + b + 2 by omega)
    linarith
  have hm1 : 1 ≤ 2 * (a + b + 1) * (a + b + 1) := by nlinarith
  have hmain' : 6 * (2 * (a + b + 1) * (a + b + 1)) ≤ T + 7 + 4 * (a + b + 1 + 1 + a) + 2 * V := by
    omega
  have hW' : V + 1 ≤ 2 * (a + b + 1) + b * Pc + a * (2 * (a + b + 1)) := by omega
  nlinarith

end SpookyTree
