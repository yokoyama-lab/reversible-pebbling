/-
# 定理 L3 の前半: 2 段の区域を頭打ちにした精密化した定理 A（すべての `h`）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 1 節（`WINDOW_LB_2026-10-31.md` の 1 節の
段 2 までを使う）。ここは木の形（`h = 3H + 1`）を使わない。

* `zone2_bound`: 区域 `Z`（親 `y ≠ 根`、親の切断の時刻 `c`）について、ある時刻 `f`（`y` が初めて空になる
  手の直前の盤面。`Z` が空なら何でもよい）があって、`K_Z = Z ∩ P_f` は `|K_Z| ≤ p − 2`、かつ
    `3|Z| ≤ (c 以後の Z への置く手) + 2|K_Z| + Σ_{u∈K_Z} min(|Z'_u|, p − 2)`
  （`Z'_u = childZone Z f u` は段 2 の区域）。`Z` の頂点は `[c, f)` で 1 回、子区域の頂点は `f` 以後に
  `zone_bound`（`K = 2`）で `|Z'| + (|Z'| − (p−2))⁺` 回置かれる。
* `window_lower_refined2`（紙の `T ≥ 2(4n − 3N_0 − 2N_1 − N_2) − 1` の形）: 根を最後に置いた直後の時刻 `c` と
  時刻の族 `f` があって、`P = pebSet h ms c`、`K_y = zoneK ms h c f y` について `|P| + 1 ≤ p`、`|K_y| ≤ p − 2`、
    `8(2^h − 1) ≤ T + 1 + 6p + 4 Σ_y |K_y| + 2 Σ_y Σ_{u∈K_y} min(|Z'_{y,u}|, p − 2)`。
-/
import SpookyTree.WindowOddLowerCount

namespace SpookyTree

variable {h cap T : ℕ} {ms : ℕ → Move}

open Classical in
/-- 段 1 の区域 `Z_y = childZone (nodes h) c y` のうち、時刻 `f y` にペブルのもの（紙の `K_{Z_y}`）。 -/
noncomputable def zoneK (ms : ℕ → Move) (h c : ℕ) (f : Node → ℕ) (y : Node) : Finset Node :=
  (childZone ms (nodes h) c y).filter (fun x => st ms (f y) x = .pebble)

open Classical in
theorem mem_zoneK {h c : ℕ} {f : Node → ℕ} {y x : Node} :
    x ∈ zoneK ms h c f y ↔ x ∈ childZone ms (nodes h) c y ∧ st ms (f y) x = .pebble := by
  unfold zoneK; exact Finset.mem_filter

open Classical in
/-- **段 2 までの区域の補題.** -/
theorem zone2_bound (hV : Valid h cap T ms) {c0 : ℕ}
    (hroot : ∀ t, c0 ≤ t → t ≤ T → st ms t [] = .pebble)
    (Z : Finset Node) (y : Node) (c : ℕ) (hc0 : c0 ≤ c) (hcT : c ≤ T) (hy : y ≠ [])
    (hyc : st ms c y = .pebble) (hZ : IsZone h ms Z y c) :
    ∃ f, (Z.filter (fun x => st ms f x = .pebble)).card ≤ cap - 2 ∧
      3 * Z.card ≤ (plAfter ms T c Z).card + 2 * (Z.filter (fun x => st ms f x = .pebble)).card +
        ∑ u ∈ Z.filter (fun x => st ms f x = .pebble), min (childZone ms Z f u).card (cap - 2) := by
  obtain ⟨hZ1, hZ2⟩ := hZ
  rcases Z.eq_empty_or_nonempty with hZe | ⟨d0, hd0⟩
  · subst hZe; exact ⟨c, by simp, by simp⟩
  -- y は内部頂点
  have hint : y.length + 1 < h := by
    obtain ⟨hl, hp, hne, -⟩ := hZ1 d0 hd0
    have : y.length < d0.length :=
      lt_of_le_of_ne hp.length_le (fun he => hne (hp.eq_of_length he).symm)
    omega
  obtain ⟨f, hcf, hfT, hyf, hf0, hf1⟩ := unpebble_time hV hy hint hcT hyc
  have hkid : ∀ b : Bool, st ms f (y ++ [b]) = .pebble := by intro b; cases b <;> assumption
  refine ⟨f, ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, q = cap - 2 := ⟨_, rfl⟩
  rw [← hq]
  obtain ⟨KZ, hKZ⟩ : ∃ KZ : Finset Node, KZ = Z.filter (fun x => st ms f x = .pebble) := ⟨_, rfl⟩
  rw [← hKZ]
  have memK : ∀ x, x ∈ KZ ↔ x ∈ Z ∧ st ms f x = .pebble := by
    intro x; rw [hKZ, Finset.mem_filter]
  -- |K_Z| ≤ p − 2（盤面 f は区域の外の根と y を含む）
  have hKcard : KZ.card ≤ q := by
    have hroot_f : st ms f [] = .pebble := hroot f (by omega) (by omega)
    have hsub : KZ ∪ {[], y} ⊆ (nodes h).filter (fun l => st ms f l = .pebble) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, mem_nodes]
      rcases hx with hx | hx | hx
      · rw [memK] at hx
        exact ⟨(hZ1 x hx.1).1, hx.2⟩
      · rw [hx]; exact ⟨by simp; omega, hroot_f⟩
      · rw [hx]; exact ⟨by omega, hyf⟩
    have hdisj : Disjoint KZ {[], y} := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      rw [memK] at hx
      obtain ⟨-, hp, hne, -⟩ := hZ1 x hx.1
      rw [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with hx2 | hx2
      · rw [hx2] at hp; exact hy (List.prefix_nil.mp hp)
      · exact hne hx2
    have h2 : ({[], y} : Finset Node).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy]), Finset.card_singleton]
    have hcap := hV.cap_le f (by omega)
    unfold pcount at hcap
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, h2] at this
    omega
  refine ⟨hKcard, ?_⟩
  -- 段: Z の全頂点が [c, f) で置かれる
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ,
      A = (Finset.range T).filter (fun i => c ≤ i ∧ i < f ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z) := ⟨_, rfl⟩
  have hAcard : Z.card ≤ A.card := by
    have hsub : Z ⊆ A.image (fun i => (ms i).v) := by
      intro d hd
      obtain ⟨hdl, hyd, hdy, -⟩ := hZ1 d hd
      obtain ⟨b, hb⟩ := prefix_child hyd hdy
      obtain ⟨i, hci, hif, hiv, hip⟩ := pathR hV _ (y ++ [b]) d rfl hb hdl c f hcf (by omega)
        (fun w hw1 hw2 => (hZ1 w (hZ2 d hd w ((List.prefix_append y [b]).trans hw1) hw2
          (ne_of_child_prefix hw1))).2.2.2)
        (hkid b)
      refine Finset.mem_image.mpr ⟨i, ?_, hiv⟩
      rw [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hci, hif, hip, by rw [hiv]; exact hd⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- 子区域に zone_bound（K = 2）
  have hsub2 : ∀ u ∈ KZ, (childZone ms Z f u).card + ((childZone ms Z f u).card - q)
      ≤ (plAfter ms T f (childZone ms Z f u)).card := by
    intro u hu
    rw [memK] at hu
    obtain ⟨huZ, hup⟩ := hu
    obtain ⟨-, hyu, huy, -⟩ := hZ1 u huZ
    have hu0 : u ≠ [] := by
      intro he; rw [he] at hyu; exact hy (List.prefix_nil.mp hyu)
    have h2 := zone_bound hV hroot 2 _ u f (by omega) (by omega) hu0 hup
      (childZone_isZone (fun d hd => (hZ1 d hd).1) (by
        intro d hd w hw1 hw2 hw3
        apply hZ2 d hd w (hyu.trans hw1) hw2
        intro he
        rw [he] at hw1
        exact huy (hyu.eq_of_length (le_antisymm hyu.length_le hw1.length_le)).symm))
    have hG0 : Gw (cap - 2) 0 = 0 := rfl
    have hG1 : Gw (cap - 2) 1 = 1 := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_one, hG0, hG1, mul_zero, mul_one,
      Nat.sub_zero, ← hq] at h2
    exact h2
  -- 被覆: Z ∖ K_Z は子区域の和
  have hcov : Z.card - KZ.card ≤ ∑ u ∈ KZ, (childZone ms Z f u).card := by
    have hsub : Z \ KZ ⊆ KZ.biUnion (fun u => childZone ms Z f u) := by
      intro d hd
      rw [Finset.mem_sdiff] at hd
      obtain ⟨hdZ, hdK⟩ := hd
      have hdf : st ms f d ≠ .pebble := fun hp => hdK ((memK d).mpr ⟨hdZ, hp⟩)
      obtain ⟨-, hyd, -, -⟩ := hZ1 d hdZ
      obtain ⟨u, huZ, -, hup, hdu⟩ := cover_zone hyf (fun b _ => hkid b) hyd hdZ hdf (hZ2 d hdZ)
      exact Finset.mem_biUnion.mpr ⟨u, (memK u).mpr ⟨huZ, hup⟩, hdu⟩
    have hdisj : (KZ : Set Node).PairwiseDisjoint (fun u => childZone ms Z f u) := by
      intro u hu u' hu' hne
      exact childZone_disjoint ((memK u).mp (Finset.mem_coe.mp hu)).2
        ((memK u').mp (Finset.mem_coe.mp hu')).2 hne
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at h1
    have h2 : KZ ⊆ Z := by intro x hx; exact ((memK x).mp hx).1
    have h3 := Finset.card_sdiff_add_card_eq_card h2
    omega
  -- 置く手の集合は互いに素で、plAfter c Z に入る
  have hle : A.card + ∑ u ∈ KZ, (plAfter ms T f (childZone ms Z f u)).card
      ≤ (plAfter ms T c Z).card := by
    have hdisjB : (KZ : Set Node).PairwiseDisjoint (fun u => plAfter ms T f (childZone ms Z f u)) := by
      intro u hu u' hu' hne
      have hd := childZone_disjoint (Z := Z) ((memK u).mp (Finset.mem_coe.mp hu)).2
        ((memK u').mp (Finset.mem_coe.mp hu')).2 hne
      show Disjoint (plAfter ms T f (childZone ms Z f u)) (plAfter ms T f (childZone ms Z f u'))
      rw [Finset.disjoint_left] at hd ⊢
      intro i hi hi'
      exact hd (mem_plAfter.mp hi).2.2.2 (mem_plAfter.mp hi').2.2.2
    have hdisjAB : Disjoint A (KZ.biUnion (fun u => plAfter ms T f (childZone ms Z f u))) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hA, Finset.mem_filter] at hiA
      obtain ⟨-, -, hif, -⟩ := hiA
      obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hiB
      have := (mem_plAfter.mp hiu).2.1
      omega
    have hsub : A ∪ KZ.biUnion (fun u => plAfter ms T f (childZone ms Z f u)) ⊆ plAfter ms T c Z := by
      intro i hi
      rw [Finset.mem_union] at hi
      rw [mem_plAfter]
      rcases hi with hi | hi
      · rw [hA, Finset.mem_filter, Finset.mem_range] at hi
        exact ⟨hi.1, hi.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
      · obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨h1, h2, h3, h4⟩ := mem_plAfter.mp hiu
        exact ⟨h1, by omega, h3, childZone_subset h4⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_biUnion hdisjB] at this
    exact this
  -- 算術: Σ (|Z'| + (|Z'| − q)) + Σ min(|Z'|, q) = 2 Σ |Z'|
  have hsumB := Finset.sum_le_sum hsub2
  have hid : ∑ u ∈ KZ, ((childZone ms Z f u).card + ((childZone ms Z f u).card - q)) +
      ∑ u ∈ KZ, min (childZone ms Z f u).card q = 2 * ∑ u ∈ KZ, (childZone ms Z f u).card := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    omega
  omega

open Classical in
/-- **2 段の精密化した定理 A.** -/
theorem window_lower_refined2 (hV : Valid h cap T ms) (hh : 1 ≤ h) :
    ∃ c, ∃ f : Node → ℕ, (pebSet h ms c).card + 1 ≤ cap ∧
      (∀ y ∈ pebSet h ms c, (zoneK ms h c f y).card ≤ cap - 2) ∧
      8 * (2 ^ h - 1) ≤ T + 1 + 6 * cap + 4 * ∑ y ∈ pebSet h ms c, (zoneK ms h c f y).card +
        2 * ∑ y ∈ pebSet h ms c, ∑ u ∈ zoneK ms h c f y,
          min (childZone ms (childZone ms (nodes h) c y) (f y) u).card (cap - 2) := by
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
  have hKP : pebSet h ms (r + 1) = K0.erase [] := by rw [hK0]; rfl
  -- 段 1 の区域ごとに zone2_bound で時刻 f y を選ぶ
  have hex : ∀ y : Node, ∃ fy : ℕ, y ∈ K0.erase [] →
      ((childZone ms (nodes h) (r + 1) y).filter (fun x => st ms fy x = .pebble)).card ≤ cap - 2 ∧
      3 * (childZone ms (nodes h) (r + 1) y).card ≤
        (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card +
        2 * ((childZone ms (nodes h) (r + 1) y).filter (fun x => st ms fy x = .pebble)).card +
        ∑ u ∈ (childZone ms (nodes h) (r + 1) y).filter (fun x => st ms fy x = .pebble),
          min (childZone ms (childZone ms (nodes h) (r + 1) y) fy u).card (cap - 2) := by
    intro y
    by_cases hy : y ∈ K0.erase []
    · obtain ⟨hy0, hyK⟩ := Finset.mem_erase.mp hy
      obtain ⟨fy, h1, h2⟩ := zone2_bound hV hroot _ y (r + 1) le_rfl (by omega) hy0
        ((memK0 y).mp hyK).2
        (childZone_isZone (fun d hd => mem_nodes.mp hd) (fun d hd w _ hw2 _ =>
          mem_nodes.mpr (lt_of_le_of_lt hw2.length_le (mem_nodes.mp hd))))
      exact ⟨fy, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose f hf using hex
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
  refine ⟨r + 1, f, ?_, ?_, ?_⟩
  · rw [hKP, Finset.card_erase_of_mem hrootK0]
    have : 1 ≤ K0.card := Finset.card_pos.mpr ⟨_, hrootK0⟩
    omega
  · intro y hy
    rw [hKP] at hy
    exact ((hf y) hy).1
  · rw [hKP]
    have hsum3 : ∑ y ∈ K0.erase [], 3 * (childZone ms (nodes h) (r + 1) y).card ≤
        ∑ y ∈ K0.erase [], ((plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card +
          2 * (zoneK ms h (r + 1) f y).card +
          ∑ u ∈ zoneK ms h (r + 1) f y,
            min (childZone ms (childZone ms (nodes h) (r + 1) y) (f y) u).card (cap - 2)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact ((hf y) hy).2
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum3
    have hmv' := moves_eq hV hh
    omega

end SpookyTree
