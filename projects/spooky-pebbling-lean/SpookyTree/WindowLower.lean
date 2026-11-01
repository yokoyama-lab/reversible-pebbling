/-
# 窓の下界: 入れ子の切断（定理 A）

紙の証明は `notes/spooky-pebbling/tree-gap/WINDOW_LB_2026-10-31.md` の 1 節。ここで機械化するのは、
そのうち事実 0(a)(b)(c)・補題 2（下り）・区域の分割と数え上げ（補題 1 は使わない）。

**主張（`window_lower_bound`）.** 高さ `h ≥ 1` の完全二分木（頂点 `n = 2^h − 1`）、ペブル上限 `cap`
（＝紙の `p`）の妥当な手順の手数 `T` について、すべての `K` で
  `T + 1 ≥ 2 Σ_{k<K} (n − S_k)⁺`、`S_0 = 0`、`S_{k+1} = p + (p − 1) Σ_{j<k} (p − 2)^{j+1}`
（`(·)⁺` は ℕ の切り捨て引き算）。`S_{k+1}` は紙の `S_{k+1} = p + (p−1) Σ_{j=1}^{k} (p−2)^j` と同じ。
`p ≥ 3` は仮定に要らない（`p ≤ 2` では右辺が `K` とともに発散するので、`h ≥ 2` の妥当な手順が無いことも従う）。

**証明の形.**
* 根がそれ以後ずっとペブルである最初の時刻を `c₀`（紙の R の直後）とする。全頂点は `c₀` より前に置かれる（補題 R）。
* 区域 `Z`（親 `y`、親の切断の時刻 `c`）の不変条件 `IsZone`: `Z` の頂点は `y` の真の子孫で時刻 `c` にペブルでなく、
  `y` から各頂点への道（`y` を除く）は `Z` に入る。
* `y` が初めて空になる手（unpebble。直前の盤面を `f` とする）では `y` と両方の子がペブル（事実 0(b) の形）。
  区域の頂点はすべて `[c, f)` で置かれる（補題 2 を道に沿って繰り返す `pathR`）。
* `f` の盤面で数え済み `K_Z = Z ∩ P_f` は根と `y` を除いて `p − 2` 個以下。`Z ∖ K_Z` は `u ∈ K_Z` ごとの子区域
  `childZone Z f u`（`u` から下る道が `f` でペブルでない頂点）に分割される（`cover_zone`・`childZone_disjoint`）。
* `K` についての帰納法で、区域 `Z` の頂点への `c` 以後の置く手は `Σ_{j<K} (|Z| − (p−2)·G_j)⁺` 以上
  （`G_0 = 0`、`G_{j+1} = 1 + (p−2) G_j`）。最上段では区域は `p − 1` 個以下。
-/
import SpookyTree.Main

namespace SpookyTree

variable {h cap T : ℕ} {ms : ℕ → Move}

/-! ## 道具 -/

theorem append_single_ne (y : Node) (b : Bool) : y ++ [b] ≠ y := by
  intro he; have := congrArg List.length he; simp at this

theorem ne_of_child_prefix {y w : Node} {b : Bool} (hw : y ++ [b] <+: w) : w ≠ y := by
  intro he; rw [he] at hw; have := hw.length_le; simp at this

/-- 最後に `P` が偽だった時刻: `¬P 0`、`P T` なら、`r < T`、`¬P r`、`(r, T]` では `P`。 -/
theorem last_cross {P : ℕ → Prop} : ∀ T, ¬ P 0 → P T → ∃ r, r < T ∧ ¬ P r ∧ ∀ t, r < t → t ≤ T → P t := by
  intro T
  induction T with
  | zero => intro h0 hT; exact absurd hT h0
  | succ T ih =>
    intro h0 hT
    by_cases hP : P T
    · obtain ⟨r, hr, hnr, hall⟩ := ih h0 hP
      refine ⟨r, by omega, hnr, fun t h1 h2 => ?_⟩
      rcases Nat.lt_or_ge T t with h3 | h3
      · have : t = T + 1 := by omega
        rw [this]; exact hT
      · exact hall t h1 h3
    · refine ⟨T, by omega, hP, fun t h1 h2 => ?_⟩
      have : t = T + 1 := by omega
      rw [this]; exact hT

/-- ℕ の切り捨て引き算の和: `Σ a_i − |s|·x ≤ Σ (a_i − x)`。 -/
theorem sum_tsub_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℕ) (x : ℕ) :
    (∑ i ∈ s, a i) - s.card * x ≤ ∑ i ∈ s, (a i - x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, add_mul, one_mul]
    omega

/-! ## 事実 0(b) と補題 2 -/

/-- **事実 0(b) の形.** 根以外の内部頂点 `y` が時刻 `c ≤ T` にペブルなら、`c ≤ f < T` のある `f` で
`y` と両方の子がペブル（`c` 以後に `y` が初めて空になる手は unpebble で、`f` はその直前の盤面）。 -/
theorem unpebble_time (hV : Valid h cap T ms) {y : Node} (hy : y ≠ []) (hint : y.length + 1 < h)
    {c : ℕ} (hcT : c ≤ T) (hyc : st ms c y = .pebble) :
    ∃ f, c ≤ f ∧ f < T ∧ st ms f y = .pebble ∧
      st ms f (y ++ [false]) = .pebble ∧ st ms f (y ++ [true]) = .pebble := by
  have hend : st ms T y = .empty := hV.others y (by omega) hy
  obtain ⟨f, hcf, hfT, hf0, hf1⟩ :=
    exists_cross (P := fun r => st ms r y = .empty) hcT (by simp [hyc]) hend
  have hmv : (ms f).v = y := by
    by_contra hne
    rw [st_succ_ne hne] at hf1
    exact hf0 hf1
  have hres : st ms (f + 1) y = result (ms f).op := by rw [← hmv]; exact st_succ_eq
  have hop : (ms f).op = .unpebble := by
    have h2 : result (ms f).op = .empty := by rw [← hres]; exact hf1
    revert h2
    generalize (ms f).op = o
    cases o <;> decide
  have hL := hV.legal f hfT
  unfold Legal at hL
  rw [hmv] at hL
  rw [hop] at hL
  have hpeb : st ms f y = .pebble := hL.2.1
  have hready : Ready h (st ms f) y := hL.2.2
  rcases hready with hleaf | ⟨h0, h1⟩
  · omega
  · exact ⟨f, hcf, hfT, hpeb, h0, h1⟩

/-- **補題 2（下り）を道に沿って繰り返す.** 時刻 `t` に `a` がペブルで、`a` から子孫 `d` への道の頂点
（両端を含む）が時刻 `g ≤ t` にどれもペブルでないなら、`d` への置く手が `[g, t)` にある。 -/
theorem pathR (hV : Valid h cap T ms) :
    ∀ (k : ℕ) (a d : Node), d.length - a.length = k → a <+: d → d.length < h →
    ∀ g t, g ≤ t → t ≤ T → (∀ w, a <+: w → w <+: d → st ms g w ≠ .pebble) →
    st ms t a = .pebble → ∃ i, g ≤ i ∧ i < t ∧ (ms i).v = d ∧ IsPlace (ms i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a d hk had hdl g t hgt htT hfree hat
  obtain ⟨i, hgi, hit, hi0, hi1⟩ :=
    exists_cross (P := fun s => st ms s a = .pebble) hgt (hfree a (List.prefix_refl a) had) hat
  obtain ⟨hmv, hplace⟩ := place_of_change hi0 hi1
  by_cases hda : d = a
  · rw [hda]; exact ⟨i, hgi, hit, hmv, hplace⟩
  · obtain ⟨b, hb⟩ := prefix_child had hda
    have hbl : a.length + 1 ≤ d.length := by simpa using hb.length_le
    have hlen : (a ++ [b]).length = a.length + 1 := by simp
    have hready : Ready h (st ms i) a := by
      have hr := ready_of_place hV (by omega) hplace
      rwa [hmv] at hr
    have hchild : st ms i (a ++ [b]) = .pebble := by
      rcases hready with hleaf | ⟨h0, h1⟩
      · omega
      · cases b <;> assumption
    obtain ⟨j, hgj, hji, hjv, hjp⟩ :=
      ih (d.length - (a ++ [b]).length) (by omega) (a ++ [b]) d rfl hb hdl g i hgi
        (by omega) (fun w hw1 hw2 => hfree w ((List.prefix_append a [b]).trans hw1) hw2) hchild
    exact ⟨j, hgj, by omega, hjv, hjp⟩

/-! ## 区域 -/

/-- 時刻 `c` 以後（`c ≤ i < T`）に、`Z` の頂点に打つ置く手の添字。 -/
def plAfter (ms : ℕ → Move) (T c : ℕ) (Z : Finset Node) : Finset ℕ :=
  (Finset.range T).filter (fun i => c ≤ i ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z)

theorem mem_plAfter {c : ℕ} {Z : Finset Node} {i : ℕ} :
    i ∈ plAfter ms T c Z ↔ i < T ∧ c ≤ i ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z := by
  unfold plAfter; rw [Finset.mem_filter, Finset.mem_range]

open Classical in
/-- 子区域: `Z` のうち `u` の真の子孫で、`u` から下る道（`u` を除き、自身を含む）が時刻 `c` にペブルでないもの。 -/
noncomputable def childZone (ms : ℕ → Move) (Z : Finset Node) (c : ℕ) (u : Node) : Finset Node :=
  Z.filter (fun d => u <+: d ∧ d ≠ u ∧ ∀ w, u <+: w → w <+: d → w ≠ u → st ms c w ≠ .pebble)

open Classical in
theorem mem_childZone {Z : Finset Node} {c : ℕ} {u d : Node} :
    d ∈ childZone ms Z c u ↔ d ∈ Z ∧ u <+: d ∧ d ≠ u ∧
      ∀ w, u <+: w → w <+: d → w ≠ u → st ms c w ≠ .pebble := by
  unfold childZone; exact Finset.mem_filter

theorem childZone_subset {Z : Finset Node} {c : ℕ} {u : Node} : childZone ms Z c u ⊆ Z := by
  intro d hd; exact (mem_childZone.mp hd).1

/-- 同じ時刻にペブルの 2 頂点の子区域は交わらない。 -/
theorem childZone_disjoint {Z : Finset Node} {c : ℕ} {u u' : Node}
    (hu : st ms c u = .pebble) (hu' : st ms c u' = .pebble) (hne : u ≠ u') :
    Disjoint (childZone ms Z c u) (childZone ms Z c u') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  obtain ⟨-, h1, -, h3⟩ := mem_childZone.mp hd
  obtain ⟨-, h1', -, h3'⟩ := mem_childZone.mp hd'
  rcases lt_trichotomy u.length u'.length with hl | hl | hl
  · exact h3 u' (List.prefix_of_prefix_length_le h1 h1' hl.le) h1' (Ne.symm hne) hu'
  · exact hne (prefix_eq_of_length h1 h1' hl)
  · exact h3' u (List.prefix_of_prefix_length_le h1' h1 hl.le) h1 hne hu

/-- 区域の不変条件（親 `y`、親の切断の時刻 `c`）。 -/
def IsZone (h : ℕ) (ms : ℕ → Move) (Z : Finset Node) (y : Node) (c : ℕ) : Prop :=
  (∀ d ∈ Z, d.length < h ∧ y <+: d ∧ d ≠ y ∧ st ms c d ≠ .pebble) ∧
  (∀ d ∈ Z, ∀ w, y <+: w → w <+: d → w ≠ y → w ∈ Z)

/-- `Z` が `u` の下で道について閉じていれば、子区域は（親 `u`、時刻 `c` の）区域。 -/
theorem childZone_isZone {Z : Finset Node} {c : ℕ} {u : Node}
    (hlen : ∀ d ∈ Z, d.length < h)
    (hclosed : ∀ d ∈ Z, ∀ w, u <+: w → w <+: d → w ≠ u → w ∈ Z) :
    IsZone h ms (childZone ms Z c u) u c := by
  constructor
  · intro d hd
    obtain ⟨hdZ, h1, h2, h3⟩ := mem_childZone.mp hd
    exact ⟨hlen d hdZ, h1, h2, h3 d h1 (List.prefix_refl d) h2⟩
  · intro d hd w hw1 hw2 hw3
    obtain ⟨hdZ, -, -, h3⟩ := mem_childZone.mp hd
    exact mem_childZone.mpr ⟨hclosed d hdZ w hw1 hw2 hw3, hw1, hw3,
      fun w' h1' h2' h3' => h3 w' h1' (h2'.trans hw2) h3'⟩

/-- 最も近いペブルの祖先: 時刻 `c` に `a` がペブルで、その子孫 `d` がペブルでないなら、
`a <+: u <+: d`、`u ≠ d`、`u` はペブルで、`u` から `d` への道（`u` を除く）はペブルでない。 -/
theorem cover (c : ℕ) (a : Node) (hac : st ms c a = .pebble) :
    ∀ d : Node, a <+: d → st ms c d ≠ .pebble →
    ∃ u, a <+: u ∧ u <+: d ∧ u ≠ d ∧ st ms c u = .pebble ∧
      ∀ w, u <+: w → w <+: d → w ≠ u → st ms c w ≠ .pebble := by
  intro d
  induction d using List.reverseRecOn with
  | nil =>
    intro had hd
    rw [List.prefix_nil.mp had] at hac
    exact absurd hac hd
  | append_singleton d' b ih =>
    intro had hd
    have had' : a <+: d' := by
      rcases List.prefix_concat_iff.mp had with heq | hp
      · rw [heq] at hac; exact absurd hac hd
      · exact hp
    by_cases hd' : st ms c d' = .pebble
    · refine ⟨d', had', List.prefix_append d' [b], (append_single_ne d' b).symm, hd', ?_⟩
      intro w hw1 hw2 hw3
      rcases List.prefix_concat_iff.mp hw2 with heq | hp
      · rw [heq]; exact hd
      · exact absurd (hp.eq_of_length (le_antisymm hp.length_le hw1.length_le)) hw3
    · obtain ⟨u, hau, hud', -, hup, hpath⟩ := ih had' hd'
      refine ⟨u, hau, hud'.trans (List.prefix_append d' [b]), ?_, hup, ?_⟩
      · intro heq
        have := hud'.length_le
        rw [heq] at this; simp at this
      · intro w hw1 hw2 hw3
        rcases List.prefix_concat_iff.mp hw2 with heq | hp
        · rw [heq]; exact hd
        · exact hpath w hw1 hp hw3

/-- **区域の分割（被覆）.** 時刻 `f` に `y` がペブル、`d` への道上の `y` の子がペブル、`d` はペブルでなく、
`y` から `d` への道（`y` を除く）が `Z` に入るなら、`d` はある `u ∈ Z`（`u ≠ y`、`f` でペブル）の子区域に入る。 -/
theorem cover_zone {Z : Finset Node} {y d : Node} {f : ℕ}
    (hy : st ms f y = .pebble)
    (htop : ∀ b : Bool, y ++ [b] <+: d → st ms f (y ++ [b]) = .pebble)
    (hyd : y <+: d) (hdZ : d ∈ Z) (hdf : st ms f d ≠ .pebble)
    (hclosed : ∀ w, y <+: w → w <+: d → w ≠ y → w ∈ Z) :
    ∃ u, u ∈ Z ∧ u ≠ y ∧ st ms f u = .pebble ∧ d ∈ childZone ms Z f u := by
  obtain ⟨u, hyu, hud, hne, hup, hpath⟩ := cover f y hy d hyd hdf
  have huy : u ≠ y := by
    intro heq
    rw [heq] at hud hne hpath
    obtain ⟨b, hb⟩ := prefix_child hud (Ne.symm hne)
    exact hpath (y ++ [b]) (List.prefix_append y [b]) hb (append_single_ne y b) (htop b hb)
  exact ⟨u, hclosed u hyu hud huy, huy, hup, mem_childZone.mpr ⟨hdZ, hud, Ne.symm hne, hpath⟩⟩

/-! ## 区域の数え上げ（`K` についての帰納法） -/

/-- `G q 0 = 0`、`G q (j+1) = 1 + q·G q j`（`= Σ_{i<j} q^i`）。 -/
def Gw (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + q * Gw q j

theorem Gw_eq_sum (q j : ℕ) : Gw q j = ∑ i ∈ Finset.range j, q ^ i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Finset.sum_range_succ']
    show 1 + q * Gw q j = _
    rw [ih, Finset.mul_sum]
    simp only [pow_succ', pow_zero]
    ring

/-- **区域の補題.** `c₀` 以後は根がずっとペブルとする。区域 `Z`（親 `y ≠ 根`、親の切断の時刻 `c ≥ c₀`、
`y` は `c` でペブル）の頂点への `c` 以後の置く手は `Σ_{j<K} (|Z| − (p−2)·G_j)⁺` 以上。 -/
theorem zone_bound (hV : Valid h cap T ms) {c0 : ℕ}
    (hroot : ∀ t, c0 ≤ t → t ≤ T → st ms t [] = .pebble) :
    ∀ (K : ℕ) (Z : Finset Node) (y : Node) (c : ℕ), c0 ≤ c → c ≤ T → y ≠ [] →
      st ms c y = .pebble → IsZone h ms Z y c →
      ∑ j ∈ Finset.range K, (Z.card - (cap - 2) * Gw (cap - 2) j) ≤ (plAfter ms T c Z).card := by
  intro K
  induction K with
  | zero => intros; simp
  | succ K ih =>
  intro Z y c hc0 hcT hy hyc hZ
  obtain ⟨hZ1, hZ2⟩ := hZ
  rcases Z.eq_empty_or_nonempty with hZe | ⟨d0, hd0⟩
  · subst hZe; simp
  -- y は内部頂点
  have hint : y.length + 1 < h := by
    obtain ⟨hl, hp, hne, -⟩ := hZ1 d0 hd0
    have : y.length < d0.length :=
      lt_of_le_of_ne hp.length_le (fun he => hne (hp.eq_of_length he).symm)
    omega
  obtain ⟨f, hcf, hfT, hyf, hf0, hf1⟩ := unpebble_time hV hy hint hcT hyc
  have hkid : ∀ b : Bool, st ms f (y ++ [b]) = .pebble := by intro b; cases b <;> assumption
  obtain ⟨q, hq⟩ : ∃ q, q = cap - 2 := ⟨_, rfl⟩
  rw [← hq] at ih ⊢
  -- 数え済み K_Z = Z ∩ P_f
  obtain ⟨KZ, hKZ⟩ : ∃ KZ : Finset Node, KZ = Z.filter (fun x => st ms f x = .pebble) := ⟨_, rfl⟩
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
  -- 子区域に帰納法の仮定
  have hsubIH : ∀ u ∈ KZ, ∑ j ∈ Finset.range K, ((childZone ms Z f u).card - q * Gw q j)
      ≤ (plAfter ms T f (childZone ms Z f u)).card := by
    intro u hu
    rw [memK] at hu
    obtain ⟨huZ, hup⟩ := hu
    obtain ⟨-, hyu, huy, -⟩ := hZ1 u huZ
    have hu0 : u ≠ [] := by
      intro he; rw [he] at hyu; exact hy (List.prefix_nil.mp hyu)
    apply ih _ u f (by omega) (by omega) hu0 hup
    apply childZone_isZone (fun d hd => (hZ1 d hd).1)
    intro d hd w hw1 hw2 hw3
    apply hZ2 d hd w (hyu.trans hw1) hw2
    intro he
    rw [he] at hw1
    exact huy (hyu.eq_of_length (le_antisymm hyu.length_le hw1.length_le)).symm
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
  -- 算術
  have hstep : ∀ j ∈ Finset.range K, Z.card - q * Gw q (j + 1)
      ≤ ∑ u ∈ KZ, ((childZone ms Z f u).card - q * Gw q j) := by
    intro j _
    have hb : (∑ u ∈ KZ, (childZone ms Z f u).card) - KZ.card * (q * Gw q j)
        ≤ ∑ u ∈ KZ, ((childZone ms Z f u).card - q * Gw q j) := sum_tsub_le _ _ _
    have hm : KZ.card * (q * Gw q j) ≤ q * (q * Gw q j) := Nat.mul_le_mul_right _ hKcard
    have hG : q * Gw q (j + 1) = q + q * (q * Gw q j) := by
      show q * (1 + q * Gw q j) = _; ring
    omega
  have hsum1 : ∑ j ∈ Finset.range K, (Z.card - q * Gw q (j + 1))
      ≤ ∑ u ∈ KZ, (plAfter ms T f (childZone ms Z f u)).card := by
    calc ∑ j ∈ Finset.range K, (Z.card - q * Gw q (j + 1))
        ≤ ∑ j ∈ Finset.range K, ∑ u ∈ KZ, ((childZone ms Z f u).card - q * Gw q j) :=
          Finset.sum_le_sum hstep
      _ = ∑ u ∈ KZ, ∑ j ∈ Finset.range K, ((childZone ms Z f u).card - q * Gw q j) :=
          Finset.sum_comm
      _ ≤ ∑ u ∈ KZ, (plAfter ms T f (childZone ms Z f u)).card := Finset.sum_le_sum hsubIH
  rw [Finset.sum_range_succ', show Gw q 0 = 0 from rfl, mul_zero, Nat.sub_zero]
  omega

/-! ## 定理 A -/

/-- 紙の `S_k`: `S_0 = 0`、`S_{k+1} = p + (p − 1) Σ_{j<k} (p − 2)^{j+1}`（`= p + (p−1) Σ_{j=1}^{k} (p−2)^j`）。 -/
def Swin (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1)

theorem Swin_succ (p k : ℕ) : Swin p (k + 1) = p + (p - 1) * ((p - 2) * Gw (p - 2) k) := by
  show p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1) = _
  rw [Gw_eq_sum]
  congr 2
  rw [Finset.mul_sum]
  simp only [pow_succ']

/-- **定理 A（入れ子の切断による窓の下界）.** 高さ `h ≥ 1` の完全二分木、ペブル上限 `cap` の妥当な手順
（手数 `T`）について、すべての `K` で `T + 1 ≥ 2 Σ_{k<K} (2^h − 1 − S_k)⁺`。 -/
theorem window_lower_bound (hV : Valid h cap T ms) (hh : 1 ≤ h) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (2 ^ h - 1 - Swin cap k) ≤ T + 1 := by
  cases K with
  | zero => simp
  | succ K =>
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
  set q := cap - 2 with hq
  -- 段 1 の区域
  have hzone : ∀ y ∈ K0.erase [], ∑ j ∈ Finset.range K,
      ((childZone ms (nodes h) (r + 1) y).card - q * Gw q j)
      ≤ (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card := by
    intro y hy
    obtain ⟨hy0, hyK⟩ := Finset.mem_erase.mp hy
    apply zone_bound hV hroot K _ y (r + 1) le_rfl (by omega) hy0 ((memK0 y).mp hyK).2
    apply childZone_isZone (fun d hd => mem_nodes.mp hd)
    intro d hd w _ hw2 _
    exact mem_nodes.mpr (lt_of_le_of_lt hw2.length_le (mem_nodes.mp hd))
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
  -- 算術
  have hK0e : (K0.erase []).card = K0.card - 1 := Finset.card_erase_of_mem hrootK0
  have hstep : ∀ j ∈ Finset.range K, 2 ^ h - 1 - Swin cap (j + 1)
      ≤ ∑ y ∈ K0.erase [], ((childZone ms (nodes h) (r + 1) y).card - q * Gw q j) := by
    intro j _
    have hb : (∑ y ∈ K0.erase [], (childZone ms (nodes h) (r + 1) y).card)
        - (K0.erase []).card * (q * Gw q j)
        ≤ ∑ y ∈ K0.erase [], ((childZone ms (nodes h) (r + 1) y).card - q * Gw q j) :=
      sum_tsub_le _ _ _
    have hm : (K0.erase []).card * (q * Gw q j) ≤ (cap - 1) * (q * Gw q j) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Swin_succ, ← hq]
    omega
  have hsum1 : ∑ j ∈ Finset.range K, (2 ^ h - 1 - Swin cap (j + 1))
      ≤ ∑ y ∈ K0.erase [], (plAfter ms T (r + 1) (childZone ms (nodes h) (r + 1) y)).card := by
    calc ∑ j ∈ Finset.range K, (2 ^ h - 1 - Swin cap (j + 1))
        ≤ ∑ j ∈ Finset.range K, ∑ y ∈ K0.erase [],
            ((childZone ms (nodes h) (r + 1) y).card - q * Gw q j) := Finset.sum_le_sum hstep
      _ = ∑ y ∈ K0.erase [], ∑ j ∈ Finset.range K,
            ((childZone ms (nodes h) (r + 1) y).card - q * Gw q j) := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum hzone
  have hmv' := moves_eq hV hh
  rw [Finset.sum_range_succ', show Swin cap 0 = 0 from rfl, Nat.sub_zero]
  omega

end SpookyTree
