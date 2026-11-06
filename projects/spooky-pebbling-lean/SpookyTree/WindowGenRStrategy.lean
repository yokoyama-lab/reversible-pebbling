/-
# 定理 genr の還元: 戦略から切断点を作り，手数の下界を出す

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` 1.1 節（区域の入れ子と
`T ≥ 2((m+1)n − mp − Σ … − V*_{m−1}) − 1`），`WINDOW_GENM_ALL_2026-11.md` 2.8 節の総和の段落．
前の煉瓦は `WindowGenRZones`（`CutData`，`val_top_le`，`card_E_le`）と `WindowLower`
（`IsZone`，`childZone`，`plAfter`，`pathR`，`cover_zone`，`zone_bound`，`unpebble_time`）．

## 作り方
妥当な手順 `ms`（手数 `T`，ペブル上限 `p`）について，根が最後に置かれた直後の時刻を `c₀` とする．
最上段（段 `top`）の区域は根 `[]`，その切断の時刻は `c₀`．段 `L < top` の区域 `y` の切断の時刻 `cT L y` は親の区域の
`f`（最上段では `c₀`，それ以外は `y` の親が初めて空になる手の直前 `ftime`）で，数え済みの点の候補は
その時刻の盤面のペブル `Kf L y = P_{fT L y}`．これで `SData.toCut : CutData` を作る（`lvS` で上から）．

## 示すこと
* `toCut_ok`: `CutData.Ok`（予算: 中の段 `|K_Z| ≤ p − 2`，最上段 `≤ p − 1`，`Q = p − 1`）．
* `zone_inv`: 段 `L < top` の区域 `Z_y` について，`c` 以後の `Z_y` への置く手の数は
  `(L + 2)|Z_y| − (L + 1)|Z_y ∩ E_0| − Val_L(y)` 以上（紙 R1 1.1 の `r(v) ≥ 1 + lev(v)` を区域ごとに）．
* `genr_lower_val`: `T + 1 ≥ 2((top + 2)(2^h − 1) − (top + 1)p − top·|E_0| − Val_top([]))`．
* `genr_lower`: これに `val_top_le`・`card_E_le` を入れた有限の下界（定理 genr の有限の形）．
-/
import SpookyTree.WindowGenRZones
import SpookyTree.WindowLower

open Finset

namespace SpookyTree
namespace GenRZones

open GenRSigma GenRDual GenRLemmaT GenRReduction

section strat
variable {h cap T : ℕ} {ms : ℕ → Move}

open Classical in
/-- 時刻 `t` の盤面のペブル（高さ `hh` の木の中）． -/
noncomputable def Pset (ms : ℕ → Move) (hh t : ℕ) : Finset Node :=
  (nodes hh).filter (fun x => st ms t x = .pebble)

theorem mem_Pset {hh t : ℕ} {x : Node} : x ∈ Pset ms hh t ↔ x.length < hh ∧ st ms t x = .pebble := by
  classical
  unfold Pset; rw [mem_filter, mem_nodes]

/-- `y` が `c` 以後に初めて空になる手の直前（`y` と両方の子がペブル）． -/
def UnpebAt (ms : ℕ → Move) (T c f : ℕ) (y : Node) : Prop :=
  c ≤ f ∧ f < T ∧ st ms f y = .pebble ∧ ∀ b : Bool, st ms f (y ++ [b]) = .pebble

open Classical in
noncomputable def ftime (ms : ℕ → Move) (T c : ℕ) (y : Node) : ℕ :=
  if hx : ∃ f, UnpebAt ms T c f y then hx.choose else c

theorem ftime_spec {c : ℕ} {y : Node} (hx : ∃ f, UnpebAt ms T c f y) :
    UnpebAt ms T c (ftime ms T c y) y := by
  unfold ftime; rw [dif_pos hx]; exact hx.choose_spec

theorem ftime_ge (c : ℕ) (y : Node) : c ≤ ftime ms T c y := by
  unfold ftime
  split_ifs with hx
  · exact hx.choose_spec.1
  · exact le_rfl

theorem ftime_le {c : ℕ} {y : Node} (hc : c ≤ T) : ftime ms T c y ≤ T := by
  unfold ftime
  split_ifs with hx
  · exact hx.choose_spec.2.1.le
  · exact hc

theorem ftime_peb {c : ℕ} {y : Node} (hyc : st ms c y = .pebble) :
    st ms (ftime ms T c y) y = .pebble := by
  unfold ftime
  split_ifs with hx
  · exact hx.choose_spec.2.2.1
  · exact hyc

/-- **区域の 1 段**（`zone_bound` の証明の中身）: 区域 `Z`（親 `y`，時刻 `c`）と `y` が空になる直前 `f` について，
`|Z| + Σ_{u ∈ Z ∩ P_f} pl(f, 子区域 u) ≤ pl(c, Z)`，`|Z| ≤ |Z ∩ P_f| + Σ_u |子区域 u|`． -/
theorem zone_split (hV : Valid h cap T ms) {Z : Finset Node} {y : Node} {c f : ℕ}
    (hZ : IsZone h ms Z y c) (hf : UnpebAt ms T c f y) :
    Z.card + ∑ u ∈ Z.filter (fun x => st ms f x = .pebble),
        (plAfter ms T f (childZone ms Z f u)).card ≤ (plAfter ms T c Z).card ∧
      Z.card ≤ (Z.filter (fun x => st ms f x = .pebble)).card +
        ∑ u ∈ Z.filter (fun x => st ms f x = .pebble), (childZone ms Z f u).card := by
  classical
  obtain ⟨hZ1, hZ2⟩ := hZ
  obtain ⟨hcf, hfT, hyf, hkid⟩ := hf
  set KZ := Z.filter (fun x => st ms f x = .pebble) with hKZ
  have memK : ∀ x, x ∈ KZ ↔ x ∈ Z ∧ st ms f x = .pebble := by
    intro x; rw [hKZ, Finset.mem_filter]
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
  have hcov : Z.card ≤ KZ.card + ∑ u ∈ KZ, (childZone ms Z f u).card := by
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
    have h2 : KZ ⊆ Z := Finset.filter_subset _ _
    have h3 := Finset.card_sdiff_add_card_eq_card h2
    omega
  exact ⟨by omega, hcov⟩

end strat

/-! ## 戦略の切断点 -/

/-- 戦略と切断の構造のパラメータ（`hgt = (top + 1) H + r`）． -/
structure SData where
  ms : ℕ → Move
  T : ℕ
  c0 : ℕ
  H : ℕ
  r : ℕ
  top : ℕ
  γ : ℝ
  Q : ℕ

namespace SData

variable (S : SData)

def hgt : ℕ := (S.top + 1) * S.H + S.r

open Classical in
/-- 上から `d` 段目の区域の根，前の段までの点，区域の切断の時刻． -/
noncomputable def lvS : ℕ → Finset Node × Finset Node × (Node → ℕ)
  | 0 => ({[]}, {[]}, fun _ => S.c0)
  | d + 1 =>
    ((lvS d).1.biUnion (fun y => (Pset S.ms S.hgt
        (if d = 0 then (lvS d).2.2 y else ftime S.ms S.T ((lvS d).2.2 y) y)).filter
          (inZ (lvS d).2.1 y)),
     (lvS d).2.1 ∪ (lvS d).1.biUnion (fun y => (Pset S.ms S.hgt
        (if d = 0 then (lvS d).2.2 y else ftime S.ms S.T ((lvS d).2.2 y) y)).filter
          (inZ (lvS d).2.1 y)),
     fun x => if hx : ∃ y ∈ (lvS d).1, inZ (lvS d).2.1 y x then
        (if d = 0 then (lvS d).2.2 hx.choose else
          ftime S.ms S.T ((lvS d).2.2 hx.choose) hx.choose) else 0)

/-- 上から `d` 段目の区域 `y` の数え済みの時刻（最上段は `c₀`，それ以外は `y` が空になる直前）． -/
noncomputable def fS (d : ℕ) (y : Node) : ℕ :=
  if d = 0 then (S.lvS d).2.2 y else ftime S.ms S.T ((S.lvS d).2.2 y) y

open Classical in
theorem lvS_succ1 (d : ℕ) : (S.lvS (d + 1)).1 =
    (S.lvS d).1.biUnion (fun y => (Pset S.ms S.hgt (S.fS d y)).filter (inZ (S.lvS d).2.1 y)) := rfl

open Classical in
theorem lvS_succ3 (d : ℕ) (x : Node) : (S.lvS (d + 1)).2.2 x =
    if hx : ∃ y ∈ (S.lvS d).1, inZ (S.lvS d).2.1 y x then S.fS d hx.choose else 0 := rfl

/-- 戦略から作った切断点の構造． -/
noncomputable def toCut : CutData where
  H := S.H
  r := S.r
  top := S.top
  γ := S.γ
  Q := S.Q
  Kf := fun L y => Pset S.ms S.hgt (S.fS (S.top - L) y)

/-- 段 `L` の区域の切断の時刻． -/
noncomputable def cT (L : ℕ) (y : Node) : ℕ := (S.lvS (S.top - L)).2.2 y
/-- 段 `L` の区域の数え済みの時刻． -/
noncomputable def fT (L : ℕ) (y : Node) : ℕ := S.fS (S.top - L) y

theorem toCut_hgt : S.toCut.hgt = S.hgt := rfl

theorem Ys_top' : S.toCut.Ys S.top = {[]} := S.toCut.Ys_top
theorem E_top' : S.toCut.E S.top = {[]} := S.toCut.E_top

theorem lv_eq : ∀ d, d ≤ S.top → S.toCut.lv d = ((S.lvS d).1, (S.lvS d).2.1) := by
  classical
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have e := ih (by omega)
    have hk : ∀ y, S.toCut.Kf (S.toCut.top - d) y = Pset S.ms S.hgt (S.fS d y) := by
      intro y
      show Pset S.ms S.hgt (S.fS (S.top - (S.top - d)) y) = _
      rw [show S.top - (S.top - d) = d by omega]
    show ((S.toCut.lv d).1.biUnion
        (fun y => (S.toCut.Kf (S.toCut.top - d) y).filter (inZ (S.toCut.lv d).2 y)),
      (S.toCut.lv d).2 ∪ (S.toCut.lv d).1.biUnion
        (fun y => (S.toCut.Kf (S.toCut.top - d) y).filter (inZ (S.toCut.lv d).2 y))) = _
    simp only [hk, e]
    rfl

theorem Ys_eq {L : ℕ} (hL : L ≤ S.top) : S.toCut.Ys L = (S.lvS (S.top - L)).1 := by
  show (if L ≤ S.top then (S.toCut.lv (S.top - L)).1 else ∅) = _
  rw [if_pos hL, S.lv_eq _ (by omega)]

theorem E_eq {L : ℕ} (hL : L ≤ S.top) : S.toCut.E L = (S.lvS (S.top - L)).2.1 := by
  show (if L ≤ S.top then (S.toCut.lv (S.top - L)).2 else {[]}) = _
  rw [if_pos hL, S.lv_eq _ (by omega)]

open Classical in
theorem KZ_def (L : ℕ) (y : Node) :
    S.toCut.KZ (L + 1) y = (Pset S.ms S.hgt (S.fT (L + 1) y)).filter (inZ (S.toCut.E (L + 1)) y) := rfl

theorem fT_top (y : Node) : S.fT S.top y = S.cT S.top y := by
  unfold fT cT fS; rw [Nat.sub_self, if_pos rfl]

theorem cT_top (y : Node) : S.cT S.top y = S.c0 := by
  unfold cT; rw [Nat.sub_self]; rfl

theorem fT_mid {L : ℕ} (hL : L < S.top) (y : Node) :
    S.fT L y = ftime S.ms S.T (S.cT L y) y := by
  unfold fT cT fS; rw [if_neg (by omega)]

/-- 子の区域の切断の時刻は親の区域の数え済みの時刻． -/
theorem child_time {L : ℕ} (hL : L < S.top) {y x : Node} (hy : y ∈ S.toCut.Ys (L + 1))
    (hx : x ∈ S.toCut.KZ (L + 1) y) : S.cT L x = S.fT (L + 1) y := by
  classical
  have hxZ : inZ (S.toCut.E (L + 1)) y x := by rw [KZ_def] at hx; exact (mem_filter.mp hx).2
  obtain ⟨d, hd1, hd2⟩ : ∃ d, S.top - L = d + 1 ∧ S.top - (L + 1) = d := ⟨_, by omega, rfl⟩
  have hY := S.Ys_eq (L := L + 1) (by omega)
  have hE := S.E_eq (L := L + 1) (by omega)
  rw [hd2] at hY hE
  unfold cT
  rw [hd1, lvS_succ3]
  have hyd : y ∈ (S.lvS d).1 := by rw [← hY]; exact hy
  have hxd : inZ (S.lvS d).2.1 y x := by rw [← hE]; exact hxZ
  have hex : ∃ y ∈ (S.lvS d).1, inZ (S.lvS d).2.1 y x := ⟨y, hyd, hxd⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h1' : hex.choose ∈ S.toCut.Ys (L + 1) := by rw [hY]; exact h1
  have h2' : inZ (S.toCut.E (L + 1)) hex.choose x := by rw [hE]; exact h2
  have : hex.choose = y := by
    by_contra hne
    exact ZoneFamily.inZ_disj (S.toCut.Ys_sub_E _ h1') (S.toCut.Ys_sub_E _ hy) hne h2' hxZ
  rw [this]
  unfold fT
  rw [hd2]

/-- 根でない区域の根は空でない道． -/
theorem ne_nil_of_Ys {L : ℕ} (hL : L < S.top) {y : Node} (hy : y ∈ S.toCut.Ys L) : y ≠ [] := by
  classical
  rw [(S.toCut.Ys_succ hL).1] at hy
  obtain ⟨y', -, hy⟩ := mem_biUnion.mp hy
  rw [KZ_def] at hy
  have := inZ_lt (mem_filter.mp hy).2
  intro he; rw [he] at this; simp at this

theorem mem_Ys_parent {L : ℕ} (hL : L < S.top) {y : Node} (hy : y ∈ S.toCut.Ys L) :
    ∃ y' ∈ S.toCut.Ys (L + 1), y ∈ S.toCut.KZ (L + 1) y' := by
  rw [(S.toCut.Ys_succ hL).1] at hy
  exact mem_biUnion.mp hy

/-- 区域の根は切断の時刻にペブル（根は `c₀` にペブルとする）． -/
theorem peb_cT (hc0 : st S.ms S.c0 [] = .pebble) : ∀ d, d ≤ S.top →
    ∀ y ∈ S.toCut.Ys (S.top - d), st S.ms (S.cT (S.top - d) y) y = .pebble := by
  classical
  intro d
  induction d with
  | zero =>
    intro _ y hy
    rw [Nat.sub_zero, S.Ys_top'] at hy
    rw [mem_singleton.mp hy, Nat.sub_zero, cT_top]
    exact hc0
  | succ d _ =>
    intro hd y hy
    obtain ⟨L, hL⟩ : ∃ L, L = S.top - (d + 1) := ⟨_, rfl⟩
    rw [← hL] at hy ⊢
    obtain ⟨y', hy', hyK⟩ := S.mem_Ys_parent (L := L) (by omega) hy
    rw [S.child_time (by omega) hy' hyK]
    rw [KZ_def] at hyK
    exact (mem_Pset.mp (mem_filter.mp hyK).1).2

theorem peb_cT' (hc0 : st S.ms S.c0 [] = .pebble) {L : ℕ} (hL : L ≤ S.top) {y : Node}
    (hy : y ∈ S.toCut.Ys L) : st S.ms (S.cT L y) y = .pebble := by
  have := S.peb_cT hc0 (S.top - L) (by omega)
  rw [show S.top - (S.top - L) = L by omega] at this
  exact this y hy

/-- 時刻は `[c₀, T]` にある． -/
theorem cT_range (hc0T : S.c0 ≤ S.T) : ∀ d, d ≤ S.top →
    ∀ y ∈ S.toCut.Ys (S.top - d), S.c0 ≤ S.cT (S.top - d) y ∧ S.cT (S.top - d) y ≤ S.T := by
  intro d
  induction d with
  | zero =>
    intro _ y _
    rw [Nat.sub_zero, cT_top]
    exact ⟨le_rfl, hc0T⟩
  | succ d ih =>
    intro hd y hy
    obtain ⟨L, hL⟩ : ∃ L, L = S.top - (d + 1) := ⟨_, rfl⟩
    rw [← hL] at hy ⊢
    obtain ⟨y', hy', hyK⟩ := S.mem_Ys_parent (L := L) (by omega) hy
    rw [S.child_time (by omega) hy' hyK]
    have hL1 : L + 1 = S.top - d := by omega
    rw [hL1] at hy' ⊢
    obtain ⟨h1, h2⟩ := ih (by omega) y' hy'
    by_cases hd0 : d = 0
    · subst hd0
      rw [Nat.sub_zero, fT_top]
      rw [Nat.sub_zero] at h1 h2
      exact ⟨h1, h2⟩
    · rw [S.fT_mid (L := S.top - d) (by omega)]
      exact ⟨h1.trans (ftime_ge _ _), ftime_le h2⟩

theorem cT_range' (hc0T : S.c0 ≤ S.T) {L : ℕ} (hL : L ≤ S.top) {y : Node}
    (hy : y ∈ S.toCut.Ys L) : S.c0 ≤ S.cT L y ∧ S.cT L y ≤ S.T := by
  have := S.cT_range hc0T (S.top - L) (by omega)
  rw [show S.top - (S.top - L) = L by omega] at this
  exact this y hy

theorem fT_range (hc0T : S.c0 ≤ S.T) {L : ℕ} (hL : L ≤ S.top) {y : Node}
    (hy : y ∈ S.toCut.Ys L) : S.c0 ≤ S.fT L y ∧ S.fT L y ≤ S.T := by
  obtain ⟨h1, h2⟩ := S.cT_range' hc0T hL hy
  rcases Nat.lt_or_ge L S.top with h | h
  · rw [fT_mid _ h]; exact ⟨h1.trans (ftime_ge _ _), ftime_le h2⟩
  · have : L = S.top := by omega
    subst this
    rw [fT_top]; exact ⟨h1, h2⟩

theorem peb_fT (hc0 : st S.ms S.c0 [] = .pebble) {L : ℕ} (hL : L ≤ S.top) {y : Node}
    (hy : y ∈ S.toCut.Ys L) : st S.ms (S.fT L y) y = .pebble := by
  have h := S.peb_cT' hc0 hL hy
  rcases Nat.lt_or_ge L S.top with h' | h'
  · rw [fT_mid _ h']; exact ftime_peb h
  · have : L = S.top := by omega
    subst this
    rw [fT_top]; exact h

/-! ### 静的な区域は動的な区域 -/

theorem E_anti (L : ℕ) : S.toCut.E (L + 1) ⊆ S.toCut.E L := by
  rcases Nat.lt_or_ge L S.top with h | h
  · rw [(S.toCut.Ys_succ h).2]; exact subset_union_left
  · have e1 : S.toCut.E (L + 1) = {[]} := by
      show (if L + 1 ≤ S.top then _ else {[]}) = _; rw [if_neg (by omega)]
    rw [e1]
    rcases Nat.lt_or_ge S.top L with h2 | h2
    · have e2 : S.toCut.E L = {[]} := by
        show (if L ≤ S.top then _ else {[]}) = _; rw [if_neg (by omega)]
      rw [e2]
    · have : L = S.top := by omega
      subst this; rw [S.E_top']

theorem E_sub_E0 : ∀ L, S.toCut.E L ⊆ S.toCut.E 0
  | 0 => subset_rfl
  | L + 1 => (S.E_anti L).trans (E_sub_E0 L)

/-- 段 `L < top` の静的な区域は，切断の時刻 `cT L y` の動的な区域． -/
theorem isZone (_hc0 : st S.ms S.c0 [] = .pebble) {L : ℕ} (hL : L < S.top) {y : Node}
    (hy : y ∈ S.toCut.Ys L) : IsZone S.hgt S.ms (S.toCut.Zs L y) y (S.cT L y) := by
  classical
  obtain ⟨y', hy', hyK⟩ := S.mem_Ys_parent hL hy
  have hct := S.child_time hL hy' hyK
  have hyZ' : inZ (S.toCut.E (L + 1)) y' y := by rw [KZ_def] at hyK; exact (mem_filter.mp hyK).2
  constructor
  · intro d hd
    obtain ⟨hdn, hdZ⟩ := mem_filter.mp hd
    rw [mem_nodes] at hdn
    refine ⟨hdn, hdZ.1, hdZ.2.1, fun hp => ?_⟩
    rw [hct] at hp
    have hdZ' : inZ (S.toCut.E (L + 1)) y' d := inZ_trans (S.E_anti L) hyZ' hdZ
    have hdK : d ∈ S.toCut.KZ (L + 1) y' := by
      rw [KZ_def]; exact mem_filter.mpr ⟨mem_Pset.mpr ⟨hdn, hp⟩, hdZ'⟩
    have hdY : d ∈ S.toCut.Ys L := by
      rw [(S.toCut.Ys_succ hL).1]; exact mem_biUnion.mpr ⟨y', hy', hdK⟩
    exact hdZ.2.2 d (S.toCut.Ys_sub_E L hdY) hdZ.1 (List.prefix_refl _) hdZ.2.1
  · intro d hd w hw1 hw2 hw3
    obtain ⟨hdn, hdZ⟩ := mem_filter.mp hd
    rw [mem_nodes] at hdn
    refine mem_filter.mpr ⟨mem_nodes.mpr (lt_of_le_of_lt hw2.length_le hdn), hw1, hw3, ?_⟩
    intro e he hye hew hey
    exact hdZ.2.2 e he hye (hew.trans hw2) hey

/-- 区域の数え済みの点は区域のうち数え済みの時刻にペブルの点． -/
theorem filter_peb (L : ℕ) (y : Node) :
    (S.toCut.Zs (L + 1) y).filter (fun x => st S.ms (S.fT (L + 1) y) x = .pebble) =
      S.toCut.KZ (L + 1) y := by
  classical
  ext x
  rw [KZ_def, mem_filter, mem_filter, mem_Pset]
  unfold CutData.Zs
  rw [mem_filter, mem_nodes]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- 子区域は静的な子の区域． -/
theorem childZone_eq {L : ℕ} (hL : L < S.top) {y x : Node} (hy : y ∈ S.toCut.Ys (L + 1))
    (hx : x ∈ S.toCut.KZ (L + 1) y) :
    childZone S.ms (S.toCut.Zs (L + 1) y) (S.fT (L + 1) y) x = S.toCut.Zs L x := by
  classical
  have hE : S.toCut.E L = S.toCut.E (L + 1) ∪ S.toCut.Ys L := (S.toCut.Ys_succ hL).2
  have hxZ : inZ (S.toCut.E (L + 1)) y x := by rw [KZ_def] at hx; exact (mem_filter.mp hx).2
  have hyE : y ∈ S.toCut.E (L + 1) := S.toCut.Ys_sub_E _ hy
  -- Z_y の点で数え済みの時刻にペブルなら Ys L の点
  have hK : ∀ w, w.length < S.hgt → inZ (S.toCut.E (L + 1)) y w →
      st S.ms (S.fT (L + 1) y) w = .pebble → w ∈ S.toCut.Ys L := by
    intro w hwl hwZ hwp
    rw [(S.toCut.Ys_succ hL).1]
    refine mem_biUnion.mpr ⟨y, hy, ?_⟩
    rw [KZ_def]; exact mem_filter.mpr ⟨mem_Pset.mpr ⟨hwl, hwp⟩, hwZ⟩
  ext d
  rw [mem_childZone]
  unfold CutData.Zs
  rw [mem_filter, mem_filter, mem_nodes, hE]
  constructor
  · rintro ⟨⟨hdn, hdZ⟩, hxd, hdx, hpath⟩
    refine ⟨hdn, hxd, hdx, ?_⟩
    intro e he hxe hed hex
    have hle : e.length < S.hgt := lt_of_le_of_lt hed.length_le hdn
    have heZ : inZ (S.toCut.E (L + 1)) y e := by
      refine ⟨hxZ.1.trans hxe, fun h => ?_, ?_⟩
      · have := inZ_lt hxZ
        have := hxe.length_le
        rw [h] at this; omega
      · intro e' he' hye' he'e hey'
        exact hdZ.2.2 e' he' hye' (he'e.trans hed) hey'
    rcases mem_union.mp he with heE | heY
    · exact hdZ.2.2 e heE heZ.1 hed heZ.2.1
    · -- e ∈ Ys L で Z_y の点なので KZ y の点 = 数え済みの時刻にペブル
      rw [(S.toCut.Ys_succ hL).1] at heY
      obtain ⟨y'', hy'', heK⟩ := mem_biUnion.mp heY
      have heZ'' : inZ (S.toCut.E (L + 1)) y'' e := by rw [KZ_def] at heK; exact (mem_filter.mp heK).2
      have : y'' = y := by
        by_contra hne
        exact ZoneFamily.inZ_disj (S.toCut.Ys_sub_E _ hy'') hyE hne heZ'' heZ
      rw [this, KZ_def] at heK
      exact hpath e hxe hed hex (mem_Pset.mp (mem_filter.mp heK).1).2
  · rintro ⟨hdn, hxd, hdx, hcond⟩
    have hdZ : inZ (S.toCut.E (L + 1)) x d :=
      ⟨hxd, hdx, fun e he h1 h2 h3 => hcond e (mem_union.mpr (Or.inl he)) h1 h2 h3⟩
    refine ⟨⟨hdn, inZ_trans subset_rfl hxZ hdZ⟩, hxd, hdx, ?_⟩
    intro w hxw hwd hwx hwp
    have hwl : w.length < S.hgt := lt_of_le_of_lt hwd.length_le hdn
    have hwZ : inZ (S.toCut.E (L + 1)) y w := by
      refine ⟨hxZ.1.trans hxw, fun h => ?_, ?_⟩
      · have := inZ_lt hxZ
        have := hxw.length_le
        rw [h] at this; omega
      · intro e' he' hye' he'w hey'
        exact (inZ_trans subset_rfl hxZ hdZ).2.2 e' he' hye' (he'w.trans hwd) hey'
    exact hcond w (mem_union.mpr (Or.inr (hK w hwl hwZ hwp))) hxw hwd hwx

/-! ### 予算 -/

theorem budget (hV : Valid S.hgt cap S.T S.ms) (hc0T : S.c0 ≤ S.T)
    (hroot : ∀ t, S.c0 ≤ t → t ≤ S.T → st S.ms t [] = .pebble) (hh : 1 ≤ S.hgt) :
    ∀ L, ∀ y ∈ S.toCut.Ys (L + 1), (S.toCut.KZ (L + 1) y).card + 1 ≤ cap := by
  classical
  intro L y hy
  have hLt := S.toCut.Ys_pos hy
  have hf := S.fT_range hc0T hLt hy
  have hcap := hV.cap_le (S.fT (L + 1) y) hf.2
  unfold pcount at hcap
  have hroot_f := hroot _ hf.1 hf.2
  have hrootK : [] ∉ S.toCut.KZ (L + 1) y := by
    intro h
    rw [KZ_def] at h
    have := inZ_lt (mem_filter.mp h).2
    simp at this
  have hsub : insert [] (S.toCut.KZ (L + 1) y) ⊆
      (nodes S.hgt).filter (fun l => st S.ms (S.fT (L + 1) y) l = .pebble) := by
    intro x hx
    rw [mem_insert] at hx
    rw [mem_filter, mem_nodes]
    rcases hx with hx | hx
    · rw [hx]; exact ⟨by simp; omega, hroot_f⟩
    · rw [KZ_def] at hx
      exact mem_Pset.mp (mem_filter.mp hx).1
  have := card_le_card hsub
  rw [card_insert_of_notMem hrootK] at this
  exact this.trans hcap

theorem toCut_ok (hV : Valid S.hgt cap S.T S.ms) (hc0T : S.c0 ≤ S.T)
    (hroot : ∀ t, S.c0 ≤ t → t ≤ S.T → st S.ms t [] = .pebble) (hh : 1 ≤ S.hgt)
    (hH : 1 ≤ S.H) (h1 : 1 ≤ S.γ) (h2 : S.γ ≤ 2) (hQ : S.Q = cap - 1)
    (hγ : (S.Q : ℝ) ≤ S.γ * 2 ^ S.H) : S.toCut.Ok where
  hH := hH
  h1 := h1
  h2 := h2
  hQ := by
    show (S.Q : ℝ) ≤ S.γ * ((2 ^ S.H : ℕ) : ℝ)
    push_cast; exact hγ
  hbud := by
    intro L y hy
    show (S.toCut.KZ L y).card ≤ S.Q
    rw [hQ]
    cases L with
    | zero => show (∅ : Finset Node).card ≤ _; simp
    | succ L => have := S.budget hV hc0T hroot hh L y hy; omega
  hlen := by
    intro L y x hx
    exact (mem_Pset.mp hx).1

/-! ### 区域ごとの数え上げ -/

/-- 子の区域の数え済みの点の和: `|K_Z| + Σ_u |Z_u ∩ E_0| ≤ |Z ∩ E_0|`． -/
theorem cuts_le {L : ℕ} (hL : L < S.top) {y : Node} (hy : y ∈ S.toCut.Ys (L + 1)) :
    (S.toCut.KZ (L + 1) y).card + ∑ u ∈ S.toCut.KZ (L + 1) y,
      ((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0)).card ≤
      ((S.toCut.Zs (L + 1) y).filter (fun d => d ∈ S.toCut.E 0)).card := by
  classical
  have hE : S.toCut.E L = S.toCut.E (L + 1) ∪ S.toCut.Ys L := (S.toCut.Ys_succ hL).2
  have hKY : S.toCut.KZ (L + 1) y ⊆ S.toCut.Ys L := by
    intro u hu; rw [(S.toCut.Ys_succ hL).1]; exact mem_biUnion.mpr ⟨y, hy, hu⟩
  have hKE : ∀ u ∈ S.toCut.KZ (L + 1) y, u ∈ S.toCut.E L :=
    fun u hu => S.toCut.Ys_sub_E L (hKY hu)
  have hKZ : ∀ u ∈ S.toCut.KZ (L + 1) y, inZ (S.toCut.E (L + 1)) y u := by
    intro u hu; rw [KZ_def] at hu; exact (mem_filter.mp hu).2
  have hdisj : ∀ u ∈ S.toCut.KZ (L + 1) y, ∀ u' ∈ S.toCut.KZ (L + 1) y, u ≠ u' →
      Disjoint ((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0))
        ((S.toCut.Zs L u').filter (fun d => d ∈ S.toCut.E 0)) := by
    intro u hu u' hu' hne
    rw [disjoint_left]
    intro d h1 h2
    exact ZoneFamily.inZ_disj (hKE u hu) (hKE u' hu') hne
      (mem_filter.mp (mem_filter.mp h1).1).2 (mem_filter.mp (mem_filter.mp h2).1).2
  rw [sum_card_eq_card_biUnion hdisj]
  have hD : Disjoint (S.toCut.KZ (L + 1) y) ((S.toCut.KZ (L + 1) y).biUnion
      (fun u => (S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0))) := by
    rw [disjoint_left]
    intro k hk hk'
    obtain ⟨u, -, hku⟩ := mem_biUnion.mp hk'
    have hZ := (mem_filter.mp (mem_filter.mp hku).1).2
    exact hZ.2.2 k (hKE k hk) hZ.1 (List.prefix_refl _) hZ.2.1
  rw [← card_union_of_disjoint hD]
  refine card_le_card ?_
  intro d hd
  rcases mem_union.mp hd with hd | hd
  · have hdZ : d ∈ S.toCut.Zs (L + 1) y := by
      rw [← S.filter_peb] at hd; exact (mem_filter.mp hd).1
    exact mem_filter.mpr ⟨hdZ, S.E_sub_E0 L (hKE d hd)⟩
  · obtain ⟨u, hu, hdu⟩ := mem_biUnion.mp hd
    obtain ⟨hdZ, hdE⟩ := mem_filter.mp hdu
    obtain ⟨hdn, hdZ⟩ := mem_filter.mp hdZ
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hdn, ?_⟩, hdE⟩
    exact inZ_trans (S.E_anti L) (hKZ u hu) hdZ

variable {S}

/-- **区域ごとの数え上げ**（紙 R1 1.1 の `r(v) ≥ 1 + lev(v)` を段 `L` の区域で）:
`c` 以後の置く手 `≥ (L + 2)|Z| − (L + 1)|Z ∩ E_0| − Val_L`． -/
theorem zone_inv (hV : Valid S.hgt cap S.T S.ms) (hc0 : st S.ms S.c0 [] = .pebble)
    (hc0T : S.c0 ≤ S.T) (hroot : ∀ t, S.c0 ≤ t → t ≤ S.T → st S.ms t [] = .pebble)
    (hQ : cap - 2 ≤ S.Q) : ∀ L, L < S.top → ∀ y ∈ S.toCut.Ys L,
      ((L : ℝ) + 2) * (S.toCut.Zs L y).card -
        ((L : ℝ) + 1) * ((S.toCut.Zs L y).filter (fun d => d ∈ S.toCut.E 0)).card -
        S.toCut.Val L y ≤ (plAfter S.ms S.T (S.cT L y) (S.toCut.Zs L y)).card
  | 0, hL, y, hy => by
    have hr := S.cT_range' hc0T hL.le hy
    have hz := zone_bound hV hroot 2 (S.toCut.Zs 0 y) y (S.cT 0 y) hr.1 hr.2
      (S.ne_nil_of_Ys hL hy) (S.peb_cT' hc0 hL.le hy) (S.isZone hc0 hL hy)
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hz
    have g0 : Gw (cap - 2) 0 = 0 := rfl
    have g1 : Gw (cap - 2) 1 = 1 := by simp [Gw]
    rw [g0, g1, mul_zero, Nat.sub_zero, mul_one] at hz
    have hV0 : S.toCut.Val 0 y = min ((S.toCut.Zs 0 y).card : ℝ) S.Q := rfl
    rw [hV0]
    have hfnn : (0 : ℝ) ≤ ((S.toCut.Zs 0 y).filter (fun d => d ∈ S.toCut.E 0)).card :=
      Nat.cast_nonneg _
    push_cast
    rcases le_total (S.toCut.Zs 0 y).card (cap - 2) with hzq | hzq
    · have e : (S.toCut.Zs 0 y).card - (cap - 2) = 0 := by omega
      rw [e, add_zero] at hz
      have hm : min ((S.toCut.Zs 0 y).card : ℝ) S.Q = (S.toCut.Zs 0 y).card :=
        min_eq_left (by exact_mod_cast hzq.trans hQ)
      have hz' : ((S.toCut.Zs 0 y).card : ℝ) ≤ (plAfter S.ms S.T (S.cT 0 y) (S.toCut.Zs 0 y)).card := by
        exact_mod_cast hz
      rw [hm]; linarith
    · have hz' : (((S.toCut.Zs 0 y).card + ((S.toCut.Zs 0 y).card - (cap - 2)) : ℕ) : ℝ) ≤
          (plAfter S.ms S.T (S.cT 0 y) (S.toCut.Zs 0 y)).card := by exact_mod_cast hz
      rw [Nat.cast_add, Nat.cast_sub hzq] at hz'
      have hm : ((cap - 2 : ℕ) : ℝ) ≤ min ((S.toCut.Zs 0 y).card : ℝ) S.Q :=
        le_min (by exact_mod_cast hzq) (by exact_mod_cast hQ)
      linarith
  | L + 1, hL, y, hy => by
    classical
    have hr := S.cT_range' hc0T hL.le hy
    have hyp := S.peb_cT' hc0 hL.le hy
    have hKsubZ : S.toCut.KZ (L + 1) y ⊆ S.toCut.Zs (L + 1) y := by
      rw [← S.filter_peb]; exact filter_subset _ _
    rcases (S.toCut.Zs (L + 1) y).eq_empty_or_nonempty with hZe | ⟨d0, hd0⟩
    · have hK0 : S.toCut.KZ (L + 1) y = ∅ := by
        rw [hZe] at hKsubZ; exact subset_empty.mp hKsubZ
      have hV0 : S.toCut.Val (L + 1) y = 0 := by
        show ∑ x ∈ S.toCut.KZ (L + 1) y, S.toCut.Val L x = 0
        rw [hK0, sum_empty]
      rw [hV0, hZe]
      simp
    have hZz := S.isZone hc0 hL hy
    have hint : y.length + 1 < S.hgt := by
      obtain ⟨hl, hp, hne, -⟩ := hZz.1 d0 hd0
      have := prefix_ne_length_lt hp hne
      omega
    obtain ⟨f', h1, h2, h3, h4, h5⟩ := unpebble_time hV (S.ne_nil_of_Ys hL hy) hint hr.2 hyp
    have hf : UnpebAt S.ms S.T (S.cT (L + 1) y) (S.fT (L + 1) y) y := by
      rw [S.fT_mid hL y]
      exact ftime_spec ⟨f', h1, h2, h3, fun b => by cases b <;> assumption⟩
    obtain ⟨hA, hB⟩ := zone_split hV hZz hf
    rw [S.filter_peb] at hA hB
    have hcz : ∀ u ∈ S.toCut.KZ (L + 1) y,
        childZone S.ms (S.toCut.Zs (L + 1) y) (S.fT (L + 1) y) u = S.toCut.Zs L u :=
      fun u hu => S.childZone_eq (by omega) hy hu
    rw [sum_congr rfl fun u hu => by rw [hcz u hu]] at hA hB
    have hIH : ∀ u ∈ S.toCut.KZ (L + 1) y,
        ((L : ℝ) + 2) * (S.toCut.Zs L u).card -
          ((L : ℝ) + 1) * ((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0)).card -
          S.toCut.Val L u ≤ (plAfter S.ms S.T (S.fT (L + 1) y) (S.toCut.Zs L u)).card := by
      intro u hu
      have huY : u ∈ S.toCut.Ys L := by
        rw [(S.toCut.Ys_succ (L := L) (by show L < S.top; omega)).1]
        exact mem_biUnion.mpr ⟨y, hy, hu⟩
      have := zone_inv hV hc0 hc0T hroot hQ L (by omega) u huY
      rwa [S.child_time (by omega) hy hu] at this
    have hsum := sum_le_sum hIH
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
    have hC := S.cuts_le (L := L) (by omega) hy
    have hValy : S.toCut.Val (L + 1) y = ∑ u ∈ S.toCut.KZ (L + 1) y, S.toCut.Val L u := rfl
    rw [hValy]
    -- 実数に
    have hA' : ((S.toCut.Zs (L + 1) y).card : ℝ) + ∑ u ∈ S.toCut.KZ (L + 1) y,
        ((plAfter S.ms S.T (S.fT (L + 1) y) (S.toCut.Zs L u)).card : ℝ) ≤
        (plAfter S.ms S.T (S.cT (L + 1) y) (S.toCut.Zs (L + 1) y)).card := by exact_mod_cast hA
    have hB' : ((S.toCut.Zs (L + 1) y).card : ℝ) ≤ ((S.toCut.KZ (L + 1) y).card : ℝ) +
        ∑ u ∈ S.toCut.KZ (L + 1) y, ((S.toCut.Zs L u).card : ℝ) := by exact_mod_cast hB
    have hC' : ((S.toCut.KZ (L + 1) y).card : ℝ) + ∑ u ∈ S.toCut.KZ (L + 1) y,
        (((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ) ≤
        (((S.toCut.Zs (L + 1) y).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ) := by
      exact_mod_cast hC
    have hCnn : (0 : ℝ) ≤ ∑ u ∈ S.toCut.KZ (L + 1) y,
        (((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ) :=
      sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    set a : ℝ := ((S.toCut.Zs (L + 1) y).card : ℝ)
    set k : ℝ := ((S.toCut.KZ (L + 1) y).card : ℝ)
    set B : ℝ := ∑ u ∈ S.toCut.KZ (L + 1) y, ((S.toCut.Zs L u).card : ℝ)
    set C : ℝ := ∑ u ∈ S.toCut.KZ (L + 1) y,
        (((S.toCut.Zs L u).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ)
    set ey : ℝ := (((S.toCut.Zs (L + 1) y).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ)
    have e1 : ((L : ℝ) + 2) * (a - k) ≤ ((L : ℝ) + 2) * B :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : ((L : ℝ) + 2) * (k + C) ≤ ((L : ℝ) + 2) * ey :=
      mul_le_mul_of_nonneg_left hC' (by linarith)
    have e3 : ((L : ℝ) + 1) * C ≤ ((L : ℝ) + 2) * C := by nlinarith
    push_cast
    nlinarith

/-! ### 全体 -/

/-- **定理 genr の数え上げの段**（紙 R1 1.1．`top = k + 1 = m − 1`）:
`2((k+3)(2^h − 1) − (k+2)p − (k+1)|E_0| − Val_top([])) ≤ T + 1`． -/
theorem genr_lower_val (hV : Valid S.hgt cap S.T S.ms) {k : ℕ} (htop : S.top = k + 1)
    (hH : 1 ≤ S.H) (hQ : cap - 2 ≤ S.Q) {r0 : ℕ} (hc0 : S.c0 = r0 + 1) (hr0T : r0 < S.T)
    (hr0 : st S.ms r0 [] ≠ .pebble)
    (hroot : ∀ t, S.c0 ≤ t → t ≤ S.T → st S.ms t [] = .pebble) :
    2 * (((k : ℝ) + 3) * (2 ^ S.hgt - 1) - ((k : ℝ) + 2) * cap -
      ((k : ℝ) + 1) * (S.toCut.E 0).card - S.toCut.Val (k + 1) []) ≤ (S.T : ℝ) + 1 := by
  classical
  have hh : 2 ≤ S.hgt := by
    unfold hgt; rw [htop]
    have : 2 * 1 ≤ (k + 1 + 1) * S.H := Nat.mul_le_mul (by omega) hH
    omega
  have hc0T : S.c0 ≤ S.T := by omega
  have hpeb : st S.ms S.c0 [] = .pebble := hroot S.c0 le_rfl hc0T
  have hpeb' : st S.ms (r0 + 1) [] = .pebble := hc0 ▸ hpeb
  obtain ⟨hmv, hplace⟩ := place_of_change hr0 hpeb'
  have hkid0 : ∀ b : Bool, st S.ms S.c0 ([] ++ [b]) = .pebble := by
    intro b
    have hready := ready_of_place hV hr0T hplace
    rw [hmv] at hready
    rw [hc0]
    rcases hready with hleaf | ⟨h0, h1⟩
    · simp at hleaf; omega
    · rw [st_succ_ne (t := r0) (v := [] ++ [b]) (by rw [hmv]; simp)]
      cases b <;> assumption
  -- 段 0: 全頂点が c₀ より前に置かれる
  obtain ⟨E1, hE1def⟩ : ∃ E1 : Finset ℕ,
      E1 = (Finset.range S.T).filter (fun i => i < S.c0 ∧ IsPlace (S.ms i)) := ⟨_, rfl⟩
  have hroot_len : ([] : Node).length < S.hgt := by simp; omega
  have hfree0 : ∀ z ∈ subtree S.hgt [], st S.ms 0 z ≠ .pebble := by intro z _; simp [st]
  have hE1 : 2 ^ S.hgt - 1 ≤ E1.card := by
    have hsub : nodes S.hgt ⊆ E1.image (fun i => (S.ms i).v) := by
      intro z hz
      obtain ⟨i, -, hi2, hi3, hi4⟩ :=
        lemmaR hV _ [] rfl hroot_len 0 S.c0 (Nat.zero_le _) hc0T hfree0 hpeb z
          (by rw [subtree_nil]; exact hz)
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      rw [hE1def, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi2, hi4⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := E1) (f := fun i => (S.ms i).v)
    rw [card_nodes] at h1
    omega
  -- 最上段の区域と数え済み
  have hy0 : ([] : Node) ∈ S.toCut.Ys (k + 1) := by
    rw [← htop, S.Ys_top']; exact mem_singleton_self _
  set K := S.toCut.KZ (k + 1) [] with hKdef
  have hkL : k < S.top := by omega
  have hKY : ∀ u ∈ K, u ∈ S.toCut.Ys k := by
    intro u hu; rw [(S.toCut.Ys_succ hkL).1]; exact mem_biUnion.mpr ⟨[], hy0, hu⟩
  have hct : ∀ u ∈ K, S.cT k u = S.c0 := by
    intro u hu
    rw [S.child_time hkL hy0 hu, ← htop, fT_top, cT_top]
  have hfT0 : S.fT (k + 1) [] = S.c0 := by rw [← htop, fT_top, cT_top]
  -- 各区域の数え上げ
  have hinv : ∀ u ∈ K, ((k : ℝ) + 2) * (S.toCut.Zs k u).card -
      ((k : ℝ) + 1) * ((S.toCut.Zs k u).filter (fun d => d ∈ S.toCut.E 0)).card -
      S.toCut.Val k u ≤ (plAfter S.ms S.T S.c0 (S.toCut.Zs k u)).card := by
    intro u hu
    have := zone_inv hV hpeb hc0T hroot hQ k hkL u (hKY u hu)
    rwa [hct u hu] at this
  -- 置く手は互いに素
  have hle : E1.card + ∑ u ∈ K, (plAfter S.ms S.T S.c0 (S.toCut.Zs k u)).card ≤ nPlace S.ms S.T := by
    have hKE : ∀ u ∈ K, u ∈ S.toCut.E k := fun u hu => S.toCut.Ys_sub_E k (hKY u hu)
    have hdisjB : ∀ u ∈ K, ∀ u' ∈ K, u ≠ u' → Disjoint (plAfter S.ms S.T S.c0 (S.toCut.Zs k u))
        (plAfter S.ms S.T S.c0 (S.toCut.Zs k u')) := by
      intro u hu u' hu' hne
      rw [Finset.disjoint_left]
      intro i hi hi'
      exact ZoneFamily.inZ_disj (hKE u hu) (hKE u' hu') hne
        (mem_filter.mp (mem_plAfter.mp hi).2.2.2).2 (mem_filter.mp (mem_plAfter.mp hi').2.2.2).2
    have hdisjAB : Disjoint E1 (K.biUnion (fun u => plAfter S.ms S.T S.c0 (S.toCut.Zs k u))) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hE1def, Finset.mem_filter] at hiA
      obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hiB
      have := (mem_plAfter.mp hiu).2.1
      have := hiA.2.1
      omega
    have hsub : E1 ∪ K.biUnion (fun u => plAfter S.ms S.T S.c0 (S.toCut.Zs k u))
        ⊆ (Finset.range S.T).filter (fun i => IsPlace (S.ms i)) := by
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
    rw [Finset.card_union_of_disjoint hdisjAB, ← sum_card_eq_card_biUnion hdisjB] at this
    exact this
  -- 最上段の区域 = 根以外の全頂点
  have hEtop : S.toCut.E (k + 1) = {[]} := by rw [← htop, S.E_top']
  have hZtop : ∀ d, d ∈ S.toCut.Zs (k + 1) [] ↔ d.length < S.hgt ∧ d ≠ [] := by
    intro d
    unfold CutData.Zs
    rw [mem_filter, mem_nodes, hEtop]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2.1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, List.nil_prefix, h2, fun e he _ _ hne => hne (mem_singleton.mp he)⟩
  have hZcard : (S.toCut.Zs (k + 1) []).card = 2 ^ S.hgt - 2 := by
    have : S.toCut.Zs (k + 1) [] = (nodes S.hgt).erase [] := by
      ext d; rw [hZtop, mem_erase, mem_nodes]; tauto
    rw [this, card_erase_of_mem (mem_nodes.mpr hroot_len), card_nodes]
    omega
  -- 被覆
  have hcov : (S.toCut.Zs (k + 1) []).card ≤ K.card + ∑ u ∈ K, (S.toCut.Zs k u).card := by
    have hsub : S.toCut.Zs (k + 1) [] \ K ⊆ K.biUnion (fun u => S.toCut.Zs k u) := by
      intro d hd
      obtain ⟨hdZ, hdK⟩ := mem_sdiff.mp hd
      have hdf : st S.ms S.c0 d ≠ .pebble := by
        intro hp
        apply hdK
        rw [hKdef, ← S.filter_peb, hfT0]
        exact mem_filter.mpr ⟨hdZ, hp⟩
      obtain ⟨u, huZ, hu0, hup, hdu⟩ := cover_zone (Z := S.toCut.Zs (k + 1) []) hpeb
        (fun b _ => hkid0 b) List.nil_prefix hdZ hdf
        (fun w _ hw2 hw3 => (hZtop w).mpr ⟨lt_of_le_of_lt hw2.length_le ((hZtop d).mp hdZ).1, hw3⟩)
      have huK : u ∈ K := by
        rw [hKdef, ← S.filter_peb, hfT0]; exact mem_filter.mpr ⟨huZ, hup⟩
      refine mem_biUnion.mpr ⟨u, huK, ?_⟩
      rw [← S.childZone_eq hkL hy0 huK, hfT0]
      exact hdu
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 := card_le_card_sdiff_add_card (s := S.toCut.Zs (k + 1) []) (t := K)
    omega
  have hbud := S.budget hV hc0T hroot (by omega) k [] hy0
  -- 数え済みの点の和
  have hcuts : ∑ u ∈ K, ((S.toCut.Zs k u).filter (fun d => d ∈ S.toCut.E 0)).card ≤
      (S.toCut.E 0).card := by
    have hKE : ∀ u ∈ K, u ∈ S.toCut.E k := fun u hu => S.toCut.Ys_sub_E k (hKY u hu)
    rw [sum_card_eq_card_biUnion (fun u hu u' hu' hne => by
      rw [disjoint_left]
      intro d h1 h2
      exact ZoneFamily.inZ_disj (hKE u hu) (hKE u' hu') hne
        (mem_filter.mp (mem_filter.mp h1).1).2 (mem_filter.mp (mem_filter.mp h2).1).2)]
    refine card_le_card ?_
    intro d hd
    obtain ⟨u, -, hdu⟩ := mem_biUnion.mp hd
    exact (mem_filter.mp hdu).2
  have hValtop : S.toCut.Val (k + 1) [] = ∑ u ∈ K, S.toCut.Val k u := rfl
  have hmoves := moves_eq hV (by omega)
  -- 実数で
  have hsum := sum_le_sum hinv
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  rw [hValtop]
  have hE1' : (2 : ℝ) ^ S.hgt - 1 ≤ E1.card := by
    have : ((2 ^ S.hgt - 1 : ℕ) : ℝ) ≤ E1.card := by exact_mod_cast hE1
    rw [Nat.cast_sub Nat.one_le_two_pow] at this
    push_cast at this; exact this
  have hle' : (E1.card : ℝ) + ∑ u ∈ K, ((plAfter S.ms S.T S.c0 (S.toCut.Zs k u)).card : ℝ) ≤
      nPlace S.ms S.T := by exact_mod_cast hle
  have h4 : 4 ≤ 2 ^ S.hgt := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ S.hgt := Nat.pow_le_pow_right (by norm_num) hh
  have hZc : ((S.toCut.Zs (k + 1) []).card : ℝ) = (2 : ℝ) ^ S.hgt - 2 := by
    rw [hZcard, Nat.cast_sub (by omega)]; push_cast; ring
  have hcov' : ((S.toCut.Zs (k + 1) []).card : ℝ) ≤ (K.card : ℝ) +
      ∑ u ∈ K, ((S.toCut.Zs k u).card : ℝ) := by exact_mod_cast hcov
  have hbud' : (K.card : ℝ) + 1 ≤ cap := by exact_mod_cast hbud
  have hcuts' : ∑ u ∈ K, (((S.toCut.Zs k u).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ) ≤
      (S.toCut.E 0).card := by exact_mod_cast hcuts
  have hmoves' : (S.T : ℝ) + 1 = 2 * (nPlace S.ms S.T : ℝ) := by exact_mod_cast hmoves
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  set B : ℝ := ∑ u ∈ K, ((S.toCut.Zs k u).card : ℝ)
  set C : ℝ := ∑ u ∈ K, (((S.toCut.Zs k u).filter (fun d => d ∈ S.toCut.E 0)).card : ℝ)
  have e1 : ((k : ℝ) + 2) * ((2 : ℝ) ^ S.hgt - 1 - cap) ≤ ((k : ℝ) + 2) * B :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e2 : ((k : ℝ) + 1) * C ≤ ((k : ℝ) + 1) * (S.toCut.E 0).card :=
    mul_le_mul_of_nonneg_left hcuts' (by linarith)
  nlinarith

end SData

/-- **定理 genr の有限の形**（紙 2.8 の総和の段落と R1 1.1．`m = k + 2 ≥ 2`，`h = mH + r`，`X = 2^H`，
`Q = p − 1 ≤ γX`，`1 ≤ γ ≤ 2`）: 高さ `h` の完全二分木，ペブル `p` の妥当な手順の手数 `T` について
`T + 1 ≥ 2((m+1)(2^h − 1) − mp − (m−1)Σ_{j≤m−1} Q^j − Bnd)`，
`Bnd = 2^{h−H} + X Σ_{j≤m−2} Q^j + Σ_{L=2}^{m−1} (1 + 3C_L) X^L Σ_{j≤m−1−L} Q^j + 2^h σ_{m,r}(γ)`
（`X^m 2^r = 2^h`）．主項は `2^h(2(m+1) − 2σ_{m,r}(γ))`，残りは `O(X^{m−1})`（`Q ≤ 2X`）． -/
theorem genr_lower {h p T k H r : ℕ} {ms : ℕ → Move} (hV : Valid h p T ms)
    (hh : h = (k + 1 + 1) * H + r) (hH : 1 ≤ H) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2)
    (hγ : ((p - 1 : ℕ) : ℝ) ≤ γ * 2 ^ H) :
    2 * (((k : ℝ) + 3) * (2 ^ h - 1) - ((k : ℝ) + 2) * p -
      ((k : ℝ) + 1) * ∑ j ∈ range (k + 2), ((p - 1 : ℕ) : ℝ) ^ j -
      ((2 : ℝ) ^ ((k + 1) * H + r) + (2 : ℝ) ^ H * ∑ j ∈ range (k + 1), ((p - 1 : ℕ) : ℝ) ^ j +
        ∑ L ∈ Icc 2 (k + 1), ((2 : ℝ) ^ H) ^ L * ∑ j ∈ range (k + 1 - L + 1), ((p - 1 : ℕ) : ℝ) ^ j +
        ∑ L ∈ Icc 2 (k + 1), 3 * CL r L * ((2 : ℝ) ^ H) ^ L *
          ∑ j ∈ range (k + 1 - L + 1), ((p - 1 : ℕ) : ℝ) ^ j +
        ((2 : ℝ) ^ H) ^ (k + 2) * (2 ^ r * genrSigma (k + 2) r γ))) ≤ (T : ℝ) + 1 := by
  subst hh
  have hroot0 : ¬ (st ms 0 [] = .pebble) := by simp [st]
  obtain ⟨r0, hr0T, hr0, hr1⟩ := last_cross (P := fun t => st ms t [] = .pebble) T hroot0 hV.root
  let S : SData := ⟨ms, T, r0 + 1, H, r, k + 1, γ, p - 1⟩
  have hV' : Valid S.hgt p S.T S.ms := hV
  have hroot : ∀ t, S.c0 ≤ t → t ≤ S.T → st S.ms t [] = .pebble := by
    intro t ht1 ht2
    exact hr1 t (by change r0 + 1 ≤ t at ht1; omega) ht2
  have hc0T : S.c0 ≤ S.T := by change r0 + 1 ≤ T; omega
  have hh1 : 1 ≤ S.hgt := by
    change 1 ≤ (k + 1 + 1) * H + r
    have : 1 ≤ (k + 1 + 1) * H := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hVal : 2 * (((k : ℝ) + 3) * (2 ^ ((k + 1 + 1) * H + r) - 1) - ((k : ℝ) + 2) * p -
      ((k : ℝ) + 1) * ((S.toCut.E 0).card : ℝ) - S.toCut.Val (k + 1) []) ≤ (T : ℝ) + 1 :=
    SData.genr_lower_val (S := S) hV' rfl hH (by change p - 2 ≤ p - 1; omega) rfl hr0T hr0 hroot
  have hOk : S.toCut.Ok := S.toCut_ok hV' hc0T hroot hh1 hH h1 h2 rfl hγ
  have hTop := CutData.val_top_le hOk (T := k) rfl
  have hX : ((S.toCut.X : ℕ) : ℝ) = 2 ^ H := by
    change ((2 ^ H : ℕ) : ℝ) = _; push_cast; rfl
  have hβ1 : S.toCut.β 1 = (k + 1) * H + r := by
    change (k + 1 + 1) * H + r - 1 * H = _
    rw [Nat.succ_mul (k + 1), one_mul]; omega
  have hr' : S.toCut.r = r := rfl
  have hγ' : S.toCut.γ = γ := rfl
  rw [hX, hβ1, hr', hγ'] at hTop
  -- |E_L| の上界
  have hEb : ∀ L, L ≤ k + 1 → ((S.toCut.E L).card : ℝ) ≤
      ∑ j ∈ range (k + 1 - L + 1), ((p - 1 : ℕ) : ℝ) ^ j := by
    intro L hL
    have h' : (S.toCut.E L).card ≤ ∑ j ∈ range (k + 1 - L + 1), (p - 1) ^ j :=
      CutData.card_E_le hOk hL
    exact_mod_cast h'
  have hE0 := hEb 0 (Nat.zero_le _)
  have hE1 := hEb 1 (by omega)
  rw [show k + 1 - 0 + 1 = k + 2 by omega] at hE0
  rw [show k + 1 - 1 + 1 = k + 1 by omega] at hE1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ 2 ^ H := by positivity
  have s1 : ∑ L ∈ Icc 2 (k + 1), ((2 : ℝ) ^ H) ^ L * ((S.toCut.E L).card : ℝ) ≤
      ∑ L ∈ Icc 2 (k + 1), ((2 : ℝ) ^ H) ^ L *
        ∑ j ∈ range (k + 1 - L + 1), ((p - 1 : ℕ) : ℝ) ^ j :=
    sum_le_sum fun L hL => mul_le_mul_of_nonneg_left (hEb L (mem_Icc.mp hL).2) (by positivity)
  have s2 : ∑ L ∈ Icc 2 (k + 1), 3 * CL r L * ((2 : ℝ) ^ H) ^ L * ((S.toCut.E L).card : ℝ) ≤
      ∑ L ∈ Icc 2 (k + 1), 3 * CL r L * ((2 : ℝ) ^ H) ^ L *
        ∑ j ∈ range (k + 1 - L + 1), ((p - 1 : ℕ) : ℝ) ^ j :=
    sum_le_sum fun L hL => mul_le_mul_of_nonneg_left (hEb L (mem_Icc.mp hL).2)
      (by have := CL_nonneg r L; positivity)
  have s3 : ((k : ℝ) + 1) * ((S.toCut.E 0).card : ℝ) ≤
      ((k : ℝ) + 1) * ∑ j ∈ range (k + 2), ((p - 1 : ℕ) : ℝ) ^ j :=
    mul_le_mul_of_nonneg_left hE0 (by linarith)
  have s4 : (2 : ℝ) ^ H * ((S.toCut.E 1).card : ℝ) ≤
      (2 : ℝ) ^ H * ∑ j ∈ range (k + 1), ((p - 1 : ℕ) : ℝ) ^ j :=
    mul_le_mul_of_nonneg_left hE1 hX0
  linarith

end GenRZones
end SpookyTree
