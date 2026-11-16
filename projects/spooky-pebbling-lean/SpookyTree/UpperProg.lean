/-
# 上界の部品: 前線への写し・内部を置く・内部を外す・部分木の計算

ブロック根 `y`（高さ `j + L`）について、`y` から `L` 段下の頂点を「前線」、それより上を「内部」と呼ぶ。

* `onFront f L y`: 前線の各頂点 `a` に、左から順に `f a` を打つ。
* `placeInt pl L y`: 内部を下から（後順で）全部置く。
* `removeInt L y`: 内部を上から（前順で）全部 unpebble する。
* `compute pl k y`: 高さ `k` の部分木を黒ペブリングの要領で計算し、`y` だけペブル・他は全部ゴーストにする
  （KSS の `fast_pebble`。外す手はすべて `ghost` にする。Lean のモデルでは `ghost` は無条件に打てる）。

それぞれについて「合法・`T(y)` の中・ペブル数の上限・打った後の配置」を示す。
-/
import SpookyTree.UpperCore

namespace SpookyTree

/-! ## 1 手の合法性 -/

/-- 置く手 `pl` が状態 `X` の頂点に打てる組み合わせ（空には pebble、ゴーストには unghost）。 -/
def PlOk (pl : Op) (X : Cell) : Prop :=
  (pl = .pebble ∧ X = .empty) ∨ (pl = .unghost ∧ X = .ghost)

theorem PlOk.ne_pebble {pl : Op} {X : Cell} (hpl : PlOk pl X) : X ≠ .pebble := by
  rcases hpl with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

theorem PlOk.result {pl : Op} {X : Cell} (hpl : PlOk pl X) : result pl = .pebble := by
  rcases hpl with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

theorem legal_place {h : ℕ} {pl : Op} {X : Cell} (hpl : PlOk pl X) {c : Config} {y : Node}
    (hy : y.length < h) (hc : c y = X) (hr : Ready h c y) : Legal h c ⟨pl, y⟩ := by
  rcases hpl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact And.intro hy (And.intro hc hr)
  · exact And.intro hy (And.intro hc hr)

theorem legal_unpebble {h : ℕ} {c : Config} {y : Node}
    (hy : y.length < h) (hc : c y = .pebble) (hr : Ready h c y) : Legal h c ⟨.unpebble, y⟩ :=
  And.intro hy (And.intro hc hr)

theorem legal_ghost {h : ℕ} {c : Config} {y : Node}
    (hy : y.length < h) (hc : c y = .pebble) : Legal h c ⟨.ghost, y⟩ :=
  And.intro hy hc

/-- 高さ `n + 1` の頂点 `y`（`|y| + (n + 1) = h`）が揃っていること: 葉（`n = 0`）か、両方の子がペブル。 -/
theorem ready_of {h n : ℕ} {y : Node} {c : Config} (hy : y.length + (n + 1) = h)
    (hk : 0 < n → c (y ++ [false]) = .pebble ∧ c (y ++ [true]) = .pebble) : Ready h c y := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact Or.inl (by omega)
  · exact Or.inr (hk hpos)

/-! ## 前線への写し -/

/-- 前線（`y` から `L` 段下）の各頂点 `a` に、左から順に `f a` を打つ。 -/
def onFront (f : Node → List Move) : ℕ → Node → List Move
  | 0, y => f y
  | L + 1, y => onFront f L (y ++ [false]) ++ onFront f L (y ++ [true])

/-- **前線への写しの仕様.** 前線の各頂点 `a`（高さ `j`）で `f a` が配置 `g0` を `g1` に変え、
`T(a)` 内のペブル数が `p` 以下なら、内部が `ci` のまま前線が全部 `g0` から `g1` に変わり、
`T(y)` 内のペブル数は `p + (2^L − 1)(w + e)` 以下。`w` は前線 1 個あたりの `g0`・`g1` のペブル数の上界、
`e` は内部がペブルなら 1。 -/
theorem onFront_spec {h j p w e : ℕ} {ci : Cell} {g0 g1 : ℕ → Cell} {f : Node → List Move}
    (hf : ∀ (a : Node) (c : Config), a.length + j = h → Pat g0 j a c →
      Runs h j a p c (f a) ∧ Pat g1 j a (run c (f a)))
    (hw0 : pcPat g0 j ≤ w) (hw1 : pcPat g1 j ≤ w) (he : (if ci = .pebble then 1 else 0) ≤ e) :
    ∀ (L : ℕ) (y : Node) (c : Config), y.length + (j + L) = h → Pat (glue ci L g0) (j + L) y c →
      Runs h (j + L) y (p + (2 ^ L - 1) * (w + e)) c (onFront f L y) ∧
      Pat (glue ci L g1) (j + L) y (run c (onFront f L y)) := by
  intro L
  induction L with
  | zero =>
    intro y c hy hP
    rw [glue_zero] at hP ⊢
    obtain ⟨h1, h2⟩ := hf y c hy hP
    exact ⟨h1.mono (Nat.le_add_right _ _), h2⟩
  | succ L ih =>
    intro y c hy hP
    have hP' : Pat (glue ci (L + 1) g0) (j + L + 1) y c := hP
    obtain ⟨hcy, hP0, hP1⟩ := Pat_succ.mp hP'
    rw [glue_succ_zero] at hcy
    rw [glue_succ_shift] at hP0 hP1
    -- 左の子
    obtain ⟨hR0, hQ0⟩ := ih (y ++ [false]) c (by simp; omega) hP0
    have hU0 := hR0.under
    have hc1y : run c (onFront f L (y ++ [false])) y = ci := by
      rw [run_outside hU0 c (not_prefix_parent y false)]; exact hcy
    have hP1' : Pat (glue ci L g0) (j + L) (y ++ [true]) (run c (onFront f L (y ++ [false]))) :=
      (Pat_run_disj hU0 (disj01 y)).mpr hP1
    -- 右の子
    obtain ⟨hR1, hQ1⟩ := ih (y ++ [true]) _ (by simp; omega) hP1'
    have hU1 := hR1.under
    have hc2y : run (run c (onFront f L (y ++ [false]))) (onFront f L (y ++ [true])) y = ci := by
      rw [run_outside hU1 _ (not_prefix_parent y true)]; exact hc1y
    have hQ0' : Pat (glue ci L g1) (j + L) (y ++ [false])
        (run (run c (onFront f L (y ++ [false]))) (onFront f L (y ++ [true]))) :=
      (Pat_run_disj hU1 (disj10 y)).mpr hQ0
    -- ペブル数
    have hite : (if c y = .pebble then 1 else 0) ≤ e := by rw [hcy]; exact he
    have hite1 : (if run c (onFront f L (y ++ [false])) y = .pebble then 1 else 0) ≤ e := by
      rw [hc1y]; exact he
    have hb0 : pc (j + L) (y ++ [true]) c ≤ (2 ^ L - 1) * e + 2 ^ L * w := by
      rw [pc_of_Pat _ _ _ hP1]; exact pcPat_glue_bound hw0 he L
    have hb1 : pc (j + L) (y ++ [false]) (run c (onFront f L (y ++ [false])))
        ≤ (2 ^ L - 1) * e + 2 ^ L * w := by
      rw [pc_of_Pat _ _ _ hQ0]; exact pcPat_glue_bound hw1 he L
    have hL0 := hR0.lift0 (Nat.add_le_add hite hb0)
    have hL1 := hR1.lift1 (Nat.add_le_add hite1 hb1)
    have harith : p + (2 ^ L - 1) * (w + e) + (e + ((2 ^ L - 1) * e + 2 ^ L * w))
        ≤ p + (2 ^ (L + 1) - 1) * (w + e) := by
      obtain ⟨a, ha⟩ : ∃ a, 2 ^ L = a + 1 :=
        ⟨2 ^ L - 1, by have := Nat.one_le_two_pow (n := L); omega⟩
      rw [pow_succ, ha]
      have h1 : a + 1 - 1 = a := by omega
      have h2 : (a + 1) * 2 - 1 = 2 * a + 1 := by omega
      rw [h1, h2]
      nlinarith
    refine ⟨?_, ?_⟩
    · show Runs h (j + L + 1) y _ c (onFront f L (y ++ [false]) ++ onFront f L (y ++ [true]))
      exact Runs_append.mpr ⟨hL0.mono harith, hL1.mono harith⟩
    · show Pat (glue ci (L + 1) g1) (j + L + 1) y
        (run c (onFront f L (y ++ [false]) ++ onFront f L (y ++ [true])))
      rw [run_append]
      refine Pat_succ.mpr ⟨?_, ?_, ?_⟩
      · rw [glue_succ_zero]; exact hc2y
      · rw [glue_succ_shift]; exact hQ0'
      · rw [glue_succ_shift]; exact hQ1

/-! ## 内部を置く -/

/-- 内部（`y` から `L` 段未満下）を後順で全部置く。 -/
def placeInt (pl : Op) : ℕ → Node → List Move
  | 0, _ => []
  | L + 1, y => placeInt pl L (y ++ [false]) ++ placeInt pl L (y ++ [true]) ++ [⟨pl, y⟩]

/-- **内部を置く手順の仕様.** 内部が全部 `X`（`pl` が打てる状態）で、前線があれば（`1 ≤ j`）前線がペブルなら、
内部は全部ペブルになる。ペブル数は終わったときの値以下。 -/
theorem placeInt_spec {h j : ℕ} {pl : Op} {X : Cell} (hpl : PlOk pl X) {g : ℕ → Cell}
    (hg : 1 ≤ j → g 0 = .pebble) :
    ∀ (L : ℕ) (y : Node) (c : Config), y.length + (j + L) = h → Pat (glue X L g) (j + L) y c →
      Runs h (j + L) y (pcPat (glue .pebble L g) (j + L)) c (placeInt pl L y) ∧
      Pat (glue .pebble L g) (j + L) y (run c (placeInt pl L y)) := by
  intro L
  induction L with
  | zero =>
    intro y c _ hP
    simp only [glue_zero] at hP ⊢
    exact ⟨Runs_nil, hP⟩
  | succ L ih =>
    intro y c hy hP
    have hP' : Pat (glue X (L + 1) g) (j + L + 1) y c := hP
    obtain ⟨hcy, hP0, hP1⟩ := Pat_succ.mp hP'
    rw [glue_succ_zero] at hcy
    rw [glue_succ_shift] at hP0 hP1
    have hylt : y.length < h := by omega
    have hB : pcPat (glue .pebble (L + 1) g) (j + L + 1)
        = 1 + 2 * pcPat (glue .pebble L g) (j + L) := by
      rw [pcPat, glue_succ_zero, glue_succ_shift, if_pos rfl]
    -- 左の子
    obtain ⟨hR0, hQ0⟩ := ih (y ++ [false]) c (by simp; omega) hP0
    have hU0 := hR0.under
    have hc1y : run c (placeInt pl L (y ++ [false])) y = X := by
      rw [run_outside hU0 c (not_prefix_parent y false)]; exact hcy
    have hP1' : Pat (glue X L g) (j + L) (y ++ [true]) (run c (placeInt pl L (y ++ [false]))) :=
      (Pat_run_disj hU0 (disj01 y)).mpr hP1
    -- 右の子
    obtain ⟨hR1, hQ1⟩ := ih (y ++ [true]) _ (by simp; omega) hP1'
    have hU1 := hR1.under
    have hc2y : run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true])) y = X := by
      rw [run_outside hU1 _ (not_prefix_parent y true)]; exact hc1y
    have hQ0' : Pat (glue .pebble L g) (j + L) (y ++ [false])
        (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true]))) :=
      (Pat_run_disj hU1 (disj10 y)).mpr hQ0
    -- ペブル数
    have hXne : X ≠ .pebble := hpl.ne_pebble
    have hq0 : (if c y = .pebble then 1 else 0) + pc (j + L) (y ++ [true]) c
        ≤ pcPat (glue .pebble L g) (j + L) := by
      rw [hcy, if_neg hXne, pc_of_Pat _ _ _ hP1, Nat.zero_add]
      exact pcPat_glue_le X g _ L
    have hq1 : (if run c (placeInt pl L (y ++ [false])) y = .pebble then 1 else 0)
        + pc (j + L) (y ++ [false]) (run c (placeInt pl L (y ++ [false])))
        ≤ pcPat (glue .pebble L g) (j + L) := by
      rw [hc1y, if_neg hXne, pc_of_Pat _ _ _ hQ0, Nat.zero_add]
    have hL0 := hR0.lift0 hq0
    have hL1 := hR1.lift1 hq1
    -- 最後の 1 手: y を置く
    have hzero : 0 < j + L → glue Cell.pebble L g 0 = .pebble := fun hpos =>
      glue_peb_zero (fun hL0' => hg (by omega))
    have hready : Ready h
        (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true]))) y := by
      refine ready_of (n := j + L) hy (fun hpos => ⟨?_, ?_⟩)
      · have := hQ0' [] (by simpa using hpos)
        simpa [hzero hpos] using this
      · have := hQ1 [] (by simpa using hpos)
        simpa [hzero hpos] using this
    have hlegal := legal_place hpl hylt hc2y hready
    have hres : step (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true])))
        ⟨pl, y⟩ y = .pebble := by rw [step_self, hpl.result]
    have hF0 : Pat (glue .pebble L g) (j + L) (y ++ [false])
        (step (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true]))) ⟨pl, y⟩) :=
      (Pat_step_out (not_prefix_parent y false) pl).mpr hQ0'
    have hF1 : Pat (glue .pebble L g) (j + L) (y ++ [true])
        (step (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true]))) ⟨pl, y⟩) :=
      (Pat_step_out (not_prefix_parent y true) pl).mpr hQ1
    have hpcfin : pc (j + L + 1) y
        (step (run (run c (placeInt pl L (y ++ [false]))) (placeInt pl L (y ++ [true]))) ⟨pl, y⟩)
        = 1 + 2 * pcPat (glue .pebble L g) (j + L) := by
      rw [pc, hres, if_pos rfl, pc_of_Pat _ _ _ hF0, pc_of_Pat _ _ _ hF1]
      ring
    refine ⟨?_, ?_⟩
    · show Runs h (j + L + 1) y (pcPat (glue .pebble (L + 1) g) (j + L + 1)) c
        (placeInt pl L (y ++ [false]) ++ placeInt pl L (y ++ [true]) ++ [⟨pl, y⟩])
      rw [hB]
      refine Runs_append.mpr ⟨Runs_append.mpr ⟨hL0.mono (by omega), ?_⟩, ?_⟩
      · exact hL1.mono (by omega)
      · rw [run_append]
        exact Runs_cons.mpr ⟨hlegal, List.prefix_refl _, le_of_eq hpcfin, Runs_nil⟩
    · show Pat (glue .pebble (L + 1) g) (j + L + 1) y
        (run c (placeInt pl L (y ++ [false]) ++ placeInt pl L (y ++ [true]) ++ [⟨pl, y⟩]))
      rw [run_append, run_append]
      refine Pat_succ.mpr ⟨?_, ?_, ?_⟩
      · rw [glue_succ_zero]; exact hres
      · rw [glue_succ_shift]; exact hF0
      · rw [glue_succ_shift]; exact hF1

/-! ## 内部を外す -/

/-- 内部を前順で全部 unpebble する。 -/
def removeInt : ℕ → Node → List Move
  | 0, _ => []
  | L + 1, y => ⟨.unpebble, y⟩ :: (removeInt L (y ++ [false]) ++ removeInt L (y ++ [true]))

/-- **内部を外す手順の仕様.** 内部が全部ペブルで、前線があれば前線もペブルなら、内部は全部空になる（跡を残さない）。 -/
theorem removeInt_spec {h j : ℕ} {g : ℕ → Cell} (hg : 1 ≤ j → g 0 = .pebble) :
    ∀ (L : ℕ) (y : Node) (c : Config), y.length + (j + L) = h →
      Pat (glue .pebble L g) (j + L) y c →
      Runs h (j + L) y (pcPat (glue .pebble L g) (j + L)) c (removeInt L y) ∧
      Pat (glue .empty L g) (j + L) y (run c (removeInt L y)) := by
  intro L
  induction L with
  | zero =>
    intro y c _ hP
    simp only [glue_zero] at hP ⊢
    exact ⟨Runs_nil, hP⟩
  | succ L ih =>
    intro y c hy hP
    have hP' : Pat (glue .pebble (L + 1) g) (j + L + 1) y c := hP
    obtain ⟨hcy, hP0, hP1⟩ := Pat_succ.mp hP'
    rw [glue_succ_zero] at hcy
    rw [glue_succ_shift] at hP0 hP1
    have hylt : y.length < h := by omega
    have hB : pcPat (glue .pebble (L + 1) g) (j + L + 1)
        = 1 + 2 * pcPat (glue .pebble L g) (j + L) := by
      rw [pcPat, glue_succ_zero, glue_succ_shift, if_pos rfl]
    have hzero : 0 < j + L → glue Cell.pebble L g 0 = .pebble := fun hpos =>
      glue_peb_zero (fun hL0' => hg (by omega))
    -- 最初の 1 手: y を unpebble
    have hready : Ready h c y := by
      refine ready_of (n := j + L) hy (fun hpos => ⟨?_, ?_⟩)
      · have := hP0 [] (by simpa using hpos)
        simpa [hzero hpos] using this
      · have := hP1 [] (by simpa using hpos)
        simpa [hzero hpos] using this
    have hlegal := legal_unpebble hylt hcy hready
    have hres : step c ⟨.unpebble, y⟩ y = .empty := by rw [step_self]; rfl
    have hS0 : Pat (glue .pebble L g) (j + L) (y ++ [false]) (step c ⟨.unpebble, y⟩) :=
      (Pat_step_out (not_prefix_parent y false) .unpebble).mpr hP0
    have hS1 : Pat (glue .pebble L g) (j + L) (y ++ [true]) (step c ⟨.unpebble, y⟩) :=
      (Pat_step_out (not_prefix_parent y true) .unpebble).mpr hP1
    have hpc1 : pc (j + L + 1) y (step c ⟨.unpebble, y⟩)
        = 2 * pcPat (glue .pebble L g) (j + L) := by
      rw [pc, hres, if_neg (show Cell.empty ≠ Cell.pebble by decide), pc_of_Pat _ _ _ hS0,
        pc_of_Pat _ _ _ hS1]
      ring
    -- 左の子
    obtain ⟨hR0, hQ0⟩ := ih (y ++ [false]) _ (by simp; omega) hS0
    have hU0 := hR0.under
    have hc1y : run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false])) y = .empty := by
      rw [run_outside hU0 _ (not_prefix_parent y false)]; exact hres
    have hS1' : Pat (glue .pebble L g) (j + L) (y ++ [true])
        (run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false]))) :=
      (Pat_run_disj hU0 (disj01 y)).mpr hS1
    -- 右の子
    obtain ⟨hR1, hQ1⟩ := ih (y ++ [true]) _ (by simp; omega) hS1'
    have hU1 := hR1.under
    have hc2y : run (run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false])))
        (removeInt L (y ++ [true])) y = .empty := by
      rw [run_outside hU1 _ (not_prefix_parent y true)]; exact hc1y
    have hQ0' : Pat (glue .empty L g) (j + L) (y ++ [false])
        (run (run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false]))) (removeInt L (y ++ [true]))) :=
      (Pat_run_disj hU1 (disj10 y)).mpr hQ0
    have hq0 : (if step c ⟨.unpebble, y⟩ y = .pebble then 1 else 0)
        + pc (j + L) (y ++ [true]) (step c ⟨.unpebble, y⟩)
        ≤ pcPat (glue .pebble L g) (j + L) := by
      rw [hres, if_neg (show Cell.empty ≠ Cell.pebble by decide), pc_of_Pat _ _ _ hS1, Nat.zero_add]
    have hq1 : (if run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false])) y = .pebble then 1 else 0)
        + pc (j + L) (y ++ [false]) (run (step c ⟨.unpebble, y⟩) (removeInt L (y ++ [false])))
        ≤ pcPat (glue .pebble L g) (j + L) := by
      rw [hc1y, if_neg (show Cell.empty ≠ Cell.pebble by decide), pc_of_Pat _ _ _ hQ0, Nat.zero_add]
      exact pcPat_glue_le .empty g _ L
    have hL0 := hR0.lift0 hq0
    have hL1 := hR1.lift1 hq1
    refine ⟨?_, ?_⟩
    · show Runs h (j + L + 1) y (pcPat (glue .pebble (L + 1) g) (j + L + 1)) c
        (⟨.unpebble, y⟩ :: (removeInt L (y ++ [false]) ++ removeInt L (y ++ [true])))
      rw [hB]
      refine Runs_cons.mpr ⟨hlegal, List.prefix_refl _, by rw [hpc1]; omega, ?_⟩
      exact Runs_append.mpr ⟨hL0.mono (by omega), hL1.mono (by omega)⟩
    · show Pat (glue .empty (L + 1) g) (j + L + 1) y
        (run c (⟨.unpebble, y⟩ :: (removeInt L (y ++ [false]) ++ removeInt L (y ++ [true]))))
      rw [run_cons, run_append]
      refine Pat_succ.mpr ⟨?_, ?_, ?_⟩
      · rw [glue_succ_zero]; exact hc2y
      · rw [glue_succ_shift]; exact hQ0'
      · rw [glue_succ_shift]; exact hQ1

/-! ## 前線をゴーストにする -/

/-- 根だけペブルで下が全部ゴーストの部分木の根を ghost にすると、全部ゴーストになる。 -/
theorem ghostRoot_spec {h j : ℕ} (hj : 1 ≤ j) :
    ∀ (a : Node) (c : Config), a.length + j = h → Pat scp j a c →
      Runs h j a 0 c [⟨.ghost, a⟩] ∧ Pat (cst .ghost) j a (run c [⟨.ghost, a⟩]) := by
  intro a c ha hP
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hca, hP0, hP1⟩ := Pat_succ.mp hP
  rw [scp_zero] at hca
  rw [scp_shift] at hP0 hP1
  have hres : step c ⟨.ghost, a⟩ a = .ghost := by rw [step_self]; rfl
  have hS0 : Pat (cst .ghost) j' (a ++ [false]) (step c ⟨.ghost, a⟩) :=
    (Pat_step_out (not_prefix_parent a false) .ghost).mpr hP0
  have hS1 : Pat (cst .ghost) j' (a ++ [true]) (step c ⟨.ghost, a⟩) :=
    (Pat_step_out (not_prefix_parent a true) .ghost).mpr hP1
  have hPost : Pat (cst .ghost) (j' + 1) a (step c ⟨.ghost, a⟩) :=
    Pat_succ.mpr ⟨hres, hS0, hS1⟩
  refine ⟨Runs_cons.mpr ⟨legal_ghost (by omega) hca, List.prefix_refl _, ?_, Runs_nil⟩, hPost⟩
  rw [pc_of_Pat _ _ _ hPost, pcPat_cst (X := .ghost) (by decide)]

/-! ## 部分木の計算 -/

/-- 高さ `k` の部分木 `T(y)` を計算する: `y` だけペブルにし、他は全部ゴーストにする。 -/
def compute (pl : Op) : ℕ → Node → List Move
  | 0, _ => []
  | 1, y => placeInt pl 1 y
  | k + 2, y => onFront (compute pl (k + 1)) 1 y ++ placeInt pl 1 y ++
      onFront (fun a => [⟨.ghost, a⟩]) 1 y

/-- **計算の仕様.** `T(y)`（高さ `k ≥ 1`）が全部 `X` なら、`compute pl k y` は合法で、
`T(y)` 内のペブル数は `k + 1` 以下、終わると `y` だけペブルで他は全部ゴースト。 -/
theorem compute_spec {h : ℕ} {pl : Op} {X : Cell} (hpl : PlOk pl X) :
    ∀ (k : ℕ) (y : Node) (c : Config), 1 ≤ k → y.length + k = h → Pat (cst X) k y c →
      Runs h k y (k + 1) c (compute pl k y) ∧ Pat scp k y (run c (compute pl k y))
  | 0, _, _, hk, _, _ => absurd hk (by decide)
  | 1, y, c, _, hy, hP => by
    have hP' : Pat (glue X 1 (cst .ghost)) (0 + 1) y c :=
      (Pat_glue_short (cst .ghost) (le_refl 1)).mpr hP
    obtain ⟨hR, hQ⟩ := placeInt_spec (j := 0) hpl (g := cst .ghost) (fun h0 => absurd h0 (by decide))
      1 y c (by omega) hP'
    have hpk : pcPat (glue Cell.pebble 1 (cst Cell.ghost)) (0 + 1) ≤ 1 + 1 := by
      have := pcPat_glue_peb (cst .ghost) 0 1
      rw [pcPat_cst (X := .ghost) (by decide)] at this
      omega
    exact ⟨hR.mono hpk, hQ⟩
  | k + 2, y, c, _, hy, hP => by
    -- 1. 両方の子を計算する
    have hP' : Pat (glue X 1 (cst X)) (k + 1 + 1) y c := by rw [glue_cst]; exact hP
    obtain ⟨hR1, hQ1⟩ := onFront_spec (j := k + 1) (p := k + 2) (w := 1) (e := 0) (ci := X)
      (g0 := cst X) (g1 := scp) (f := compute pl (k + 1))
      (fun a c' ha hPa => compute_spec hpl (k + 1) a c' (by omega) ha hPa)
      (by rw [pcPat_cst hpl.ne_pebble]; omega) (le_of_eq (pcPat_scp k))
      (by simp [hpl.ne_pebble]) 1 y c (by omega) hP'
    -- 2. y を置く
    obtain ⟨hR2, hQ2⟩ := placeInt_spec (j := k + 1) hpl (g := scp) (fun _ => scp_zero)
      1 y _ (by omega) hQ1
    -- 3. 両方の子をゴーストにする
    obtain ⟨hR3, hQ3⟩ := onFront_spec (j := k + 1) (p := 0) (w := 1) (e := 1) (ci := .pebble)
      (g0 := scp) (g1 := cst .ghost) (f := fun a => [⟨.ghost, a⟩])
      (fun a c' ha hPa => ghostRoot_spec (by omega) a c' ha hPa)
      (le_of_eq (pcPat_scp k)) (by rw [pcPat_cst (X := .ghost) (by decide)]; omega)
      (by simp) 1 y _ (by omega) hQ2
    have hpk2 : pcPat (glue Cell.pebble 1 scp) (k + 1 + 1) ≤ k + 2 + 1 := by
      have := pcPat_glue_peb scp (k + 1) 1
      rw [pcPat_scp] at this
      omega
    refine ⟨?_, ?_⟩
    · show Runs h (k + 1 + 1) y (k + 2 + 1) c
        (onFront (compute pl (k + 1)) 1 y ++ placeInt pl 1 y ++ onFront (fun a => [⟨.ghost, a⟩]) 1 y)
      refine Runs_append.mpr ⟨Runs_append.mpr ⟨hR1.mono (by norm_num), hR2.mono hpk2⟩, ?_⟩
      rw [run_append]
      exact hR3.mono (by norm_num)
    · show Pat scp (k + 1 + 1) y
        (run c (onFront (compute pl (k + 1)) 1 y ++ placeInt pl 1 y ++
          onFront (fun a => [⟨.ghost, a⟩]) 1 y))
      rw [run_append, run_append]
      exact hQ3

end SpookyTree
