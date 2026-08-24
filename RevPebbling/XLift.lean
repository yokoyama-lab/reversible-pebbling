import RevPebbling.Subsolution
import RevPebbling.CompositionAnchor
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Set

/-!
# The integer lift: a general-purpose sound upper-bound DP

This module formalises the **integer lift** used by `m48_exact_replay.py`
(`scripts/probe_brw/m48_exact_replay.py:460-503`): a DP that, given a row `X`
of upper bounds at space level `s` over a finite grid `gv`, produces a row
`liftLevel gv X cap cand` of upper bounds at level `s + 1`, by combining a
"self" term `X i` with the best of finitely many candidate splits.

The point of this file is a **single soundness theorem**
(`liftAux_sound` / `liftLevel_sound` / `liftIter_sound`): the lift never
exceeds the true count function `C`, *for any choice of `cand` and `cap`
whatsoever*. Neither the candidate-selection heuristic (the "two-finger scan"
of the Python DP) nor the numeric cap affects correctness — they only affect
*sharpness* (how close the lift gets to `C`). See
`notes/xlift_lean_design.md` §3 in the companion manuscript repo for the
full discussion of what does and does not feed into the soundness proof.

Index convention: lists are indexed with `List.getD _ i 0`, i.e. out-of-range
reads are `0`. Since `0 ≤ C s v` always, this is a safe convention in every
direction the argument needs it.

Level convention: `rowIter s` here is the row of *Lean* space level `s + 2`
(see `RevPebbling/CountRecursion.lean`'s header comment). The `m48` "level
`s`, cap `2^{s-1} - 1`" bookkeeping is *not* reproduced here — the cap is a
free parameter with no bearing on soundness (see the table in the design
note), and levels are simply chained via `s ↦ s + 1`.
-/

namespace RevPebbling.XLift

open RevPebbling.CountRecursion

/-! ## Definitions -/

/-- `w` 以下の最大の格子点における行の値（無ければ `0`）。`gxs` は
`(格子点, 行の値)` の対の並び。左から走査して最後に条件を満たしたものを
返す＝ソート済みなら bisect と一致する。 -/
def floorVal (gxs : List (Nat × Nat)) (w : Nat) : Nat :=
  gxs.foldl (fun acc gx => if gx.1 ≤ w then gx.2 else acc) 0

/-- 添字 `i` における分割候補の最良値。`cand` は候補添字の並び（m48 の
二本指走査は `[p, p+1]` を返す）。健全性は `cand` の中身に一切依存しない。 -/
def bestSplit (gv X acc : List Nat) (i : Nat) (cand : List Nat) : Nat :=
  cand.foldl
    (fun b j => max b (min (acc.getD j 0)
                           (floorVal (gv.zip X) (gv.getD i 0 - gv.getD j 0))))
    0

/-- 1 レベル分を左から `n` 点まで作る（`acc` は確定済み接頭辞）。 -/
def liftAux (gv X : List Nat) (cap : Nat) (cand : Nat → List Nat) :
    Nat → List Nat
  | 0     => []
  | n + 1 =>
      let acc := liftAux gv X cap cand n
      acc ++ [min cap (1 + X.getD n 0 + bestSplit gv X acc n (cand n))]

def liftLevel (gv X : List Nat) (cap : Nat) (cand : Nat → List Nat) : List Nat :=
  liftAux gv X cap cand gv.length

/-- `k` レベル持ち上げる。`cap t`・`cand t` は基底から数えて `t` 段目で使う
スライスで、レベルごとに変わってよい（m48 の `cap = 2^{s} − 1` は実際に
レベルごとに変わる）。健全性はそのどちらにも依存しない。 -/
def liftIter (gv : List Nat) :
    (Nat → Nat) → (Nat → Nat → List Nat) → List Nat → Nat → List Nat
  | _,   _,    X, 0     => X
  | cap, cand, X, k + 1 =>
      liftIter gv (fun t => cap (t + 1)) (fun t => cand (t + 1))
        (liftLevel gv X (cap 0) (cand 0)) k

/-! ## Unfolding lemmas (structural, all `rfl`) -/

theorem liftAux_zero (gv X : List Nat) (cap : Nat) (cand : Nat → List Nat) :
    liftAux gv X cap cand 0 = [] := rfl

theorem liftAux_succ (gv X : List Nat) (cap : Nat) (cand : Nat → List Nat) (n : Nat) :
    liftAux gv X cap cand (n + 1) =
      liftAux gv X cap cand n ++
        [min cap (1 + X.getD n 0
          + bestSplit gv X (liftAux gv X cap cand n) n (cand n))] := rfl

theorem liftIter_zero (gv : List Nat) (cap : Nat → Nat) (cand : Nat → Nat → List Nat)
    (X : List Nat) : liftIter gv cap cand X 0 = X := rfl

theorem liftIter_succ (gv : List Nat) (cap : Nat → Nat) (cand : Nat → Nat → List Nat)
    (X : List Nat) (k : Nat) :
    liftIter gv cap cand X (k + 1) =
      liftIter gv (fun t => cap (t + 1)) (fun t => cand (t + 1))
        (liftLevel gv X (cap 0) (cand 0)) k := rfl

/-! ## Generic `foldl` invariants -/

/-- `floorVal` is bounded by any value that bounds every entry whose grid
coordinate is `≤ w`. -/
theorem floorVal_le {gxs : List (Nat × Nat)} {w B : Nat}
    (h : ∀ gx ∈ gxs, gx.1 ≤ w → gx.2 ≤ B) : floorVal gxs w ≤ B := by
  have hgen : ∀ (gxs : List (Nat × Nat)) (a0 : Nat), a0 ≤ B →
      (∀ gx ∈ gxs, gx.1 ≤ w → gx.2 ≤ B) →
      gxs.foldl (fun acc gx => if gx.1 ≤ w then gx.2 else acc) a0 ≤ B := by
    intro gxs
    induction gxs with
    | nil => intro a0 ha0 _; simpa using ha0
    | cons hd tl ih =>
      intro a0 ha0 hh
      simp only [List.foldl_cons]
      split
      next hc =>
        exact ih hd.2 (hh hd (List.mem_cons_self ..) hc)
          (fun gx hgx => hh gx (List.mem_cons_of_mem _ hgx))
      next _hc =>
        exact ih a0 ha0 (fun gx hgx => hh gx (List.mem_cons_of_mem _ hgx))
  unfold floorVal
  exact hgen gxs 0 (Nat.zero_le _) h

/-- Same bound, but for `floorVal` evaluated on a *zipped* pair of lists
`gv.zip X`, phrased directly in terms of the index-wise hypothesis on `gv`
and `X` (avoiding any reasoning about `List.zip` membership). -/
theorem floorVal_zip_le {gv X : List Nat} {w B : Nat}
    (h : ∀ i, gv.getD i 0 ≤ w → X.getD i 0 ≤ B) :
    floorVal (gv.zip X) w ≤ B := by
  have hgen : ∀ (gv X : List Nat) (a0 : Nat), a0 ≤ B →
      (∀ i, gv.getD i 0 ≤ w → X.getD i 0 ≤ B) →
      (gv.zip X).foldl (fun acc gx => if gx.1 ≤ w then gx.2 else acc) a0 ≤ B := by
    intro gv
    induction gv with
    | nil =>
      intro X a0 ha0 _
      simp only [List.zip_nil_left, List.foldl_nil]
      exact ha0
    | cons ga gt ih =>
      intro X a0 ha0 hh
      cases X with
      | nil =>
        simp only [List.zip_nil_right, List.foldl_nil]
        exact ha0
      | cons xa xt =>
        have hh' : ∀ i, gt.getD i 0 ≤ w → xt.getD i 0 ≤ B := by
          intro i hi
          have hgi : (ga :: gt).getD (i + 1) 0 ≤ w := by
            rw [List.getD_cons_succ]; exact hi
          have hres := hh (i + 1) hgi
          rwa [List.getD_cons_succ] at hres
        simp only [List.zip_cons_cons, List.foldl_cons]
        split
        next hc =>
          have hg0 : (ga :: gt).getD 0 0 ≤ w := by
            rw [List.getD_cons_zero]; exact hc
          have hxa : xa ≤ B := by
            have hres := hh 0 hg0
            rwa [List.getD_cons_zero] at hres
          exact ih xt xa hxa hh'
        next _hc =>
          exact ih xt a0 ha0 hh'
  unfold floorVal
  exact hgen gv X 0 (Nat.zero_le _) h

/-- `foldl max` over a list, starting from an accumulator `a0`, stays below
`Bound` whenever the accumulator does and every entry `k + f a` does — kept
additive (`k + …`) throughout so that no natural-number subtraction ever
has to appear at the call sites. -/
theorem foldl_max_add_le (l : List Nat) (f : Nat → Nat) (k Bound a0 : Nat)
    (h0 : k + a0 ≤ Bound) (h : ∀ a ∈ l, k + f a ≤ Bound) :
    k + l.foldl (fun b a => max b (f a)) a0 ≤ Bound := by
  induction l generalizing a0 with
  | nil => simpa using h0
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd := h hd (List.mem_cons_self ..)
    exact ih (max a0 (f hd)) (by omega) (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Specialisation of `foldl_max_add_le` to `bestSplit`'s own fold. -/
theorem bestSplit_le {gv X acc : List Nat} {i : Nat} {cand : List Nat}
    {k Bound : Nat}
    (h0 : k + 0 ≤ Bound)
    (h : ∀ j, k + min (acc.getD j 0)
        (floorVal (gv.zip X) (gv.getD i 0 - gv.getD j 0)) ≤ Bound) :
    k + bestSplit gv X acc i cand ≤ Bound := by
  unfold bestSplit
  exact foldl_max_add_le cand
    (fun j => min (acc.getD j 0) (floorVal (gv.zip X) (gv.getD i 0 - gv.getD j 0)))
    k Bound 0 h0 (fun j _ => h j)

theorem liftAux_length (gv X : List Nat) (cap : Nat) (cand : Nat → List Nat)
    (n : Nat) : (liftAux gv X cap cand n).length = n := by
  induction n with
  | zero => rw [liftAux_zero]; rfl
  | succ n ih => rw [liftAux_succ]; simp [ih]

/-! ## Soundness -/

/-- **1 レベルの健全性**。`cand` にも `cap` にも条件が付かないことが要。 -/
theorem liftAux_sound {C : Nat → Nat → Nat} {gv X : List Nat}
    {cap s : Nat} {cand : Nat → List Nat}
    (hrec : ∀ t u w, 1 ≤ u + w →
      1 + C t (u + w) + min (C t u) (C (t + 1) w) ≤ C (t + 1) (u + w))
    (hmono : ∀ t v v', v ≤ v' → C t v ≤ C t v')
    (hgmono : ∀ a b, a ≤ b → b < gv.length → gv.getD a 0 ≤ gv.getD b 0)
    (hgpos  : ∀ v ∈ gv, 1 ≤ v)
    (hX : ∀ i, X.getD i 0 ≤ C s (gv.getD i 0))
    (n : Nat) (hn : n ≤ gv.length) :
    ∀ i, (liftAux gv X cap cand n).getD i 0 ≤ C (s + 1) (gv.getD i 0) := by
  induction n with
  | zero => intro i; exact Nat.zero_le _
  | succ n ih =>
    intro i
    have hn' : n ≤ gv.length := by omega
    have ihn := ih hn'
    have hn_lt : n < gv.length := by omega
    have hacclen : (liftAux gv X cap cand n).length = n := liftAux_length gv X cap cand n
    rw [liftAux_succ]
    set acc := liftAux gv X cap cand n with hacc_def
    set y := min cap (1 + X.getD n 0 + bestSplit gv X acc n (cand n)) with hy_def
    have hvpos : 1 ≤ gv.getD n 0 := by
      rw [List.getD_eq_getElem gv 0 hn_lt]
      exact hgpos _ (List.getElem_mem hn_lt)
    have h0 : 1 + X.getD n 0 + 0 ≤ C (s + 1) (gv.getD n 0) := by
      have hrec0 := hrec s (gv.getD n 0) 0 (by omega)
      simp only [Nat.add_zero] at hrec0
      have hXn := hX n
      omega
    have hcand : ∀ j : Nat,
        (1 + X.getD n 0) + min (acc.getD j 0)
          (floorVal (gv.zip X) (gv.getD n 0 - gv.getD j 0)) ≤ C (s + 1) (gv.getD n 0) := by
      intro j
      rcases lt_or_ge j n with hji | hji
      · have hw_le : gv.getD j 0 ≤ gv.getD n 0 := hgmono j n (le_of_lt hji) hn_lt
        have huw : gv.getD n 0 - gv.getD j 0 + gv.getD j 0 = gv.getD n 0 := by omega
        have hrec_inst := hrec s (gv.getD n 0 - gv.getD j 0) (gv.getD j 0) (by omega)
        rw [huw] at hrec_inst
        have hfloor : floorVal (gv.zip X) (gv.getD n 0 - gv.getD j 0)
            ≤ C s (gv.getD n 0 - gv.getD j 0) :=
          floorVal_zip_le (fun k' hk' => le_trans (hX k') (hmono s (gv.getD k' 0) _ hk'))
        have hacc_j := ihn j
        have hXn := hX n
        omega
      · have hacc0 : acc.getD j 0 = 0 := List.getD_eq_default _ _ (by omega)
        omega
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [List.getD_append acc _ 0 i (by omega)]
      exact ihn i
    · rw [hi]
      rw [List.getD_append_right acc _ 0 n (by omega)]
      have hidx : n - acc.length = 0 := by omega
      rw [hidx, List.getD_cons_zero, hy_def]
      apply le_trans (min_le_right _ _)
      exact bestSplit_le h0 hcand
    · have hle : acc.length ≤ i := by omega
      rw [List.getD_append_right acc _ 0 i hle]
      have hz : ([y] : List Nat).getD (i - acc.length) 0 = 0 :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [hz]
      exact Nat.zero_le _

theorem liftLevel_sound {C : Nat → Nat → Nat} {gv X : List Nat}
    {cap s : Nat} {cand : Nat → List Nat}
    (hrec : ∀ t u w, 1 ≤ u + w →
      1 + C t (u + w) + min (C t u) (C (t + 1) w) ≤ C (t + 1) (u + w))
    (hmono : ∀ t v v', v ≤ v' → C t v ≤ C t v')
    (hgmono : ∀ a b, a ≤ b → b < gv.length → gv.getD a 0 ≤ gv.getD b 0)
    (hgpos  : ∀ v ∈ gv, 1 ≤ v)
    (hX : ∀ i, X.getD i 0 ≤ C s (gv.getD i 0)) :
    ∀ i, (liftLevel gv X cap cand).getD i 0 ≤ C (s + 1) (gv.getD i 0) := by
  unfold liftLevel
  exact liftAux_sound hrec hmono hgmono hgpos hX gv.length (Nat.le_refl _)

/-- **多レベルの健全性**（`k` について帰納）。 -/
theorem liftIter_sound {C : Nat → Nat → Nat} {gv : List Nat}
    {cap : Nat → Nat} {cand : Nat → Nat → List Nat} {s₀ : Nat}
    (hrec : ∀ t u w, 1 ≤ u + w →
      1 + C t (u + w) + min (C t u) (C (t + 1) w) ≤ C (t + 1) (u + w))
    (hmono : ∀ t v v', v ≤ v' → C t v ≤ C t v')
    (hgmono : ∀ a b, a ≤ b → b < gv.length → gv.getD a 0 ≤ gv.getD b 0)
    (hgpos  : ∀ v ∈ gv, 1 ≤ v)
    {X : List Nat} (hX : ∀ i, X.getD i 0 ≤ C s₀ (gv.getD i 0)) (k : Nat) :
    ∀ i, (liftIter gv cap cand X k).getD i 0 ≤ C (s₀ + k) (gv.getD i 0) := by
  induction k generalizing X s₀ cap cand with
  | zero =>
    intro i
    rw [liftIter_zero]
    simpa using hX i
  | succ k ih =>
    intro i
    have hX' : ∀ j, (liftLevel gv X (cap 0) (cand 0)).getD j 0
        ≤ C (s₀ + 1) (gv.getD j 0) :=
      liftLevel_sound hrec hmono hgmono hgpos hX
    have hres := ih (cap := fun t => cap (t + 1)) (cand := fun t => cand (t + 1))
      (X := liftLevel gv X (cap 0) (cand 0)) (s₀ := s₀ + 1) hX' i
    have heq : s₀ + (k + 1) = s₀ + 1 + k := by omega
    rw [liftIter_succ, heq]
    exact hres

/-- 実物 `C S v = countLe (rowIter S) v` での実例化。 -/
theorem liftIter_le_count {gv X : List Nat} {s₀ : Nat}
    {cap : Nat → Nat} {cand : Nat → Nat → List Nat}
    (hgmono : ∀ a b, a ≤ b → b < gv.length → gv.getD a 0 ≤ gv.getD b 0)
    (hgpos  : ∀ v ∈ gv, 1 ≤ v)
    (hbase : ∀ i, X.getD i 0 ≤ countLe (rowIter s₀) (gv.getD i 0)) (k : Nat) :
    ∀ i, (liftIter gv cap cand X k).getD i 0
           ≤ countLe (rowIter (s₀ + k)) (gv.getD i 0) :=
  liftIter_sound (C := fun t v => countLe (rowIter t) v)
    (fun t u w h => count_recursion_split t u w h)
    (fun t _ _ h => RevPebbling.CompositionAnchor.countLe_mono_val (rowIter t) h)
    hgmono hgpos hbase k

/-! ## Computational sanity check

The theorems above hold for *any* `cand`/`cap`, so a "wrong but
self-consistent" definition of `liftAux`/`bestSplit` could in principle
still satisfy them; the point of this section is to check numerically,
independent of the proof above, that the *actual* definitions really do
stay under the true count on a small concrete instance. -/

/-- All splits `j < i` — the honest `max_j` of the DP (m48's two-finger scan
returns a two-element subset of this; soundness holds for either). -/
private def fullCand (i : Nat) : List Nat := List.range i

private def sampleGrid : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

/-- Exact row at level `s`, restricted to `sampleGrid`. -/
private def sampleRow (s : Nat) : List Nat :=
  sampleGrid.map (fun v => countLe (rowIter s) v)

/-- m48's actual two-finger scan returns a *subset* of `fullCand i`; this is
the extreme case of a bad subset (one candidate only), kept to exercise the
"soundness does not depend on `cand`" claim computationally. -/
private def poorCand (i : Nat) : List Nat := if i = 0 then [] else [i - 1]

-- The three rows involved, pinned so that a change in `rowIter` or `countLe`
-- shows up here rather than silently shifting the checks below.
example : sampleRow 2 = [3, 6, 7, 7, 7, 7, 7, 7] := by decide
example : sampleRow 3 = [4, 10, 12, 14, 15, 15, 15, 15] := by decide
example : sampleRow 4 = [5, 15, 18, 25, 28, 30, 31, 31] := by decide

/-- **1 レベル持ち上げは完全格子上で厳密行に一致する**（`≤` ではなく `=`）。
`m48_exact_replay.py` の `lift()` を同じ入力で走らせた出力
`[4, 10, 12, 14, 15, 15, 15, 15]` とも一致する（2026-08-24 実測）。
等号なので、定義を潰した実装（恒等・全 0 など）はここで落ちる。 -/
example : liftLevel sampleGrid (sampleRow 2) 999 fullCand = sampleRow 3 := by decide

/-- **2 レベルでも厳密**。m48 の `lift(gv, X0, 4, {5,6})` の出力
`[5, 15, 18, 25, 28, 30, 31, 31]` と一致（2026-08-24 実測）。 -/
example :
    liftIter sampleGrid (fun _ => 999) (fun _ => fullCand) (sampleRow 2) 2
      = sampleRow 4 := by decide

/-- 床が実際に効いていること（`cap = 5` で頭打ちになる）。床は値を下げる
方向にしか効かないので、健全性は保たれたまま鋭さだけが失われる。 -/
example : liftLevel sampleGrid (sampleRow 2) 5 fullCand
    = [4, 5, 5, 5, 5, 5, 5, 5] := by decide

/-- 候補を 1 個に削ると鋭さは落ちるが、`liftLevel_sound` の主張どおり
厳密行を超えない。 -/
example :
    let Xn := liftLevel sampleGrid (sampleRow 2) 999 poorCand
    Xn ≠ sampleRow 3 ∧ ∀ i, i < sampleGrid.length → Xn.getD i 0 ≤ (sampleRow 3).getD i 0 := by
  decide

end RevPebbling.XLift

#print axioms RevPebbling.XLift.liftIter_le_count
