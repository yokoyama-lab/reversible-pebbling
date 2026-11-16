import RevPebbling.XLift
import RevPebbling.RLECertify
import Mathlib.Data.List.GetD

/-!
# XLift の基底行と、配列上の証明書検査器

`notes/xlift_lean_design.md` §5 に対応する。

* `xlift_base_329` は **計算を一切要しない**。`XLift.liftIter_le_count` の健全性が
  `cap`・`cand`・格子に対して一般だからで、S = 60 の基底行 `X60` は
  `chain_sound` 経由の `baseRowOf_le` から得る（`rleRows 60` は評価しない）。
* 水準 329 の行の数値内容（固定値）は、後で `liftChain` ＋ `native_decide` で得る。
  `checkStep` は信頼しない生成器の出力 `Y` と証明書 `(t, q)` を Bool で検査し、
  健全性は格子の単調性を要しない。
-/

namespace RevPebbling.XLiftBase

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift

/-! ## 1. run-length 上の count -/

def countLeRuns (r : Runs) (v : Nat) : Nat :=
  r.foldl (fun acc vc => if vc.1 ≤ v then acc + vc.2 else acc) 0

theorem countLe_replicate_append (c x v : Nat) (l : List Nat) :
    countLe (List.replicate c x ++ l) v
      = (if x ≤ v then c else 0) + countLe l v := by
  unfold countLe
  rw [List.countP_append, List.countP_replicate]
  by_cases h : x ≤ v <;> simp [h]

theorem foldl_runs_eq (v : Nat) :
    ∀ (r : Runs) (a : Nat),
      r.foldl (fun acc vc => if vc.1 ≤ v then acc + vc.2 else acc) a
        = a + countLe (expand r) v
  | [], a => by simp [expand, countLe]
  | (x, c) :: r, a => by
    rw [List.foldl_cons, foldl_runs_eq v r, expand_cons, countLe_replicate_append]
    by_cases h : x ≤ v <;> simp [h] <;> omega

theorem countLeRuns_eq (r : Runs) (v : Nat) :
    countLeRuns r v = countLe (expand r) v := by
  unfold countLeRuns
  rw [foldl_runs_eq]
  omega

example : countLeRuns [(1,1),(2,3),(5,2)] 0 = 0 := by decide
example : countLeRuns [(1,1),(2,3),(5,2)] 1 = 1 := by decide
example : countLeRuns [(1,1),(2,3),(5,2)] 2 = 4 := by decide
example : countLeRuns [(1,1),(2,3),(5,2)] 4 = 4 := by decide
example : countLeRuns [(1,1),(2,3),(5,2)] 5 = 6 := by decide

/-! ## 2. 認証済みの鎖から読む基底行 -/

def baseRowOf (o : Option Runs) (g : List Nat) : List Nat :=
  match o with
  | some r => g.map (countLeRuns r)
  | none   => g.map (fun _ => 0)

theorem baseRowOf_le (rows : Array RLERow) (k : Nat) (g : List Nat) :
    ∀ i, (baseRowOf (checkChainOpt rows k) g).getD i 0
      ≤ countLe (rowIter k) (g.getD i 0) := by
  intro i
  unfold baseRowOf
  cases hc : checkChainOpt rows k with
  | none =>
    simp only []
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases g[i]? <;> simp
  | some r =>
    simp only []
    have he := chain_sound rows k r hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases g[i]? with
    | none => simp
    | some a => simp [countLeRuns_eq, he]

/-- S = 60 の基底行（格子 `g` 上）。 -/
def X60 (g : List Nat) : List Nat := baseRowOf (checkChainOpt (rleRows 60) 58) g

theorem X60_le (g : List Nat) :
    ∀ i, (X60 g).getD i 0 ≤ countLe (rowIter 58) (g.getD i 0) :=
  baseRowOf_le (rleRows 60) 58 g

/-! ## 3. 設計書の目標（ε = 0.0035、S₀ = 329 = rowIter 327 = 58 + 269） -/

theorem xlift_base_329 (g : List Nat)
    (hgmono : ∀ a b, a ≤ b → b < g.length → g.getD a 0 ≤ g.getD b 0)
    (hgpos : ∀ v ∈ g, 1 ≤ v) (cap : Nat → Nat) (cand : Nat → Nat → List Nat) :
    ∀ i, (liftIter g cap cand (X60 g) 269).getD i 0 ≤ countLe (rowIter 327) (g.getD i 0) := by
  intro i
  have h := XLift.liftIter_le_count (cap := cap) (cand := cand) hgmono hgpos (X60_le g) 269 i
  exact h

/-! ## 4. 配列上の証明書検査器 -/

def stepOk (g X Y : Array Nat) (cert : Array (Nat × Nat)) (i : Nat) : Bool :=
  let gi := g.getD i 0; let xi := X.getD i 0; let yi := Y.getD i 0
  let c := cert.getD i (0, 0)
  decide (1 ≤ gi) &&
    (decide (yi ≤ 1 + xi) ||
     (decide (c.1 < i) && decide (g.getD c.2 0 + g.getD c.1 0 ≤ gi) &&
      decide (yi ≤ 1 + xi + min (Y.getD c.1 0) (X.getD c.2 0))))

def checkStep (g X Y : Array Nat) (cert : Array (Nat × Nat)) : Bool :=
  (List.range Y.size).all (stepOk g X Y cert)

theorem checkStep_sound {C : Nat → Nat → Nat}
    (hrec : ∀ t u w, 1 ≤ u + w → 1 + C t (u + w) + min (C t u) (C (t + 1) w) ≤ C (t + 1) (u + w))
    (hmono : ∀ t v v', v ≤ v' → C t v ≤ C t v')
    {g X Y : Array Nat} {cert : Array (Nat × Nat)} {s : Nat}
    (hX : ∀ i, X.getD i 0 ≤ C s (g.getD i 0)) (h : checkStep g X Y cert = true) :
    ∀ i, Y.getD i 0 ≤ C (s + 1) (g.getD i 0) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < Y.size
    · have hall := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
      simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hall
      obtain ⟨hg, h1 | ⟨⟨hc1, hc2⟩, hc3⟩⟩ := hall
      · have := hrec s (g.getD i 0) 0 hg
        simp only [Nat.add_zero] at this
        have := hX i
        omega
      · generalize hct : (cert.getD i (0, 0)).1 = t at hc1 hc2 hc3
        generalize hcq : (cert.getD i (0, 0)).2 = q at hc2 hc3
        have hYt : Y.getD t 0 ≤ C (s + 1) (g.getD t 0) := ih t hc1
        have hgq : g.getD q 0 ≤ g.getD i 0 - g.getD t 0 := by omega
        have hXq : X.getD q 0 ≤ C s (g.getD i 0 - g.getD t 0) :=
          le_trans (hX q) (hmono s _ _ hgq)
        have huw : g.getD i 0 - g.getD t 0 + g.getD t 0 = g.getD i 0 := by omega
        have hr := hrec s (g.getD i 0 - g.getD t 0) (g.getD t 0) (by omega)
        rw [huw] at hr
        have := hX i
        omega
    · have : Y.getD i 0 = 0 := by
        unfold Array.getD
        rw [dif_neg hi]
      rw [this]
      exact Nat.zero_le _

def liftChain (g : Array Nat) (gen : Nat → Array Nat → Array Nat × Array (Nat × Nat))
    (X0 : Array Nat) : Nat → Option (Array Nat)
  | 0 => some X0
  | k + 1 => match liftChain g gen X0 k with
    | none => none
    | some X => let p := gen k X; if checkStep g X p.1 p.2 then some p.1 else none

theorem liftChain_sound {C : Nat → Nat → Nat}
    (hrec : ∀ t u w, 1 ≤ u + w → 1 + C t (u + w) + min (C t u) (C (t + 1) w) ≤ C (t + 1) (u + w))
    (hmono : ∀ t v v', v ≤ v' → C t v ≤ C t v')
    {g : Array Nat} {gen : Nat → Array Nat → Array Nat × Array (Nat × Nat)}
    {X0 : Array Nat} {s₀ : Nat}
    (hX0 : ∀ i, X0.getD i 0 ≤ C s₀ (g.getD i 0)) :
    ∀ k Y, liftChain g gen X0 k = some Y → ∀ i, Y.getD i 0 ≤ C (s₀ + k) (g.getD i 0) := by
  intro k
  induction k with
  | zero =>
    intro Y hY i
    simp only [liftChain, Option.some.injEq] at hY
    subst hY
    simpa using hX0 i
  | succ k ih =>
    intro Y hY
    simp only [liftChain] at hY
    cases hk : liftChain g gen X0 k with
    | none => rw [hk] at hY; simp at hY
    | some X =>
      rw [hk] at hY
      simp only [] at hY
      split at hY
      · next hc =>
        have hY' := Option.some.inj hY
        subst hY'
        exact checkStep_sound hrec hmono (ih X hk) hc
      · simp at hY

theorem liftChain_le_count
    {g : Array Nat} {gen : Nat → Array Nat → Array Nat × Array (Nat × Nat)}
    {X0 : Array Nat} {s₀ : Nat}
    (hX0 : ∀ i, X0.getD i 0 ≤ countLe (rowIter s₀) (g.getD i 0)) :
    ∀ k Y, liftChain g gen X0 k = some Y →
      ∀ i, Y.getD i 0 ≤ countLe (rowIter (s₀ + k)) (g.getD i 0) :=
  liftChain_sound (C := fun t v => countLe (rowIter t) v)
    (fun t u w h => count_recursion_split t u w h)
    (fun t _ _ h => RevPebbling.CompositionAnchor.countLe_mono_val (rowIter t) h)
    hX0

/-! ## 5. 小さな固定値の例 -/

/-- 信頼しない生成器。各 `i` で `t < i` を全部試し、`min Y[t] X[q]` が最大のものを採る
（`q` は `g[q] ≤ g[i] - g[t]` を満たす最大の添字）。 -/
def genFull (g : Array Nat) (_k : Nat) (X : Array Nat) : Array Nat × Array (Nat × Nat) :=
  (List.range g.size).foldl
    (fun (p : Array Nat × Array (Nat × Nat)) i =>
      let Y := p.1
      let gi := g.getD i 0
      let best : Nat × Nat × Nat :=
        (List.range i).foldl
          (fun (b : Nat × Nat × Nat) t =>
            let gt := g.getD t 0
            if gt ≤ gi then
              match (List.range g.size).foldl
                  (fun (acc : Option Nat) q => if g.getD q 0 ≤ gi - gt then some q else acc)
                  none with
              | none => b
              | some q =>
                let m := min (Y.getD t 0) (X.getD q 0)
                if m > b.1 then (m, t, q) else b
            else b)
          (0, 0, 0)
      (Y.push (1 + X.getD i 0 + best.1), p.2.push (best.2.1, best.2.2)))
    (#[], #[])

def g8 : Array Nat := #[1,2,3,4,5,6,7,8]
def X2 : Array Nat := #[3,6,7,7,7,7,7,7]

example : liftChain g8 (genFull g8) X2 1
    = some #[4,10,12,14,15,15,15,15] := by decide

set_option maxRecDepth 100000 in
example : liftChain g8 (genFull g8) X2 2
    = some #[5,15,18,25,28,30,31,31] := by decide

/-- 受理される基準の対。 -/
example : checkStep g8 X2 (genFull g8 0 X2).1 (genFull g8 0 X2).2 = true := by decide

/-- 否定例: 添字 7 を 16 に上げる。 -/
example : checkStep g8 X2 ((genFull g8 0 X2).1.set! 7 16) (genFull g8 0 X2).2 = false := by
  decide

/-- 否定例: 添字 3 を 15 に上げる。 -/
example : checkStep g8 X2 ((genFull g8 0 X2).1.set! 3 15) (genFull g8 0 X2).2 = false := by
  decide

/-- `t = i` の証明書は値を上げない。ただしこの例は `c.1 < i` の検査が無くても
`false` になる（格子が正なので `g[q] + g[i] ≤ g[i]` が成り立たない）。`<` を `≤` に
緩める変異を落とすのは `checkStep_sound` の証明の側（`ih t` が `t < i` を要る）であって、
この例ではない。 -/
example : stepOk g8 #[3,6,7,7,7,7,7,7] #[4,10,12,14,15,15,15,15]
    #[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)] 7 = false := by
  decide

/-- 小さな鎖の基底: `rleRows 4` を評価できれば固定値が出る。 -/
example : baseRowOf (checkChainOpt (rleRows 4) 2) [1,2,3,4,5,6,7,8]
    = [3,6,7,7,7,7,7,7] := by decide +kernel

end RevPebbling.XLiftBase

#print axioms RevPebbling.XLiftBase.xlift_base_329
#print axioms RevPebbling.XLiftBase.checkStep_sound
#print axioms RevPebbling.XLiftBase.liftChain_le_count
#print axioms RevPebbling.XLiftBase.countLeRuns_eq
