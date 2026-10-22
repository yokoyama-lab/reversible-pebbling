import lean.XLiftBase

/-!
# 基底行の高速版: 2 本指の生成器と、run を 1 回だけ走査する検査器

`XLiftBase.baseRowOf` は格子点ごとに run 列全体を畳み込む。X60（格子 229,375 点、
`rleRows 60` の鎖は 13.1M runs）では約 3×10^12 回の run 訪問になり、m83 の 269 段
（rc=124）と m84 の 40 段がどちらも基底行で止まっていた原因である。

ここでは信頼しない生成器 `genBase`（`List.span` による 2 本指、O(runs + 格子)）の出力 `Y` を、
run 列を 1 回だけ走査する検査器 `chkBase` に通す。健全性 `baseRowFast_le` は `baseRowOf_le` と
同じ形で、**run と格子の昇順性を要しない**（昇順でなければ検査が落ちて 0 の行になるだけ）。
-/

namespace RevPebbling.XLiftBaseFast

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase

theorem countLeRuns_cons (a c : Nat) (r : Runs) (v : Nat) :
    countLeRuns ((a, c) :: r) v = (if a ≤ v then c else 0) + countLeRuns r v := by
  rw [countLeRuns_eq, countLeRuns_eq, expand_cons, countLe_replicate_append]

/-! ## 1. 検査器 -/

/-- `cnt`・`mx` は走査済みの run の個数の和と値の最大。点 `(v, y)` は `y = 0` か
`mx ≤ v ∧ y ≤ cnt` なら消化し、そうでなければ run を 1 つ進める。燃料は構造的再帰のため。 -/
def chkFuel : Nat → Runs → Nat → Nat → List (Nat × Nat) → Bool
  | _, _, _, _, [] => true
  | 0, _, _, _, _ :: _ => false
  | n + 1, r, cnt, mx, (v, y) :: ps =>
    if y = 0 ∨ (mx ≤ v ∧ y ≤ cnt) then chkFuel n r cnt mx ps
    else match r with
      | [] => false
      | (a, c) :: r' => chkFuel n r' (cnt + c) (max mx a) ((v, y) :: ps)

/-- 1 歩ごとに点か run が 1 つ減るので、燃料は `r.length + ps.length` で足りる。 -/
def chkBase (r : Runs) (ps : List (Nat × Nat)) : Bool :=
  chkFuel (r.length + ps.length) r 0 0 ps

theorem chkFuel_sound (R : Runs) :
    ∀ (n : Nat) (r : Runs) (cnt mx : Nat) (ps : List (Nat × Nat)),
      (∀ v, mx ≤ v → cnt + countLeRuns r v ≤ countLeRuns R v) →
      chkFuel n r cnt mx ps = true → ∀ p ∈ ps, p.2 ≤ countLeRuns R p.1 := by
  intro n
  induction n with
  | zero =>
    intro r cnt mx ps _ hc p hp
    cases ps with
    | nil => simp at hp
    | cons q ps => simp [chkFuel] at hc
  | succ n ih =>
    intro r cnt mx ps hinv hc p hp
    cases ps with
    | nil => simp at hp
    | cons q ps =>
      obtain ⟨v, y⟩ := q
      simp only [chkFuel] at hc
      split at hc
      · next hd =>
        rcases List.mem_cons.mp hp with rfl | hp'
        · rcases hd with h0 | ⟨h1, h2⟩
          · simp [h0]
          · have := hinv v h1
            show y ≤ countLeRuns R v
            omega
        · exact ih r cnt mx ps hinv hc p hp'
      · cases r with
        | nil => simp at hc
        | cons ac r' =>
          obtain ⟨a, c⟩ := ac
          refine ih r' (cnt + c) (max mx a) ((v, y) :: ps) ?_ hc p hp
          intro w hw
          have h1 : mx ≤ w := le_trans (Nat.le_max_left _ _) hw
          have h2 : a ≤ w := le_trans (Nat.le_max_right _ _) hw
          have := hinv w h1
          rw [countLeRuns_cons, if_pos h2] at this
          omega

theorem chkBase_sound (r : Runs) (ps : List (Nat × Nat)) (h : chkBase r ps = true) :
    ∀ p ∈ ps, p.2 ≤ countLeRuns r p.1 := by
  unfold chkBase at h
  exact chkFuel_sound r _ r 0 0 ps (fun v _ => by omega) h

/-! ## 2. 生成器（信頼しない）と高速版の基底行 -/

/-- 格子点ごとに `List.span` で値 `≤ v` の run の先頭部分を切り出し、個数を足し込む。
run と格子が昇順なら `countLeRuns` と一致する。証明はしない（`chkBase` が検査する）。 -/
def genBase (r : Runs) (g : List Nat) : List Nat :=
  (g.foldl
    (fun (st : Runs × Nat × List Nat) v =>
      let p := st.1.span (fun x => decide (x.1 ≤ v))
      let cnt := st.2.1 + p.1.foldl (fun s x => s + x.2) 0
      (p.2, cnt, cnt :: st.2.2))
    (r, 0, [])).2.2.reverse

def baseRowFast (o : Option Runs) (g : List Nat) : List Nat :=
  match o with
  | some r =>
    if (genBase r g).length = g.length ∧ chkBase r (g.zip (genBase r g)) = true
    then genBase r g else g.map (fun _ => 0)
  | none => g.map (fun _ => 0)

theorem getD_map_zero (g : List Nat) (i : Nat) : (g.map (fun _ => 0)).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases g[i]? <;> simp

theorem row_le_runs (r : Runs) (g Y : List Nat) (hl : Y.length = g.length)
    (hc : chkBase r (g.zip Y) = true) : ∀ i, Y.getD i 0 ≤ countLeRuns r (g.getD i 0) := by
  intro i
  by_cases hi : i < Y.length
  · have hg : i < g.length := hl ▸ hi
    have hmem : (g[i], Y[i]) ∈ g.zip Y := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    have := chkBase_sound r _ hc _ hmem
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hg]
    simpa using this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-- `baseRowOf_le` の高速版。 -/
theorem baseRowFast_le (rows : Array RLERow) (k : Nat) (g : List Nat) :
    ∀ i, (baseRowFast (checkChainOpt rows k) g).getD i 0
      ≤ countLe (rowIter k) (g.getD i 0) := by
  intro i
  unfold baseRowFast
  cases hc : checkChainOpt rows k with
  | none =>
    simp only []
    rw [getD_map_zero]
    exact Nat.zero_le _
  | some r =>
    simp only []
    have he := chain_sound rows k r hc
    split
    · next h =>
      have := row_le_runs r g _ h.1 h.2 i
      rw [countLeRuns_eq, he] at this
      exact this
    · rw [getD_map_zero]
      exact Nat.zero_le _

/-! ## 3. 小さな固定値の例（kernel で評価） -/

/-- 小さな鎖では `baseRowOf` と同じ行を出す。 -/
example : baseRowFast (checkChainOpt (rleRows 4) 2) [1,2,3,4,5,6,7,8]
    = [3,6,7,7,7,7,7,7] := by decide +kernel

example : baseRowFast (checkChainOpt (rleRows 5) 3) [1,2,3,4,5,6,7,8,9,10,11,12]
    = baseRowOf (checkChainOpt (rleRows 5) 3) [1,2,3,4,5,6,7,8,9,10,11,12] := by decide +kernel

/-- 生成器と昇順入力の組は検査を通る。 -/
example : chkBase [(1,1),(2,3),(5,2)] ([0,1,2,4,5,9].zip (genBase [(1,1),(2,3),(5,2)] [0,1,2,4,5,9]))
    = true := by decide

/-- 否定例: 真の個数 4（v = 4）を 5 に上げると落ちる。 -/
example : chkBase [(1,1),(2,3),(5,2)] [(0,0),(1,1),(2,4),(4,5),(5,6),(9,6)] = false := by decide

/-- 否定例: 真の個数 0（v = 0）を 1 に上げると落ちる。 -/
example : chkBase [(1,1),(2,3),(5,2)] [(0,1),(1,1),(2,4),(4,4),(5,6),(9,6)] = false := by decide

/-- 昇順でない run でも健全（検査は落ちるか、真の個数以下しか受理しない）。
ここでは値 5 の run が先頭にあるので、v = 2 で y = 1 を受理するには run を進める必要があり、
`mx` が 5 になって受理できない。真の個数は 1 なので健全性は保たれ、完全性だけが失われる。 -/
example : chkBase [(5,2),(1,1)] [(2,1)] = false := by decide

end RevPebbling.XLiftBaseFast

#print axioms RevPebbling.XLiftBaseFast.chkBase_sound
#print axioms RevPebbling.XLiftBaseFast.baseRowFast_le
