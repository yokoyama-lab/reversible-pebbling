/-
# 計算による検査（テストファースト）

**定義が正しいことは証明できない。**できるのは、独立に得た値と突き合わせて
「間違っていたら落ちる」ようにしておくことだけ。ここでは 2 種類を置く。

1. **陽性**: `~/dev/notes/spooky-pebbling` の BFS（`kss.py` / `witness_up.py`、
   Knill の既知値 5 点と独立 2 実装 40 点で校正済み）が返した**最適手順そのもの**を
   転記し、`by decide` で妥当性を検査する。同時に `T… ≤ 値` の上界も得る
2. **陰性（変異注入）**: 前提条件・上限・終状態・範囲を 1 つずつ壊した手順が
   **`Run` にならない**ことを `by decide` で検査する。陽性だけだと
   「何でも `Run` になる」定義でも通ってしまう

値の出典は README の表（$T_{UP}(n,2)=n^2+n-3$、$T_{UG}(n,2)=n^2+n-4$、
$T_P(n,3)=n^2-n-3$、$k\le s$ で $T_{UP}=2k-1$、$n\le s$ で $T_{UG}=2n$）。
-/
import SpookyPebbling.Slope6Exact

namespace Spooky

/-! ## 陽性: BFS の最適手順を転記して検査する -/

/-- BFS が返した最適手順（TUP(2,2) = 3）。 -/
def wUP2_2 : List Move := [⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 2 2 (sinkPebble 2) wUP2_2 allEmpty := by decide
example : TUP 2 2 ≤ 3 := TUP_le ⟨wUP2_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUP(3,2) = 9）。 -/
def wUP3_2 : List Move := [⟨.pebble, 0⟩, ⟨.ghost, 2⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 3 2 (sinkPebble 3) wUP3_2 allEmpty := by decide
example : TUP 3 2 ≤ 9 := TUP_le ⟨wUP3_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUP(4,2) = 17）。 -/
def wUP4_2 : List Move := [⟨.pebble, 0⟩, ⟨.ghost, 3⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩, ⟨.unghost, 3⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 0⟩, ⟨.ghost, 2⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 4 2 (sinkPebble 4) wUP4_2 allEmpty := by decide
example : TUP 4 2 ≤ 17 := TUP_le ⟨wUP4_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUP(3,3) = 5）。 -/
def wUP3_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 3 3 (sinkPebble 3) wUP3_3 allEmpty := by decide
example : TUP 3 3 ≤ 5 := TUP_le ⟨wUP3_3, rfl, by decide⟩

/-- BFS が返した最適手順（TUP(4,4) = 7）。 -/
def wUP4_4 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.unpebble, 3⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 4 4 (sinkPebble 4) wUP4_4 allEmpty := by decide
example : TUP 4 4 ≤ 7 := TUP_le ⟨wUP4_4, rfl, by decide⟩

/-- BFS が返した最適手順（TUP(5,3) = 13）。 -/
def wUP5_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 3⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 5 3 (sinkPebble 5) wUP5_3 allEmpty := by decide
example : TUP 5 3 ≤ 13 := TUP_le ⟨wUP5_3, rfl, by decide⟩

/-- BFS が返した最適手順（TUG(2,2) = 4）。 -/
def wUG2_2 : List Move := [⟨.pebble, 0⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 2 2 (sinkGhost 2) wUG2_2 allEmpty := by decide
example : TUG 2 2 ≤ 4 := TUG_le ⟨wUG2_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUG(3,2) = 8）。 -/
def wUG3_2 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 3 2 (sinkGhost 3) wUG3_2 allEmpty := by decide
example : TUG 3 2 ≤ 8 := TUG_le ⟨wUG3_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUG(4,2) = 16）。 -/
def wUG4_2 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩, ⟨.unghost, 3⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 0⟩, ⟨.ghost, 2⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 4 2 (sinkGhost 4) wUG4_2 allEmpty := by decide
example : TUG 4 2 ≤ 16 := TUG_le ⟨wUG4_2, rfl, by decide⟩

/-- BFS が返した最適手順（TUG(3,3) = 6）。 -/
def wUG3_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 3 3 (sinkGhost 3) wUG3_3 allEmpty := by decide
example : TUG 3 3 ≤ 6 := TUG_le ⟨wUG3_3, rfl, by decide⟩

/-- BFS が返した最適手順（TUG(5,3) = 14）。 -/
def wUG5_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.unghost, 4⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 3⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 5 3 (sinkGhost 5) wUG5_3 allEmpty := by decide
example : TUG 5 3 ≤ 14 := TUG_le ⟨wUG5_3, rfl, by decide⟩

/-- BFS が返した最適手順（TP(4,3) = 9）。 -/
def wP4_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.pebble, 3⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 4 3 allEmpty wP4_3 (sinkPebble 4) := by decide
example : TP 4 3 ≤ 9 := TP_le ⟨wP4_3, rfl, by decide⟩

/-- BFS が返した最適手順（TP(5,3) = 17）。 -/
def wP5_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 0⟩, ⟨.ghost, 2⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 5 3 allEmpty wP5_3 (sinkPebble 5) := by decide
example : TP 5 3 ≤ 17 := TP_le ⟨wP5_3, rfl, by decide⟩

/-- BFS が返した最適手順（TP(3,3) = 5）。 -/
def wP3_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]
example : Run 3 3 allEmpty wP3_3 (sinkPebble 3) := by decide
example : TP 3 3 ≤ 5 := TP_le ⟨wP3_3, rfl, by decide⟩

/-! ## 陰性（変異注入）: 1 つ壊すと `Run` にならないこと

陽性の検査だけでは「常に真」の定義でも通る。以下が**すべて偽**であることを確かめる。
-/

/-- 上限を 1 下げると通らない（`wUP2_2` は途中で 2 個持つ）。 -/
example : ¬ Run 2 1 (sinkPebble 2) wUP2_2 allEmpty := by decide

/-- 前提条件: `v₀` にペブルが無いのに `unpebble v₁` は打てない。 -/
example : ¬ Run 2 2 (sinkPebble 2) [⟨.unpebble, 1⟩] allEmpty := by decide

/-- 前提条件: `v₀` にペブルが無いのに `unghost v₁` は打てない。 -/
example : ¬ Run 2 2 (sinkGhost 2) [⟨.unghost, 1⟩, ⟨.unpebble, 1⟩] allEmpty := by decide

/-- 終状態: ゴーストを残したまま終わってはいけない（$G_\tau=\emptyset$）。 -/
example : ¬ Run 2 2 (sinkPebble 2) [⟨.ghost, 1⟩] allEmpty := by decide

/-- 範囲: 鎖の外の頂点は触れない。 -/
example : ¬ Run 2 2 (sinkPebble 2) [⟨.pebble, 5⟩] allEmpty := by decide

/-- 手順を 1 手削ると終状態に届かない。 -/
example : ¬ Run 2 2 (sinkPebble 2) [⟨.pebble, 0⟩, ⟨.unpebble, 1⟩] allEmpty := by decide

/-! ## `ghost` だけは前提を持たない（測定）

これは Quist–Laarman Def 2.2 の逐語。`ghost` に前提を付けてしまうと落ちる検査。
-/

/-- $v_0$ が空のまま `ghost v₁` を打てる（そのあと `unghost` には $v_0$ が要る）。 -/
example : Run 2 2 (sinkPebble 2)
    [⟨.ghost, 1⟩, ⟨.pebble, 0⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩] allEmpty := by
  decide

/-! ## 3 量の関係（KSS Thm 4.11 の片側）を小さい点で確かめる

`TUG n s ≤ TUP n s + 1`（KSS Lemma 4.10）と `TUP n s ≤ TUG n s + 1`（Lemma 4.9）は
上の上界だけからは出ないが、$n=3,s=2$ では $T_{UP}=9$, $T_{UG}=8$ で差が 1。
ここでは上界どうしの比較だけを記録する（下界は `Parity.lean` の議論が要る）。
-/

example : TUG 3 2 ≤ 8 := TUG_le ⟨wUG3_2, rfl, by decide⟩
example : TUP 3 2 ≤ 9 := TUP_le ⟨wUP3_2, rfl, by decide⟩

/-! ## 主定理が空虚でないこと

`decomp_ge` の仮定は充足可能である（上の witness）。実際に適用して結論を得る。
-/

example : ∃ k, 1 ≤ k ∧ k < 3 ∧ 2 * k - 1 + TUP k 3 + TUP (3 - k) 2 ≤ wUP3_3.length :=
  decomp_ge (by omega) (by decide)

example : ∃ k, 1 ≤ k ∧ k < 5 ∧ 2 * k - 1 + TUP k 3 + TUP (5 - k) 2 ≤ wUP5_3.length :=
  decomp_ge (by omega) (by decide)

/-! ## `<=` 方向の構成も空虚でない

`n = 5, k = 2, s = 3` で、頭（長さ 2・上限 3）と尻尾（長さ 3・上限 2）の手順から
実際に長さ `3 + 9 + 3 = 15` の手順が組み上がる（`k = 2` は最適ではないので
`T_UP(5,3) = 13 ≤ 15`。等号は最適な `k` で立つ）。
-/

example : ∃ ms : List Move, ms.length = 2 * 1 + 1 + wUP3_2.length + wUP2_2.length ∧
    Run 5 3 (sinkPebble 5) ms allEmpty :=
  decomp_le_run (by omega) (by omega) (by decide) (by decide)

/-! ## 定理B と BFS の突き合わせ（交差検証）

`TUG_eq_slope4` が与える値が、上で転記した BFS の最適手順の長さと一致することを確かめる。
**片方は定理・片方は全数探索**なので、どちらかが間違っていれば落ちる。
-/

theorem TUG_3_2 : TUG 3 2 = 8 := by
  have := TUG_eq_slope4 (s := 2) (n := 3) (by omega) (by omega) (by decide); omega

theorem TUG_3_3 : TUG 3 3 = 6 := by
  have := TUG_eq_slope4 (s := 3) (n := 3) (by omega) (by omega) (by decide); omega

theorem TUG_5_3 : TUG 5 3 = 14 := by
  have := TUG_eq_slope4 (s := 3) (n := 5) (by omega) (by omega) (by decide); omega

/-- BFS の最適手順の長さ（8）と定理B の値が一致する。 -/
example : TUG 3 2 = wUG3_2.length := by rw [TUG_3_2]; rfl

example : TUG 3 3 = wUG3_3.length := by rw [TUG_3_3]; rfl

example : TUG 5 3 = wUG5_3.length := by rw [TUG_5_3]; rfl

/-! ## 定理C・定理D と BFS の突き合わせ（交差検証）

`TUP_eq_slope4`（定理C）が与える値も BFS の最適手順の長さと一致する。
`(n,s)=(5,3)` は **`n = θ(s)-1`（傾き 4 の領域の右端・δ が反転する 1 つ手前）**なので、
範囲の境界そのものを検査していることになる。
-/

theorem TUP_2_2 : TUP 2 2 = 3 := by
  have := TUP_eq_slope4 (s := 2) (n := 2) (by omega) (by omega) (by decide); omega

theorem TUP_3_3 : TUP 3 3 = 5 := by
  have := TUP_eq_slope4 (s := 3) (n := 3) (by omega) (by omega) (by decide); omega

theorem TUP_5_3 : TUP 5 3 = 13 := by
  have := TUP_eq_slope4 (s := 3) (n := 5) (by omega) (by omega) (by decide); omega

example : TUP 2 2 = wUP2_2.length := by rw [TUP_2_2]; rfl

example : TUP 3 3 = wUP3_3.length := by rw [TUP_3_3]; rfl

example : TUP 5 3 = wUP5_3.length := by rw [TUP_5_3]; rfl

/-- **δ = T_UG - T_UP = +1**（定理C の系）。両辺とも BFS の最適手順で裏が取れている。 -/
example : TUG 3 3 = TUP 3 3 + 1 := TUG_eq_TUP_add_one (by omega) (by omega) (by decide)

example : TUG 5 3 = TUP 5 3 + 1 := TUG_eq_TUP_add_one (by omega) (by omega) (by decide)

example : wUG3_3.length = wUP3_3.length + 1 := rfl

example : wUG5_3.length = wUP5_3.length + 1 := rfl

/-- **定理D は `(n,s) = (3,2)` で等号**: `6·3 - 2·(2+3) = 8` が BFS の最適手数 8 に一致する。 -/
example : TUG 3 2 = 8 ∧ 6 * 3 ≤ TUG 3 2 + 2 * (2 + 3) :=
  ⟨TUG_3_2, TUG_ge_slope6 (by omega) 3 (by omega)⟩

/-- 定理D は `(n,s) = (5,3)` では緩い（`30 ≤ 14 + 18`）。緊密でない点も記録しておく。 -/
example : 6 * 5 ≤ TUG 5 3 + 3 * (3 + 3) := TUG_ge_slope6 (by omega) 5 (by omega)

/-! ## 定理F（傾き 6 の領域の厳密値）と BFS の突き合わせ

`s=3` の傾き 6 の区間は `θ(3)=6 ≤ n ≤ B₄(3)-1 = 8`。下の 2 本は独立に走らせた BFS の
最適手順で、長さが定理F の値 `6n-18` に一致する。
-/

def wUG6_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩,
  ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩, ⟨.unghost, 5⟩, ⟨.unpebble, 5⟩,
  ⟨.pebble, 3⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 3⟩, ⟨.unghost, 1⟩,
  ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]

example : Run 6 3 (sinkGhost 6) wUG6_3 allEmpty := by decide

def wUG7_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩,
  ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.ghost, 2⟩, ⟨.pebble, 4⟩, ⟨.pebble, 5⟩, ⟨.unpebble, 4⟩,
  ⟨.unghost, 6⟩, ⟨.unpebble, 6⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.pebble, 0⟩,
  ⟨.unpebble, 4⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 3⟩,
  ⟨.pebble, 0⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]

example : Run 7 3 (sinkGhost 7) wUG7_3 allEmpty := by decide

theorem TUG_6_3 : TUG 6 3 = 18 := by
  have := TUG_eq_slope6 (s := 3) (n := 6) (by omega) (by decide) (by decide); omega

theorem TUG_7_3 : TUG 7 3 = 24 := by
  have := TUG_eq_slope6 (s := 3) (n := 7) (by omega) (by decide) (by decide); omega

theorem TUG_8_3 : TUG 8 3 = 30 := by
  have := TUG_eq_slope6 (s := 3) (n := 8) (by omega) (by decide) (by decide); omega

/-- 定理F の値が BFS の最適手順の長さと一致する。 -/
example : TUG 6 3 = wUG6_3.length := by rw [TUG_6_3]; rfl

example : TUG 7 3 = wUG7_3.length := by rw [TUG_7_3]; rfl

/-- **区間の右端 `B₄(3)-1 = 8` は本物**: `n = 9` を含めると値は 38 で、`6·9-18 = 36` ではない
（BFS で確認。ここでは「定理F が `n = B₄(s)` を主張していない」ことだけを記録する）。 -/
example : ¬ (9 + 1 ≤ B4 3) := by decide

/-- `T_UG` と `T_UP` の差はちょうど 1（両側不等式＋パリティ）。 -/
example : TUG 5 3 = TUP 5 3 + 1 ∨ TUP 5 3 = TUG 5 3 + 1 :=
  TUG_TUP_diff_one (by omega) (by omega)
    (UPLengths_nonempty (by omega) (by omega)) (UGLengths_nonempty (by omega) (by omega))

end Spooky
