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
import SpookyPebbling.Lemma48Gen

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

/-! ## `T_UP(n,2) = n²+n-3` と δ の符号反転

上限 2 の閉形式（`Cap2.lean`）は、既に転記してある `wUP3_2`（9 手）・`wUP4_2`（17 手）と
一致する。`s=3` では **`n=5` で `δ=+1`・`n=6` で `δ=-1`** となり、
`θ(3)=6` がちょうど反転点であることが BFS の最適手順の長さでも確かめられる。
-/

theorem TUP_3_2 : TUP 3 2 = 9 := by have := TUP_cap2 (n := 3) (by omega); omega

theorem TUP_4_2 : TUP 4 2 = 17 := by have := TUP_cap2 (n := 4) (by omega); omega

example : TUP 3 2 = wUP3_2.length := by rw [TUP_3_2]; rfl

example : TUP 4 2 = wUP4_2.length := by rw [TUP_4_2]; rfl

def wUP6_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩,
  ⟨.ghost, 1⟩, ⟨.pebble, 3⟩, ⟨.ghost, 2⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.pebble, 0⟩,
  ⟨.unpebble, 4⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 3⟩,
  ⟨.pebble, 0⟩, ⟨.unpebble, 2⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]

example : Run 6 3 (sinkPebble 6) wUP6_3 allEmpty := by decide

theorem TUP_6_3 : TUP 6 3 = 19 := by
  have := TUP_eq_slope6 (s := 3) (n := 6) (by omega) (by decide) (by decide); omega

example : TUP 6 3 = wUP6_3.length := by rw [TUP_6_3]; rfl

/-- **符号の反転**: `n = 5 = θ(3)-1` では `δ = +1`、`n = 6 = θ(3)` では `δ = -1`。 -/
example : TUG 5 3 = TUP 5 3 + 1 := TUG_eq_TUP_add_one (by omega) (by omega) (by decide)

example : TUP 6 3 = TUG 6 3 + 1 := TUP_eq_TUG_add_one (by omega) (by decide) (by decide)

/-- 転記した BFS の最適手順の長さでも同じ向きに 1 だけ違う。 -/
example : wUG5_3.length = wUP5_3.length + 1 := rfl

example : wUP6_3.length = wUG6_3.length + 1 := rfl

/-! ## 上限 2 の全貌（`Cap2Exact.lean`）

`T_UG(n,2)=n²+n-4` は転記した `wUG3_2`（8 手）・`wUG4_2`（16 手）と一致する。
`n=4` は `B₄(2)-1 = 3` より先なので、定理F の範囲外でも `δ = -1` が言えている。
-/

theorem TUG_4_2' : TUG 4 2 = 16 := by have := TUG_cap2 (n := 4) (by omega); omega

example : TUG 3 2 = wUG3_2.length := by rw [TUG_3_2]; rfl

example : TUG 4 2 = wUG4_2.length := by rw [TUG_4_2']; rfl

/-- `s = 2` では `δ = -1` が `B₄(2)-1 = 3` より先でも成り立つ。 -/
example : TUP 4 2 = TUG 4 2 + 1 := TUP_eq_TUG_add_one_cap2 (by omega)

/-! ## 上限 2 では鎖の先端に届かない（上限 3 なら届く）

同じ長さ 3 の鎖で、上限 3 では 5 手の手順が在り（`wP3_3`）、上限 2 では
**どんな手順も存在しない**。片方は具体的な witness、片方は不可能性の定理。 -/

example : Run 3 3 allEmpty wP3_3 (sinkPebble 3) := by decide

example (ms : List Move) : ¬ Run 3 2 allEmpty ms (sinkPebble 3) :=
  not_run_p_cap2 (by omega)

example : ¬ (PLengths 5 2).Nonempty := PLengths_cap2_empty (by omega)

/-! ## `T(n,3) = n²-n-3`（`Bridge.lean` ＋ `Lemma48.lean`）

KSS Lemma 3.2（unghosting → pebbling、1 手挿すだけ）と `T_UG(n,2)=n²+n-4` の合成。
`Lemma48.lean` で下界も付き、**`T(n,3)=n²-n-3` は等式として層1 になった**。
上で転記した `wP4_3`（9 手）・`wP5_3`（17 手）は独立に走らせた BFS の**最適**手順で、
定理の値と一致する（BFS: `T_P(4,3)=9`・`T_P(5,3)=17`・`T_P(6,3)=27`）。
-/

theorem TP_4_3 : TP 4 3 = 9 := by have := TP_cap3 (n := 4) (by omega); omega

theorem TP_5_3 : TP 5 3 = 17 := by have := TP_cap3 (n := 5) (by omega); omega

theorem TP_6_3 : TP 6 3 = 27 := by have := TP_cap3 (n := 6) (by omega); omega

example : wP4_3.length = 9 := rfl

example : wP5_3.length = 17 := rfl

/-- 橋渡しそのもの（KSS Thm 4.11）: `T_P(4,3) = T_UG(3,2)+1 = 9`。 -/
example : TP 4 3 = TUG 3 2 + 1 := TP_eq_TUG_succ_cap3 (p := 1)

/-- **主定理と BFS の突き合わせ**: `T_P(4,3)=9`・`T_P(5,3)=17` は
転記した BFS の**最適**手順の長さそのもの。`T_P(6,3)=27` も BFS と一致する。 -/
example : TP 4 3 = wP4_3.length := by rw [TP_4_3]; rfl

example : TP 5 3 = wP5_3.length := by rw [TP_5_3]; rfl

/-! ## 定理E（任意の傾き）と、既証明の定理A・定理D の突き合わせ

`SlopeE.lean` の一般形から `m = 2, 3` を取り出すと、独立に証明してある `TUG_ge_slope4`
（定理A）・`TUG_ge_slope6`（定理D）とまったく同じ主張になる。**二重に証明したことになる。**
-/

example {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : 4 * n ≤ TUG n s + 2 * s :=
  TUG_ge_slope4_of_E hs hn

example {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : 6 * n ≤ TUG n s + s * (s + 3) :=
  TUG_ge_slope6_of_E hs hn

/-- 係数の値。`c_2(s)=2s`・`c_3(s)=s(s+3)` は厳密、`c_4(3)=38` は緩い（実測 34）。 -/
example : cc 2 5 = 10 := cc_two 5 (by omega)

example : cc 3 4 = 28 := cc_three 4 (by omega)

example : cc 4 3 = 38 := cc_four_three

/-! ## KSS Thm 4.11（一般の `s`）

`Lemma48Gen.lean` で `T_P(n+1,s+1) = T_UG(n,s)+1` が任意の `s` で層1 になった。
上限 3 の場合は `Lemma48.lean` の特化版と合わせて**2 通りに証明されている**。
-/

example {p : ℕ} : TP (p + 3) 3 = TUG (p + 2) 2 + 1 := TP_eq_TUG_succ_cap3

example {p : ℕ} : TP (p + 3) 3 = TUG (p + 2) 2 + 1 := TP_eq_TUG_succ (s := 2) (by omega)

/-- 一般版から `T_P(4,3)=9`（BFS の最適手数と一致）。 -/
example : TP 4 3 = 9 := by
  have h1 : TP 4 3 = TUG 3 2 + 1 := TP_eq_TUG_succ (p := 1) (s := 2) (by omega)
  have h2 := TUG_3_2
  omega

/-- 一般版から `T_P(5,3)=17`。 -/
example : TP 5 3 = 17 := by
  have h1 : TP 5 3 = TUG 4 2 + 1 := TP_eq_TUG_succ (p := 2) (s := 2) (by omega)
  have h2 := TUG_4_2'
  omega

/-- 傾き 4 の領域の `T_P` の厳密値（`s=3`・`n=5=θ(3)-1`）。`T_UG(5,3)=14` から 15。 -/
example : TP 6 4 = 15 := by
  have h1 : TP 6 4 = TUG 5 3 + 1 := TP_eq_TUG_succ (p := 3) (s := 3) (by omega)
  have h2 := TUG_5_3
  omega

end Spooky
