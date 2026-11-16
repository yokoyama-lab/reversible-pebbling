/-!
# XLift の格子 `buildGrid`（m48 `build_grid()` の Lean 版）

`scripts/probe_brw/m48_exact_replay.py` の `grid_tables()` と `build_grid()` を写す。
本番の格子（`GRID_DENSE = 4096`・`GRID_R = 2048`・`GRID_B = 128`・`topoct = 122`、
229,375 点）を Lean の中で作れるようにし、`XLiftGen.genTwoPtr` の本番実行に
巨大な配列リテラルを持ち込まずに済ませる。

* 格子は健全性には効かない（`XLiftBase.liftChain_le_count` は任意の格子で成り立つ）。
  ここで固定するのは **m48 と同じ格子であること** だけで、値の突き合わせのための同一化である。
* `tableT B k` は `grid_tables`（`R = 2^k`）。`t1 = isqrt^k (2^(B·R+1))` を Newton 法
  `sqrtIter`（上からの反復、燃料つき）で出し、`T[j] = (T[j-1]·t1) >>> B`。
* `buildGrid dense B k topoct` は `build_grid`。`1..dense` の後に、`q = log2 dense .. topoct-1`、
  `j = 0..R-1` の `(T[j] <<< q) >>> B` を、直前の点より大きいときだけ足す。
* `lvd`（各点の水準 `n/R`）はまだ写していない（Ψ ≤ X の比較で要る。設計書 §13）。

## 何が一般で、何が有界か

* `tiny_grid` は `decide +kernel`（カーネル評価。公理を足さない）。
* `medium_digest`・`prod_digest`・`medium_strict`・`prod_strict` は **有界な機械検査**で、
  一般の証明ではない（`native_decide`、`#print axioms` に `…_native.native_decide.ax_*` が出る）。
* 「BEGIN GENERATED」行から「END GENERATED」行までは
  `scripts/probe_brw/m80_xlift_grid_lean.py --regen` が m48 から書き直す。手で編集しない。
-/

namespace RevPebbling.XLiftGrid

/-- Newton 法（上から）。`x ≥ ⌊√n⌋` から始めれば `⌊√n⌋` で止まる。燃料 `f`。 -/
def sqrtIter : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then sqrtIter f n y else x

/-- `n < 2^e` のときの `⌊√n⌋`（初期値 `2^(e/2+1) > √n`）。 -/
def isqrtE (n e : Nat) : Nat := sqrtIter (e + 2) n (2 ^ (e / 2 + 1))

/-- `isqrt` を `k` 回。`e` は `t < 2^e` を保つ指数。 -/
def rootChain : Nat → Nat → Nat → Nat
  | 0, t, _ => t
  | k + 1, t, e => rootChain k (isqrtE t e) (e / 2 + 1)

/-- m48 `grid_tables()`（`GRID_R = 2^k`、`GRID_B = B`）。 -/
def tableT (B k : Nat) : Array Nat :=
  let R := 2 ^ k
  let t1 := rootChain k (2 ^ (B * R + 1)) (B * R + 2)
  (List.range (R - 1)).foldl (fun acc _ => acc.push ((acc.back?.getD 0 * t1) >>> B)) #[2 ^ B]

/-- m48 `build_grid(topoct)`（`GRID_DENSE = dense`）。 -/
def buildGrid (dense B k topoct : Nat) : Array Nat :=
  let T := tableT B k
  let q0 := dense.log2
  let init : Array Nat := (List.range dense).toArray.map (· + 1)
  (List.range (topoct - q0)).foldl (fun acc qi =>
    let q := q0 + qi
    (List.range (2 ^ k)).foldl (fun acc j =>
      let g := (T.getD j 0 <<< q) >>> B
      if acc.back?.getD 0 < g then acc.push g else acc) acc) init

/-- 狭義昇順（`bisect_right` を使う生成器の前提）。 -/
def strictInc (g : Array Nat) : Bool :=
  (List.range (g.size - 1)).all fun i => g.getD i 0 < g.getD (i + 1) 0

/-- 法 `2^61 - 1` の多項式ハッシュ（m80 の `digest` と同じ式）。 -/
def hashMod (g : Array Nat) : Nat :=
  g.foldl (fun h x => (h * 1000003 + x) % (2 ^ 61 - 1)) 0

/-- 点数・総和・ハッシュ・最上端。 -/
def digest (g : Array Nat) : Nat × Nat × Nat × Nat :=
  (g.size, g.foldl (· + ·) 0, hashMod g, g.back?.getD 0)

-- BEGIN GENERATED (m80 --regen)
/-- 小さな格子（dense=4, R=4, topoct=5）。 -/
theorem tiny_grid : buildGrid 4 128 2 5 = #[1,2,3,4,5,6,8,9,11,13,16,19,22,26] := by decide +kernel
/-- 中規模（m79 の gM と同じ。dense=256, R=64, topoct=48）。 -/
theorem medium_digest : digest (buildGrid 256 128 6 48) = (2815, 25848799946511335, 822077843633307153, 278442931975302) := by native_decide
theorem medium_strict : strictInc (buildGrid 256 128 6 48) = true := by native_decide
/-- 本番（dense=4096, R=2048, topoct=122、229375 点）。 -/
theorem prod_digest : digest (buildGrid 4096 128 11 122) = (229375, 15706899558249333657663059224423946549650, 1836512282775048188, 5315112774664524918037284934037416181) := by native_decide
theorem prod_strict : strictInc (buildGrid 4096 128 11 122) = true := by native_decide
-- END GENERATED

end RevPebbling.XLiftGrid

#print axioms RevPebbling.XLiftGrid.tiny_grid
#print axioms RevPebbling.XLiftGrid.medium_digest
#print axioms RevPebbling.XLiftGrid.medium_strict
#print axioms RevPebbling.XLiftGrid.prod_digest
#print axioms RevPebbling.XLiftGrid.prod_strict
