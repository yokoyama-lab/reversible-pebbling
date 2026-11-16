import lean.XLiftGrid

/-!
# XLift の格子の証明書指数 `lvd`（m48 `build_grid()` の第 2 成分の Lean 版）

`scripts/probe_brw/m48_exact_replay.py` の `build_grid()` は格子 `gv` と並べて
`lvd[i]`（疎な点では `Fraction(n, R)`、`gv[i] ≤ 2^{n/R}`、密な点では `None`）を返す。
Ψ ≤ X の比較（設計書 §7、(d)）で `staggered_check` が使う証明書である。

* `buildGridLvd dense B k topoct` は `XLiftGrid.buildGrid` と同じ走査で、点を足すたびに
  分子 `n = q·R + j`（`R = 2^k`）を `some n` で並べる。密な点は `none`。
* `lvdCert k g lv`: 疎な点ごとに `g[i]^R ≤ 2^n`（＝ `g[i] ≤ 2^{n/R}`、m48 の docstring の主張）。
* `lvdTight k g lv`: 疎な点ごとに `2^(n-1) < g[i]^R`（証明書が 1/R オクターブ以内で鋭い）。
  これが無いと、指数を上にずらした証明書（健全だが緩い）を見逃す。

## 何が一般で、何が有界か

* `tiny_lvd` は `decide +kernel`（カーネル評価。公理を足さない）。
* `prod_*` は **有界な機械検査**で、一般の証明ではない（`native_decide`、
  `#print axioms` に `…_native.native_decide.ax_*` が出る）。
* 「BEGIN GENERATED」行から「END GENERATED」行までは
  `scripts/probe_brw/m81_xlift_lvd_lean.py --regen` が m48 から書き直す。手で編集しない。
-/

namespace RevPebbling.XLiftLvd

open RevPebbling.XLiftGrid

/-- m48 `build_grid(topoct)` の `(gv, lvd)`。`lvd` は分子 `n`（`lvd = n / 2^k`）、密な点は `none`。 -/
def buildGridLvd (dense B k topoct : Nat) : Array Nat × Array (Option Nat) :=
  let T := tableT B k
  let q0 := dense.log2
  let init : Array Nat × Array (Option Nat) :=
    ((List.range dense).toArray.map (· + 1), Array.replicate dense none)
  (List.range (topoct - q0)).foldl (fun acc qi =>
    let q := q0 + qi
    (List.range (2 ^ k)).foldl (fun acc j =>
      let g := (T.getD j 0 <<< q) >>> B
      if acc.1.back?.getD 0 < g then (acc.1.push g, acc.2.push (some (q * 2 ^ k + j))) else acc)
      acc) init

/-- 疎な点ごとに `g[i]^(2^k) ≤ 2^n`。長さの一致も見る。 -/
def lvdCert (k : Nat) (g : Array Nat) (lv : Array (Option Nat)) : Bool :=
  g.size == lv.size &&
  (List.range g.size).all fun i =>
    match lv.getD i none with
    | none => true
    | some n => g.getD i 0 ^ (2 ^ k) ≤ 2 ^ n

/-- 疎な点ごとに `2^(n-1) < g[i]^(2^k)`（証明書が 1/R 以内で鋭い）。 -/
def lvdTight (k : Nat) (g : Array Nat) (lv : Array (Option Nat)) : Bool :=
  (List.range g.size).all fun i =>
    match lv.getD i none with
    | none => true
    | some n => 2 ^ (n - 1) < g.getD i 0 ^ (2 ^ k)

/-- 証明書の要約: 疎な点の個数・分子の総和・法 `2^61 - 1` の多項式ハッシュ・最後の分子。
密な点は 0 として畳む（m81 の `lvd_digest` と同じ式）。 -/
def lvdDigest (lv : Array (Option Nat)) : Nat × Nat × Nat × Nat :=
  (lv.foldl (fun c o => if o.isSome then c + 1 else c) 0,
   lv.foldl (fun s o => s + o.getD 0) 0,
   lv.foldl (fun h o => (h * 1000003 + o.getD 0) % (2 ^ 61 - 1)) 0,
   (lv.back?.getD none).getD 0)

-- BEGIN GENERATED (m81 --regen)
/-- 小さな格子（dense=4, R=4, topoct=5）の (gv, lvd 分子)。 -/
theorem tiny_lvd : buildGridLvd 4 128 2 5 =
    (#[1,2,3,4,5,6,8,9,11,13,16,19,22,26],
     #[none,none,none,none,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19]) := by decide +kernel
/-- 本番（dense=4096, R=2048, topoct=122）。格子は m80 の buildGrid と同じ。 -/
theorem prod_same_grid : (buildGridLvd 4096 128 11 122).1 == buildGrid 4096 128 11 122 := by native_decide
theorem prod_lvd_digest : lvdDigest (buildGridLvd 4096 128 11 122).2 = (225279, 30911883264, 1107473709722387769, 249855) := by native_decide
theorem prod_lvd_cert : lvdCert 11 (buildGridLvd 4096 128 11 122).1 (buildGridLvd 4096 128 11 122).2 = true := by native_decide
theorem prod_lvd_tight : lvdTight 11 (buildGridLvd 4096 128 11 122).1 (buildGridLvd 4096 128 11 122).2 = true := by native_decide
-- END GENERATED

end RevPebbling.XLiftLvd

#print axioms RevPebbling.XLiftLvd.tiny_lvd
#print axioms RevPebbling.XLiftLvd.prod_same_grid
#print axioms RevPebbling.XLiftLvd.prod_lvd_digest
#print axioms RevPebbling.XLiftLvd.prod_lvd_cert
#print axioms RevPebbling.XLiftLvd.prod_lvd_tight
