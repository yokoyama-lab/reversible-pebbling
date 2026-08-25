/-
# 上界側 — 深さ優先巡回が `2n` 手で妥当であることを `decide` で検査する

README §9 定理 1c の「$\Leftarrow$」方向（$p\ge d+1$ なら $2n$ 手で足りる）の具体例。
**下界（定理 1a、`Defs.lean`）と合わせて、これらの $n$ では最小手数が $2n$ に確定する。**

`decide` で検査する意義は 2 つある:

1. **模型が意図した規則になっているかの検査。** 定義を間違えていれば、この巡回は違法になる
2. **上界の証拠。** 手順を書き下してあるので、読み手は数えて確かめられる

⚠ `native_decide` は使わない（コンパイラを信頼に加えたくない）。
-/
import AbandonPebbling.Defs

namespace Abandon

/-! ## 完全二分 out-tree -/

/-- 完全二分 out-tree（深さ `d`、頂点数 `2^(d+1) - 1`）。根が 0、`v` の子は `2v+1, 2v+2`。 -/
def cbt (d : ℕ) : OutTree where
  n := 2 ^ (d + 1) - 1
  par := fun v => (v - 1) / 2
  par_lt := by
    intro v hv _
    omega

/-- 深さ 1（頂点 3 個）。 -/
abbrev T1 : OutTree := cbt 1
/-- 深さ 2（頂点 7 個）。 -/
abbrev T2 : OutTree := cbt 2

/-- `place v` の略記。 -/
def pl (v : ℕ) : Move := ⟨Op.place, v⟩
/-- `remove v` の略記。 -/
def rm (v : ℕ) : Move := ⟨Op.remove, v⟩

/-! ## 深さ 1: 3 頂点・2n = 6 手・ペブル 2 個 -/

/-- 深さ優先巡回（入るときに置き、出るときに外す）。 -/
def tour1 : List Move := [pl 0, pl 1, rm 1, pl 2, rm 2, rm 0]

example : tour1.length = 2 * T1.n := by decide

/-- 巡回が妥当（`p = 2 = d+1`）であることを機械で検査する。 -/
theorem tour1_run : ∃ cs, Run T1 2 tour1 cs := by
  refine ⟨(trace T1 emptyC tour1).get (by decide),
    (Option.some_get (by decide)).symm, by decide, by decide, by decide⟩

/-! ## 深さ 2: 7 頂点・2n = 14 手・ペブル 3 個 -/

def tour2 : List Move :=
  [pl 0, pl 1, pl 3, rm 3, pl 4, rm 4, rm 1, pl 2, pl 5, rm 5, pl 6, rm 6, rm 2, rm 0]

example : tour2.length = 2 * T2.n := by decide

theorem tour2_run : ∃ cs, Run T2 3 tour2 cs := by
  refine ⟨(trace T2 emptyC tour2).get (by decide),
    (Option.some_get (by decide)).symm, by decide, by decide, by decide⟩

/-! ## 陰性対照 — 定義が生きていることの確認

ペブルを 1 つ減らすと、この巡回は空間の条件を満たさない。 -/

example : ¬ ∃ cs, Run T2 2 tour2 cs := by
  rintro ⟨cs, R⟩
  have h : some cs = some ((trace T2 emptyC tour2).get (by decide)) := by
    rw [← R.traced, Option.some_get]
  have hcs : cs = (trace T2 emptyC tour2).get (by decide) := Option.some_injective _ h
  subst hcs
  exact absurd R.space (by decide)

/-- 親を置かずに子を置く手は違法（`ready` が効いていることの確認）。 -/
example : legal T2 emptyC (pl 1) = false := by decide

/-- 根は親が無いので常に置ける。 -/
example : legal T2 emptyC (pl 0) = true := by decide

end Abandon
