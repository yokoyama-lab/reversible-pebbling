import Revgarbage.P5TreeKnill

/-! P5TreeKnill.lean の照合（有界．`native_decide` を使うので主定理の公理には入らない）。 -/
open P5Tree
-- 鎖のリポが BFS の独立な値と照合した点（RowExact の examples と同じ S）で Fc が同じ値
example : Fc 4 3 = 9 := by native_decide
example : Fc 8 4 = 25 := by native_decide
example : Fc 12 5 = 39 := by native_decide
example : Fc 16 5 = 71 := by native_decide
example : Fc 5 5 = 9 := by native_decide
-- 3 頂点の道は 2 個では終えられない（Fc 3 2 = ⊤）
example : Fc 3 2 = ⊤ := by native_decide
def pred3 : Fin 3 → Finset (Fin 3) := fun v => if v = 0 then {1} else if v = 1 then {2} else ∅
example (n : ℕ) : ¬ Pebbling pred3 ∅ ∅ {0} 2 n := by
  intro h
  have := path_Fc_le (L := [0, 1, 2]) (by decide) (by decide) (by decide) (by rfl) h
  have h3 : Fc (Fintype.card (Fin 3)) 2 = ⊤ := by native_decide
  rw [h3] at this
  exact ENat.coe_ne_top n (top_le_iff.1 this)
