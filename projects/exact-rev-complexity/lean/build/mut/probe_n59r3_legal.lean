import LevelCert
set_option autoImplicit false
namespace SplitLemma
open Finset HullLemma

def predT3p : ℕ → Finset ℕ := fun v =>
  if v = 1 then {2, 3} else if v = 2 then {4, 5} else if v = 3 then {6, 7}
  else if v = 4 then {8, 9} else if v = 5 then {10, 11}
  else if v = 6 then {12, 13} else if v = 7 then {14, 15} else ∅

def FT3p : Finset ℕ := {8, 9, 10, 11, 12, 13, 14, 15}

-- C: `synthInstance.maxSize` を上げれば 17 手でも通るか（A で 3 手は通った）
set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
example : Legal predT3p FT3p [4, 5, 2, 4, 5, 6, 7, 3, 1, 3, 4, 6, 5, 2, 4, 5, 7] ∅ := by
  simp only [Legal]
  decide

-- D: 対照 — 不正な列（最初の手で 2 を toggle。子 4,5 が未ペブル）は落ちるべき
set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
example : Legal predT3p FT3p [2, 5, 2, 4, 5, 6, 7, 3, 1, 3, 4, 6, 5, 2, 4, 5, 7] ∅ := by
  simp only [Legal]
  decide

end SplitLemma
