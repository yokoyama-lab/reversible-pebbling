/-
# 窓の上界の準備: 割った前線の内部を少ないペブルで計算し、跡を消す（紙の comp_B・clr_B）

前線（`n` 個、`SpookyTree/WindowUpperSP.lean` の割った形）がペブルで、前線より下がゴースト
（前線の部分木は `Pat scp`）のとき:
* `cB pl k n y`（紙の comp_B）: 内部が全部 `X` なら、`y` だけペブル・他の内部は全部ゴーストにする。
  外す手は全部 `ghost`（Lean の規則では無条件に打てる）。ペブル数は `n + k + 1` 以下。
* `clB k n y`（紙の clr_B）: `y` がペブル・他の内部がゴーストなら、内部を全部空にする。ペブル数は `n + k + 2` 以下。
* `rootP k n y`（紙の G 段の手 2、keep）: 内部が全部空なら、`y` だけペブル・他の内部は全部空にする。
  ペブル数は `n + k + 4` 以下（`k + 1` は `T(y)` の高さ）。
手数は `|cB| ≤ 2n − 2`、`|clB| ≤ 2nk`、`|rootP| ≤ 2n(k+1)`（紙の Λ の閉じた式より粗いが、定理 B には足りる）。
-/
import SpookyTree.WindowUpperSP

namespace SpookyTree

/-- 内部の頂点ならゴーストにする（前線なら何もしない）。 -/
def gh (n : ℕ) (z : Node) : List Move := if n ≤ 1 then [] else [⟨.ghost, z⟩]

/-- 紙の comp_B。 -/
def cB (pl : Op) : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | k + 1, n, y => if n ≤ 1 then [] else
      cB pl k ((n + 1) / 2) (y ++ [false]) ++ cB pl k (n / 2) (y ++ [true]) ++ [⟨pl, y⟩] ++
        (gh ((n + 1) / 2) (y ++ [false]) ++ gh (n / 2) (y ++ [true]))

/-- 紙の clr_B。 -/
def clB : ℕ → ℕ → Node → List Move
  | 0, _, _ => []
  | k + 1, n, y => if n ≤ 1 then [] else
      cB .unghost k ((n + 1) / 2) (y ++ [false]) ++ cB .unghost k (n / 2) (y ++ [true]) ++
        [⟨.unpebble, y⟩] ++ (clB k ((n + 1) / 2) (y ++ [false]) ++ clB k (n / 2) (y ++ [true]))

/-- 紙の G 段の手 2（keep）。`k` は子の高さ。 -/
def rootP (k n : ℕ) (y : Node) : List Move :=
  cB .pebble k ((n + 1) / 2) (y ++ [false]) ++ cB .pebble k (n / 2) (y ++ [true]) ++
    [⟨.pebble, y⟩] ++ (clB k ((n + 1) / 2) (y ++ [false]) ++ clB k (n / 2) (y ++ [true]))

theorem pw_scp {lo hi : ℕ} : ∀ j, lo ≤ j → j ≤ hi → pcPat scp j ≤ 1 := fun j _ _ => pcPat_scp_le j

theorem gh_spec {h k n : ℕ} {z : Node} {c : Config} (hk : 1 ≤ k) (hz : z.length + k = h)
    (hS : SP scp k scp n z c) :
    Runs h k z (pcSP scp k scp n) c (gh n z) ∧ SP scp k (cst .ghost) n z (run c (gh n z)) := by
  by_cases hn : n ≤ 1
  · rw [gh, if_pos hn]
    exact ⟨Runs_nil, (SP_front_A hn).mp hS⟩
  · rw [gh, if_neg hn]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [SP_int hn] at hS
    obtain ⟨hcz, h0, h1⟩ := hS
    rw [scp_shift] at h0 h1
    rw [scp_zero] at hcz
    have h0' := (SP_step_out (not_prefix_parent z false) .ghost (c := c)).mpr h0
    have h1' := (SP_step_out (not_prefix_parent z true) .ghost (c := c)).mpr h1
    refine ⟨one_spec (legal_ghost (by omega) hcz) ?_, ?_⟩
    · rw [pc_step_self, pc_of_SP _ _ _ _ h0, pc_of_SP _ _ _ _ h1, pcSP, if_neg hn, scp_shift,
        scp_zero]
      simp [result]
    · rw [run_cons, run_nil, SP_int hn, cst_shift, cst_apply]
      exact ⟨by rw [step_self]; rfl, h0', h1'⟩

/-- **comp_B の仕様.** -/
theorem cB_spec {h lo hi : ℕ} (hlo : 1 ≤ lo) {pl : Op} {X : Cell} (hpl : PlOk pl X) :
    ∀ (k n : ℕ) (y : Node) (c : Config), Shp lo hi k n → y.length + k = h →
      SP scp k (cst X) n y c →
      Runs h k y (n + k + 1) c (cB pl k n y) ∧ SP scp k scp n y (run c (cB pl k n y)) := by
  intro k
  induction k with
  | zero => intro n y c _ _ _; exact ⟨Runs_nil, by simp [SP]⟩
  | succ k ih =>
    intro n y c hS hy hP
    by_cases hn : n ≤ 1
    · have hon : cB pl (k + 1) n y = [] := by rw [cB, if_pos hn]
      rw [hon]
      exact ⟨Runs_nil, (SP_front_A hn).mp hP⟩
    · obtain ⟨hSL, hSR⟩ := hS.child hn
      have hk : 1 ≤ k := hSL.pos hlo
      have hs := half_sum n
      rw [SP_int hn] at hP
      obtain ⟨hcy, hP0, hP1⟩ := hP
      rw [cst_shift] at hP0 hP1
      rw [cst_apply] at hcy
      have hX0 : (if c y = .pebble then 1 else 0) = 0 := by rw [hcy, if_neg hpl.ne_pebble]
      -- 1. 左右の子を計算する
      obtain ⟨hR0, hQ0⟩ := ih _ _ c hSL (by simp; omega) hP0
      have a1 := pcSP_cst_le (X := X) hpl.ne_pebble pw_scp k (n / 2) hSR
      have a2 := pcSP_scp_le pw_scp hSL
      obtain ⟨hRA, hyA, hQA0, hQA1⟩ := pair_spec (P := n + (k + 1) + 1) hR0 hQ0 hP1
        (fun c' hc' => ih _ _ c' hSR (by simp; omega) hc')
        (by rw [hX0]; omega) (by rw [hX0]; omega)
      set c1 := run c (cB pl k ((n + 1) / 2) (y ++ [false]) ++ cB pl k (n / 2) (y ++ [true]))
        with hc1
      -- 2. y を置く
      have hc1y : c1 y = X := by rw [hyA, hcy]
      have hready : Ready h c1 y := ready_of (n := k) (by omega) (fun _ =>
        ⟨SP_top_peb hk hQA0 scp_zero scp_zero, SP_top_peb hk hQA1 scp_zero scp_zero⟩)
      have hlegal := legal_place hpl (by omega) hc1y hready
      have hc2y : step c1 ⟨pl, y⟩ y = .pebble := by rw [step_self, hpl.result]
      have hB0 := (SP_step_out (not_prefix_parent y false) pl (c := c1)).mpr hQA0
      have hB1 := (SP_step_out (not_prefix_parent y true) pl (c := c1)).mpr hQA1
      have b0 := pcSP_scp_le pw_scp hSL
      have b1 := pcSP_scp_le pw_scp hSR
      have hpc2 : pc (k + 1) y (step c1 ⟨pl, y⟩) ≤ n + (k + 1) + 1 := by
        rw [pc_step_self, hpl.result, if_pos rfl, pc_of_SP _ _ _ _ hQA0,
          pc_of_SP _ _ _ _ hQA1]
        omega
      -- 3. 内部の子をゴーストにする
      obtain ⟨hG0, hG0'⟩ := gh_spec (h := h) hk (by simp; omega) hB0
      have g1 := pcSP_cst_le (X := .ghost) (by decide) pw_scp k ((n + 1) / 2) hSL
      obtain ⟨hRB, hyB, hQB0, hQB1⟩ := pair_spec (P := n + (k + 1) + 1) hG0 hG0' hB1
        (fun c' hc' => gh_spec hk (by simp; omega) hc')
        (by rw [hc2y, if_pos rfl]; omega) (by rw [hc2y, if_pos rfl]; omega)
      have hc2' : run c (cB pl k ((n + 1) / 2) (y ++ [false]) ++ cB pl k (n / 2) (y ++ [true]) ++
          [⟨pl, y⟩]) = step c1 ⟨pl, y⟩ := by rw [run_append, ← hc1]; rfl
      have hcB : cB pl (k + 1) n y = cB pl k ((n + 1) / 2) (y ++ [false]) ++
          cB pl k (n / 2) (y ++ [true]) ++ [⟨pl, y⟩] ++
            (gh ((n + 1) / 2) (y ++ [false]) ++ gh (n / 2) (y ++ [true])) := by
        rw [cB, if_neg hn]
      rw [hcB]
      refine ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨hRA, ?_⟩, ?_⟩, ?_⟩
      · rw [← hc1]; exact one_spec hlegal hpc2
      · rw [hc2']; exact hRB
      · rw [run_append, hc2', SP_int hn, scp_shift, scp_zero]
        exact ⟨by rw [hyB, hc2y], hQB0, hQB1⟩

/-- **clr_B の仕様.** -/
theorem clB_spec {h lo hi : ℕ} (hlo : 1 ≤ lo) :
    ∀ (k n : ℕ) (y : Node) (c : Config), Shp lo hi k n → y.length + k = h →
      SP scp k scp n y c →
      Runs h k y (n + k + 2) c (clB k n y) ∧ SP scp k (cst .empty) n y (run c (clB k n y)) := by
  have hug : PlOk .unghost .ghost := Or.inr ⟨rfl, rfl⟩
  intro k
  induction k with
  | zero => intro n y c _ _ _; exact ⟨Runs_nil, by simp [SP]⟩
  | succ k ih =>
    intro n y c hS hy hP
    by_cases hn : n ≤ 1
    · have hon : clB (k + 1) n y = [] := by rw [clB, if_pos hn]
      rw [hon]
      exact ⟨Runs_nil, (SP_front_A hn).mp hP⟩
    · obtain ⟨hSL, hSR⟩ := hS.child hn
      have hk : 1 ≤ k := hSL.pos hlo
      have hs := half_sum n
      rw [SP_int hn] at hP
      obtain ⟨hcy, hP0, hP1⟩ := hP
      rw [scp_shift] at hP0 hP1
      rw [scp_zero] at hcy
      -- 1. 左右の子を計算し直す
      obtain ⟨hR0, hQ0⟩ := cB_spec (h := h) hlo hug k _ _ c hSL (by simp; omega) hP0
      have a1 := pcSP_cst_le (X := .ghost) (by decide) pw_scp k (n / 2) hSR
      have a2 := pcSP_scp_le pw_scp hSL
      obtain ⟨hRA, hyA, hQA0, hQA1⟩ := pair_spec (P := n + (k + 1) + 2) hR0 hQ0 hP1
        (fun c' hc' => cB_spec (h := h) hlo hug k _ _ c' hSR (by simp; omega) hc')
        (by rw [hcy, if_pos rfl]; omega) (by rw [hcy, if_pos rfl]; omega)
      set c1 := run c (cB .unghost k ((n + 1) / 2) (y ++ [false]) ++
        cB .unghost k (n / 2) (y ++ [true])) with hc1
      -- 2. y を外す
      have hc1y : c1 y = .pebble := by rw [hyA, hcy]
      have hready : Ready h c1 y := ready_of (n := k) (by omega) (fun _ =>
        ⟨SP_top_peb hk hQA0 scp_zero scp_zero, SP_top_peb hk hQA1 scp_zero scp_zero⟩)
      have hlegal := legal_unpebble (by omega) hc1y hready
      have hc2y : step c1 ⟨.unpebble, y⟩ y = .empty := by rw [step_self]; rfl
      have hB0 := (SP_step_out (not_prefix_parent y false) .unpebble (c := c1)).mpr hQA0
      have hB1 := (SP_step_out (not_prefix_parent y true) .unpebble (c := c1)).mpr hQA1
      have b0 := pcSP_scp_le pw_scp hSL
      have b1 := pcSP_scp_le pw_scp hSR
      have hpc2 : pc (k + 1) y (step c1 ⟨.unpebble, y⟩) ≤ n + (k + 1) + 2 := by
        rw [pc_step_self, pc_of_SP _ _ _ _ hQA0, pc_of_SP _ _ _ _ hQA1]
        simp only [result]
        rw [if_neg (by decide)]
        omega
      -- 3. 左右の子の内部を空にする
      obtain ⟨hG0, hG0'⟩ := ih _ _ (step c1 ⟨.unpebble, y⟩) hSL (by simp; omega) hB0
      have g1 := pcSP_cst_le (X := .empty) (by decide) pw_scp k ((n + 1) / 2) hSL
      have hE : (if step c1 ⟨.unpebble, y⟩ y = .pebble then 1 else 0) = 0 := by rw [hc2y]; rfl
      obtain ⟨hRB, hyB, hQB0, hQB1⟩ := pair_spec (P := n + (k + 1) + 2) hG0 hG0' hB1
        (fun c' hc' => ih _ _ c' hSR (by simp; omega) hc')
        (by rw [hE]; omega) (by rw [hE]; omega)
      have hc2' : run c (cB .unghost k ((n + 1) / 2) (y ++ [false]) ++
          cB .unghost k (n / 2) (y ++ [true]) ++ [⟨.unpebble, y⟩]) = step c1 ⟨.unpebble, y⟩ := by
        rw [run_append, ← hc1]; rfl
      have hcl : clB (k + 1) n y = cB .unghost k ((n + 1) / 2) (y ++ [false]) ++
          cB .unghost k (n / 2) (y ++ [true]) ++ [⟨.unpebble, y⟩] ++
            (clB k ((n + 1) / 2) (y ++ [false]) ++ clB k (n / 2) (y ++ [true])) := by
        rw [clB, if_neg hn]
      rw [hcl]
      refine ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨hRA, ?_⟩, ?_⟩, ?_⟩
      · rw [← hc1]; exact one_spec hlegal hpc2
      · rw [hc2']; exact hRB
      · rw [run_append, hc2', SP_int hn, cst_shift, cst_apply]
        exact ⟨by rw [hyB, hc2y], hQB0, hQB1⟩

/-- **G 段の手 2（keep）の仕様.** 内部が全部空・前線がペブルで下がゴーストなら、
`y` だけペブル・他の内部は空になる。 -/
theorem rootP_spec {h lo hi k n : ℕ} (hlo : 1 ≤ lo) {y : Node} {c : Config}
    (hS : Shp lo hi (k + 1) n) (hn : ¬ n ≤ 1) (hy : y.length + (k + 1) = h)
    (hP : SP scp (k + 1) (cst .empty) n y c) :
    Runs h (k + 1) y (n + k + 4) c (rootP k n y) ∧ run c (rootP k n y) y = .pebble ∧
      SP scp k (cst .empty) ((n + 1) / 2) (y ++ [false]) (run c (rootP k n y)) ∧
      SP scp k (cst .empty) (n / 2) (y ++ [true]) (run c (rootP k n y)) := by
  have hpe : PlOk .pebble .empty := Or.inl ⟨rfl, rfl⟩
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hk : 1 ≤ k := hSL.pos hlo
  have hs := half_sum n
  rw [SP_int hn] at hP
  obtain ⟨hcy, hP0, hP1⟩ := hP
  rw [cst_shift] at hP0 hP1
  rw [cst_apply] at hcy
  have hX0 : (if c y = .pebble then 1 else 0) = 0 := by rw [hcy]; rfl
  -- 1. 左右の子を計算する
  obtain ⟨hR0, hQ0⟩ := cB_spec (h := h) hlo hpe k _ _ c hSL (by simp; omega) hP0
  have a1 := pcSP_cst_le (X := .empty) (by decide) pw_scp k (n / 2) hSR
  have a2 := pcSP_scp_le pw_scp hSL
  obtain ⟨hRA, hyA, hQA0, hQA1⟩ := pair_spec (P := n + k + 4) hR0 hQ0 hP1
    (fun c' hc' => cB_spec (h := h) hlo hpe k _ _ c' hSR (by simp; omega) hc')
    (by rw [hX0]; omega) (by rw [hX0]; omega)
  set c1 := run c (cB .pebble k ((n + 1) / 2) (y ++ [false]) ++
    cB .pebble k (n / 2) (y ++ [true])) with hc1
  -- 2. y を置く
  have hc1y : c1 y = .empty := by rw [hyA, hcy]
  have hready : Ready h c1 y := ready_of (n := k) (by omega) (fun _ =>
    ⟨SP_top_peb hk hQA0 scp_zero scp_zero, SP_top_peb hk hQA1 scp_zero scp_zero⟩)
  have hlegal := legal_place hpe (by omega) hc1y hready
  have hc2y : step c1 ⟨.pebble, y⟩ y = .pebble := by rw [step_self]; rfl
  have hB0 := (SP_step_out (not_prefix_parent y false) .pebble (c := c1)).mpr hQA0
  have hB1 := (SP_step_out (not_prefix_parent y true) .pebble (c := c1)).mpr hQA1
  have b0 := pcSP_scp_le pw_scp hSL
  have b1 := pcSP_scp_le pw_scp hSR
  have hpc2 : pc (k + 1) y (step c1 ⟨.pebble, y⟩) ≤ n + k + 4 := by
    rw [pc_step_self, pc_of_SP _ _ _ _ hQA0, pc_of_SP _ _ _ _ hQA1,
      show result Op.pebble = Cell.pebble from rfl, if_pos rfl]
    omega
  -- 3. 左右の子の内部を空にする
  obtain ⟨hG0, hG0'⟩ := clB_spec (h := h) hlo k _ _ (step c1 ⟨.pebble, y⟩) hSL (by simp; omega) hB0
  have g1 := pcSP_cst_le (X := .empty) (by decide) pw_scp k ((n + 1) / 2) hSL
  obtain ⟨hRB, hyB, hQB0, hQB1⟩ := pair_spec (P := n + k + 4) hG0 hG0' hB1
    (fun c' hc' => clB_spec (h := h) hlo k _ _ c' hSR (by simp; omega) hc')
    (by rw [hc2y, if_pos rfl]; omega) (by rw [hc2y, if_pos rfl]; omega)
  have hc2' : run c (cB .pebble k ((n + 1) / 2) (y ++ [false]) ++
      cB .pebble k (n / 2) (y ++ [true]) ++ [⟨.pebble, y⟩]) = step c1 ⟨.pebble, y⟩ := by
    rw [run_append, ← hc1]; rfl
  unfold rootP
  refine ⟨Runs_append.mpr ⟨Runs_append.mpr ⟨hRA, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hc1]; exact one_spec hlegal hpc2
  · rw [hc2']; exact hRB
  · rw [run_append, hc2', hyB, hc2y]
  · rw [run_append, hc2']; exact hQB0
  · rw [run_append, hc2']; exact hQB1

/-! ## 手数 -/

theorem length_gh (n : ℕ) (z : Node) : (gh n z).length = if n ≤ 1 then 0 else 1 := by
  unfold gh; split_ifs <;> rfl

theorem length_cB (pl : Op) : ∀ (k n : ℕ) (y : Node), 1 ≤ n →
    (cB pl k n y).length + 3 ≤ 2 * n + (if n ≤ 1 then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro n y hn
    rw [show cB pl 0 n y = [] from rfl, List.length_nil]
    split_ifs <;> omega
  | succ k ih =>
    intro n y hn
    by_cases h1 : n ≤ 1
    · rw [cB, if_pos h1, if_pos h1, List.length_nil]; omega
    · rw [cB, if_neg h1, if_neg h1]
      simp only [List.length_append, List.length_singleton, length_gh]
      have a := ih ((n + 1) / 2) (y ++ [false]) (by omega)
      have b := ih (n / 2) (y ++ [true]) (by omega)
      split_ifs at a b ⊢ <;> omega

theorem length_cB_le (pl : Op) (k n : ℕ) (y : Node) (hn : 1 ≤ n) :
    (cB pl k n y).length + 2 ≤ 2 * n := by
  have := length_cB pl k n y hn
  split_ifs at this <;> omega

theorem length_clB : ∀ (k n : ℕ) (y : Node), 1 ≤ n → (clB k n y).length ≤ 2 * n * k := by
  intro k
  induction k with
  | zero => intro n y _; simp [clB]
  | succ k ih =>
    intro n y hn
    by_cases h1 : n ≤ 1
    · rw [clB, if_pos h1]; simp
    · rw [clB, if_neg h1]
      simp only [List.length_append, List.length_singleton]
      have a := length_cB_le .unghost k ((n + 1) / 2) (y ++ [false]) (by omega)
      have b := length_cB_le .unghost k (n / 2) (y ++ [true]) (by omega)
      have c := ih ((n + 1) / 2) (y ++ [false]) (by omega)
      have d := ih (n / 2) (y ++ [true]) (by omega)
      have hs := half_sum n
      have e : 2 * ((n + 1) / 2) * k + 2 * (n / 2) * k = 2 * n * k := by
        rw [← add_mul, ← mul_add, hs]
      have f : 2 * n * (k + 1) = 2 * n * k + 2 * n := by ring
      rw [f]
      omega

theorem length_rootP (k n : ℕ) (y : Node) (hn : 2 ≤ n) :
    (rootP k n y).length ≤ 2 * n * (k + 1) := by
  unfold rootP
  simp only [List.length_append, List.length_singleton]
  have a := length_cB_le .pebble k ((n + 1) / 2) (y ++ [false]) (by omega)
  have b := length_cB_le .pebble k (n / 2) (y ++ [true]) (by omega)
  have c := length_clB k ((n + 1) / 2) (y ++ [false]) (by omega)
  have d := length_clB k (n / 2) (y ++ [true]) (by omega)
  have hs := half_sum n
  have e : 2 * ((n + 1) / 2) * k + 2 * (n / 2) * k = 2 * n * k := by
    rw [← add_mul, ← mul_add, hs]
  have f : 2 * n * (k + 1) = 2 * n * k + 2 * n := by ring
  rw [f]
  omega

end SpookyTree
