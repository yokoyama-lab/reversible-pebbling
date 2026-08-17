/-
# KSS Lemma 4.5 — 正準な置き方

> 頂点 `v_0..v_M` を順に置き、`v_{i+1}` を置いた**直後**に、目標の形 `g` でペブルでない
> `v_i` を落とす。

`Sweep.lean` の `sweep` は `g` のペブルが `v_M` の 1 個だけの場合にあたる。ここでは
`g` を任意の配置にして一般化する（KSS Lemma 4.5 の `I`）。落とし方は `unpebble` ではなく
**`ghost`** にしてある（`unpebble v_i` は `v_{i-1}` のペブルを要求するので打てない。
`Sweep.lean` と同じ事情で、残ったゴーストは後段が `Run_reghost` で回収する）。

* 手数: `2M+1 - |{v<M : g v = pebble}|`（`placeUpto_length`）
* ペブル: 高々 `|{v<M : g v = pebble}| + 2`（`placeUpto_spec`）
-/
import SpookyPebbling.SlopeE

namespace Spooky

/-- 正準な置き方。`v_0..v_M` を置き、`g` でペブルでない `v_i (i<M)` は落とす。 -/
def placeUpto (g : Config) : ℕ → List Move
  | 0 => [⟨Op.pebble, 0⟩]
  | (i + 1) => placeUpto g i ++
      (if g i = Cell.pebble then [⟨Op.pebble, i + 1⟩]
       else [⟨Op.pebble, i + 1⟩, ⟨Op.ghost, i⟩])

/-- `placeUpto` の終状態。 -/
def placed (g : Config) (M : ℕ) (c : Config) : Config :=
  fun v => if v = M then Cell.pebble
    else if v < M then (if g v = Cell.pebble then Cell.pebble else Cell.ghost)
    else c v

@[simp] theorem placed_at {g : Config} {M : ℕ} {c : Config} : placed g M c M = Cell.pebble := by
  unfold placed; rw [if_pos rfl]

theorem placed_below {g : Config} {M : ℕ} {c : Config} {v : ℕ} (h : v < M) :
    placed g M c v = if g v = Cell.pebble then Cell.pebble else Cell.ghost := by
  unfold placed; rw [if_neg (by omega), if_pos h]

theorem placed_above {g : Config} {M : ℕ} {c : Config} {v : ℕ} (h : M < v) :
    placed g M c v = c v := by
  unfold placed; rw [if_neg (by omega), if_neg (by omega)]

theorem placed_ne_pebble {g : Config} {M : ℕ} {c : Config} {v : ℕ} (h : v < M)
    (hg : g v ≠ Cell.pebble) : placed g M c v = Cell.ghost := by
  rw [placed_below h, if_neg hg]

theorem placeUpto_mem_le (g : Config) : ∀ (M : ℕ), ∀ m ∈ placeUpto g M, m.v ≤ M := by
  intro M
  induction M with
  | zero => intro m hm; simp [placeUpto] at hm; simp [hm]
  | succ M ih =>
      intro m hm
      rw [placeUpto] at hm
      rcases List.mem_append.mp hm with h | h
      · exact le_trans (ih m h) (by omega)
      · by_cases hg : g M = Cell.pebble
        · rw [if_pos hg] at h
          have hm' : m = ⟨Op.pebble, M + 1⟩ := by simpa using h
          subst hm'; exact Nat.le_refl _
        · rw [if_neg hg] at h
          have hm' : m = ⟨Op.pebble, M + 1⟩ ∨ m = ⟨Op.ghost, M⟩ := by simpa using h
          rcases hm' with rfl | rfl
          · exact Nat.le_refl _
          · exact Nat.le_succ _

/-- 手数 `2M+1 - |{v<M : g v = pebble}|`。 -/
theorem placeUpto_length (g : Config) : ∀ (M : ℕ),
    (placeUpto g M).length + pcount M g = 2 * M + 1 := by
  intro M
  induction M with
  | zero => simp [placeUpto, pcount]
  | succ M ih =>
      rw [placeUpto, pcount_succ]
      by_cases hg : g M = Cell.pebble
      · rw [if_pos hg, if_pos hg]; simp at ih ⊢; omega
      · rw [if_neg hg, if_neg hg]; simp at ih ⊢; omega

/-- **正準な置き方の仕様**: 妥当・終状態・全時刻のペブル数。 -/
theorem placeUpto_spec (g : Config) : ∀ (M : ℕ) (c : Config), (∀ i, i ≤ M → c i = Cell.empty) →
    valid (M + 1) c (placeUpto g M) = true ∧
    exec c (placeUpto g M) = placed g M c ∧
    (∀ d ∈ traj c (placeUpto g M), pcount (M + 1) d ≤ pcount M g + 2) := by
  intro M
  induction M with
  | zero =>
      intro c hc
      have hc0 : c 0 = Cell.empty := hc 0 le_rfl
      refine ⟨?_, ?_, ?_⟩
      · show valid 1 c [⟨Op.pebble, 0⟩] = true
        simp [valid, legal, ready, hc0]
      · funext i
        show step c ⟨Op.pebble, 0⟩ i = placed g 0 c i
        unfold placed step result
        by_cases hi : i = 0
        · subst hi; simp
        · rw [Function.update_of_ne hi, if_neg hi, if_neg (by omega)]
      · intro d hd
        have hd' : d = c ∨ d = step c ⟨Op.pebble, 0⟩ := by
          have : d ∈ traj c [(⟨Op.pebble, 0⟩ : Move)] := hd
          simpa [traj] using this
        rcases hd' with rfl | rfl
        · rw [pcount_succ, pcount]; simp [hc0]
        · rw [pcount_succ, pcount]
          have hz : step c (⟨Op.pebble, 0⟩ : Move) 0 = Cell.pebble := Function.update_self _ _ _
          rw [hz]; simp
  | succ M ih =>
      intro c hc
      obtain ⟨hv, he, hp⟩ := ih c (fun i hi => hc i (by omega))
      have hcM1 : c (M + 1) = Cell.empty := hc (M + 1) le_rfl
      have hpc : pcount (M + 1) g = pcount M g + (if g M = Cell.pebble then 1 else 0) :=
        pcount_succ M g
      -- 第 1 手: `v_{M+1}` を置く
      have hleg1 : legal (M + 2) (placed g M c) ⟨Op.pebble, M + 1⟩ = true := by
        unfold legal ready
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
        refine ⟨by omega, ?_, ?_⟩
        · rw [placed_above (by omega)]; exact hcM1
        · exact Or.inr (by simpa using placed_at (g := g) (M := M) (c := c))
      have hstep1 : step (placed g M c) ⟨Op.pebble, M + 1⟩
          = Function.update (placed g M c) (M + 1) Cell.pebble := rfl
      have hpcplaced : pcount (M + 1) (placed g M c) = pcount M g + 1 := by
        rw [pcount_succ, placed_at, if_pos rfl]
        congr 1
        unfold pcount
        refine congrArg Finset.card (Finset.filter_congr fun v hv => ?_)
        rw [placed_below (Finset.mem_range.mp hv)]
        by_cases hgv : g v = Cell.pebble <;> simp [hgv]
      refine ⟨?_, ?_, ?_⟩
      · rw [placeUpto]
        refine valid_append _ _ c (valid_mono (by omega) _ c hv) ?_
        rw [he]
        by_cases hg : g M = Cell.pebble
        · rw [if_pos hg]
          simp only [valid_cons, valid_nil, Bool.and_true]
          exact hleg1
        · rw [if_neg hg]
          simp only [valid_cons, valid_nil, Bool.and_true, Bool.and_eq_true]
          refine ⟨hleg1, ?_⟩
          unfold legal
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨by omega, ?_⟩
          rw [hstep1, Function.update_of_ne (by omega)]
          simpa using placed_at (g := g) (M := M) (c := c)
      · rw [placeUpto, exec_append, he]
        by_cases hg : g M = Cell.pebble
        · rw [if_pos hg]
          show step (placed g M c) ⟨Op.pebble, M + 1⟩ = placed g (M + 1) c
          funext i
          rw [hstep1]
          by_cases hi : i = M + 1
          · subst hi; rw [Function.update_self, placed_at]
          · rw [Function.update_of_ne hi]
            by_cases hiM : i = M
            · subst hiM
              rw [placed_at, placed_below (by omega), if_pos hg]
            · by_cases hlt : i < M
              · rw [placed_below hlt, placed_below (by omega)]
              · rw [placed_above (by omega), placed_above (by omega)]
        · rw [if_neg hg]
          show step (step (placed g M c) ⟨Op.pebble, M + 1⟩) ⟨Op.ghost, M⟩ = placed g (M + 1) c
          funext i
          show Function.update (Function.update (placed g M c) (M + 1) Cell.pebble) M Cell.ghost i
             = placed g (M + 1) c i
          by_cases hiM : i = M
          · subst hiM
            rw [Function.update_self, placed_below (by omega), if_neg hg]
          · rw [Function.update_of_ne hiM]
            by_cases hi : i = M + 1
            · subst hi; rw [Function.update_self, placed_at]
            · rw [Function.update_of_ne hi]
              by_cases hlt : i < M
              · rw [placed_below hlt, placed_below (by omega)]
              · rw [placed_above (by omega), placed_above (by omega)]
      · intro d hd
        rw [placeUpto] at hd
        have hpcg : pcount (M + 1) g = pcount M g + (if g M = Cell.pebble then 1 else 0) :=
          pcount_succ M g
        have hsame : pcount (M + 1) (Function.update (placed g M c) (M + 1) Cell.pebble)
            = pcount (M + 1) (placed g M c) :=
          pcount_congr fun w hw => (Function.update_of_ne (by omega) _ _)
        rcases traj_append_mem (placeUpto g M) c _ d hd with hd | hd
        · have hup : d (M + 1) = c (M + 1) :=
            traj_above (k := M + 1) (placeUpto g M) c
              (fun m hm => by have := placeUpto_mem_le g M m hm; omega) d hd (M + 1) (by omega)
          have hb := hp d hd
          rw [pcount_succ, hup, hcM1, if_neg (by simp)]
          omega
        · rw [he] at hd
          by_cases hg : g M = Cell.pebble
          · rw [if_pos hg] at hd hpcg
            have hd' : d = placed g M c ∨ d = step (placed g M c) ⟨Op.pebble, M + 1⟩ := by
              simpa [traj] using hd
            rcases hd' with rfl | rfl
            · rw [pcount_succ, placed_above (by omega), hcM1, if_neg (by simp), hpcplaced]
              omega
            · rw [hstep1, pcount_succ, Function.update_self, if_pos rfl, hsame, hpcplaced]
              omega
          · rw [if_neg hg] at hd hpcg
            have hd' : d = placed g M c ∨ d = step (placed g M c) ⟨Op.pebble, M + 1⟩
                ∨ d = step (step (placed g M c) ⟨Op.pebble, M + 1⟩) ⟨Op.ghost, M⟩ := by
              simpa [traj] using hd
            rcases hd' with rfl | rfl | rfl
            · rw [pcount_succ, placed_above (by omega), hcM1, if_neg (by simp), hpcplaced]
              omega
            · rw [hstep1, pcount_succ, Function.update_self, if_pos rfl, hsame, hpcplaced]
              omega
            · have h1 : step (step (placed g M c) ⟨Op.pebble, M + 1⟩) ⟨Op.ghost, M⟩ (M + 1)
                  = Cell.pebble := by
                show Function.update (step (placed g M c) ⟨Op.pebble, M + 1⟩) M Cell.ghost (M + 1)
                  = Cell.pebble
                rw [Function.update_of_ne (by omega), hstep1, Function.update_self]
              have hmp : step (placed g M c) ⟨Op.pebble, M + 1⟩ M = Cell.pebble := by
                rw [hstep1, Function.update_of_ne (by omega)]; exact placed_at
              have h2 : pcount (M + 1)
                  (step (step (placed g M c) ⟨Op.pebble, M + 1⟩) ⟨Op.ghost, M⟩) + 1
                  = pcount (M + 1) (step (placed g M c) ⟨Op.pebble, M + 1⟩) := by
                show pcount (M + 1)
                    (Function.update (step (placed g M c) ⟨Op.pebble, M + 1⟩) M Cell.ghost) + 1
                  = pcount (M + 1) (step (placed g M c) ⟨Op.pebble, M + 1⟩)
                exact pcount_update_nonpebble (by omega) hmp (by simp)
              have h3 : pcount (M + 1) (step (placed g M c) ⟨Op.pebble, M + 1⟩)
                  = pcount (M + 1) (placed g M c) := by rw [hstep1]; exact hsame
              rw [pcount_succ, h1, if_pos rfl]
              omega

end Spooky
