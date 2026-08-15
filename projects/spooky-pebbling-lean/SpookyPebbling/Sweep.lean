/-
# 掃き — `v_0` から `v_{k-1}` まで進んでペブル 1 個を残す（`2k-1` 手）

$\le$ 方向の第 1 段。空の頭 `0..k-1` から出発し、`2k-1` 手で「`v_{k-1}` だけにペブル」に
到達する。

**⚠ 紙の証明が触れていない点**: この掃きは `unpebble` では書けない。`unpebble v_i` は
`v_{i-1} ∈ P` を要求するが、掃きでは `v_{i-1}` を既に外しているからである
（`v_0` だけは前提が無いので外せる）。手数がちょうど `2k-1`（各頂点を 1 回置き、
`v_{k-1}` 以外を 1 回外す）である以上、余分な手を入れる余地は無い。したがって

> **掃きは `ghost` を使い、`v_0..v_{k-2}` にゴーストを残す。**

ゴーストは頭の手順が回収する（頭の手順はどのみち各頂点を 1 回は置くので、その
`pebble` を `unghost` に読み替えればよい。手数は変わらない）。これは `Reghost.lean`。

ペブルは同時に高々 2 個（`v_{i-1}` と `v_i`）。元の鎖では `v_{n-1}` の初期ペブルが
加わるので **3 個**になり、これが $s\ge3$ の由来である。
-/
import SpookyPebbling.Lift

namespace Spooky

/-- `v_0` から `v_{k-1}` まで掃く手順（`k ≥ 1` で `2k-1` 手）。 -/
def sweep : ℕ → List Move
  | 0 => []
  | 1 => [⟨Op.pebble, 0⟩]
  | (k + 2) => sweep (k + 1) ++ [⟨Op.pebble, k + 1⟩, ⟨Op.ghost, k⟩]

/-- 掃いた後の配置: `v_k` にペブル、`v_0..v_{k-1}` にゴースト、それ以外は元のまま。 -/
def swept (k : ℕ) (c : Config) : Config :=
  fun i => if i = k then Cell.pebble else if i < k then Cell.ghost else c i

@[simp] theorem sweep_one : sweep 1 = [⟨Op.pebble, 0⟩] := rfl

@[simp] theorem sweep_succ_succ (k : ℕ) :
    sweep (k + 2) = sweep (k + 1) ++ [⟨Op.pebble, k + 1⟩, ⟨Op.ghost, k⟩] := rfl

theorem sweep_length (k : ℕ) : (sweep (k + 1)).length = 2 * k + 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sweep_succ_succ]; simp [ih]; omega

theorem sweep_mem_le (k : ℕ) : ∀ m ∈ sweep (k + 1), m.v ≤ k := by
  induction k with
  | zero => intro m hm; simp at hm; simp [hm]
  | succ k ih =>
      intro m hm
      rw [sweep_succ_succ] at hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | rfl | rfl
      · exact le_trans (ih m hm) (by omega)
      · simp
      · simp

/-- 掃きの手はすべて `< k+1` の頂点に作用する。 -/
theorem sweep_mem_lt (k : ℕ) : ∀ m ∈ sweep (k + 1), m.v < k + 1 :=
  fun m hm => by have := sweep_mem_le k m hm; omega

theorem swept_below {k : ℕ} {c : Config} {i : ℕ} (h : i < k) : swept k c i = Cell.ghost := by
  unfold swept; rw [if_neg (by omega), if_pos h]

@[simp] theorem swept_at {k : ℕ} {c : Config} : swept k c k = Cell.pebble := by
  unfold swept; rw [if_pos rfl]

theorem swept_above {k : ℕ} {c : Config} {i : ℕ} (h : k < i) : swept k c i = c i := by
  unfold swept; rw [if_neg (by omega), if_neg (by omega)]

/-- 掃いた後の頭のペブルはちょうど 1 個。 -/
theorem pcount_swept (k : ℕ) (c : Config) : pcount (k + 1) (swept k c) = 1 := by
  classical
  unfold pcount
  have hset : (Finset.range (k + 1)).filter (fun v => swept k c v = Cell.pebble) = {k} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hp⟩
      by_contra hne
      rw [swept_below (by omega)] at hp
      exact Cell.noConfusion hp
    · rintro rfl
      exact ⟨by omega, swept_at⟩
  rw [hset]; simp

/-- **掃きの仕様**: 妥当・終状態・全時刻のペブル数。 -/
theorem sweep_spec : ∀ (k : ℕ) (c : Config), (∀ i, i ≤ k → c i = Cell.empty) →
    valid (k + 1) c (sweep (k + 1)) = true ∧
    exec c (sweep (k + 1)) = swept k c ∧
    (∀ d ∈ traj c (sweep (k + 1)), pcount (k + 1) d ≤ 2) := by
  intro k
  induction k with
  | zero =>
      intro c hc
      have hc0 : c 0 = Cell.empty := hc 0 le_rfl
      refine ⟨?_, ?_, ?_⟩
      · show valid 1 c [⟨Op.pebble, 0⟩] = true
        simp [valid, legal, ready, hc0]
      · funext i
        show step c ⟨Op.pebble, 0⟩ i = swept 0 c i
        unfold swept step result
        by_cases hi : i = 0
        · subst hi; simp
        · rw [Function.update_of_ne hi, if_neg hi, if_neg (by omega)]
      · intro d hd
        have hd' : d = c ∨ d = step c ⟨Op.pebble, 0⟩ := by
          have : d ∈ traj c [(⟨Op.pebble, 0⟩ : Move)] := hd
          simpa [traj] using this
        rcases hd' with rfl | rfl
        · rw [pcount_succ, pcount]
          simp [hc0]
        · rw [pcount_succ, pcount]
          have hz : step c (⟨Op.pebble, 0⟩ : Move) 0 = Cell.pebble := Function.update_self _ _ _
          rw [hz]
          simp
  | succ k ih =>
      intro c hc
      obtain ⟨hv, he, hp⟩ := ih c (fun i hi => hc i (by omega))
      have hck1 : c (k + 1) = Cell.empty := hc (k + 1) le_rfl
      -- 掃きの続き 2 手
      have hleg1 : legal (k + 2) (swept k c) ⟨Op.pebble, k + 1⟩ = true := by
        unfold legal ready
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
        refine ⟨by omega, ?_, ?_⟩
        · rw [swept_above (by omega)]; exact hck1
        · exact Or.inr (by simpa using swept_at)
      have hstep1 : step (swept k c) ⟨Op.pebble, k + 1⟩
          = Function.update (swept k c) (k + 1) Cell.pebble := rfl
      have hleg2 : legal (k + 2) (step (swept k c) ⟨Op.pebble, k + 1⟩) ⟨Op.ghost, k⟩ = true := by
        unfold legal
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rw [hstep1, Function.update_of_ne (by omega)]
        simpa using swept_at
      have hfinal : step (step (swept k c) ⟨Op.pebble, k + 1⟩) ⟨Op.ghost, k⟩ = swept (k + 1) c := by
        funext i
        show Function.update (Function.update (swept k c) (k + 1) Cell.pebble) k Cell.ghost i
           = swept (k + 1) c i
        by_cases hik : i = k
        · subst hik
          rw [Function.update_self]
          rw [swept_below (by omega)]
        · rw [Function.update_of_ne hik]
          by_cases hik1 : i = k + 1
          · subst hik1
            rw [Function.update_self, swept_at]
          · rw [Function.update_of_ne hik1]
            unfold swept
            by_cases hlt : i < k
            · rw [if_neg hik, if_pos hlt, if_neg hik1, if_pos (by omega)]
            · rw [if_neg hik, if_neg hlt, if_neg hik1, if_neg (by omega)]
      refine ⟨?_, ?_, ?_⟩
      · rw [sweep_succ_succ]
        refine valid_append _ _ c (valid_mono (by omega) _ c hv) ?_
        rw [he]
        simp only [valid_cons, valid_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨hleg1, hleg2⟩
      · rw [sweep_succ_succ, exec_append, he]
        exact hfinal
      · intro d hd
        rw [sweep_succ_succ] at hd
        rcases traj_append_mem (sweep (k + 1)) c _ d hd with hd | hd
        · -- 前半: IH と「k+1 に触っていない」から
          have hup : d (k + 1) = c (k + 1) :=
            traj_above (sweep (k + 1)) c (sweep_mem_lt k) d hd (k + 1) (by omega)
          rw [pcount_succ, hup, hck1]
          simpa using hp d hd
        · rw [he] at hd
          have hd' : d = swept k c ∨ d = step (swept k c) ⟨Op.pebble, k + 1⟩
              ∨ d = step (step (swept k c) ⟨Op.pebble, k + 1⟩) ⟨Op.ghost, k⟩ := by
            simpa [traj] using hd
          rcases hd' with rfl | rfl | rfl
          · rw [pcount_succ, swept_above (by omega), hck1]
            simp [pcount_swept]
          · rw [hstep1, pcount_succ]
            have hc2 : pcount (k + 1) (Function.update (swept k c) (k + 1) Cell.pebble)
                = pcount (k + 1) (swept k c) :=
              pcount_congr (fun v hv => (Function.update_of_ne (by omega) _ _))
            have hval : Function.update (swept k c) (k + 1) Cell.pebble (k + 1) = Cell.pebble :=
              Function.update_self _ _ _
            rw [hc2, hval, pcount_swept]
            simp
          · rw [hfinal, pcount_swept]
            omega

end Spooky
