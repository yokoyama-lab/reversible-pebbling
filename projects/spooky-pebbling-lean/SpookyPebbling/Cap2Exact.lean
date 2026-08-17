/-
# 上限 2 の全貌 — `T_UG(n,2) = n²+n-4`、そして「上限 2 では鎖の先端に**到達できない**」

`Cap2.lean` の `T_UP(n,2)=n²+n-3` から、$s=2$ の行が全部埋まる。

* **`T_UG(n,2) = n²+n-4`（`n ≥ 3`）** — Cor 4.12（`Unghost.lean`）に `k=n-1` が強制される
  （尻尾の上限が 1 なので `not_run_ug_cap_one`）。上下とも同じ 1 本で出る:
  $2(n-1)-1 + T_{UP}(n-1,2) + T_{UG}(1,1) = (2n-3) + (n^2-n-3) + 2 = n^2+n-4$。
* **`δ = -1` が `s=2` では全ての `n ≥ 3` で成り立つ** — 定理F は $n\le B_4(s)-1$ までしか
  言わないが、$s=2$ では閉形式が両方あるので範囲の制限が要らない。
* **`Run n 2 allEmpty ms (sinkPebble n)` は `n ≥ 3` で存在しない**（KSS Cor 4.7 の $\infty$ 条項）。

## 到達不能性の証明（不変条件 1 本）

> **`v_{n-1}` がペブルなら `v_{n-2}` は空でない。**

始状態 `allEmpty` では前件が偽なので成立。1 手ごとに保たれる:

* `v_{n-1}` をペブルにする手（`pebble` / `unghost`）は `ready`、すなわち **`v_{n-2}` の
  ペブル**を要求するので、直後も `v_{n-2}` は空でない
* `v_{n-2}` を空にする手は `unpebble` だけで、これは `v_{n-3}` のペブルを要求する。
  `v_{n-1}` がペブルなら `v_{n-3}, v_{n-2}, v_{n-1}` の **3 個**になり上限 2 を超える
  （`v_{n-2}` がゴーストの間は空にできない。ゴーストから出る手は `unghost` だけで、
  行き先はペブルであって空ではない）

ところが終状態 `sinkPebble n` は `v_{n-1}` がペブルで `v_{n-2}` が空。**矛盾**。∎
-/
import SpookyPebbling.Sign

namespace Spooky

/-! ## `T_UG(n,2) = n²+n-4` -/

theorem TUG_cap2 {n : ℕ} (hn : 3 ≤ n) : TUG n 2 + 4 = n * n + n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have hexp : (j + 3) * (j + 3) + (j + 3) = (j + 2) * (j + 2) + (j + 2) + 2 * (j + 3) := by ring
  have hup : TUP (j + 2) 2 + 3 = (j + 2) * (j + 2) + (j + 2) := TUP_cap2 (by omega)
  have hone : TUG 1 (2 - 1) = 2 := TUG_eq_of_le' (by omega) (by omega)
  have hnk : j + 3 - (j + 2) = 1 := by omega
  have hne : (UGLengths (j + 3 - (j + 2)) (2 - 1)).Nonempty := by
    rw [hnk]; exact ⟨2, _, rfl, run_ug_one le_rfl⟩
  -- 上界: `k = n-1` を選ぶ
  have hle := decomp_ug_le (n := j + 3) (s := 2) (k := j + 2) le_rfl (by omega) (by omega) hne
  rw [hnk] at hle
  -- 下界: `k = n-1` が強制される
  obtain ⟨ms, hlen, hrun⟩ :=
    Nat.sInf_mem (UGLengths_nonempty (n := j + 3) (s := 2) le_rfl (by omega))
  obtain ⟨k, hk, hkn, hbound, msT, hrunT⟩ := decomp_ug_ge' (by omega) hrun
  have hnk1 : j + 3 - k ≤ 1 := by
    by_contra hc
    exact not_run_ug_cap_one (by omega) hrunT
  have hkeq : k = j + 2 := by omega
  rw [hkeq, hnk] at hbound
  have hlen' : ms.length = TUG (j + 3) 2 := hlen
  omega

/-- **`s = 2` では `δ = -1` が全ての `n ≥ 3` で成り立つ**（定理F の範囲制限が要らない）。 -/
theorem TUP_eq_TUG_add_one_cap2 {n : ℕ} (hn : 3 ≤ n) : TUP n 2 = TUG n 2 + 1 := by
  have h1 := TUP_cap2 (n := n) (by omega)
  have h2 := TUG_cap2 hn
  omega

/-! ## 上限 2 では鎖の先端に到達できない（KSS Cor 4.7 の `∞` 条項） -/

/-- **不変条件**: `v_{n-1}` がペブルなら `v_{n-2}` は空でない。 -/
theorem sink_pred_ne_empty {n : ℕ} (hn : 3 ≤ n) : ∀ (l : List Move) (c : Config),
    valid n c l = true → (∀ d ∈ traj c l, pcount n d ≤ 2) →
    (c (n - 1) = Cell.pebble → c (n - 2) ≠ Cell.empty) →
    exec c l (n - 1) = Cell.pebble → exec c l (n - 2) ≠ Cell.empty := by
  intro l
  induction l with
  | nil => intro c _ _ hinv hp; exact hinv hp
  | cons a l ih =>
      intro c hv hcap hinv hp
      rw [valid_cons] at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨hleg, hrest⟩ := hv
      have hlt : a.v < n := legal_lt hleg
      have hlegm := Bool.and_elim_right (by unfold legal at hleg; exact hleg)
      have hcap' : ∀ d ∈ traj (step c a) l, pcount n d ≤ 2 := by
        intro d hd
        exact hcap d (by rw [traj_cons]; simp [hd])
      have hinv' : step c a (n - 1) = Cell.pebble → step c a (n - 2) ≠ Cell.empty := by
        intro hpb hemp
        by_cases h1 : a.v = n - 1
        · -- `v_{n-1}` をペブルにする手は `ready`＝`v_{n-2}` のペブルを要求する
          have hcm2 : c (n - 2) = Cell.empty := by
            rw [← step_ne_of_ne (c := c) (m := a) (i := n - 2) (by omega)]
            exact hemp
          have hres : result a.op = Cell.pebble := by
            rw [← step_self c a, h1]; exact hpb
          have hrd : ready c a.v = true := by
            cases hop : a.op with
            | pebble => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
            | unghost => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
            | unpebble => rw [hop] at hres; exact absurd hres (by simp [result])
            | ghost => rw [hop] at hres; exact absurd hres (by simp [result])
          unfold ready at hrd
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hrd
          rcases hrd with h0 | hpre
          · omega
          · rw [h1, show n - 1 - 1 = n - 2 by omega, hcm2] at hpre
            exact Cell.noConfusion hpre
        · by_cases h2 : a.v = n - 2
          · -- `v_{n-2}` を空にできるのは `unpebble` だけ。3 個目が要る
            have hres : result a.op = Cell.empty := by
              rw [← step_self c a, h2]; exact hemp
            have hun : a.op = Op.unpebble := by
              cases hop : a.op with
              | pebble => rw [hop] at hres; exact absurd hres (by simp [result])
              | unghost => rw [hop] at hres; exact absurd hres (by simp [result])
              | ghost => rw [hop] at hres; exact absurd hres (by simp [result])
              | unpebble => rfl
            rw [hun] at hlegm
            have hcv : c a.v = Cell.pebble := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hrd : ready c a.v = true := Bool.and_elim_right hlegm
            unfold ready at hrd
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hrd
            have hpb' : c (n - 1) = Cell.pebble := by
              rw [← step_ne_of_ne (c := c) (m := a) (i := n - 1) (by omega)]
              exact hpb
            rcases hrd with h0 | hpre
            · omega
            · rw [h2, show n - 2 - 1 = n - 3 by omega] at hpre
              rw [h2] at hcv
              have h3 := three_le_pcount (n := n) (c := c) (a := n - 3) (b := n - 2) (e := n - 1)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                hpre hcv hpb'
              have := hcap c (by rw [traj_cons]; simp)
              omega
          · -- どちらでもない手は 2 つの成分を変えない
            refine hinv ?_ ?_
            · rw [← step_ne_of_ne (c := c) (m := a) (i := n - 1) h1]; exact hpb
            · rw [← step_ne_of_ne (c := c) (m := a) (i := n - 2) h2]; exact hemp
      exact ih (step c a) hrest hcap' hinv' hp

/-- **KSS Cor 4.7 の `∞` 条項**: 上限 2 では長さ 3 以上の鎖の先端にペブルを置けない。 -/
theorem not_run_p_cap2 {n : ℕ} (hn : 3 ≤ n) {ms : List Move} :
    ¬ Run n 2 allEmpty ms (sinkPebble n) := by
  intro h
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, hcap⟩ := (ok_iff ms allEmpty).mp hok
  have hp : exec allEmpty ms (n - 1) = Cell.pebble := by
    rw [hagree (n - 1) (by omega), sinkPebble_apply, if_pos rfl]
  have hemp : exec allEmpty ms (n - 2) = Cell.empty := by
    rw [hagree (n - 2) (by omega), sinkPebble_apply, if_neg (by omega)]
  have hinv0 : allEmpty (n - 1) = Cell.pebble → allEmpty (n - 2) ≠ Cell.empty := by
    intro hpb
    exact absurd hpb (by simp [allEmpty])
  exact sink_pred_ne_empty hn ms allEmpty hv hcap hinv0 hp hemp

/-- `PLengths n 2` は `n ≥ 3` で空（`T_P(n,2) = ∞`）。 -/
theorem PLengths_cap2_empty {n : ℕ} (hn : 3 ≤ n) : ¬ (PLengths n 2).Nonempty := by
  rintro ⟨L, ms, _, hrun⟩
  exact not_run_p_cap2 hn hrun

end Spooky
