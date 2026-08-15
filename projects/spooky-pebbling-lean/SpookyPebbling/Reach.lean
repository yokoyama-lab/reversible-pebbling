/-
# 到達可能性 — ペブル 2 個あれば、どんな長さの鎖も片付く

`TUP` は `sInf` で定義しているので、**手順が 1 本も無いと `sInf ∅ = 0`** になり、
下界としては嘘の値を返す。そのため `decomp_le` / `decomp_exact` は右辺に現れる量の
実現可能性を仮定に置いていた。ここでそれを外す。

> **`(UPLengths n 2).Nonempty`（$n\ge1$）。上限は単調なので $s\ge2$ でも同じ。**

構成は $n$ についての帰納法で、`Sweep.lean` と `Reghost.lean` をそのまま使う:

1. `ghost v_{n-1}` — 終端のペブルを先に測定して枠を空ける（**これをしないと掃きで
   3 個必要になる**）
2. `sweep (n-1)` — `v_0..v_{n-2}` を掃いて `v_{n-2}` にペブル 1 個（ペブルは高々 2）
3. `unghost v_{n-1}`, `unpebble v_{n-1}` — ここだけ 2 個
4. 長さ `n-1` の鎖の手順（帰納法の仮定）を、掃きが残したゴースト向けに読み替える
   （`Run_reghost`）

手数は `1 + (2(n-1)-1) + 2 + T_{UP}(n-1,2) = 2n + T_{UP}(n-1,2)` で、
$T_{UP}(n,2)=n^2+n-3$ の階差 `2n` と一致する（＝この構成は最適）。
ただしここで要るのは**存在**だけなので手数は主張しない。
-/
import SpookyPebbling.Reghost
import SpookyPebbling.Parity

namespace Spooky

/-- 上限は緩める方向に単調。 -/
theorem ok_cap_mono {n s s' : ℕ} (hs : s ≤ s') : ∀ (ms : List Move) (c : Config),
    ok n s c ms = true → ok n s' c ms = true := by
  intro ms
  induction ms with
  | nil =>
      intro c h
      unfold ok at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      omega
  | cons m ms ih =>
      intro c h
      unfold ok at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨⟨by omega, h.1.2⟩, ih (step c m) h.2⟩

/-- 長さ 1 の鎖は 1 手で片付く。 -/
theorem run_one {s : ℕ} (hs : 1 ≤ s) :
    Run 1 s (sinkPebble 1) [⟨Op.unpebble, 0⟩] allEmpty := by
  have hcell : sinkPebble 1 0 = Cell.pebble := by rw [sinkPebble_apply]; simp
  have hstep : step (sinkPebble 1) (⟨Op.unpebble, 0⟩ : Move) 0 = Cell.empty :=
    Function.update_self _ _ _
  constructor
  · unfold ok
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [pcount_sinkPebble (by omega)]; exact hs
    · unfold legal ready
      simp [hcell]
    · unfold ok
      simp only [decide_eq_true_eq]
      have : pcount 1 (step (sinkPebble 1) (⟨Op.unpebble, 0⟩ : Move)) = 0 := by
        refine pcount_eq_zero_iff.mpr ?_
        intro v hv
        rw [show v = 0 by omega, hstep]
        simp
      omega
  · intro v hv
    rw [show v = 0 by omega]
    show step (sinkPebble 1) (⟨Op.unpebble, 0⟩ : Move) 0 = allEmpty 0
    rw [hstep]; rfl

/-- **帰納段**: 長さ `j+1` の鎖の手順から、長さ `j+2` の鎖の手順を作る（上限 2）。 -/
theorem run_cap2_step {j : ℕ} {msH : List Move}
    (hH : Run (j + 1) 2 (sinkPebble (j + 1)) msH allEmpty) :
    ∃ ms : List Move, Run (j + 2) 2 (sinkPebble (j + 2)) ms allEmpty := by
  classical
  obtain ⟨hokH, hagreeH⟩ := hH
  -- 第 1 手: 終端を測定して枠を空ける
  have hsink : sinkPebble (j + 2) (j + 1) = Cell.pebble := by
    rw [sinkPebble_apply]; simp
  set c₁ := step (sinkPebble (j + 2)) (⟨Op.ghost, j + 1⟩ : Move) with hc₁def
  have hc₁at : c₁ (j + 1) = Cell.ghost := Function.update_self _ _ _
  have hc₁off : ∀ v, v ≠ j + 1 → c₁ v = sinkPebble (j + 2) v := by
    intro v hv
    show Function.update (sinkPebble (j + 2)) (j + 1) (result Op.ghost) v = _
    exact Function.update_of_ne hv _ _
  have hc₁below : ∀ i, i ≤ j → c₁ i = Cell.empty := by
    intro i hi
    rw [hc₁off i (by omega), sinkPebble_apply, if_neg (by omega)]
  have hc₁above : ∀ v, j + 2 ≤ v → c₁ v = Cell.empty := by
    intro v hv
    rw [hc₁off v (by omega), sinkPebble_apply, if_neg (by omega)]
  -- 第 2 段: 掃き
  obtain ⟨hsv, hse, hsp⟩ := sweep_spec j c₁ hc₁below
  set c₂ := swept j c₁ with hc₂def
  have hc₂at : c₂ j = Cell.pebble := swept_at
  have hc₂ghost : ∀ v, v < j → c₂ v = Cell.ghost := fun v hv => swept_below hv
  have hc₂top : c₂ (j + 1) = Cell.ghost := by rw [hc₂def, swept_above (by omega)]; exact hc₁at
  have hc₂above : ∀ v, j + 2 ≤ v → c₂ v = Cell.empty := by
    intro v hv; rw [hc₂def, swept_above (by omega)]; exact hc₁above v hv
  have hc₂count : pcount (j + 1) c₂ = 1 := pcount_swept j c₁
  -- 第 3 段: 終端を戻して外す
  set c₃ := step c₂ (⟨Op.unghost, j + 1⟩ : Move) with hc₃def
  set H := step c₃ (⟨Op.unpebble, j + 1⟩ : Move) with hHdef
  have hc₃off : ∀ v, v ≠ j + 1 → c₃ v = c₂ v := by
    intro v hv
    show Function.update c₂ (j + 1) (result Op.unghost) v = _
    exact Function.update_of_ne hv _ _
  have hHoff : ∀ v, v ≠ j + 1 → H v = c₃ v := by
    intro v hv
    show Function.update c₃ (j + 1) (result Op.unpebble) v = _
    exact Function.update_of_ne hv _ _
  have hc₃low : ∀ v, v < j + 1 → c₃ v = c₂ v := fun v hv => hc₃off v (by omega)
  have hHlow : ∀ v, v < j + 1 → H v = c₂ v := by
    intro v hv
    rw [hHoff v (by omega)]
    exact hc₃low v hv
  have hHtop : H (j + 1) = Cell.empty := Function.update_self _ _ _
  have hHabove : ∀ v, j + 2 ≤ v → H v = Cell.empty := by
    intro v hv
    rw [hHoff v (by omega), hc₃off v (by omega)]
    exact hc₂above v hv
  -- 第 4 段: 頭の手順をゴースト向けに読み替える
  have hdom : Dom2 msH H (sinkPebble (j + 1)) := by
    intro v
    by_cases hvj : v < j
    · right
      refine ⟨by rw [hHlow v (by omega)]; exact hc₂ghost v hvj, ?_, ?_⟩
      · rw [sinkPebble_apply, if_neg (by omega)]
      · exact head_places ⟨hokH, hagreeH⟩ v (by omega)
    · left
      by_cases hvj2 : v = j
      · rw [hvj2, hHlow j (by omega), hc₂at, sinkPebble_apply, if_pos (by omega)]
      · rw [sinkPebble_apply, if_neg (by omega)]
        by_cases hv2 : v = j + 1
        · rw [hv2, hHtop]
        · exact hHabove v (by omega)
  obtain ⟨hrunH', hlenH'⟩ := Run_reghost hdom ⟨hokH, hagreeH⟩
  obtain ⟨hokH', hagreeH'⟩ := hrunH'
  obtain ⟨hvH', hcapH'⟩ := (ok_iff (strip2 H msH) H).mp hokH'
  have hstriplt : ∀ m ∈ strip2 H msH, m.v < j + 1 := fun m hm => valid_lt _ _ hvH' m hm
  -- 各段の終状態に名前を付ける
  have hex1 : exec (sinkPebble (j + 2)) [(⟨Op.ghost, j + 1⟩ : Move)] = c₁ := rfl
  have hex2 : exec (sinkPebble (j + 2))
      ([(⟨Op.ghost, j + 1⟩ : Move)] ++ sweep (j + 1)) = c₂ := by
    rw [exec_append, hex1, hse]
  have hex3 : exec (sinkPebble (j + 2))
      ([(⟨Op.ghost, j + 1⟩ : Move)] ++ sweep (j + 1)
        ++ [(⟨Op.unghost, j + 1⟩ : Move), (⟨Op.unpebble, j + 1⟩ : Move)]) = H := by
    rw [exec_append, hex2]; rfl
  have hc₃at : c₃ (j + 1) = Cell.pebble := Function.update_self _ _ _
  have hc₃j : c₃ j = Cell.pebble := by rw [hc₃low j (by omega)]; exact hc₂at
  -- 組み立て
  refine ⟨[⟨Op.ghost, j + 1⟩] ++ sweep (j + 1)
      ++ [⟨Op.unghost, j + 1⟩, ⟨Op.unpebble, j + 1⟩] ++ strip2 H msH, ?_, ?_⟩
  · refine (ok_iff _ (sinkPebble (j + 2))).mpr ⟨?_, ?_⟩
    · refine valid_append _ _ _ (valid_append _ _ _ (valid_append _ _ _ ?_ ?_) ?_) ?_
      · simp only [valid_cons, valid_nil, Bool.and_true]
        unfold legal
        simp [hsink]
      · rw [hex1]; exact valid_mono (by omega) _ _ hsv
      · rw [hex2]
        simp only [valid_cons, valid_nil, Bool.and_true, Bool.and_eq_true]
        constructor
        · unfold legal ready
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
          exact ⟨by omega, hc₂top, Or.inr hc₂at⟩
        · unfold legal ready
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
          exact ⟨by omega, hc₃at, Or.inr hc₃j⟩
      · rw [hex3]; exact valid_mono (by omega) _ _ hvH'
    · intro d hd
      rcases traj_append_mem _ (sinkPebble (j + 2)) _ d hd with hd | hd
      · rcases traj_append_mem _ (sinkPebble (j + 2)) _ d hd with hd | hd
        · rcases traj_append_mem _ (sinkPebble (j + 2)) _ d hd with hd | hd
          · -- 第 1 手の前後
            have hd' : d = sinkPebble (j + 2) ∨ d = c₁ := by simpa [traj] using hd
            have hzero : pcount (j + 1) c₁ = 0 :=
              pcount_eq_zero_iff.mpr fun v hv => by rw [hc₁below v (by omega)]; simp
            rcases hd' with rfl | rfl
            · rw [pcount_sinkPebble (by omega)]; omega
            · rw [pcount_succ, hc₁at, if_neg (by simp), hzero]
              omega
          · -- 掃きの間: 終端はゴーストのまま
            rw [hex1] at hd
            have htop : d (j + 1) = c₁ (j + 1) :=
              traj_above (sweep (j + 1)) c₁ (fun m hm => sweep_mem_lt j m hm) d hd (j + 1) (by omega)
            have hb := hsp d hd
            rw [pcount_succ, htop, hc₁at, if_neg (by simp)]
            omega
        · -- unghost / unpebble の 2 手
          rw [hex2] at hd
          have hd' : d = c₂ ∨ d = c₃ ∨ d = H := by simpa [traj] using hd
          have hc₃low' : pcount (j + 1) c₃ = pcount (j + 1) c₂ :=
            pcount_congr fun v hv => hc₃low v hv
          have hHlow' : pcount (j + 1) H = pcount (j + 1) c₂ :=
            pcount_congr fun v hv => hHlow v hv
          rcases hd' with rfl | rfl | rfl
          · rw [pcount_succ, hc₂top, if_neg (by simp), hc₂count]
            omega
          · rw [pcount_succ, hc₃at, if_pos rfl, hc₃low', hc₂count]
          · rw [pcount_succ, hHtop, if_neg (by simp), hHlow', hc₂count]
            omega
      · -- 頭の間: 終端は空のまま
        rw [hex3] at hd
        have htop : d (j + 1) = H (j + 1) := traj_above _ H hstriplt d hd (j + 1) (by omega)
        have hb := hcapH' d hd
        rw [pcount_succ, htop, hHtop, if_neg (by simp)]
        omega
  · -- 終状態
    intro v hv
    rw [exec_append, hex3]
    by_cases hvk : v < j + 1
    · exact hagreeH' v hvk
    · have hkeep : exec H (strip2 H msH) v = H v :=
        traj_above _ H hstriplt _ (exec_mem_traj _ _) v (by omega)
      rw [hkeep, show v = j + 1 by omega, hHtop]
      rfl

/-- **到達可能性（上限 2）**: どんな長さの鎖も片付く。 -/
theorem UPLengths_two_nonempty : ∀ n, 1 ≤ n → (UPLengths n 2).Nonempty := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · have hn1 : n = 1 := by omega
        subst hn1
        exact ⟨1, [⟨Op.unpebble, 0⟩], rfl, run_one (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
        obtain ⟨_, msH, _, hrunH⟩ := ih (j + 1) (by omega) (by omega)
        obtain ⟨ms, hrun⟩ := run_cap2_step hrunH
        exact ⟨ms.length, ms, rfl, hrun⟩

/-- **到達可能性**: `s ≥ 2` なら `T_UP n s` は実現される（`sInf ∅ = 0` を避けられる）。 -/
theorem UPLengths_nonempty {n s : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : (UPLengths n s).Nonempty := by
  obtain ⟨L, ms, hlen, hok, hagree⟩ := UPLengths_two_nonempty n hn
  exact ⟨L, ms, hlen, ok_cap_mono hs ms _ hok, hagree⟩

end Spooky
