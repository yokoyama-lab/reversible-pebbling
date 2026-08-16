/-
# 分解の $\le$ 方向（構成）

$$T_{UP}(n,s)\ \le\ 2k-1 + T_{UP}(k,s) + T_{UP}(n-k,s-1) \qquad (s\ge3,\ 1\le k<n)$$

3 段の連結で作る（頂点は 0-indexed、頭 = `0..k-1`、尻尾 = `k..n-1`）:

1. **掃き** `sweep k` — `2k-1` 手で `v_{k-1}` だけにペブルを残す。
   `v_0..v_{k-2}` にはゴーストが残る（`Sweep.lean`）
2. **尻尾** `liftT k msT` — 部分鎖の手順を `+k` して持ち上げる。`v_{k-1}` の
   ペブルが前提を満たし続けるので妥当（`Lift.lean`）。上限は `s-1`
3. **頭** `strip2 _ msH` — `sinkPebble k` からの手順を、掃きが残したゴースト入りの
   始状態向けに読み替える。手数は変わらない（`Reghost.lean`）

ペブル数は各段で `pcount n = pcount k + pcount (n-k) ∘ shiftC k` に分けて数える:
掃きの間は `≤ 2 + 1 = 3`、尻尾の間は `1 + (s-1) = s`、頭の間は `s + 0 = s`。
**掃きの `3` が $s\ge3$ の由来**である。
-/
import SpookyPebbling.Reach

namespace Spooky

/-- 鎖の外（`≥ n`）は空。 -/
theorem sinkPebble_above {n v : ℕ} (hn : 0 < n) (h : n ≤ v) : sinkPebble n v = Cell.empty := by
  rw [sinkPebble_apply, if_neg (by omega)]

/-- **$\le$ 方向の構成**: 頭と尻尾の手順から、元の鎖の手順を組み立てる。 -/
theorem decomp_le_run {n s j : ℕ} (hs : 3 ≤ s) (hjn : j + 1 < n)
    {msH msT : List Move}
    (hH : Run (j + 1) s (sinkPebble (j + 1)) msH allEmpty)
    (hT : Run (n - (j + 1)) (s - 1) (sinkPebble (n - (j + 1))) msT allEmpty) :
    ∃ ms : List Move, ms.length = 2 * j + 1 + msT.length + msH.length ∧
      Run n s (sinkPebble n) ms allEmpty := by
  classical
  obtain ⟨hokH, hagreeH⟩ := hH
  obtain ⟨hokT, hagreeT⟩ := hT
  obtain ⟨hvH, hcapH⟩ := (ok_iff msH (sinkPebble (j + 1))).mp hokH
  obtain ⟨hvT, hcapT⟩ := (ok_iff msT (sinkPebble (n - (j + 1)))).mp hokT
  -- 第 1 段: 掃き
  have hc₀empty : ∀ i, i ≤ j → sinkPebble n i = Cell.empty := by
    intro i hi
    rw [sinkPebble_apply, if_neg (by omega)]
  obtain ⟨hsv, hse, hsp⟩ := sweep_spec j (sinkPebble n) hc₀empty
  -- 掃いた後の配置から見た尻尾は、部分鎖の始状態と一致する
  have hshift₁ : AgreeOn (n - (j + 1)) (shiftC (j + 1) (swept j (sinkPebble n)))
      (sinkPebble (n - (j + 1))) := by
    intro t ht
    rw [shiftC_apply, swept_above (by omega)]
    exact shiftC_sinkPebble (by omega) hjn t ht
  have hpedestal : swept j (sinkPebble n) (j + 1 - 1) = Cell.pebble := by
    rw [show j + 1 - 1 = j by omega]; exact swept_at
  have hheadcount : pcount (j + 1) (swept j (sinkPebble n)) = 1 := pcount_swept j (sinkPebble n)
  -- 第 2 段: 尻尾を持ち上げる
  have hvT' : valid (n - (j + 1)) (shiftC (j + 1) (swept j (sinkPebble n))) msT = true :=
    valid_congr (fun t ht => (hshift₁ t ht).symm) _ hvT
  have hvlift : valid n (swept j (sinkPebble n)) (liftT (j + 1) msT) = true :=
    valid_liftT (by omega) msT _ hpedestal hvT'
  have hc₂head : ∀ jj, jj < j + 1 →
      exec (swept j (sinkPebble n)) (liftT (j + 1) msT) jj = swept j (sinkPebble n) jj :=
    fun jj hjj => exec_liftT_below msT _ hjj
  have hc₂tail : AgreeOn (n - (j + 1))
      (shiftC (j + 1) (exec (swept j (sinkPebble n)) (liftT (j + 1) msT))) allEmpty := by
    intro t ht
    rw [exec_liftT_shift]
    rw [← exec_congr msT (fun t' ht' => (hshift₁ t' ht').symm) t ht]
    exact hagreeT t ht
  -- 前 2 段の手はすべて `< n` に作用する
  have hmvlt : ∀ m ∈ sweep (j + 1) ++ liftT (j + 1) msT, m.v < n := by
    intro m hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have := sweep_mem_lt j m hm; omega
    · simp only [liftT, List.mem_map] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      have := valid_lt msT _ hvT' m' hm'
      simp only [liftM_v]; omega
  have habove : ∀ v, n ≤ v →
      exec (swept j (sinkPebble n)) (liftT (j + 1) msT) v = sinkPebble n v := by
    intro v hv
    have hmem : exec (swept j (sinkPebble n)) (liftT (j + 1) msT)
        ∈ traj (sinkPebble n) (sweep (j + 1) ++ liftT (j + 1) msT) := by
      rw [← hse]
      exact traj_append_subset (sweep (j + 1)) (sinkPebble n) (liftT (j + 1) msT) _
        (by rw [hse]; exact exec_mem_traj _ _)
    exact traj_above _ (sinkPebble n) (fun m hm => by have := hmvlt m hm; omega) _ hmem v (by omega)
  -- 第 3 段: 頭（ゴーストの読み替え）
  have hdom : Dom2 msH (exec (swept j (sinkPebble n)) (liftT (j + 1) msT)) (sinkPebble (j + 1)) := by
    intro v
    by_cases hvk : v < j + 1
    · rw [hc₂head v hvk]
      by_cases hvj : v = j
      · left; rw [hvj, swept_at, sinkPebble_apply, if_pos (by omega)]
      · right
        refine ⟨swept_below (by omega), ?_, ?_⟩
        · rw [sinkPebble_apply, if_neg (by omega)]
        · exact head_places ⟨hokH, hagreeH⟩ v (by omega)
    · left
      rw [sinkPebble_apply, if_neg (by omega)]
      by_cases hvn : v < n
      · have h := hc₂tail (v - (j + 1)) (by omega)
        rw [shiftC_apply, show v - (j + 1) + (j + 1) = v by omega] at h
        exact h
      · rw [habove v (by omega), sinkPebble_above (by omega) (by omega)]
  obtain ⟨hrunH', hlenH'⟩ := Run_reghost hdom ⟨hokH, hagreeH⟩
  obtain ⟨hokH', hagreeH'⟩ := hrunH'
  obtain ⟨hvH', hcapH'⟩ :=
    (ok_iff (strip2 (exec (swept j (sinkPebble n)) (liftT (j + 1) msT)) msH) _).mp hokH'
  have hstriplt : ∀ m ∈ strip2 (exec (swept j (sinkPebble n)) (liftT (j + 1) msT)) msH,
      m.v < j + 1 := fun m hm => valid_lt _ _ hvH' m hm
  -- 組み立て
  refine ⟨sweep (j + 1) ++ liftT (j + 1) msT
      ++ strip2 (exec (swept j (sinkPebble n)) (liftT (j + 1) msT)) msH, ?_, ?_, ?_⟩
  · simp only [List.length_append, liftT_length, hlenH', sweep_length]
  · refine (ok_iff _ (sinkPebble n)).mpr ⟨?_, ?_⟩
    · refine valid_append _ _ _ (valid_append _ _ _ (valid_mono (by omega) _ _ hsv) ?_) ?_
      · rw [hse]; exact hvlift
      · rw [exec_append, hse]
        exact valid_mono (by omega) _ _ hvH'
    · intro d hd
      rcases traj_append_mem _ (sinkPebble n) _ d hd with hd | hd
      · rcases traj_append_mem (sweep (j + 1)) (sinkPebble n) (liftT (j + 1) msT) d hd with hd | hd
        · -- 掃きの間: 頭 ≤ 2、尻尾 = 1
          rw [pcount_split n j (by omega) d]
          have h1 : pcount (j + 1) d ≤ 2 := hsp d hd
          have h2 : pcount (n - (j + 1)) (shiftC (j + 1) d) = 1 := by
            have hkeep : ∀ v, j + 1 ≤ v → d v = sinkPebble n v :=
              traj_above (sweep (j + 1)) (sinkPebble n) (fun m hm => sweep_mem_lt j m hm) d hd
            have hagree : AgreeOn (n - (j + 1)) (shiftC (j + 1) d) (sinkPebble (n - (j + 1))) := by
              intro t ht
              rw [shiftC_apply, hkeep (t + (j + 1)) (by omega)]
              exact shiftC_sinkPebble (by omega) hjn t ht
            rw [pcount_congr hagree, pcount_sinkPebble (by omega)]
          omega
        · -- 尻尾の間: 頭 = 1、尻尾 ≤ s-1
          rw [hse] at hd
          rw [pcount_split n j (by omega) d]
          obtain ⟨hbelow, hin⟩ := traj_liftT msT (swept j (sinkPebble n)) d hd
          have h1 : pcount (j + 1) d = 1 := by
            rw [pcount_congr (fun v hv => hbelow v hv)]; exact hheadcount
          have h2 : pcount (n - (j + 1)) (shiftC (j + 1) d) ≤ s - 1 := by
            obtain ⟨e, he, hae⟩ :=
              traj_agree msT _ (sinkPebble (n - (j + 1))) hshift₁ _ hin
            rw [pcount_congr hae]
            exact hcapT e he
          omega
      · -- 頭の間: 頭 ≤ s、尻尾 = 0
        rw [exec_append, hse] at hd
        rw [pcount_split n j (by omega) d]
        have h1 : pcount (j + 1) d ≤ s := hcapH' d hd
        have h2 : pcount (n - (j + 1)) (shiftC (j + 1) d) = 0 := by
          have hkeep : ∀ v, j + 1 ≤ v →
              d v = exec (swept j (sinkPebble n)) (liftT (j + 1) msT) v :=
            traj_above _ _ hstriplt d hd
          refine pcount_eq_zero_iff.mpr ?_
          intro t ht
          rw [shiftC_apply, hkeep (t + (j + 1)) (by omega)]
          have h := hc₂tail t ht
          rw [shiftC_apply] at h
          rw [h]
          simp [allEmpty]
        omega
  · -- 終状態
    intro v hv
    rw [exec_append, exec_append, hse]
    by_cases hvk : v < j + 1
    · exact hagreeH' v hvk
    · have hkeep : exec (exec (swept j (sinkPebble n)) (liftT (j + 1) msT))
          (strip2 (exec (swept j (sinkPebble n)) (liftT (j + 1) msT)) msH) v
          = exec (swept j (sinkPebble n)) (liftT (j + 1) msT) v :=
        traj_above _ _ hstriplt _ (exec_mem_traj _ _) v (by omega)
      rw [hkeep]
      have h := hc₂tail (v - (j + 1)) (by omega)
      rw [shiftC_apply, show v - (j + 1) + (j + 1) = v by omega] at h
      exact h

/-- **$\le$ 方向**（`T_UP` の形）。到達可能性（`Reach.lean`）で仮定は不要になった。 -/
theorem decomp_le {n s k : ℕ} (hs : 3 ≤ s) (hk : 1 ≤ k) (hkn : k < n) :
    TUP n s ≤ 2 * k - 1 + TUP k s + TUP (n - k) (s - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨msH, hlenH, hrunH⟩ :=
    Nat.sInf_mem (UPLengths_nonempty (n := j + 1) (s := s) (by omega) (by omega))
  obtain ⟨msT, hlenT, hrunT⟩ :=
    Nat.sInf_mem (UPLengths_nonempty (n := n - (j + 1)) (s := s - 1) (by omega) (by omega))
  obtain ⟨ms, hlen, hrun⟩ := decomp_le_run hs hkn hrunH hrunT
  have hb := TUP_le (n := n) (s := s) ⟨ms, rfl, hrun⟩
  rw [hlen] at hb
  unfold TUP at hb ⊢
  omega

/-! ## 両方向を合わせて等号 -/

/-- **分解は厳密**（`s ≥ 3`）: ある `k` で等号が成り立ち、どの `k` も上界を与える。 -/
theorem decomp_exact {n s : ℕ} (hs : 3 ≤ s) (hn : 2 ≤ n) :
    (∃ k, 1 ≤ k ∧ k < n ∧ TUP n s = 2 * k - 1 + TUP k s + TUP (n - k) (s - 1)) ∧
    (∀ k, 1 ≤ k → k < n → TUP n s ≤ 2 * k - 1 + TUP k s + TUP (n - k) (s - 1)) := by
  refine ⟨?_, fun k hk hkn => decomp_le hs hk hkn⟩
  obtain ⟨k, hk, hkn, hge⟩ :=
    TUP_ge_decomp hn (UPLengths_nonempty (n := n) (s := s) (by omega) (by omega))
  exact ⟨k, hk, hkn, le_antisymm (decomp_le hs hk hkn) hge⟩

end Spooky
