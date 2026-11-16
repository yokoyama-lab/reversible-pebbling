/-
# `T_UP(n,2) = n² + n - 3` — 上限 2 の閉形式

`closed2.py` が底として別扱いしていた $s=2$ の閉形式。**分解（`decomp_ge`）だけでは出ない**
（$s=2$ では分解が緊密でなく $T_{UP}(3,2)\ge7$ しか出ないが真の値は 9）ので、
足りない **`2` を終端の手数から取り返す**のがこのファイルの内容である。

## 足りない 2 の在り処

分解の $\ge$ 方向は、尻尾（＝上限 1）の長さを $T_{UP}(1,1)=1$ と見積もる。射影された
長さ 1 の鎖では `unpebble` 1 手で終わるからである。ところが**元の鎖では**
`unpebble v_{n-1}` は $v_{n-2}$ のペブルを要求し、$v_{n-1}$ と合わせて 2 個になる。
その $v_{n-2}$ を置くには $v_{n-3}$ のペブルが要るので **3 個目が必要**になり、上限 2 では不可能。

したがって $v_{n-1}$ は**必ず一度ゴーストにされ**、`ghost` → `unghost` → `unpebble` の
**3 手**が要る。これが足りない 2 である（`three_le_countP_sink`）。

## 構成側

`Reach.lean` の `run_cap2_step` がそのまま最適な構成になっている:
`ghost v_{n-1}` → `sweep (n-1)` → `unghost v_{n-1}`, `unpebble v_{n-1}` → 頭（`Run_reghost`）
で `1 + (2n-3) + 2 + T_{UP}(n-1,2) = T_{UP}(n-1,2) + 2n`。

## これで何が開くか

$\delta = T_{UG}-T_{UP}$ の **$-1$ 側**（$n\ge\theta(s)$）。望遠鏡
$$(2k-1) + (4k-2s-1) + \bigl(6(n-k)-(s-1)(s+2)+1\bigr) = 6n-s(s+3)+1$$
は回るが、底の $s=2$ だけがここに依存していた。
-/
import SpookyPebbling.Slope6Exact

namespace Spooky

/-! ## 3 個のペブル -/

theorem three_le_pcount {n : ℕ} {c : Config} {a b e : ℕ}
    (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e) (ha : a < n) (hb : b < n) (he : e < n)
    (hpa : c a = Cell.pebble) (hpb : c b = Cell.pebble) (hpe : c e = Cell.pebble) :
    3 ≤ pcount n c := by
  classical
  unfold pcount
  have hsub : ({a, b, e} : Finset ℕ) ⊆ (Finset.range n).filter (fun v => c v = Cell.pebble) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;>
      simp [Finset.mem_filter, Finset.mem_range, ha, hb, he, hpa, hpb, hpe]
  calc 3 = ({a, b, e} : Finset ℕ).card := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hae]),
          Finset.card_insert_of_notMem (by simpa using hbe)]
        simp
    _ ≤ _ := Finset.card_le_card hsub

/-! ## 1 つの頂点に何手要るか -/

/-- 対象頂点に手が来なければ、その頂点の値は変わらない。 -/
theorem exec_untouched {v : ℕ} : ∀ (l : List Move) (c : Config),
    (∀ m ∈ l, m.v ≠ v) → exec c l v = c v := by
  intro l
  induction l with
  | nil => intro c _; rfl
  | cons m l ih =>
      intro c h
      show exec (step c m) l v = c v
      rw [ih (step c m) (fun x hx => h x (by simp [hx]))]
      show Function.update c m.v (result m.op) v = c v
      exact Function.update_of_ne (Ne.symm (h m (by simp))) _ _

/-- ペブル → 空 には、その頂点に少なくとも 1 手要る。 -/
theorem one_le_countP_of_pebble {v : ℕ} (l : List Move) (c : Config)
    (hp : c v = Cell.pebble) (he : exec c l v = Cell.empty) :
    1 ≤ l.countP (fun m => decide (m.v = v)) := by
  by_contra hlt
  have hzero : l.countP (fun m => decide (m.v = v)) = 0 := by omega
  have hall : ∀ m ∈ l, m.v ≠ v := by
    intro m hm hmv
    have := (List.countP_eq_zero).mp hzero m hm
    simp [hmv] at this
  rw [exec_untouched l c hall, hp] at he
  exact Cell.noConfusion he

/-- ゴースト → 空 には、その頂点に少なくとも 2 手要る（`unghost` してから `unpebble`）。 -/
theorem two_le_countP_of_ghost {n v : ℕ} : ∀ (l : List Move) (c : Config),
    valid n c l = true → c v = Cell.ghost → exec c l v = Cell.empty →
    2 ≤ l.countP (fun m => decide (m.v = v)) := by
  intro l
  induction l with
  | nil =>
      intro c _ hg he
      rw [show exec c [] v = c v from rfl, hg] at he
      exact Cell.noConfusion he
  | cons m l ih =>
      intro c hv hg he
      rw [valid_cons] at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨hleg, hrest⟩ := hv
      by_cases hmv : m.v = v
      · -- ゴーストに打てるのは `unghost` だけ
        have hcv : c m.v = Cell.ghost := by rw [hmv]; exact hg
        have hop : m.op = Op.unghost := by
          unfold legal at hleg
          have h2 := Bool.and_elim_right hleg
          cases hop : m.op with
          | pebble =>
              rw [hop] at h2
              rw [of_decide_eq_true (Bool.and_elim_left h2)] at hcv
              exact Cell.noConfusion hcv
          | unpebble =>
              rw [hop] at h2
              rw [of_decide_eq_true (Bool.and_elim_left h2)] at hcv
              exact Cell.noConfusion hcv
          | ghost =>
              rw [hop] at h2
              rw [of_decide_eq_true h2] at hcv
              exact Cell.noConfusion hcv
          | unghost => rfl
        have hstep : step c m v = Cell.pebble := by
          show Function.update c m.v (result m.op) v = Cell.pebble
          rw [← hmv, Function.update_self, hop]; rfl
        have h1 : 1 ≤ l.countP (fun m => decide (m.v = v)) :=
          one_le_countP_of_pebble l (step c m) hstep he
        rw [List.countP_cons]
        simp only [decide_eq_true_eq, hmv, if_pos]
        omega
      · have hstep : step c m v = Cell.ghost := by
          show Function.update c m.v (result m.op) v = Cell.ghost
          rw [Function.update_of_ne (Ne.symm hmv)]; exact hg
        have := ih (step c m) hrest hstep he
        rw [List.countP_cons]
        simp only [decide_eq_true_eq, hmv]
        omega

/-! ## 上限 2 では終端に 3 手要る -/

/-- **本補題**: 上限 2・中間の頂点にペブルが無い状態から始めると、
終端 `v_{n-1}` に打つ手は **3 手以上**。

`unpebble v_{n-1}` は `v_{n-2}` のペブルを要求するが、上限 2 では `v_{n-2}` を
置くこと自体ができない（置くには `v_{n-3}` が要り、`v_{n-1}` と合わせて 3 個になる）。
したがって最初の 1 手は `ghost` に限られ、そこから空へ戻すのに更に 2 手要る。 -/
theorem three_le_countP_sink {n : ℕ} (hn : 3 ≤ n) : ∀ (l : List Move) (c : Config),
    valid n c l = true → (∀ d ∈ traj c l, pcount n d ≤ 2) →
    (∀ j, 1 ≤ j → j + 1 < n → c j ≠ Cell.pebble) →
    c (n - 1) = Cell.pebble → exec c l (n - 1) = Cell.empty →
    3 ≤ l.countP (fun m => decide (m.v = n - 1)) := by
  intro l
  induction l with
  | nil =>
      intro c _ _ _ hp he
      rw [show exec c [] (n - 1) = c (n - 1) from rfl, hp] at he
      exact Cell.noConfusion he
  | cons m l ih =>
      intro c hv hcap hmid hp he
      rw [valid_cons] at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨hleg, hrest⟩ := hv
      have hlt : m.v < n := legal_lt hleg
      have hcap' : ∀ d ∈ traj (step c m) l, pcount n d ≤ 2 := by
        intro d hd
        exact hcap d (by rw [traj_cons]; simp [hd])
      have hlegm := Bool.and_elim_right (by unfold legal at hleg; exact hleg)
      by_cases hmv : m.v = n - 1
      · -- 終端への手。`c (n-1) = pebble` なので `ghost` か `unpebble`
        have hcv : c m.v = Cell.pebble := by rw [hmv]; exact hp
        have hghost : m.op = Op.ghost := by
          cases hop : m.op with
          | pebble =>
              rw [hop] at hlegm
              rw [of_decide_eq_true (Bool.and_elim_left hlegm)] at hcv
              exact Cell.noConfusion hcv
          | unghost =>
              rw [hop] at hlegm
              rw [of_decide_eq_true (Bool.and_elim_left hlegm)] at hcv
              exact Cell.noConfusion hcv
          | unpebble =>
              -- `ready` が `v_{n-2}` のペブルを要求するが、中間の頂点にペブルは無い
              rw [hop] at hlegm
              have hrd : ready c m.v = true := Bool.and_elim_right hlegm
              unfold ready at hrd
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hrd
              rcases hrd with h0 | h1
              · omega
              · rw [hmv] at h1
                exact absurd h1 (hmid (n - 1 - 1) (by omega) (by omega))
          | ghost => rfl
        have hstep : step (c) m (n - 1) = Cell.ghost := by
          show Function.update c m.v (result m.op) (n - 1) = Cell.ghost
          rw [← hmv, Function.update_self, hghost]; rfl
        have h2 := two_le_countP_of_ghost (n := n) l (step c m) hrest hstep he
        rw [List.countP_cons]
        simp only [decide_eq_true_eq, hmv, if_pos]
        omega
      · -- 終端以外の手。不変条件を保つ
        have hltm : m.v < n - 1 := by omega
        have hp' : step c m (n - 1) = Cell.pebble := by
          show Function.update c m.v (result m.op) (n - 1) = Cell.pebble
          rw [Function.update_of_ne (Ne.symm hmv)]; exact hp
        have hmid' : ∀ j, 1 ≤ j → j + 1 < n → step c m j ≠ Cell.pebble := by
          intro j hj1 hj2
          by_cases hjm : j = m.v
          · -- `v_{m.v}` を置くなら `v_{m.v-1}` のペブルが要る
            intro hpj
            rw [hjm] at hpj
            have hres : result m.op = Cell.pebble := by
              have h : Function.update c m.v (result m.op) m.v = Cell.pebble := hpj
              rwa [Function.update_self] at h
            have hrd : ready c m.v = true := by
              cases hop : m.op with
              | pebble => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
              | unghost => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
              | unpebble => rw [hop] at hres; exact absurd hres (by simp [result])
              | ghost => rw [hop] at hres; exact absurd hres (by simp [result])
            unfold ready at hrd
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hrd
            rcases hrd with h0 | h1
            · omega
            · rcases Nat.lt_or_ge 1 m.v with hmv1 | hmv1
              · exact (hmid (m.v - 1) (by omega) (by omega)) h1
              · -- `m.v = 1`: 置いた直後に `v_0`・`v_1`・`v_{n-1}` の 3 個になる
                have hone' : m.v = 1 := by omega
                have h0' : step c m 0 = Cell.pebble := by
                  show Function.update c m.v (result m.op) 0 = Cell.pebble
                  rw [Function.update_of_ne (by omega)]
                  rw [hone'] at h1; exact h1
                have hp1 : step c m 1 = Cell.pebble := by rw [← hone']; exact hpj
                have h3 := three_le_pcount (n := n) (c := step c m) (a := 0) (b := 1) (e := n - 1)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  h0' hp1 hp'
                have hle := hcap (step c m)
                  (by rw [traj_cons]; simp [mem_traj_self (step c m) l])
                omega
          · intro hpj
            refine (hmid j hj1 hj2) ?_
            rw [show c j = step c m j from
              (Function.update_of_ne (fun h => hjm h) _ _).symm]
            exact hpj
        have := ih (step c m) hrest hcap' hmid' hp' he
        rw [List.countP_cons]
        simp only [decide_eq_true_eq, hmv]
        omega

/-! ## 上限 1 では長さ 2 以上の鎖は片付かない -/

theorem not_run_up_cap_one {m : ℕ} (hm : 2 ≤ m) {ms : List Move} :
    ¬ Run m 1 (sinkPebble m) ms allEmpty := by
  intro h
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, hcap⟩ := (ok_iff ms (sinkPebble m)).mp hok
  obtain ⟨d, hd, hd2⟩ := two_pebbles_of_clear ms.length ms le_rfl (sinkPebble m) hv
    (i := m - 1) (by omega) (by omega) (by rw [sinkPebble_apply]; simp)
    (by rw [hagree (m - 1) (by omega)]; rfl)
  have := hcap d hd
  omega

/-! ## 漸化 -/

/-- **下界の帰納段**: `T_UP(j+2,2) ≥ T_UP(j+1,2) + 2(j+2)`。 -/
theorem TUP_cap2_ge_step {j : ℕ} (hj : 1 ≤ j) :
    TUP (j + 1) 2 + 2 * (j + 2) ≤ TUP (j + 2) 2 := by
  obtain ⟨ms, hlen, hrun⟩ :=
    Nat.sInf_mem (UPLengths_nonempty (n := j + 2) (s := 2) le_rfl (by omega))
  obtain ⟨hok, hagree⟩ := hrun
  obtain ⟨hv, hcapall⟩ := (ok_iff ms (sinkPebble (j + 2))).mp hok
  obtain ⟨u, hun1, hbound, hrunT⟩ := decomp_ge_pieces (n := j + 2) (s := 2) (by omega)
    (fun i hi => by rw [sinkPebble_apply, if_neg (by omega)]; simp)
    (two_pebbles_of_clear ms.length ms le_rfl (sinkPebble (j + 2)) hv (i := j + 1)
      (by omega) (by omega) (by rw [sinkPebble_apply]; simp)
      (by rw [hagree (j + 1) (by omega)]; rfl))
    ⟨hok, hagree⟩
  -- 尻尾は上限 1 なので長さ 1 に強制される
  have hshift : AgreeOn (j + 2 - (u + 1)) (shiftC (u + 1) (sinkPebble (j + 2)))
      (sinkPebble (j + 2 - (u + 1))) := shiftC_sinkPebble (by omega) hun1
  have hrunT' : Run (j + 2 - (u + 1)) 1 (sinkPebble (j + 2 - (u + 1)))
      (tailMoves u ms) allEmpty := by
    refine ⟨ok_cap_mono (by omega) _ _ (ok_congr hshift hrunT.1), ?_⟩
    intro v hv1
    rw [← exec_congr (tailMoves u ms) hshift v hv1]
    exact hrunT.2 v hv1
  have hone : j + 2 - (u + 1) = 1 := by
    by_contra hc
    exact not_run_up_cap_one (by omega) hrunT'
  have hueq : u = j := by omega
  -- 終端には 3 手要る
  have h3 : 3 ≤ ms.countP (fun m => decide (m.v = j + 2 - 1)) := by
    refine three_le_countP_sink (n := j + 2) (by omega) ms (sinkPebble (j + 2)) hv hcapall
      (fun i hi1 hi2 => by rw [sinkPebble_apply, if_neg (by omega)]; simp) ?_ ?_
    · rw [sinkPebble_apply, if_pos (by omega)]
    · rw [hagree (j + 2 - 1) (by omega)]; rfl
  have htail : 3 ≤ (tailMoves u ms).length := by
    have hmap : (tailMoves u ms).length = ms.countP (fun m => decide (u < m.v)) := by
      unfold tailMoves
      rw [List.length_map, ← List.countP_eq_length_filter]
    have hmono : ms.countP (fun m => decide (m.v = j + 2 - 1))
        ≤ ms.countP (fun m => decide (u < m.v)) := by
      refine List.countP_mono_left ?_
      intro x _ hx
      simp only [decide_eq_true_eq] at hx ⊢
      omega
    omega
  rw [hueq] at hbound htail
  unfold TUP at hbound ⊢
  omega

/-- **上界の帰納段**: `T_UP(j+2,2) ≤ T_UP(j+1,2) + 2(j+2)`（`Reach.lean` の構成）。 -/
theorem TUP_cap2_le_step (j : ℕ) : TUP (j + 2) 2 ≤ TUP (j + 1) 2 + 2 * (j + 2) := by
  obtain ⟨msH, hlenH, hrunH⟩ :=
    Nat.sInf_mem (UPLengths_nonempty (n := j + 1) (s := 2) le_rfl (by omega))
  obtain ⟨ms, hlen, hrun⟩ := run_cap2_step hrunH
  have hle := TUP_le (n := j + 2) (s := 2) ⟨ms, rfl, hrun⟩
  have hH : msH.length = TUP (j + 1) 2 := hlenH
  omega

/-! ## 閉形式 -/

/-- **`T_UP(n,2) = n² + n - 3`（`n ≥ 2`）**。 -/
theorem TUP_cap2 {n : ℕ} (hn : 2 ≤ n) : TUP n 2 + 3 = n * n + n := by
  induction n, hn using Nat.le_induction with
  | base =>
      have := TUP_eq_of_le' (k := 2) (s := 2) (by omega) (by omega)
      omega
  | succ n hn ih =>
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      show TUP (j + 2) 2 + 3 = (j + 2) * (j + 2) + (j + 2)
      have hge := TUP_cap2_ge_step (j := j) (by omega)
      have hle := TUP_cap2_le_step j
      have hexp : (j + 2) * (j + 2) + (j + 2)
          = (j + 1) * (j + 1) + (j + 1) + 2 * (j + 2) := by ring
      omega

end Spooky
