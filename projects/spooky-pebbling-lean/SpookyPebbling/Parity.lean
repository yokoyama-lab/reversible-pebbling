/-
# パリティ不変量 — `|T_UG - T_UP| = 1` の「0 でない」側

KSS Thm 4.11 は $T_{UG}(n,s) = T_{UP}(n,s) \pm 1$ を主張するが、これは Lemma 4.9/4.10 の
**両側の不等式** $T_{UP}\le T_{UG}+1$ と $T_{UG}\le T_{UP}+1$ から出るものにすぎず、
**$T_{UG} = T_{UP}$ の可能性が排除されていない**。

排除できる。各頂点の状態に
$$\varphi(\text{empty})=0,\quad \varphi(\text{pebble})=1,\quad \varphi(\text{ghost})=0$$
を割り当てると、**4 つの操作はいずれも作用した頂点の $\varphi$ を反転させる**
（pebble $0\to1$、unpebble $1\to0$、ghost $1\to0$、unghost $0\to1$）。
したがってペブル総数のパリティは 1 手ごとに反転し、手数は始状態と終状態だけで決まる。

- unpebbling: $1 \to 0$ なので**手数は奇数**
- unghosting: $0 \to 0$ なので**手数は偶数**

ゆえに $T_{UG}(n,s) \ne T_{UP}(n,s)$。KSS の $\pm1$ と合わせて $|T_{UG}-T_{UP}|=1$ が
厳密に決まる。**一般 DAG でも成り立つ**が、本ファイルは鎖の設定で述べる。
-/
import SpookyPebbling.Defs

namespace Spooky

/-! ## `pcount` の基本 -/

@[simp] theorem pcount_allEmpty (n : ℕ) : pcount n allEmpty = 0 := by
  unfold pcount allEmpty
  simp

/-- ペブル以外の値をペブルに書き換えると個数はちょうど 1 増える。 -/
theorem pcount_update_pebble {n u : ℕ} {c : Config} (hu : u < n) (hc : c u ≠ Cell.pebble) :
    pcount n (Function.update c u Cell.pebble) = pcount n c + 1 := by
  unfold pcount
  have hset : (Finset.range n).filter (fun v => Function.update c u Cell.pebble v = Cell.pebble)
      = insert u ((Finset.range n).filter (fun v => c v = Cell.pebble)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Function.update_apply]
    by_cases hv : v = u
    · subst hv; simp [hu]
    · simp [hv]
  rw [hset, Finset.card_insert_of_notMem]
  simp [hc]

/-- ペブルをペブル以外に書き換えると個数はちょうど 1 減る。 -/
theorem pcount_update_nonpebble {n u : ℕ} {c : Config} {x : Cell}
    (hu : u < n) (hc : c u = Cell.pebble) (hx : x ≠ Cell.pebble) :
    pcount n (Function.update c u x) + 1 = pcount n c := by
  unfold pcount
  have hset : (Finset.range n).filter (fun v => Function.update c u x v = Cell.pebble)
      = ((Finset.range n).filter (fun v => c v = Cell.pebble)).erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Function.update_apply]
    by_cases hv : v = u
    · subst hv; simp [hx]
    · simp [hv]
  rw [hset, Finset.card_erase_add_one]
  simp [Finset.mem_filter, Finset.mem_range, hu, hc]

/-! ## 1 手ごとにパリティが反転する -/

/-- **補題1（パリティ）**: 妥当な 1 手はペブル数のパリティを反転させる。 -/
theorem pcount_step_parity {n : ℕ} {c : Config} {m : Move} (h : legal n c m = true) :
    pcount n (step c m) % 2 = (pcount n c + 1) % 2 := by
  have hu : m.v < n := legal_lt h
  unfold legal at h
  have h' := Bool.and_elim_right h
  cases hop : m.op with
  | pebble =>
      rw [hop] at h'
      have hc : c m.v = Cell.empty := of_decide_eq_true (Bool.and_elim_left h')
      have hs : step c m = Function.update c m.v Cell.pebble := by simp [step, result, hop]
      rw [hs, pcount_update_pebble hu (by rw [hc]; simp)]
  | unghost =>
      rw [hop] at h'
      have hc : c m.v = Cell.ghost := of_decide_eq_true (Bool.and_elim_left h')
      have hs : step c m = Function.update c m.v Cell.pebble := by simp [step, result, hop]
      rw [hs, pcount_update_pebble hu (by rw [hc]; simp)]
  | unpebble =>
      rw [hop] at h'
      have hc : c m.v = Cell.pebble := of_decide_eq_true (Bool.and_elim_left h')
      have hs : step c m = Function.update c m.v Cell.empty := by simp [step, result, hop]
      rw [hs]
      have := pcount_update_nonpebble (x := Cell.empty) hu hc (by simp)
      omega
  | ghost =>
      rw [hop] at h'
      have hc : c m.v = Cell.pebble := of_decide_eq_true h'
      have hs : step c m = Function.update c m.v Cell.ghost := by simp [step, result, hop]
      rw [hs]
      have := pcount_update_nonpebble (x := Cell.ghost) hu hc (by simp)
      omega

/-- `ok` から先頭の手の妥当性を取り出す。 -/
theorem ok_head {n s : ℕ} {c : Config} {m : Move} {ms : List Move}
    (h : ok n s c (m :: ms) = true) : legal n c m = true := by
  unfold ok at h
  exact Bool.and_elim_right (Bool.and_elim_left h)

/-- `ok` から残りの手順を取り出す。 -/
theorem ok_tail {n s : ℕ} {c : Config} {m : Move} {ms : List Move}
    (h : ok n s c (m :: ms) = true) : ok n s (step c m) ms = true := by
  unfold ok at h
  exact Bool.and_elim_right h

/-- **パリティ保存**: 手数は始状態と終状態のペブル数のパリティ差で決まる。 -/
theorem pcount_exec_parity {n s : ℕ} {c : Config} {ms : List Move} (h : ok n s c ms = true) :
    pcount n (exec c ms) % 2 = (pcount n c + ms.length) % 2 := by
  induction ms generalizing c with
  | nil => simp [exec]
  | cons m ms ih =>
      have hstep := pcount_step_parity (ok_head h)
      have := ih (ok_tail h)
      simp only [exec, List.length_cons]
      omega

/-! ## 帰結: unpebbling は奇数手、unghosting は偶数手 -/

@[simp] theorem pcount_sinkPebble {n : ℕ} (hn : 0 < n) : pcount n (sinkPebble n) = 1 := by
  unfold sinkPebble sink
  rw [pcount_update_pebble (by omega) (by simp [allEmpty])]
  simp

@[simp] theorem pcount_sinkGhost {n : ℕ} : pcount n (sinkGhost n) = 0 := by
  unfold pcount sinkGhost sink
  refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
  intro v _
  simp only [Function.update_apply]
  by_cases hv : v = n - 1 <;> simp [hv, allEmpty]

/-- unpebbling（$v_{n-1}$ のペブル → 空）の手数は**奇数**。 -/
theorem UP_length_odd {n s : ℕ} (hn : 0 < n) {ms : List Move}
    (h : Run n s (sinkPebble n) ms allEmpty) : ms.length % 2 = 1 := by
  obtain ⟨hok, hagree⟩ := h
  have hpar := pcount_exec_parity hok
  rw [pcount_congr hagree, pcount_allEmpty, pcount_sinkPebble hn] at hpar
  omega

/-- unghosting（$v_{n-1}$ のゴースト → 空）の手数は**偶数**。 -/
theorem UG_length_even {n s : ℕ} {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) : ms.length % 2 = 0 := by
  obtain ⟨hok, hagree⟩ := h
  have hpar := pcount_exec_parity hok
  rw [pcount_congr hagree, pcount_allEmpty, pcount_sinkGhost] at hpar
  omega

/-- pebbling（空 → $v_{n-1}$ のペブル）の手数も**奇数**。 -/
theorem P_length_odd {n s : ℕ} (hn : 0 < n) {ms : List Move}
    (h : Run n s allEmpty ms (sinkPebble n)) : ms.length % 2 = 1 := by
  obtain ⟨hok, hagree⟩ := h
  have hpar := pcount_exec_parity hok
  rw [pcount_congr hagree, pcount_sinkPebble hn, pcount_allEmpty] at hpar
  omega

/-! ## 主定理: `T_UG ≠ T_UP`

KSS Thm 4.11 の $\pm1$ は $0$ を排除していない。パリティが排除する。
-/

theorem TUP_odd {n s : ℕ} (hn : 0 < n) (h : (UPLengths n s).Nonempty) : TUP n s % 2 = 1 := by
  unfold TUP
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem h
  rw [← hlen]
  exact UP_length_odd hn hrun

theorem TUG_even {n s : ℕ} (h : (UGLengths n s).Nonempty) : TUG n s % 2 = 0 := by
  unfold TUG
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem h
  rw [← hlen]
  exact UG_length_even hrun

/-- **$T_{UG}(n,s) \ne T_{UP}(n,s)$。** KSS が $\pm1$ で止めている所を 1 段締める。 -/
theorem TUG_ne_TUP {n s : ℕ} (hn : 0 < n)
    (hUP : (UPLengths n s).Nonempty) (hUG : (UGLengths n s).Nonempty) :
    TUG n s ≠ TUP n s := by
  intro heq
  have h1 := TUP_odd hn hUP
  have h2 := TUG_even hUG
  rw [heq] at h2
  omega

/-- 同様に $T_P$ と $T_{UG}$ も一致しない。 -/
theorem TP_ne_TUG {n s : ℕ} (hn : 0 < n)
    (hP : (PLengths n s).Nonempty) (hUG : (UGLengths n s).Nonempty) :
    TP n s ≠ TUG n s := by
  intro heq
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hP
  have h1 : TP n s % 2 = 1 := by unfold TP; rw [← hlen]; exact P_length_odd hn hrun
  have h2 := TUG_even hUG
  rw [heq] at h1
  omega

end Spooky
