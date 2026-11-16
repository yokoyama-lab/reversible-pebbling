/-
# KSS Lemma 3.2 — `T_P(n+1, s+1) ≤ T_UG(n,s) + 1`

**unghosting は pebbling に 1 手で化ける。** KSS の証明（Lemma 3.2）は 1 行:

> $U_g$ の**`v_n` に触る最初の手の直後に `pebble v_{n+1}` を挿す**。
> `v_n` はゴーストで始まるので、その最初の手は必ず `unghost`（＝ペブルを置く手）である。

長さ `n` の unghosting を長さ `n+1` の pebbling に読み替える。始状態が
「`v_{n-1}` がゴースト」から「全空」に変わるが、**鎖の終端は誰の前提条件にもならない**
（`UGvsUP.lean` と同じ観察）ので、最初の手が来るまでは同じ手をそのまま打てる。
最初の手だけ `unghost` → `pebble` に読み替え、直後に `pebble v_n`（0-indexed）を挿す。
以後 `v_n` はペブルのまま動かないので、上限が 1 増えるだけで済む。

## 何が開くか

**KSS Thm 4.11 の半分**。`Cap2Exact.lean` の $T_{UG}(n,2)=n^2+n-4$ と合わせると

$$T_P(n,3) \;\le\; T_{UG}(n-1,2)+1 \;=\; \bigl((n-1)^2+(n-1)-4\bigr)+1 \;=\; n^2-n-3 ,$$

すなわち **$T(n,3)=n^2-n-3$ の上界**が出る。**KSS Cor 4.7 は要らない**。
傾き 4/6 の領域でも同様に $T_P$ の上界が出る。

下界（KSS Lemma 4.8）は逆向きの外科手術で、Lemma 4.5 の正準な置き方（`I`）による
**正規化**が要る。そこは未移植。
-/
import SpookyPebbling.Cap2Exact

namespace Spooky

/-! ## 鎖を 1 つ伸ばす -/

/-- 終端 `v_n` にペブルが載っていて手が `< n` にしか来ないなら、
上限を 1 増やして長さ `n+1` の鎖の手順と見なせる。 -/
theorem ok_extend_pebble {n s : ℕ} : ∀ (l : List Move) (c : Config),
    (∀ m ∈ l, m.v < n) → c n = Cell.pebble → ok n s c l = true →
    ok (n + 1) (s + 1) c l = true := by
  intro l
  induction l with
  | nil =>
      intro c _ hpn h
      unfold ok at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      rw [pcount_succ, if_pos hpn]
      omega
  | cons a l ih =>
      intro c hlt hpn h
      have hav : a.v < n := hlt a (by simp)
      unfold ok at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      refine ⟨⟨?_, legal_mono (by omega) h.1.2⟩, ?_⟩
      · rw [pcount_succ, if_pos hpn]; omega
      · refine ih (step c a) (fun m hm => hlt m (by simp [hm])) ?_ h.2
        rw [step_ne_of_ne (by omega)]; exact hpn

/-! ## 本体 -/

/-- **KSS Lemma 3.2 の核**。`c` は長さ `n` の鎖の unghosting の始状態（終端がゴースト）、
`d` は長さ `n+1` の鎖の全空。 -/
theorem run_pebble_of_ghost {n s : ℕ} (hn : 1 ≤ n) :
    ∀ (ms : List Move) (c d : Config),
      (∀ v, v < n - 1 → c v = d v) →
      c (n - 1) = Cell.ghost → d (n - 1) = Cell.empty → d n = Cell.empty →
      Run n s c ms allEmpty →
      ∃ ms', ms'.length ≤ ms.length + 1 ∧
        Run (n + 1) (s + 1) d ms' (sinkPebble (n + 1)) := by
  intro ms
  induction ms with
  | nil =>
      intro c d _ hc _ _ h
      obtain ⟨_, hagree⟩ := h
      have h0 : c (n - 1) = allEmpty (n - 1) := hagree (n - 1) (by omega)
      rw [hc] at h0
      simp [allEmpty] at h0
  | cons a ms ih =>
      intro c d hcd hc hd hdn h
      obtain ⟨hok, hagree⟩ := h
      have hleg : legal n c a = true := ok_head hok
      have hlt : a.v < n := legal_lt hleg
      have hcap : pcount n c ≤ s := by
        unfold ok at hok
        exact of_decide_eq_true (Bool.and_elim_left (Bool.and_elim_left hok))
      have hokT : ok n s (step c a) ms = true := ok_tail hok
      have hcapT : pcount n (step c a) ≤ s := by
        cases ms with
        | nil => unfold ok at hokT; simpa using hokT
        | cons b l =>
            unfold ok at hokT
            exact of_decide_eq_true (Bool.and_elim_left (Bool.and_elim_left hokT))
      have hmsv : ∀ m ∈ ms, m.v < n := by
        have hval : valid n (step c a) ms = true := ((ok_iff ms (step c a)).mp hokT).1
        exact fun m hm => valid_lt ms (step c a) hval m hm
      -- `[0,n)` 上のペブル数は等しい（終端はゴースト vs 空でどちらも非ペブル）
      have hpc : pcount n c = pcount n d := by
        unfold pcount
        refine congrArg Finset.card (Finset.filter_congr fun v hv => ?_)
        have hvn : v < n := Finset.mem_range.mp hv
        by_cases h1 : v = n - 1
        · subst h1; rw [hc, hd]; simp
        · rw [hcd v (by omega)]
      have hpcd : pcount (n + 1) d = pcount n d := by
        rw [pcount_succ, if_neg (by rw [hdn]; simp)]
        omega
      have hlegm := Bool.and_elim_right (by unfold legal at hleg; exact hleg)
      by_cases hv : a.v = n - 1
      · -- 終端への最初の手。`c (n-1) = ghost` なので `unghost` に限られる
        have hcv : c a.v = Cell.ghost := by rw [hv]; exact hc
        have hop : a.op = Op.unghost := by
          cases hop : a.op with
          | pebble =>
              rw [hop] at hlegm
              rw [of_decide_eq_true (Bool.and_elim_left hlegm)] at hcv
              exact Cell.noConfusion hcv
          | unpebble =>
              rw [hop] at hlegm
              rw [of_decide_eq_true (Bool.and_elim_left hlegm)] at hcv
              exact Cell.noConfusion hcv
          | ghost =>
              rw [hop] at hlegm
              rw [of_decide_eq_true hlegm] at hcv
              exact Cell.noConfusion hcv
          | unghost => rfl
        have hrc : ready c a.v = true := by rw [hop] at hlegm; exact Bool.and_elim_right hlegm
        have hready : ready d (n - 1) = true := by
          unfold ready at hrc ⊢
          by_cases h0 : n - 1 = 0
          · simp [h0]
          · rw [← hcd (n - 1 - 1) (by omega), ← hv]; exact hrc
        -- 第 1 手 `pebble (n-1)`、第 2 手 `pebble n`
        have h1n : ∀ w, w ≠ n - 1 → step d ⟨Op.pebble, n - 1⟩ w = d w :=
          fun w hw => step_ne_of_ne (Ne.symm hw)
        have h1at : step d ⟨Op.pebble, n - 1⟩ (n - 1) = Cell.pebble := step_self _ _
        have h2n : ∀ w, w ≠ n → step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩ w
            = step d ⟨Op.pebble, n - 1⟩ w := fun w hw => step_ne_of_ne (Ne.symm hw)
        have h2at : step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩ n = Cell.pebble :=
          step_self _ _
        have hA : AgreeOn n (step c a)
            (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩) := by
          intro w hw
          rw [h2n w (by omega)]
          by_cases h1 : w = n - 1
          · subst h1
            rw [h1at, ← hv, step_self, hop]; rfl
          · rw [h1n w h1, step_ne_of_ne (by omega)]
            exact hcd w (by omega)
        -- ペブル数
        have hA1 : AgreeOn n (step c a) (step d ⟨Op.pebble, n - 1⟩) := by
          intro w hw
          rw [← h2n w (by omega)]
          exact hA w hw
        have hpc1 : pcount n (step d ⟨Op.pebble, n - 1⟩) = pcount n (step c a) :=
          (pcount_congr hA1).symm
        have hpcd1 : pcount (n + 1) (step d ⟨Op.pebble, n - 1⟩)
            = pcount n (step c a) := by
          rw [pcount_succ, if_neg (by rw [h1n n (by omega), hdn]; simp), hpc1]
          omega
        have hpc2 : pcount n (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩)
            = pcount n (step d ⟨Op.pebble, n - 1⟩) :=
          pcount_congr (fun w hw => h2n w (by omega))
        have hpcd2 : pcount (n + 1) (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩)
            = pcount n (step c a) + 1 := by
          rw [pcount_succ, if_pos h2at, hpc2, hpc1]
        refine ⟨⟨Op.pebble, n - 1⟩ :: ⟨Op.pebble, n⟩ :: ms, by simp, ?_, ?_⟩
        · show (decide (pcount (n + 1) d ≤ s + 1) && legal (n + 1) d ⟨Op.pebble, n - 1⟩
                && ok (n + 1) (s + 1) (step d ⟨Op.pebble, n - 1⟩) (⟨Op.pebble, n⟩ :: ms)) = true
          have hleg1 : legal (n + 1) d ⟨Op.pebble, n - 1⟩ = true := by
            show (decide (n - 1 < n + 1) &&
              (decide (d (n - 1) = Cell.empty) && ready d (n - 1))) = true
            rw [hd, hready]; simp
          have hleg2 : legal (n + 1) (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩ = true := by
            show (decide (n < n + 1) &&
              (decide (step d ⟨Op.pebble, n - 1⟩ n = Cell.empty)
                && ready (step d ⟨Op.pebble, n - 1⟩) n)) = true
            have : ready (step d ⟨Op.pebble, n - 1⟩) n = true := by
              unfold ready
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              exact Or.inr (by rw [show n - 1 = n - 1 from rfl]; exact h1at)
            rw [h1n n (by omega), hdn, this]; simp
          have htail : ok (n + 1) (s + 1)
              (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩) ms = true :=
            ok_extend_pebble ms _ hmsv h2at (ok_congr hA hokT)
          rw [hleg1]
          show (decide (pcount (n + 1) d ≤ s + 1) && true &&
            (decide (pcount (n + 1) (step d ⟨Op.pebble, n - 1⟩) ≤ s + 1)
              && legal (n + 1) (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩
              && ok (n + 1) (s + 1) (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩) ms)) = true
          rw [hleg2, htail]
          simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
          omega
        · intro v hv1
          show exec (step (step d ⟨Op.pebble, n - 1⟩) ⟨Op.pebble, n⟩) ms v = sinkPebble (n + 1) v
          rw [sinkPebble_apply]
          by_cases hvn : v = n
          · subst hvn
            rw [exec_untouched ms _ (fun m hm => by have := hmsv m hm; omega), h2at,
              if_pos (by omega)]
          · rw [if_neg (by omega), ← exec_congr ms hA v (by omega)]
            exact hagree v (by omega)
      · -- 終端以外の手はそのまま真似できる
        have hltm : a.v < n - 1 := by omega
        have hlegd : legal n d a = true := by
          have hrd : ready d a.v = ready c a.v := by
            unfold ready; rw [hcd (a.v - 1) (by omega)]
          unfold legal at hleg ⊢
          rw [← hcd a.v hltm, hrd]
          exact hleg
        obtain ⟨ms'', hlen'', hok'', hag''⟩ :=
          ih (step c a) (step d a)
            (fun w hw => by
              by_cases h1 : w = a.v
              · subst h1; rw [step_self, step_self]
              · rw [step_ne_of_ne (Ne.symm h1), step_ne_of_ne (Ne.symm h1)]; exact hcd w hw)
            (by rw [step_ne_of_ne (by omega)]; exact hc)
            (by rw [step_ne_of_ne (by omega)]; exact hd)
            (by rw [step_ne_of_ne (by omega)]; exact hdn)
            ⟨hokT, hagree⟩
        refine ⟨a :: ms'', by simp; omega, ?_, ?_⟩
        · show (decide (pcount (n + 1) d ≤ s + 1) && legal (n + 1) d a
                && ok (n + 1) (s + 1) (step d a) ms'') = true
          rw [legal_mono (by omega) hlegd, hok'']
          simp only [Bool.and_true, decide_eq_true_eq]
          omega
        · exact hag''

/-- **KSS Lemma 3.2**: `T_P(n+1, s+1) ≤ T_UG(n,s) + 1`。 -/
theorem TP_le_TUG_succ {n s : ℕ} (hn : 1 ≤ n) (hne : (UGLengths n s).Nonempty) :
    TP (n + 1) (s + 1) ≤ TUG n s + 1 := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨ms', hlen', hrun'⟩ :=
    run_pebble_of_ghost hn ms (sinkGhost n) allEmpty
      (fun v hv => by rw [sinkGhost_apply, if_neg (by omega)]; rfl)
      (by rw [sinkGhost_apply, if_pos rfl])
      rfl rfl hrun
  have h1 : TP (n + 1) (s + 1) ≤ ms'.length := TP_le ⟨ms', rfl, hrun'⟩
  unfold TUG
  omega

/-! ## `T(n,3) = n²-n-3` の上界 -/

/-- **`T_P(n,3) ≤ n²-n-3`（`n ≥ 4`）**。`T_UG(n-1,2)=（n-1)²+(n-1)-4` を橋渡しするだけ。 -/
theorem TP_cap3_le {n : ℕ} (hn : 4 ≤ n) : TP n 3 + n + 3 ≤ n * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have hbridge : TP (j + 4) 3 ≤ TUG (j + 3) 2 + 1 :=
    TP_le_TUG_succ (n := j + 3) (s := 2) (by omega)
      (UGLengths_nonempty (by omega) (by omega))
  have hug : TUG (j + 3) 2 + 4 = (j + 3) * (j + 3) + (j + 3) := TUG_cap2 (by omega)
  have hexp : (j + 4) * (j + 4) = (j + 3) * (j + 3) + 2 * j + 7 := by ring
  omega

end Spooky
