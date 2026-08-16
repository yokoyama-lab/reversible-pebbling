/-
# KSS Lemma 4.10 — `T_UG(n,s) ≤ T_UP(n,s) + 1`

unghosting は unpebbling より **たかだか 1 手しか損をしない**。

## 証明（外科手術）

始状態の違いは終端 `v_{n-1}` の 1 マスだけである（ペブル vs ゴースト）。
**鎖の終端には後続が無いので、そのマスは誰の前提条件にもならない**
（前提条件 `ready c v` が見るのは `v - 1` で、手は `v < n` にしか打てないから
`v - 1 ≤ n - 2`）。したがって unpebbling の手順をそのまま真似できる。

真似できなくなるのは、手順が初めて `v_{n-1}` を触る瞬間だけ。そのときの手は
（`v_{n-1}` がペブルなので）`ghost` か `unpebble` の 2 通りしかない。

- **`ghost (n-1)`**: こちらは既にゴーストなので **その 1 手を飛ばす**（`-1` 手）
- **`unpebble (n-1)`**: 直前に **`unghost (n-1)` を 1 手挿む**（`+1` 手）。
  `unpebble` が打てた以上 `ready` は成立しているので `unghost` も打てる。
  ペブル数は挿入前は相手より 1 少なく、挿入後はちょうど等しいので上限も破らない

どちらの枝でも `≤ |M| + 1`。**ゴースト側が 1 手得をすることもある**（前者の枝）のが、
`T_UG` が `T_UP` より小さくなりうる理由である。パリティ（`Parity.lean`）が
`T_UG ≠ T_UP` を保証するので、差は必ず `±1` 以上。

「初めて触る瞬間」を明示的に切り出す代わりに、**始配置を一般化した帰納法**で書く
（`Decomp.lean` / `Upper.lean` と同じ手口）。不変条件「`c` と `d` は `v_{n-1}` 以外で
一致し、そこだけ `c` はペブル・`d` はゴースト」を保ったまま手を 1 つずつ進め、
`v_{n-1}` に手が来た所で上の 2 枝に分かれて帰納が終わる。
-/
import SpookyPebbling.Slope4

namespace Spooky

/-! ## 不変条件つきの外科手術 -/

/-- **KSS Lemma 4.10 の核**。`c` は終端がペブル、`d` は終端がゴースト、他は一致。
`c` から空へ行く手順が在れば、`d` から空へ行く手順が高々 1 手増しで在る。 -/
theorem run_ghost_of_pebble {n s : ℕ} (hn : 1 ≤ n) :
    ∀ (ms : List Move) (c d : Config),
      (∀ v, v ≠ n - 1 → c v = d v) → c (n - 1) = Cell.pebble → d (n - 1) = Cell.ghost →
      Run n s c ms allEmpty →
      ∃ ms', ms'.length ≤ ms.length + 1 ∧ Run n s d ms' allEmpty := by
  intro ms
  induction ms with
  | nil =>
      intro c d _ hc _ h
      obtain ⟨_, hagree⟩ := h
      have h0 : c (n - 1) = allEmpty (n - 1) := hagree (n - 1) (by omega)
      rw [hc] at h0
      simp [allEmpty] at h0
  | cons m ms ih =>
      intro c d hcd hc hd h
      obtain ⟨hok, hagree⟩ := h
      have hleg : legal n c m = true := ok_head hok
      have hlt : m.v < n := legal_lt hleg
      have hcap : pcount n c ≤ s := by
        unfold ok at hok
        exact of_decide_eq_true (Bool.and_elim_left (Bool.and_elim_left hok))
      -- ゴースト側のペブル数はちょうど 1 少ない
      have hagd : AgreeOn n (Function.update c (n - 1) Cell.ghost) d := by
        intro v hv
        by_cases h1 : v = n - 1
        · subst h1; rw [Function.update_self]; exact hd.symm
        · rw [Function.update_of_ne h1]; exact hcd v h1
      have hdc : pcount n d + 1 = pcount n c := by
        rw [← pcount_congr hagd]
        exact pcount_update_nonpebble (by omega) hc (by simp)
      by_cases hv : m.v = n - 1
      · -- 終端に手が来た。`c` がペブルなので `ghost` か `unpebble` しかない
        have hcv : c m.v = Cell.pebble := by rw [hv]; exact hc
        unfold legal at hleg
        have hleg' := Bool.and_elim_right hleg
        cases hop : m.op with
        | pebble =>
            rw [hop] at hleg'
            have h1 := of_decide_eq_true (Bool.and_elim_left hleg')
            rw [hcv] at h1; exact Cell.noConfusion h1
        | unghost =>
            rw [hop] at hleg'
            have h1 := of_decide_eq_true (Bool.and_elim_left hleg')
            rw [hcv] at h1; exact Cell.noConfusion h1
        | ghost =>
            -- その 1 手を飛ばす
            have hA : AgreeOn n (step c m) d := by
              intro w hw
              show Function.update c m.v (result m.op) w = d w
              rw [hop]
              by_cases h1 : w = m.v
              · subst h1; rw [Function.update_self, hv]; exact hd.symm
              · rw [Function.update_of_ne h1]; exact hcd w (by omega)
            refine ⟨ms, by simp only [List.length_cons]; omega, ok_congr hA (ok_tail hok), ?_⟩
            intro v hvn
            rw [← exec_congr ms hA v hvn]
            exact hagree v hvn
        | unpebble =>
            -- 直前に `unghost (n-1)` を挿む
            rw [hop] at hleg'
            have hrc : ready c m.v = true := Bool.and_elim_right hleg'
            have hlt1 : n - 1 < n := by omega
            have hready : ready d (n - 1) = true := by
              unfold ready at hrc ⊢
              by_cases h0 : n - 1 = 0
              · simp [h0]
              · rw [← hcd (n - 1 - 1) (by omega), ← hv]; exact hrc
            have hlegg : legal n d ⟨Op.unghost, n - 1⟩ = true := by
              show (decide (n - 1 < n) && (decide (d (n - 1) = Cell.ghost) && ready d (n - 1)))
                  = true
              rw [hd, hready]
              simp [hlt1]
            -- `unghost` の後は `c` と完全に一致する
            have hA : AgreeOn n c (step d ⟨Op.unghost, n - 1⟩) := by
              intro w hw
              show c w = Function.update d (n - 1) Cell.pebble w
              by_cases h1 : w = n - 1
              · subst h1; rw [Function.update_self]; exact hc
              · rw [Function.update_of_ne h1]; exact hcd w h1
            refine ⟨⟨Op.unghost, n - 1⟩ :: m :: ms,
              by simp only [List.length_cons]; omega, ?_, ?_⟩
            · show (decide (pcount n d ≤ s) && legal n d ⟨Op.unghost, n - 1⟩
                    && ok n s (step d ⟨Op.unghost, n - 1⟩) (m :: ms)) = true
              rw [hlegg, ok_congr hA hok]
              simp only [Bool.and_true, decide_eq_true_eq]
              omega
            · intro v hvn
              show exec (step d ⟨Op.unghost, n - 1⟩) (m :: ms) v = allEmpty v
              rw [← exec_congr (m :: ms) hA v hvn]
              exact hagree v hvn
      · -- 終端以外の手はそのまま真似できる
        have hrd : ready d m.v = ready c m.v := by
          unfold ready
          rw [hcd (m.v - 1) (by omega)]
        have hlegd : legal n d m = true := by
          unfold legal at hleg ⊢
          rw [← hcd m.v hv, hrd]
          exact hleg
        obtain ⟨ms'', hlen'', hok'', hag''⟩ :=
          ih (step c m) (step d m)
            (by
              intro w hw
              unfold step
              by_cases h1 : w = m.v
              · subst h1; rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne h1, Function.update_of_ne h1]; exact hcd w hw)
            (by unfold step; rw [Function.update_of_ne (by omega : n - 1 ≠ m.v)]; exact hc)
            (by unfold step; rw [Function.update_of_ne (by omega : n - 1 ≠ m.v)]; exact hd)
            ⟨ok_tail hok, hagree⟩
        refine ⟨m :: ms'', by simp only [List.length_cons]; omega, ?_, ?_⟩
        · show (decide (pcount n d ≤ s) && legal n d m && ok n s (step d m) ms'') = true
          rw [hlegd, hok'']
          simp only [Bool.and_true, decide_eq_true_eq]
          omega
        · exact hag''

/-! ## 主張 -/

/-- **KSS Lemma 4.10**: `T_UG(n,s) ≤ T_UP(n,s) + 1`。 -/
theorem TUG_le_TUP_succ {n s : ℕ} (hn : 1 ≤ n) (hne : (UPLengths n s).Nonempty) :
    TUG n s ≤ TUP n s + 1 := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨ms', hlen', hrun'⟩ :=
    run_ghost_of_pebble hn ms (sinkPebble n) (sinkGhost n)
      (fun v hv => by rw [sinkPebble_apply, sinkGhost_apply, if_neg hv, if_neg hv])
      (by rw [sinkPebble_apply, if_pos rfl])
      (by rw [sinkGhost_apply, if_pos rfl])
      hrun
  have h1 : TUG n s ≤ ms'.length := TUG_le ⟨ms', rfl, hrun'⟩
  unfold TUP
  omega

/-- **定理A の `T_UP` 版**: `T_UP(n,s) ≥ 4n - 2s - 1`（`s ≥ 2`）。

定理D（傾き 6 の下界）の望遠鏡が、頭の unpebbling についてこの形を要求する。 -/
theorem TUP_ge_slope4 {n s : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) (hne : (UPLengths n s).Nonempty) :
    4 * n ≤ TUP n s + 2 * s + 1 := by
  have h1 := TUG_ge_slope4 hs n hn
  have h2 := TUG_le_TUP_succ hn hne
  omega

end Spooky
