/-
# KSS Lemma 4.8 — `T_UG(n,s) + 1 ≤ T_P(n+1, s+1)`（上限 3 → 2 の場合）

`Bridge.lean` の逆向き。pebbling を unghosting に落とす。KSS の証明:

> $P$ が `v_{n+1}`（0-indexed `v_n`）に**最後に**作用する手を $t$ とする。これは置く手なので
> `v_n`(0-indexed `v_{n-1}`) も `v_{n+1}` もペブル。前半を Lemma 4.5 の正準な置き方
> `I` に置き換えると 2 手以上短くなり、後半は `v_n` への外科手術（Lemma 4.10 と同型）で
> 高々 1 手増える。

**上限 3 → 2 に特化する。** これで $T(n,3)=n^2-n-3$ が閉じる。上限 3 では時刻 $t$ に
`v_{n-1}` と `v_n` が埋まっているので、**頭のペブルは高々 1 個**。したがって Lemma 4.5 の
正準な置き方は `Sweep.lean` の `sweep`（ペブル 2 個・`2M+1` 手）でよく、
一般の $s$ に要る「任意の集合 $S$ を置く正準手順」を作らずに済む。

## 段取り

1. `v_n` への最後の手で `ms = l₁ ++ a :: l₂` と切る（`split_last`）
2. **数え上げ**: `l₁ ++ [a]` は `v_0..v_n` を各 1 回以上置き、`v_0..v_{M-1}` を各 1 回以上
   外す。よって `|l₁| + 1 ≥ (n+1) + M`
3. **後半**: `l₂` の手はすべて `< n` で `v_n` はペブルのまま。上限を落として長さ `n` の鎖の
   手順にする（`ok_restrict`）
4. **ゴーストの辻褄**: `Run_stripGhosts`（余分なゴーストを消す）→ `Run_reghost`（掃きが
   残すゴーストを足す）→ `run_ghost_of_pebble`（終端をペブルからゴーストへ、+1 手）
5. **前半**: `sweep (M+1)`（`2M+1` 手）。合計 `2M+2+|l₂| ≤ |l₁|+|l₂| = |ms|-1`
   （`M ≤ n-2` から）
-/
import SpookyPebbling.Bridge

namespace Spooky

/-! ## 補助 -/

/-- 対象頂点への**最後の**手で切る。 -/
theorem split_last {v : ℕ} : ∀ (ms : List Move), (∃ m ∈ ms, m.v = v) →
    ∃ l₁ a l₂, ms = l₁ ++ a :: l₂ ∧ a.v = v ∧ ∀ m ∈ l₂, m.v ≠ v := by
  intro ms
  induction ms with
  | nil => intro h; obtain ⟨m, hm, _⟩ := h; simp at hm
  | cons b ms ih =>
      intro h
      by_cases hrest : ∃ m ∈ ms, m.v = v
      · obtain ⟨l₁, a, l₂, heq, hav, hl₂⟩ := ih hrest
        exact ⟨b :: l₁, a, l₂, by rw [heq, List.cons_append], hav, hl₂⟩
      · have hbv : b.v = v := by
          obtain ⟨m, hm, hmv⟩ := h
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact hmv
          · exact absurd ⟨m, hm', hmv⟩ hrest
        refine ⟨[], b, ms, rfl, hbv, ?_⟩
        intro m hm hmv
        exact hrest ⟨m, hm, hmv⟩

/-- 上限を落とす（`ok_extend_pebble` の逆）。 -/
theorem ok_restrict {n s : ℕ} : ∀ (l : List Move) (c : Config),
    (∀ m ∈ l, m.v < n) → c n = Cell.pebble → ok (n + 1) (s + 1) c l = true →
    ok n s c l = true := by
  intro l
  induction l with
  | nil =>
      intro c _ hpn h
      unfold ok at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      rw [pcount_succ, if_pos hpn] at h
      omega
  | cons a l ih =>
      intro c hlt hpn h
      have hav : a.v < n := hlt a (by simp)
      unfold ok at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := h.1.1; rw [pcount_succ, if_pos hpn] at this; omega
      · have hleg := h.1.2
        unfold legal at hleg ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hleg ⊢
        exact ⟨hav, hleg.2⟩
      · refine ih (step c a) (fun m hm => hlt m (by simp [hm])) ?_ h.2
        rw [step_ne_of_ne (by omega)]; exact hpn

/-- 一般の始配置からでも「最下位ペブルより下は必ず 1 回は置かれる」。 -/
theorem places_below {n s M : ℕ} {a : Config} {ms : List Move}
    (hM : M < n) (hpa : a M = Cell.pebble) (hbelow : ∀ j, j < M → a j ≠ Cell.pebble)
    (h : Run n s a ms allEmpty) :
    ∀ j, j < M → 0 < ms.countP (isPlace j) := by
  intro j hj
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, _⟩ := (ok_iff ms a).mp hok
  have hend : exec a ms M = Cell.empty := by rw [hagree M hM]; rfl
  obtain ⟨l₁, l₂, heq, hpp⟩ :=
    pred_pebbled_of_clear ms.length ms le_rfl a hv (by omega) hpa hend
  have hv₁ : valid n a l₁ = true := valid_append_left l₁ l₂ _ (heq ▸ hv)
  obtain ⟨r₁, r₂, hr, hrp⟩ :=
    reaches_below (M - 1) l₁ a hv₁ (fun t ht => hbelow t (by omega)) hpp j (by omega)
  have hplace : 0 < r₁.countP (isPlace j) := exists_place r₁ a (hbelow j hj) hrp
  have h1 : r₁.countP (isPlace j) ≤ ms.countP (isPlace j) := by
    rw [heq, hr, List.append_assoc, List.countP_append]; omega
  omega

/-- `M` より上に手が来ないなら、`pcount` は `M+1` までで決まる。 -/
theorem pcount_eq_of_above_clear {n k : ℕ} {c : Config} (hkn : k ≤ n)
    (h : ∀ v, k ≤ v → v < n → c v ≠ Cell.pebble) : pcount n c = pcount k c := by
  unfold pcount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨by by_contra hc; exact h v (by omega) hv hp, hp⟩
  · rintro ⟨hv, hp⟩
    exact ⟨by omega, hp⟩


/-- `ok` から先頭の上限を取り出す。 -/
theorem ok_cap {n s : ℕ} {c : Config} : ∀ {l : List Move}, ok n s c l = true → pcount n c ≤ s
  | [], h => by unfold ok at h; simpa using h
  | _ :: _, h => by
      unfold ok at h
      exact of_decide_eq_true (Bool.and_elim_left (Bool.and_elim_left h))

/-- `Bridge.lean` の構成から、長さ `n+1` の pebbling は実現可能。 -/
theorem PLengths_succ_nonempty {n s : ℕ} (hn : 1 ≤ n) (hne : (UGLengths n s).Nonempty) :
    (PLengths (n + 1) (s + 1)).Nonempty := by
  obtain ⟨ms, _, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨ms', _, hrun'⟩ :=
    run_pebble_of_ghost hn ms (sinkGhost n) allEmpty
      (fun v hv => by rw [sinkGhost_apply, if_neg (by omega)]; rfl)
      (by rw [sinkGhost_apply, if_pos rfl]) rfl rfl hrun
  exact ⟨ms'.length, ms', rfl, hrun'⟩

/-! ## 本体 -/

/-- **KSS Lemma 4.8（上限 3 → 2）**: `T_UG(n,2) + 1 ≤ T_P(n+1,3)`。 -/
theorem TUG_le_TP_cap3 {p : ℕ} : TUG (p + 2) 2 + 1 ≤ TP (p + 3) 3 := by
  obtain ⟨ms, hlen, hrun⟩ :=
    Nat.sInf_mem (PLengths_succ_nonempty (n := p + 2) (s := 2) (by omega)
      (UGLengths_nonempty (by omega) (by omega)))
  obtain ⟨hok, hagree⟩ := hrun
  obtain ⟨hv, hcapall⟩ := (ok_iff ms allEmpty).mp hok
  -- `v_{p+2}` は必ず置かれる
  have hend : exec allEmpty ms (p + 2) = Cell.pebble := by
    rw [hagree (p + 2) (by omega), sinkPebble_apply, if_pos (by omega)]
  have hcount : 0 < ms.countP (isPlace (p + 2)) :=
    exists_place ms allEmpty (by simp [allEmpty]) hend
  have hex : ∃ m ∈ ms, m.v = p + 2 := by
    by_contra hcon
    have hz : ms.countP (isPlace (p + 2)) = 0 := by
      refine List.countP_eq_zero.mpr fun m hm => ?_
      simp only [Bool.not_eq_true]
      by_contra hp
      simp only [Bool.not_eq_false] at hp
      exact hcon ⟨m, hm, isPlace_v hp⟩
    omega
  obtain ⟨l₁, a, l₂, hms, hav, hl₂⟩ := split_last ms hex
  subst hms
  -- 記号
  have hc₁ : exec allEmpty (l₁ ++ [a]) = step (exec allEmpty l₁) a := by
    rw [exec_append]; rfl
  set c₁ := exec allEmpty l₁ with hc₁def
  set b := step c₁ a with hbdef
  have hokmid : ok (p + 3) 3 c₁ (a :: l₂) = true := ok_append_right l₁ (a :: l₂) allEmpty hok
  have hlega : legal (p + 3) c₁ a = true := ok_head hokmid
  have hokT : ok (p + 3) 3 b l₂ = true := ok_tail hokmid
  have hvT : valid (p + 3) b l₂ = true := ((ok_iff l₂ b).mp hokT).1
  have hl₂lt : ∀ m ∈ l₂, m.v < p + 2 := by
    intro m hm
    have h1 := valid_lt l₂ b hvT m hm
    have h2 := hl₂ m hm
    omega
  -- `b` の終端はペブル
  have hbn : b (p + 2) = Cell.pebble := by
    have : exec b l₂ (p + 2) = Cell.pebble := by
      rw [show exec b l₂ = exec allEmpty (l₁ ++ a :: l₂) by rw [exec_append]; rfl]
      exact hend
    rwa [exec_untouched l₂ b (fun m hm => hl₂ m hm)] at this
  -- `a` は置く手で、`v_{p+1}` のペブルを要求する
  have hres : result a.op = Cell.pebble := by rw [← step_self c₁ a, hav]; exact hbn
  have hlegm := Bool.and_elim_right (by unfold legal at hlega; exact hlega)
  have hplacea : isPlace (p + 2) a = true := by
    unfold isPlace
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨hav, ?_⟩
    cases hop : a.op with
    | pebble => exact Or.inl rfl
    | unghost => exact Or.inr rfl
    | unpebble => rw [hop] at hres; exact absurd hres (by simp [result])
    | ghost => rw [hop] at hres; exact absurd hres (by simp [result])
  have hready : ready c₁ a.v = true := by
    cases hop : a.op with
    | pebble => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
    | unghost => rw [hop] at hlegm; exact Bool.and_elim_right hlegm
    | unpebble => rw [hop] at hres; exact absurd hres (by simp [result])
    | ghost => rw [hop] at hres; exact absurd hres (by simp [result])
  have hc₁pred : c₁ (p + 1) = Cell.pebble := by
    unfold ready at hready
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hready
    rcases hready with h0 | h1
    · omega
    · rw [hav] at h1; simpa using h1
  have hbpred : b (p + 1) = Cell.pebble := by
    rw [hbdef, step_ne_of_ne (by omega)]; exact hc₁pred
  -- 頭のペブルは高々 1 個
  have hbcap : pcount (p + 3) b ≤ 3 := ok_cap hokT
  have hcnt : pcount (p + 1) b ≤ 1 := by
    have h1 : pcount (p + 3) b = pcount (p + 2) b + 1 := by
      rw [pcount_succ, if_pos hbn]
    have h2 : pcount (p + 2) b = pcount (p + 1) b + 1 := by
      rw [pcount_succ, if_pos hbpred]
    omega
  -- 後半は長さ `p+2` の鎖の上限 2 の手順
  have hsuf : Run (p + 2) 2 b l₂ allEmpty := by
    refine ⟨ok_restrict l₂ b hl₂lt hbn hokT, ?_⟩
    intro w hw
    rw [show exec b l₂ = exec allEmpty (l₁ ++ a :: l₂) by rw [exec_append]; rfl,
      hagree w (by omega), sinkPebble_apply, if_neg (by omega)]
    rfl
  -- ゴーストを落とす
  obtain ⟨hsuf', hlen'⟩ := Run_stripGhosts hsuf
  have hsg : ∀ w, stripGhosts b w = Cell.pebble ↔ b w = Cell.pebble := by
    intro w; unfold stripGhosts
    by_cases hg : b w = Cell.ghost <;> simp [hg]
  have hsgP : stripGhosts b (p + 1) = Cell.pebble := (hsg _).mpr hbpred
  have hcell3 : ∀ x : Cell, x ≠ Cell.pebble → x ≠ Cell.ghost → x = Cell.empty := by
    intro x h1 h2; cases x <;> simp_all
  have hsgE : ∀ w, b w ≠ Cell.pebble → stripGhosts b w = Cell.empty := by
    intro w hw
    unfold stripGhosts
    by_cases hg : b w = Cell.ghost
    · simp [hg]
    · rw [if_neg hg]; exact hcell3 (b w) hw hg
  -- 数え上げ（前半）
  have hvfull : valid (p + 3) allEmpty (l₁ ++ [a]) = true := by
    refine valid_append_left (l₁ ++ [a]) l₂ allEmpty ?_
    rw [List.append_assoc]; exact hv
  have hv₁ : valid (p + 3) allEmpty l₁ = true := valid_append_left l₁ _ allEmpty hvfull
  have hplaces : ∀ j, j < p + 3 → 0 < (l₁ ++ [a]).countP (isPlace j) := by
    intro j hj
    rcases Nat.lt_or_ge j (p + 2) with hjlt | hjge
    · obtain ⟨r₁, r₂, hr, hrp⟩ :=
        reaches_below (p + 1) l₁ allEmpty hv₁ (fun t _ => by simp [allEmpty])
          hc₁pred j (by omega)
      have h1 : 0 < r₁.countP (isPlace j) :=
        exists_place r₁ allEmpty (by simp [allEmpty]) hrp
      have h2 : r₁.countP (isPlace j) ≤ (l₁ ++ [a]).countP (isPlace j) := by
        rw [hr, List.append_assoc, List.countP_append]; omega
      omega
    · have hjeq : j = p + 2 := by omega
      subst hjeq
      rw [List.countP_append]
      have : (0 : ℕ) < ([a] : List Move).countP (isPlace (p + 2)) := by
        simp [List.countP_cons, hplacea]
      omega
  have hlenTP : (l₁ ++ a :: l₂).length = TP (p + 3) 3 := hlen
  have hR₁len : (strip (stripGhosts b) l₂).length = l₂.length := hlen'
  rcases Nat.eq_zero_or_pos (pcount (p + 1) b) with h0 | hpos
  · -- 場合A: 頭にペブルが無い。前半は要らない
    have hemptyhead : ∀ w, w < p + 1 → b w ≠ Cell.pebble := pcount_eq_zero_iff.mp h0
    have hAg : AgreeOn (p + 2) (stripGhosts b) (sinkPebble (p + 2)) := by
      intro w hw
      rw [sinkPebble_apply]
      by_cases hw1 : w = p + 1
      · subst hw1; rw [hsgP, if_pos (by omega)]
      · rw [if_neg (by omega), hsgE w (hemptyhead w (by omega))]
    have hrunP : Run (p + 2) 2 (sinkPebble (p + 2)) (strip (stripGhosts b) l₂) allEmpty := by
      refine ⟨ok_congr hAg hsuf'.1, ?_⟩
      intro w hw
      rw [← exec_congr _ hAg w hw]
      exact hsuf'.2 w hw
    obtain ⟨R₃, hR₃len, hR₃⟩ :=
      run_ghost_of_pebble (n := p + 2) (s := 2) (by omega) _ (sinkPebble (p + 2))
        (sinkGhost (p + 2))
        (fun w hw => by
          rw [sinkPebble_apply, sinkGhost_apply, if_neg (by omega), if_neg (by omega)])
        (by rw [sinkPebble_apply, if_pos (by omega)])
        (by rw [sinkGhost_apply, if_pos (by omega)])
        hrunP
    have hub : TUG (p + 2) 2 ≤ R₃.length := TUG_le ⟨R₃, rfl, hR₃⟩
    have hcnt2 : (p + 3) + 0 ≤ (l₁ ++ [a]).length :=
      length_ge_of_places_removes hplaces (fun j hj => absurd hj (by omega))
    simp only [List.length_append, List.length_cons, List.length_nil] at hcnt2 hlenTP
    omega
  · -- 場合B: 頭のペブルはちょうど 1 個
    have hone : pcount (p + 1) b = 1 := by omega
    obtain ⟨hMlt, hMp, hMmin⟩ := minPeb_spec (n := p + 1) (c := b) hpos
    have hMuniq : ∀ w, w < p + 1 → w ≠ minPeb (p + 1) b → b w ≠ Cell.pebble := by
      intro w hw hne hpb
      have := two_le_pcount (n := p + 1) (c := b) hne hw hMlt hpb hMp
      omega
    -- 正準化した後半の始配置
    have hA2 : AgreeOn (p + 2) (stripGhosts b)
        (fun v => if v = p + 1 then Cell.pebble
          else if v = minPeb (p + 1) b then Cell.pebble else Cell.empty) := by
      intro w hw
      by_cases hw1 : w = p + 1
      · subst hw1; rw [hsgP]; simp
      · by_cases hw2 : w = minPeb (p + 1) b
        · subst hw2; rw [(hsg _).mpr hMp]; simp [hw1]
        · rw [hsgE w (hMuniq w (by omega) hw2)]; simp [hw1, hw2]
    have hrun2 : Run (p + 2) 2
        (fun v => if v = p + 1 then Cell.pebble
          else if v = minPeb (p + 1) b then Cell.pebble else Cell.empty)
        (strip (stripGhosts b) l₂) allEmpty := by
      refine ⟨ok_congr hA2 hsuf'.1, ?_⟩
      intro w hw
      rw [← exec_congr _ hA2 w hw]
      exact hsuf'.2 w hw
    have hplacesR : ∀ j, j < minPeb (p + 1) b →
        0 < (strip (stripGhosts b) l₂).countP (isPlace j) := by
      refine places_below (M := minPeb (p + 1) b) (by omega) ?_ ?_ hrun2
      · simp [show minPeb (p + 1) b ≠ p + 1 from by omega]
      · intro j hj
        simp [show j ≠ p + 1 from by omega, show j ≠ minPeb (p + 1) b from by omega]
    -- 掃きが残すゴーストを足す
    have hdom : Dom2 (strip (stripGhosts b) l₂)
        (fun v => if v = p + 1 then Cell.pebble else swept (minPeb (p + 1) b) (sinkGhost (p + 2)) v)
        (fun v => if v = p + 1 then Cell.pebble
          else if v = minPeb (p + 1) b then Cell.pebble else Cell.empty) := by
      intro v
      by_cases hv1 : v = p + 1
      · left; simp [hv1]
      · by_cases hv2 : v = minPeb (p + 1) b
        · left; subst hv2; simp [hv1, swept_at]
        · rcases Nat.lt_or_ge v (minPeb (p + 1) b) with hlt | hge
          · right
            refine ⟨by simp only [if_neg hv1]; exact swept_below hlt, ?_, hplacesR v hlt⟩
            simp [hv1, hv2]
          · left
            simp only [if_neg hv1, if_neg hv2]
            rw [swept_above (by omega), sinkGhost_apply, if_neg (by omega)]
    obtain ⟨hrun3, hlen3⟩ := Run_reghost hdom hrun2
    -- 終端をペブルからゴーストへ
    obtain ⟨R₃, hR₃len, hR₃⟩ :=
      run_ghost_of_pebble (n := p + 2) (s := 2) (by omega) _
        (fun v => if v = p + 1 then Cell.pebble
          else swept (minPeb (p + 1) b) (sinkGhost (p + 2)) v)
        (swept (minPeb (p + 1) b) (sinkGhost (p + 2)))
        (fun w hw => by simp only [if_neg (by omega : ¬ (w = p + 1))])
        (by simp only [if_pos (by omega : (p + 2 - 1) = p + 1)])
        (by rw [swept_above (by omega), sinkGhost_apply, if_pos rfl])
        hrun3
    -- 前半（掃き）
    obtain ⟨hsv, hse, hsp⟩ :=
      sweep_spec (minPeb (p + 1) b) (sinkGhost (p + 2))
        (fun i hi => by rw [sinkGhost_apply, if_neg (by omega)])
    have hswlt : ∀ m ∈ sweep (minPeb (p + 1) b + 1), m.v < minPeb (p + 1) b + 1 := by
      intro m hm; have := sweep_mem_le (minPeb (p + 1) b) m hm; omega
    have hokAll : ok (p + 2) 2 (sinkGhost (p + 2))
        (sweep (minPeb (p + 1) b + 1) ++ R₃) = true := by
      obtain ⟨hokR, hagR⟩ := hR₃
      obtain ⟨hvR, hcapR⟩ := (ok_iff R₃ _).mp hokR
      refine (ok_iff _ (sinkGhost (p + 2))).mpr ⟨?_, ?_⟩
      · refine valid_append _ _ _ (valid_mono (by omega) _ _ hsv) ?_
        rw [hse]; exact hvR
      · intro dd hdd
        rcases traj_append_mem _ (sinkGhost (p + 2)) _ dd hdd with hdd | hdd
        · have habove : ∀ v, minPeb (p + 1) b + 1 ≤ v → dd v = sinkGhost (p + 2) v :=
            fun v hv => traj_above _ (sinkGhost (p + 2)) hswlt dd hdd v hv
          have hclear : ∀ v, minPeb (p + 1) b + 1 ≤ v → v < p + 2 → dd v ≠ Cell.pebble := by
            intro v hv1 hv2
            rw [habove v hv1, sinkGhost_apply]
            by_cases hvq : v = p + 2 - 1
            · rw [if_pos hvq]; exact fun hcon => Cell.noConfusion hcon
            · rw [if_neg hvq]; exact fun hcon => Cell.noConfusion hcon
          rw [pcount_eq_of_above_clear (n := p + 2) (k := minPeb (p + 1) b + 1) (c := dd)
            (by omega) hclear]
          exact hsp dd hdd
        · rw [hse] at hdd; exact hcapR dd hdd
    have hendAll : AgreeOn (p + 2) (exec (sinkGhost (p + 2))
        (sweep (minPeb (p + 1) b + 1) ++ R₃)) allEmpty := by
      intro w hw
      rw [exec_append, hse]
      exact hR₃.2 w hw
    have hub : TUG (p + 2) 2 ≤ (sweep (minPeb (p + 1) b + 1) ++ R₃).length :=
      TUG_le ⟨_, rfl, hokAll, hendAll⟩
    -- 数え上げ（外す手）
    have hremoves : ∀ j, j < minPeb (p + 1) b → 0 < (l₁ ++ [a]).countP (isRemove j) := by
      intro j hj
      obtain ⟨r₁, r₂, hr, hrp⟩ :=
        reaches_below (p + 1) l₁ allEmpty hv₁ (fun t _ => by simp [allEmpty])
          hc₁pred j (by omega)
      have hne : exec (exec allEmpty r₁) (r₂ ++ [a]) j ≠ Cell.pebble := by
        rw [← exec_append r₁ (r₂ ++ [a]) allEmpty, ← List.append_assoc, ← hr, hc₁]
        exact hMuniq j (by omega) (by omega)
      have h1 : 0 < (r₂ ++ [a]).countP (isRemove j) :=
        exists_remove (r₂ ++ [a]) (exec allEmpty r₁) hrp hne
      have h2 : (r₂ ++ [a]).countP (isRemove j) ≤ (l₁ ++ [a]).countP (isRemove j) := by
        rw [hr]
        simp only [List.append_assoc, List.countP_append]
        omega
      omega
    have hcnt2 : (p + 3) + minPeb (p + 1) b ≤ (l₁ ++ [a]).length :=
      length_ge_of_places_removes hplaces hremoves
    have hswl := sweep_length (minPeb (p + 1) b)
    simp only [List.length_append, List.length_cons, List.length_nil] at hcnt2 hlenTP hub
    omega

/-! ## `T(n,3) = n²-n-3` -/

/-- **KSS Thm 4.11（上限 3）**: `T_P(n+1,3) = T_UG(n,2) + 1`。 -/
theorem TP_eq_TUG_succ_cap3 {p : ℕ} : TP (p + 3) 3 = TUG (p + 2) 2 + 1 := by
  have h1 := TUG_le_TP_cap3 (p := p)
  have h2 : TP (p + 3) 3 ≤ TUG (p + 2) 2 + 1 :=
    TP_le_TUG_succ (n := p + 2) (s := 2) (by omega) (UGLengths_nonempty (by omega) (by omega))
  omega

/-- **主定理 `T(n,3) = n² - n - 3`（`n ≥ 4`）**。`theorem_p3.py` の段5。 -/
theorem TP_cap3 {n : ℕ} (hn : 4 ≤ n) : TP n 3 + n + 3 = n * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have h1 : TP (j + 4) 3 = TUG (j + 3) 2 + 1 := TP_eq_TUG_succ_cap3 (p := j + 1)
  have h2 : TUG (j + 3) 2 + 4 = (j + 3) * (j + 3) + (j + 3) := TUG_cap2 (by omega)
  have hexp : (j + 4) * (j + 4) = (j + 3) * (j + 3) + 2 * j + 7 := by ring
  omega

end Spooky
