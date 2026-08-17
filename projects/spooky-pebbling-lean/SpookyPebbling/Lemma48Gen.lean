/-
# KSS Lemma 4.8（一般の `s`）と KSS Thm 4.11

`Lemma48.lean` は上限 3 → 2 に特化していた（頭のペブルが高々 1 個なので前半の正準形が
`sweep` で足りた）。ここでは `PlaceI.lean` の一般の正準形 `placeUpto` を使って
**任意の `s`** で回す:

$$T_{UG}(n,s) + 1 \;\le\; T_P(n+1,\,s+1) .$$

`Bridge.lean` の Lemma 3.2（逆向き）と合わせて **KSS Thm 4.11**:

$$T_P(n+1,\,s+1) \;=\; T_{UG}(n,s) + 1 .$$

つまり **$T_P$ は $T_{UG}$ で完全に決まる**。傾き 4/6 の厳密値・$\theta$・$\delta$ の
符号反転はすべて $T_{UG}$ 側で層1 になっているので、それらがそのまま $T_P$ に移る。

## 段取り（`Lemma48.lean` と同じ骨格）

1. `v_n` への**最後の**手で `ms = l₁ ++ a :: l₂` と切る
2. 数え上げ: `l₁ ++ [a]` は `v_0..v_n` を各 1 回以上置き、`v_j (j<M)` で
   `b j ≠ pebble` のものを各 1 回以上外す（`length_ge_places_removes_gen`）
3. 後半を上限 `s` に落とす（`ok_restrict`）
4. ゴーストの辻褄: `Run_stripGhosts` → `Run_reghost` → `run_ghost_of_pebble`（+1 手）
5. 前半を `placeUpto b M` に置き換える（`2M+1-|{v<M : b v = pebble}|` 手・ペブル `≤ s`）
-/
import SpookyPebbling.PlaceI

namespace Spooky

/-! ## 下からの連鎖 -/

/-- `v_M` にペブルが在って最後は空になるなら、`v_t (t ≤ M)` はどこかでペブルになる。 -/
theorem places_cascade {n s : ℕ} {a : Config} {ms : List Move}
    (h : Run n s a ms allEmpty) {M : ℕ} (hM : M < n) (hMp : a M = Cell.pebble) :
    ∀ t, t ≤ M → (0 < ms.countP (isPlace t) ∨ a t = Cell.pebble) := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, _⟩ := (ok_iff ms a).mp hok
  have key : ∀ k t, t + k = M → (0 < ms.countP (isPlace t) ∨ a t = Cell.pebble) := by
    intro k
    induction k with
    | zero => intro t ht; rw [show t = M by omega]; exact Or.inr hMp
    | succ k ih =>
        intro t ht
        have hQ := ih (t + 1) (by omega)
        have hpp : ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec a l₁ t = Cell.pebble := by
          rcases hQ with hpl | hpb
          · obtain ⟨l₁, l₂, heq, hp⟩ := pred_pebbled ms a hv (i := t + 1) (by omega) hpl
            exact ⟨l₁, l₂, heq, by simpa using hp⟩
          · have hend : exec a ms (t + 1) = Cell.empty := by
              rw [hagree (t + 1) (by omega)]; rfl
            obtain ⟨l₁, l₂, heq, hp⟩ :=
              pred_pebbled_of_clear ms.length ms le_rfl a hv (i := t + 1) (by omega) hpb hend
            exact ⟨l₁, l₂, heq, by simpa using hp⟩
        obtain ⟨l₁, l₂, heq, hp⟩ := hpp
        by_cases hat : a t = Cell.pebble
        · exact Or.inr hat
        · left
          have h1 : 0 < l₁.countP (isPlace t) := exists_place l₁ a hat hp
          have h2 : l₁.countP (isPlace t) ≤ ms.countP (isPlace t) := by
            rw [heq, List.countP_append]; omega
          omega
  intro t ht
  exact key (M - t) t (by omega)

/-! ## 数え上げの一般形 -/

/-- 置く手（`0..N-1`）と外す手（`{j<M : g j ≠ pebble}`）を並べた述語族。 -/
def cTag (g : Config) (N : ℕ) (i : ℕ) (m : Move) : Bool :=
  if i < N then isPlace i m
  else if g (i - N) = Cell.pebble then false else isRemove (i - N) m

theorem cTag_lt {g : Config} {N i : ℕ} (h : i < N) : cTag g N i = isPlace i := by
  funext m; unfold cTag; rw [if_pos h]

theorem cTag_ge_peb {g : Config} {N i : ℕ} (h : ¬ i < N) (hg : g (i - N) = Cell.pebble) :
    cTag g N i = fun _ => false := by
  funext m; unfold cTag; rw [if_neg h, if_pos hg]

theorem cTag_ge_ne {g : Config} {N i : ℕ} (h : ¬ i < N) (hg : g (i - N) ≠ Cell.pebble) :
    cTag g N i = isRemove (i - N) := by
  funext m; unfold cTag; rw [if_neg h, if_neg hg]

theorem cTag_disjoint (g : Config) (N : ℕ) :
    ∀ (m : Move) (i j : ℕ), i ≠ j → cTag g N i m = true → cTag g N j m = false := by
  intro m i j hne h
  unfold cTag at h ⊢
  by_cases hi : i < N
  · rw [if_pos hi] at h
    by_cases hj : j < N
    · rw [if_pos hj]
      unfold isPlace
      have hv : m.v = i := isPlace_v h
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by rw [hv]; exact hne)
    · rw [if_neg hj]
      by_cases hg : g (j - N) = Cell.pebble
      · rw [if_pos hg]
      · rw [if_neg hg]; exact isPlace_isRemove h
  · rw [if_neg hi] at h
    by_cases hgi : g (i - N) = Cell.pebble
    · rw [if_pos hgi] at h; exact absurd h (by simp)
    · rw [if_neg hgi] at h
      by_cases hj : j < N
      · rw [if_pos hj]; exact isRemove_isPlace h
      · rw [if_neg hj]
        by_cases hg : g (j - N) = Cell.pebble
        · rw [if_pos hg]
        · rw [if_neg hg]
          unfold isRemove
          have hv : m.v = i - N := isRemove_v h
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Or.inl (by rw [hv]; omega)

/-- **一般形の数え上げ**: `v_0..v_{N-1}` を各 1 回以上置き、`j < M` で `g j ≠ pebble` の
ものを各 1 回以上外すなら、手数は `N + M - |{j<M : g j = pebble}|` 以上。 -/
theorem length_ge_places_removes_gen {ms : List Move} {N : ℕ} {g : Config}
    (hp : ∀ j, j < N → 0 < ms.countP (isPlace j)) :
    ∀ M, (∀ j, j < M → g j ≠ Cell.pebble → 0 < ms.countP (isRemove j)) →
      N + M ≤ ms.length + pcount M g := by
  have hsum : ∀ M, (∀ j, j < M → g j ≠ Cell.pebble → 0 < ms.countP (isRemove j)) →
      N + M ≤ (∑ i ∈ Finset.range (N + M), ms.countP (cTag g N i)) + pcount M g := by
    intro M
    induction M with
    | zero =>
        intro _
        have h1 : N ≤ ∑ i ∈ Finset.range N, ms.countP (cTag g N i) := by
          calc N = ∑ _i ∈ Finset.range N, 1 := by simp
            _ ≤ _ := Finset.sum_le_sum fun i hi => by
                  rw [cTag_lt (Finset.mem_range.mp hi)]
                  exact hp i (Finset.mem_range.mp hi)
        simpa [pcount] using h1
    | succ M ih =>
        intro hr
        have hih := ih (fun j hj => hr j (by omega))
        rw [show N + (M + 1) = (N + M) + 1 from rfl, Finset.sum_range_succ, pcount_succ]
        have hsub : N + M - N = M := by omega
        have hidx : ms.countP (cTag g N (N + M))
            = if g M = Cell.pebble then 0 else ms.countP (isRemove M) := by
          by_cases hg : g M = Cell.pebble
          · rw [if_pos hg, cTag_ge_peb (by omega) (by rw [hsub]; exact hg)]
            simp
          · rw [if_neg hg, cTag_ge_ne (by omega) (by rw [hsub]; exact hg), hsub]
        rw [hidx]
        by_cases hg : g M = Cell.pebble
        · rw [if_pos hg, if_pos hg]; omega
        · rw [if_neg hg, if_neg hg]
          have := hr M (by omega) hg
          omega
  intro M hr
  have h1 := hsum M hr
  have h2 : (∑ i ∈ Finset.range (N + M), ms.countP (cTag g N i)) ≤ ms.length :=
    sum_countP_le_length (cTag g N) (cTag_disjoint g N) ms (N + M)
  omega

/-! ## 本体 -/

/-- **KSS Lemma 4.8（一般の `s`）**: `T_UG(n,s) + 1 ≤ T_P(n+1, s+1)`。 -/
theorem TUG_le_TP_succ {p s : ℕ} (hs : 2 ≤ s) : TUG (p + 2) s + 1 ≤ TP (p + 3) (s + 1) := by
  obtain ⟨ms, hlen, hrun⟩ :=
    Nat.sInf_mem (PLengths_succ_nonempty (n := p + 2) (s := s) (by omega)
      (UGLengths_nonempty hs (by omega)))
  obtain ⟨hok, hagree⟩ := hrun
  obtain ⟨hv, hcapall⟩ := (ok_iff ms allEmpty).mp hok
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
  have hc₁ : exec allEmpty (l₁ ++ [a]) = step (exec allEmpty l₁) a := by rw [exec_append]; rfl
  set c₁ := exec allEmpty l₁ with hc₁def
  set b := step c₁ a with hbdef
  have hokmid : ok (p + 3) (s + 1) c₁ (a :: l₂) = true := ok_append_right l₁ (a :: l₂) allEmpty hok
  have hlega : legal (p + 3) c₁ a = true := ok_head hokmid
  have hokT : ok (p + 3) (s + 1) b l₂ = true := ok_tail hokmid
  have hvT : valid (p + 3) b l₂ = true := ((ok_iff l₂ b).mp hokT).1
  have hl₂lt : ∀ m ∈ l₂, m.v < p + 2 := by
    intro m hm
    have h1 := valid_lt l₂ b hvT m hm
    have h2 := hl₂ m hm
    omega
  have hbn : b (p + 2) = Cell.pebble := by
    have hbb : exec b l₂ (p + 2) = Cell.pebble := by
      rw [show exec b l₂ = exec allEmpty (l₁ ++ a :: l₂) by rw [exec_append]; rfl]
      exact hend
    rwa [exec_untouched l₂ b (fun m hm => hl₂ m hm)] at hbb
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
  have hbcap : pcount (p + 3) b ≤ s + 1 := ok_cap hokT
  have hcnt : pcount (p + 1) b + 2 ≤ s + 1 := by
    have h1 : pcount (p + 3) b = pcount (p + 2) b + 1 := by rw [pcount_succ, if_pos hbn]
    have h2 : pcount (p + 2) b = pcount (p + 1) b + 1 := by rw [pcount_succ, if_pos hbpred]
    omega
  -- 後半
  have hsuf : Run (p + 2) s b l₂ allEmpty := by
    refine ⟨ok_restrict l₂ b hl₂lt hbn hokT, ?_⟩
    intro w hw
    rw [show exec b l₂ = exec allEmpty (l₁ ++ a :: l₂) by rw [exec_append]; rfl,
      hagree w (by omega), sinkPebble_apply, if_neg (by omega)]
    rfl
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
  -- 前半の数え上げ（置く手）
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
      have hone : (0 : ℕ) < ([a] : List Move).countP (isPlace (p + 2)) := by
        simp [hplacea]
      omega
  have hlenTP : (l₁ ++ a :: l₂).length = TP (p + 3) (s + 1) := hlen
  by_cases hhead : ∃ v, v ≤ p ∧ b v = Cell.pebble
  · -- 場合B: 頭にペブルが在る。最大のものを `M` として正準形で置き直す
    obtain ⟨v₀, hv₀le, hv₀p⟩ := hhead
    set M := Nat.findGreatest (fun v => b v = Cell.pebble) p with hMdef
    have hMp : b M = Cell.pebble :=
      Nat.findGreatest_spec (P := fun v => b v = Cell.pebble) hv₀le hv₀p
    have hMle : M ≤ p := Nat.findGreatest_le (P := fun v => b v = Cell.pebble) p
    have hMmax : ∀ k, M < k → k ≤ p → b k ≠ Cell.pebble :=
      fun k h1 h2 => Nat.findGreatest_is_greatest (P := fun v => b v = Cell.pebble) h1 h2
    -- 正準化した後半の始配置
    have hA2 : AgreeOn (p + 2) (stripGhosts b)
        (fun v => if v = p + 1 then Cell.pebble
          else if v < p + 1 ∧ b v = Cell.pebble then Cell.pebble else Cell.empty) := by
      intro w hw
      by_cases hw1 : w = p + 1
      · subst hw1; rw [hsgP]; simp
      · by_cases hwp : b w = Cell.pebble
        · rw [(hsg _).mpr hwp]; simp [hw1, hwp, show w < p + 1 by omega]
        · rw [hsgE w hwp]; simp [hw1, hwp]
    have hrun2 : Run (p + 2) s
        (fun v => if v = p + 1 then Cell.pebble
          else if v < p + 1 ∧ b v = Cell.pebble then Cell.pebble else Cell.empty)
        (strip (stripGhosts b) l₂) allEmpty := by
      refine ⟨ok_congr hA2 hsuf'.1, ?_⟩
      intro w hw
      rw [← exec_congr _ hA2 w hw]
      exact hsuf'.2 w hw
    have hcascade := places_cascade hrun2 (M := M) (by omega)
      (by simp [show M ≠ p + 1 by omega, show M < p + 1 by omega, hMp])
    have hplacesR : ∀ j, j < M → b j ≠ Cell.pebble →
        0 < (strip (stripGhosts b) l₂).countP (isPlace j) := by
      intro j hj hjp
      rcases hcascade j (by omega) with h | h
      · exact h
      · rw [if_neg (by omega), if_neg (by simp [hjp])] at h
        exact absurd h (by simp)
    -- 掃きが残すゴーストを足す
    have hdom : Dom2 (strip (stripGhosts b) l₂)
        (fun v => if v = p + 1 then Cell.pebble else placed b M (sinkGhost (p + 2)) v)
        (fun v => if v = p + 1 then Cell.pebble
          else if v < p + 1 ∧ b v = Cell.pebble then Cell.pebble else Cell.empty) := by
      intro v
      by_cases hv1 : v = p + 1
      · left; simp [hv1]
      · simp only [if_neg hv1]
        rcases Nat.lt_or_ge v M with hlt | hge
        · by_cases hvp : b v = Cell.pebble
          · left; rw [placed_below hlt, if_pos hvp]; simp [hvp, show v < p + 1 by omega]
          · right
            refine ⟨placed_ne_pebble hlt hvp, ?_, hplacesR v hlt hvp⟩
            simp [hvp]
        · rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · left; rw [← heq, placed_at]
            simp [hMp, show M < p + 1 by omega, ← heq]
          · left
            rw [placed_above hgt, sinkGhost_apply, if_neg (by omega)]
            rcases Nat.lt_or_ge v (p + 1) with hvlt | hvge
            · simp [hMmax v hgt (by omega)]
            · simp [show ¬ (v < p + 1) by omega]
    obtain ⟨hrun3, hlen3⟩ := Run_reghost hdom hrun2
    obtain ⟨R₃, hR₃len, hR₃⟩ :=
      run_ghost_of_pebble (n := p + 2) (s := s) (by omega) _
        (fun v => if v = p + 1 then Cell.pebble else placed b M (sinkGhost (p + 2)) v)
        (placed b M (sinkGhost (p + 2)))
        (fun w hw => by simp only [if_neg (by omega : ¬ (w = p + 1))])
        (by simp only [if_pos (by omega : (p + 2 - 1) = p + 1)])
        (by rw [placed_above (by omega), sinkGhost_apply, if_pos rfl])
        hrun3
    -- 前半（正準形）
    obtain ⟨hsv, hse, hsp⟩ :=
      placeUpto_spec b M (sinkGhost (p + 2))
        (fun i hi => by rw [sinkGhost_apply, if_neg (by omega)])
    have hMcap : pcount M b + 2 ≤ s := by
      have h1 : pcount (M + 1) b = pcount M b + 1 := by rw [pcount_succ, if_pos hMp]
      have h2 : pcount (M + 1) b ≤ pcount (p + 1) b := pcount_mono (by omega) b
      omega
    have hokAll : ok (p + 2) s (sinkGhost (p + 2)) (placeUpto b M ++ R₃) = true := by
      obtain ⟨hokR, hagR⟩ := hR₃
      obtain ⟨hvR, hcapR⟩ := (ok_iff R₃ _).mp hokR
      refine (ok_iff _ (sinkGhost (p + 2))).mpr ⟨?_, ?_⟩
      · refine valid_append _ _ _ (valid_mono (by omega) _ _ hsv) ?_
        rw [hse]; exact hvR
      · intro dd hdd
        rcases traj_append_mem _ (sinkGhost (p + 2)) _ dd hdd with hdd | hdd
        · have habove : ∀ v, M + 1 ≤ v → dd v = sinkGhost (p + 2) v :=
            fun v hvv => traj_above (k := M + 1) _ (sinkGhost (p + 2))
              (fun m hm => by have := placeUpto_mem_le b M m hm; omega) dd hdd v hvv
          have hclear : ∀ v, M + 1 ≤ v → v < p + 2 → dd v ≠ Cell.pebble := by
            intro v hv1 hv2
            rw [habove v hv1, sinkGhost_apply]
            by_cases hvq : v = p + 2 - 1
            · rw [if_pos hvq]; exact fun hcon => Cell.noConfusion hcon
            · rw [if_neg hvq]; exact fun hcon => Cell.noConfusion hcon
          rw [pcount_eq_of_above_clear (n := p + 2) (k := M + 1) (c := dd) (by omega) hclear]
          have := hsp dd hdd
          omega
        · rw [hse] at hdd; exact hcapR dd hdd
    have hendAll : AgreeOn (p + 2) (exec (sinkGhost (p + 2)) (placeUpto b M ++ R₃)) allEmpty := by
      intro w hw
      rw [exec_append, hse]
      exact hR₃.2 w hw
    have hub : TUG (p + 2) s ≤ (placeUpto b M ++ R₃).length :=
      TUG_le ⟨_, rfl, hokAll, hendAll⟩
    -- 数え上げ（外す手）
    have hremoves : ∀ j, j < M → b j ≠ Cell.pebble → 0 < (l₁ ++ [a]).countP (isRemove j) := by
      intro j hj hjp
      obtain ⟨r₁, r₂, hr, hrp⟩ :=
        reaches_below (p + 1) l₁ allEmpty hv₁ (fun t _ => by simp [allEmpty])
          hc₁pred j (by omega)
      have hne : exec (exec allEmpty r₁) (r₂ ++ [a]) j ≠ Cell.pebble := by
        rw [← exec_append r₁ (r₂ ++ [a]) allEmpty, ← List.append_assoc, ← hr, hc₁]
        exact hjp
      have h1 : 0 < (r₂ ++ [a]).countP (isRemove j) :=
        exists_remove (r₂ ++ [a]) (exec allEmpty r₁) hrp hne
      have h2 : (r₂ ++ [a]).countP (isRemove j) ≤ (l₁ ++ [a]).countP (isRemove j) := by
        rw [hr]
        simp only [List.append_assoc, List.countP_append]
        omega
      omega
    have hcnt2 : (p + 3) + M ≤ (l₁ ++ [a]).length + pcount M b :=
      length_ge_places_removes_gen hplaces M hremoves
    have hpl := placeUpto_length b M
    simp only [List.length_append, List.length_cons, List.length_nil] at hcnt2 hlenTP hub
    omega
  · -- 場合A: 頭にペブルが無い
    have hemptyhead : ∀ w, w < p + 1 → b w ≠ Cell.pebble := by
      intro w hw hp
      exact hhead ⟨w, by omega, hp⟩
    have hAg : AgreeOn (p + 2) (stripGhosts b) (sinkPebble (p + 2)) := by
      intro w hw
      rw [sinkPebble_apply]
      by_cases hw1 : w = p + 1
      · subst hw1; rw [hsgP, if_pos (by omega)]
      · rw [if_neg (by omega), hsgE w (hemptyhead w (by omega))]
    have hrunP : Run (p + 2) s (sinkPebble (p + 2)) (strip (stripGhosts b) l₂) allEmpty := by
      refine ⟨ok_congr hAg hsuf'.1, ?_⟩
      intro w hw
      rw [← exec_congr _ hAg w hw]
      exact hsuf'.2 w hw
    obtain ⟨R₃, hR₃len, hR₃⟩ :=
      run_ghost_of_pebble (n := p + 2) (s := s) (by omega) _ (sinkPebble (p + 2))
        (sinkGhost (p + 2))
        (fun w hw => by
          rw [sinkPebble_apply, sinkGhost_apply, if_neg (by omega), if_neg (by omega)])
        (by rw [sinkPebble_apply, if_pos (by omega)])
        (by rw [sinkGhost_apply, if_pos (by omega)])
        hrunP
    have hub : TUG (p + 2) s ≤ R₃.length := TUG_le ⟨R₃, rfl, hR₃⟩
    have hcnt2 : (p + 3) + 0 ≤ (l₁ ++ [a]).length + pcount 0 b :=
      length_ge_places_removes_gen hplaces 0 (fun j hj => absurd hj (by omega))
    have hz : pcount 0 b = 0 := by simp [pcount]
    simp only [List.length_append, List.length_cons, List.length_nil] at hcnt2 hlenTP
    omega

/-- **KSS Thm 4.11**: `T_P(n+1, s+1) = T_UG(n,s) + 1`（`n ≥ 2`・`s ≥ 2`）。 -/
theorem TP_eq_TUG_succ {p s : ℕ} (hs : 2 ≤ s) : TP (p + 3) (s + 1) = TUG (p + 2) s + 1 := by
  have h1 := TUG_le_TP_succ (p := p) hs
  have h2 : TP (p + 3) (s + 1) ≤ TUG (p + 2) s + 1 :=
    TP_le_TUG_succ (n := p + 2) (s := s) (by omega) (UGLengths_nonempty hs (by omega))
  omega

/-! ## `T_P` は `T_UG` で決まる

`TP_eq_TUG_succ` により、`T_UG` 側で層1 になっている結果がそのまま `T_P` に移る。
-/

/-- `Lemma48.lean` の上限 3 の場合と一致する（**二重に証明したことになる**）。 -/
example {p : ℕ} : TP (p + 3) 3 = TUG (p + 2) 2 + 1 := TP_eq_TUG_succ (s := 2) (by omega)

/-- **傾き 4 の領域の `T_P` の厳密値**（定理B の `T_P` 版）。 -/
theorem TP_eq_slope4 {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) (hn1 : s ≤ n) (hn2 : n ≤ theta s) :
    TP (n + 1) (s + 1) + 2 * s = 4 * n + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  show TP (p + 3) (s + 1) + 2 * s = 4 * (p + 2) + 1
  have h1 : TP (p + 3) (s + 1) = TUG (p + 2) s + 1 := TP_eq_TUG_succ hs
  have h2 := TUG_eq_slope4 hs hn1 hn2
  omega

/-- **傾き 6 の領域の `T_P` の厳密値**（定理F の `T_P` 版）。 -/
theorem TP_eq_slope6 {s n : ℕ} (hs : 2 ≤ s) (hn : 2 ≤ n) (hn1 : theta s ≤ n)
    (hn2 : n + 1 ≤ B4 s) : TP (n + 1) (s + 1) + s * (s + 3) = 6 * n + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  show TP (p + 3) (s + 1) + s * (s + 3) = 6 * (p + 2) + 1
  have h1 : TP (p + 3) (s + 1) = TUG (p + 2) s + 1 := TP_eq_TUG_succ hs
  have h2 := TUG_eq_slope6 hs hn1 hn2
  omega

/-- **`T_P` の任意の傾きの下界**（定理E の `T_P` 版）。 -/
theorem TP_ge_slope {m s n : ℕ} (hm : 1 ≤ m) (hs : 2 ≤ s) (hn : 2 ≤ n) :
    2 * m * n + 1 ≤ TP (n + 1) (s + 1) + cc m s := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  show 2 * m * (p + 2) + 1 ≤ TP (p + 3) (s + 1) + cc m s
  have h1 : TP (p + 3) (s + 1) = TUG (p + 2) s + 1 := TP_eq_TUG_succ hs
  have h2 := TUG_ge_slope m hm s (by omega) (p + 2) (by omega)
    (UGLengths_nonempty hs (by omega))
  omega

end Spooky
