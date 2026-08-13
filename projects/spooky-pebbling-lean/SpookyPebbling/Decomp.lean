/-
# 分解の $\ge$ 方向（本丸）

$$T_{UP}(n,s)\ \ge\ \min_{k\in[1,n)}\ \bigl[\,2k-1 + T_{UP}(k,s) + T_{UP}(n-k,s-1)\,\bigr]$$

KSS Lemma 4.1 の $P^\bot$ 交換論法（「すべての最適算法のうち $k$ を最大にするものを取る」）
は**要らない**。$k$ を*与えられた手順の内側*で

$$s^\dagger := \max_t |P_t|,\qquad F := \{t : |P_t| = s^\dagger\},\qquad
  u := \max_{t\in F}\ \min\{i : v_i\in P_t\},\qquad k := u+1$$

と取れば、必要な「尻尾のペブルは常に $\le s^\dagger-1$」が**定義から**出る。
（`Count.lean` の段(i)、`Project.lean` の射影、`Ghost.lean` の補題G と合流する。）
-/
import SpookyPebbling.Split
import SpookyPebbling.Ghost

namespace Spooky

/-! ## 手順の分割と軌跡 -/

theorem valid_append_right {n : ℕ} : ∀ (l₁ l₂ : List Move) (c : Config),
    valid n c (l₁ ++ l₂) = true → valid n (exec c l₁) l₂ = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ c h; exact h
  | cons a as ih =>
      intro l₂ c h
      simp only [List.cons_append, valid_cons, Bool.and_eq_true] at h
      exact ih l₂ (step c a) h.2

theorem ok_append_right {n s : ℕ} : ∀ (l₁ l₂ : List Move) (c : Config),
    ok n s c (l₁ ++ l₂) = true → ok n s (exec c l₁) l₂ = true := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ c h; exact h
  | cons a as ih =>
      intro l₂ c h
      rw [List.cons_append] at h
      unfold ok at h
      simp only [Bool.and_eq_true] at h
      exact ih l₂ (step c a) h.2

theorem traj_append_subset : ∀ (l₁ : List Move) (c : Config) (l₂ : List Move),
    ∀ d ∈ traj (exec c l₁) l₂, d ∈ traj c (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro c l₂ d h; exact h
  | cons a as ih =>
      intro c l₂ d h
      simp only [List.cons_append, traj_cons, List.mem_cons]
      exact Or.inr (ih (step c a) l₂ d h)

theorem mem_traj_split : ∀ (ms : List Move) (c d : Config), d ∈ traj c ms →
    ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ exec c l₁ = d := by
  intro ms
  induction ms with
  | nil => intro c d h; simp only [traj_nil, List.mem_singleton] at h; exact ⟨[], [], rfl, h.symm⟩
  | cons m ms ih =>
      intro c d h
      simp only [traj_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨[], m :: ms, rfl, rfl⟩
      · obtain ⟨l₁, l₂, heq, hx⟩ := ih (step c m) d h
        exact ⟨m :: l₁, l₂, by rw [List.cons_append, ← heq], hx⟩

/-! ## `s† ≥ 2`（ゴーストの巡回を経ても、いつか 2 個同時に持つ） -/

/-- 妥当な手順では、ゴーストは（終状態が空なら）必ずいつかペブルに戻る。 -/
theorem ghost_becomes_pebble {n : ℕ} : ∀ (ms : List Move) (c : Config), valid n c ms = true →
    ∀ {i : ℕ}, c i = Cell.ghost → exec c ms i = Cell.empty →
    ∃ l₁ l₂, ms = l₁ ++ l₂ ∧ l₁ ≠ [] ∧ exec c l₁ i = Cell.pebble := by
  intro ms
  induction ms with
  | nil =>
      intro c _ i hg he
      rw [show exec c [] i = c i from rfl, hg] at he
      exact absurd he (by simp)
  | cons m ms ih =>
      intro c hv i hg he
      simp only [valid_cons, Bool.and_eq_true] at hv
      by_cases hmv : m.v = i
      · subst hmv
        have hleg := hv.1
        unfold legal at hleg
        simp only [Bool.and_eq_true] at hleg
        have h2 := hleg.2
        have hop : m.op = Op.unghost := by
          cases hcase : m.op <;> rw [hcase] at h2 <;>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 <;> simp_all
        refine ⟨[m], ms, rfl, by simp, ?_⟩
        show step c m m.v = Cell.pebble
        rw [step_self, hop]
        rfl
      · have hg' : step c m i = Cell.ghost := by rw [step_ne_of_ne hmv]; exact hg
        obtain ⟨l₁, l₂, heq, hne, hp⟩ := ih (step c m) hv.2 hg' he
        refine ⟨m :: l₁, l₂, by rw [List.cons_append, ← heq], by simp, hp⟩

/-- ペブルの在る頂点 `i (0 < i < n)` が最後に空になるなら、途中で `pcount ≥ 2` の時刻が在る。 -/
theorem two_pebbles_of_clear {n : ℕ} : ∀ (N : ℕ) (ms : List Move), ms.length ≤ N →
    ∀ (c : Config), valid n c ms = true →
    ∀ {i : ℕ}, 0 < i → i < n → c i = Cell.pebble → exec c ms i = Cell.empty →
    ∃ d ∈ traj c ms, 2 ≤ pcount n d := by
  intro N
  induction N with
  | zero =>
      intro ms hlen c _ i _ _ hp he
      have : ms = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [show exec c [] i = c i from rfl, hp] at he
      exact absurd he (by simp)
  | succ N ih =>
      intro ms hlen c hv i hi hin hp he
      match ms with
      | [] =>
          rw [show exec c [] i = c i from rfl, hp] at he
          exact absurd he (by simp)
      | m :: ms' =>
          simp only [valid_cons, Bool.and_eq_true] at hv
          simp only [List.length_cons] at hlen
          by_cases hmv : m.v = i
          · subst hmv
            have hleg := hv.1
            unfold legal at hleg
            simp only [Bool.and_eq_true] at hleg
            have h2 := hleg.2
            -- `c m.v = pebble` なので打てるのは unpebble か ghost
            have hop : m.op = Op.unpebble ∨ m.op = Op.ghost := by
              cases hcase : m.op <;> rw [hcase] at h2 <;>
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 <;> simp_all
            rcases hop with hop | hop
            · -- unpebble: 直前の頂点もペブル → その時刻で 2 個
              refine ⟨c, mem_traj_self c (m :: ms'), ?_⟩
              have hr : ready c m.v = true := by
                rw [hop] at h2; exact Bool.and_elim_right h2
              unfold ready at hr
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
              rcases hr with hr | hr
              · omega
              · exact two_le_pcount (by omega) hin (by omega) hp hr
            · -- ghost: いつか unghost に戻るので、そこから再帰
              have hgh : step c m m.v = Cell.ghost := by rw [step_self, hop]; rfl
              have he' : exec (step c m) ms' m.v = Cell.empty := he
              obtain ⟨l₁, l₂, heq, hne, hpp⟩ :=
                ghost_becomes_pebble ms' (step c m) hv.2 hgh he'
              have hl₁ : 0 < l₁.length := List.length_pos_of_ne_nil hne
              have hlen₂ : l₂.length ≤ N := by
                have : l₁.length + l₂.length = ms'.length := by rw [heq]; simp
                omega
              have hv₂ : valid n (exec (step c m) l₁) l₂ = true :=
                valid_append_right l₁ l₂ (step c m) (heq ▸ hv.2)
              have he₂ : exec (exec (step c m) l₁) l₂ m.v = Cell.empty := by
                rw [← exec_append l₁ l₂ (step c m), ← heq]; exact he'
              obtain ⟨d, hd, hdc⟩ :=
                ih l₂ hlen₂ (exec (step c m) l₁) hv₂ hi hin hpp he₂
              refine ⟨d, ?_, hdc⟩
              simp only [traj_cons, List.mem_cons]
              exact Or.inr (heq ▸ traj_append_subset l₁ (step c m) l₂ d hd)
          · -- i に触らない手: そのまま先へ
            have hp' : step c m i = Cell.pebble := by rw [step_ne_of_ne hmv]; exact hp
            obtain ⟨d, hd, hdc⟩ := ih ms' (by omega) (step c m) hv.2 hi hin hp' he
            exact ⟨d, by simp only [traj_cons, List.mem_cons]; exact Or.inr hd, hdc⟩

/-! ## 射影の `ok` と `exec` -/

theorem ok_headMoves {n s u : ℕ} (hu : u + 1 ≤ n) : ∀ (ms : List Move) (c : Config),
    ok n s c ms = true → ok (u + 1) s c (headMoves u ms) = true := by
  intro ms
  induction ms with
  | nil =>
      intro c h
      rw [headMoves_nil]
      unfold ok at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact le_trans (pcount_mono hu c) h
  | cons m ms ih =>
      intro c h
      unfold ok at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hcap, hleg⟩, htail⟩ := h
      by_cases hm : m.v ≤ u
      · rw [headMoves_cons_head ms hm]
        unfold ok
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨le_trans (pcount_mono hu c) hcap, legal_head hleg hm⟩, ih (step c m) htail⟩
      · simp only [Nat.not_le] at hm
        rw [headMoves_cons_tail ms hm]
        exact ok_congr (fun v hv => (agree_step_tail hm v hv).symm) (ih (step c m) htail)

theorem exec_headMoves {u : ℕ} : ∀ (ms : List Move) (c : Config),
    AgreeOn (u + 1) (exec c ms) (exec c (headMoves u ms)) := by
  intro ms
  induction ms with
  | nil => intro c; exact fun v _ => rfl
  | cons m ms ih =>
      intro c
      by_cases hm : m.v ≤ u
      · rw [headMoves_cons_head ms hm]
        exact ih (step c m)
      · simp only [Nat.not_le] at hm
        rw [headMoves_cons_tail ms hm]
        intro v hv
        rw [show exec c (m :: ms) = exec (step c m) ms from rfl]
        exact (ih (step c m) v hv).trans
          (exec_congr (headMoves u ms)
            (fun w hw => (agree_step_tail hm w hw).symm) v hv)

theorem exec_tailMoves {u : ℕ} : ∀ (ms : List Move) (c : Config),
    shiftC (u + 1) (exec c ms) = exec (shiftC (u + 1) c) (tailMoves u ms) := by
  intro ms
  induction ms with
  | nil => intro c; rfl
  | cons m ms ih =>
      intro c
      by_cases hm : u < m.v
      · rw [tailMoves_cons_tail ms hm]
        show shiftC (u + 1) (exec (step c m) ms) = exec (step (shiftC (u + 1) c) _) _
        rw [← shiftC_step_tail hm]
        exact ih (step c m)
      · simp only [Nat.not_lt] at hm
        rw [tailMoves_cons_head ms hm]
        show shiftC (u + 1) (exec (step c m) ms) = _
        rw [ih (step c m), shiftC_step_head hm]

theorem ok_tailMoves {n s' u : ℕ} : ∀ (ms : List Move) (c : Config), valid n c ms = true →
    (∀ d ∈ traj c ms, pcount (n - (u + 1)) (shiftC (u + 1) d) ≤ s') →
    ok (n - (u + 1)) s' (shiftC (u + 1) c) (tailMoves u ms) = true := by
  intro ms
  induction ms with
  | nil =>
      intro c _ hcap
      unfold ok
      exact decide_eq_true (hcap c (by simp))
  | cons m ms ih =>
      intro c hv hcap
      simp only [valid_cons, Bool.and_eq_true] at hv
      have hrest : ∀ d ∈ traj (step c m) ms, pcount (n - (u + 1)) (shiftC (u + 1) d) ≤ s' :=
        fun d hd => hcap d (by simp only [traj_cons, List.mem_cons]; exact Or.inr hd)
      by_cases hm : u < m.v
      · rw [tailMoves_cons_tail ms hm]
        unfold ok
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨hcap c (by simp), legal_tail hv.1 hm⟩, ?_⟩
        rw [← shiftC_step_tail hm]
        exact ih (step c m) hv.2 hrest
      · simp only [Nat.not_lt] at hm
        rw [tailMoves_cons_head ms hm, ← shiftC_step_head (c := c) hm]
        exact ih (step c m) hv.2 hrest

/-! ## 長さの分解 -/

theorem headMoves_tailMoves_length (u : ℕ) : ∀ (ms : List Move),
    (headMoves u ms).length + (tailMoves u ms).length = ms.length := by
  intro ms
  induction ms with
  | nil => simp
  | cons m ms ih =>
      by_cases hm : m.v ≤ u
      · rw [headMoves_cons_head ms hm, tailMoves_cons_head ms hm]
        simp only [List.length_cons]
        omega
      · simp only [Nat.not_le] at hm
        rw [headMoves_cons_tail ms hm, tailMoves_cons_tail ms hm]
        simp only [List.length_cons]
        omega

theorem headMoves_append (u : ℕ) (l₁ l₂ : List Move) :
    headMoves u (l₁ ++ l₂) = headMoves u l₁ ++ headMoves u l₂ := by
  unfold headMoves; rw [List.filter_append]

/-! ## 始状態の成分 -/

theorem sinkPebble_apply (n j : ℕ) :
    sinkPebble n j = if j = n - 1 then Cell.pebble else Cell.empty := by
  unfold sinkPebble sink allEmpty
  rw [Function.update_apply]

/-! ## 主定理 -/

/-- **$T_{UP}$ 分解の $\ge$ 方向**。KSS の $P^\bot$ 交換論法は使わない。 -/
theorem decomp_ge {n s : ℕ} (hn : 2 ≤ n) {ms : List Move}
    (h : Run n s (sinkPebble n) ms allEmpty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUP (n - k) (s - 1) ≤ ms.length := by
  classical
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, hcapall⟩ := (ok_iff ms (sinkPebble n)).mp hok
  -- s† = 軌跡上のペブル数の最大
  obtain ⟨dmax, hdmax, hmax⟩ :=
    exists_max_on (pcount n) (traj (sinkPebble n) ms) (traj_ne_nil _ _)
  have hsd_le_s : pcount n dmax ≤ s := hcapall dmax hdmax
  -- s† ≥ 2: v_{n-1} のペブルは（ゴーストを経ても）いつか 2 個同時に持たないと消せない
  have h2 : 2 ≤ pcount n dmax := by
    obtain ⟨d, hd, hd2⟩ :=
      two_pebbles_of_clear ms.length ms le_rfl (sinkPebble n) hv (i := n - 1)
        (by omega) (by omega) (by rw [sinkPebble_apply]; simp)
        (by rw [hagree (n - 1) (by omega)]; rfl)
    exact le_trans hd2 (hmax d hd)
  -- 満室の時刻のうち、最下位ペブルが最大のものを取る
  set F := (traj (sinkPebble n) ms).filter (fun d => decide (pcount n d = pcount n dmax)) with hF
  have hFne : F ≠ [] := by
    intro hnil
    have hm : dmax ∈ F := by simp [hF, List.mem_filter, hdmax]
    rw [hnil] at hm; simp at hm
  obtain ⟨d₁, hd₁F, humax⟩ := exists_max_on (minPeb n) F hFne
  have hd₁ : d₁ ∈ traj (sinkPebble n) ms ∧ pcount n d₁ = pcount n dmax := by
    simpa [hF, List.mem_filter] using hd₁F
  set u := minPeb n d₁ with hu
  obtain ⟨hun, hupeb, hulow⟩ := minPeb_spec (n := n) (c := d₁) (by omega)
  -- 頭 `0..u` のペブルはちょうど 1 個
  have hhead1 : pcount (u + 1) d₁ = 1 := by
    unfold pcount
    have hset : (Finset.range (u + 1)).filter (fun v => d₁ v = Cell.pebble) = {u} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hv1, hp⟩
        by_contra hne
        exact hulow v (by omega) hp
      · rintro rfl
        exact ⟨by omega, hupeb⟩
    rw [hset]; simp
  -- したがって u+1 < n（`k < n` になる）
  have hun1 : u + 1 < n := by
    rcases Nat.lt_or_ge (u + 1) n with hlt | hge
    · exact hlt
    · exfalso
      have : u + 1 = n := by omega
      rw [this] at hhead1
      omega
  -- 尻尾のペブルは常に s†-1 以下（k の取り方から定義的に出る）
  have htailcap : ∀ d ∈ traj (sinkPebble n) ms,
      pcount (n - (u + 1)) (shiftC (u + 1) d) ≤ pcount n dmax - 1 := by
    intro d hd
    by_contra hcon
    simp only [Nat.not_le] at hcon
    have hsplit := pcount_split n u (by omega) d
    have hle : pcount n d ≤ pcount n dmax := hmax d hd
    have hhead0 : pcount (u + 1) d = 0 := by omega
    have hdsd : pcount n d = pcount n dmax := by omega
    have hdF : d ∈ F := by simp [hF, List.mem_filter, hd, hdsd]
    have hmin_le : minPeb n d ≤ u := humax d hdF
    obtain ⟨_, hpebd, _⟩ := minPeb_spec (n := n) (c := d) (by omega)
    exact (pcount_eq_zero_iff.mp hhead0) (minPeb n d) (by omega) hpebd
  -- 手順を d₁ の時刻で切る
  obtain ⟨ms₁, ms₂, hmseq, hexec₁⟩ := mem_traj_split ms (sinkPebble n) d₁ hd₁.1
  have hv₁ : valid n (sinkPebble n) ms₁ = true := valid_append_left ms₁ ms₂ _ (hmseq ▸ hv)
  have hc₀ : ∀ j, j ≤ u → sinkPebble n j ≠ Cell.pebble := by
    intro j hj
    rw [sinkPebble_apply, if_neg (by omega)]
    simp
  -- 段(i): 前半の頭の手は 2u+1 手以上
  have hbefore : 2 * u + 1 ≤ (headMoves u ms₁).length := by
    refine length_ge_two_mul_add_one (n := u + 1) (headMoves u ms₁) (sinkPebble n)
      (valid_headMoves ms₁ _ hv₁) hc₀ ?_ ?_
    · rw [← exec_headMoves ms₁ _ u (by omega), hexec₁]; exact hupeb
    · intro j hj
      rw [← exec_headMoves ms₁ _ j (by omega), hexec₁]
      exact hulow j hj
  -- 段(iii): 後半の頭の手は TUP (u+1) s 以上（補題G を使う）
  have hafter : TUP (u + 1) s ≤ (headMoves u ms₂).length := by
    refine TUP_le_of_ghosts (a := d₁) ?_ ⟨?_, ?_⟩
    · intro v hv1
      rw [sinkPebble_apply]
      unfold stripGhosts
      by_cases hvu : v = u
      · subst hvu; rw [hupeb]; simp
      · have : d₁ v ≠ Cell.pebble := hulow v (by omega)
        cases hcell : d₁ v <;> simp [hcell, hvu, (by omega : ¬ (v = u + 1 - 1))] <;> simp_all
    · exact ok_headMoves (by omega) ms₂ d₁
        (hexec₁ ▸ ok_append_right ms₁ ms₂ (sinkPebble n) (hmseq ▸ hok))
    · intro v hv1
      rw [← exec_headMoves ms₂ d₁ v hv1, ← hexec₁, ← exec_append ms₁ ms₂ (sinkPebble n), ← hmseq]
      exact hagree v (by omega)
  -- 段(ii): 尻尾の手は TUP (n-(u+1)) (s-1) 以上
  have hshift : AgreeOn (n - (u + 1)) (shiftC (u + 1) (sinkPebble n)) (sinkPebble (n - (u + 1))) := by
    intro v hv1
    rw [shiftC_apply, sinkPebble_apply, sinkPebble_apply]
    by_cases hvv : v = n - (u + 1) - 1
    · rw [if_pos hvv, if_pos (by omega)]
    · rw [if_neg hvv, if_neg (by omega)]
  have htail : TUP (n - (u + 1)) (s - 1) ≤ (tailMoves u ms).length := by
    refine TUP_le ⟨tailMoves u ms, rfl, ?_, ?_⟩
    · refine ok_congr hshift (ok_tailMoves ms (sinkPebble n) hv ?_)
      intro d hd
      exact le_trans (htailcap d hd) (by omega)
    · intro v hv1
      rw [← exec_congr (tailMoves u ms) hshift v hv1, ← exec_tailMoves ms (sinkPebble n),
        shiftC_apply]
      exact hagree (v + (u + 1)) (by omega)
  -- 合流
  refine ⟨u + 1, by omega, by omega, ?_⟩
  have hlen : (headMoves u ms₁).length + (headMoves u ms₂).length + (tailMoves u ms).length
      = ms.length := by
    have hht := headMoves_tailMoves_length u ms
    have hsplit : (headMoves u ms).length
        = (headMoves u ms₁).length + (headMoves u ms₂).length := by
      rw [hmseq, headMoves_append, List.length_append]
    omega
  have hk : 2 * (u + 1) - 1 = 2 * u + 1 := by omega
  rw [hk]
  omega

/-- 論文の形: `T_UP(n,s)` そのものについての下界。 -/
theorem TUP_ge_decomp {n s : ℕ} (hn : 2 ≤ n) (hne : (UPLengths n s).Nonempty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUP (n - k) (s - 1) ≤ TUP n s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨k, h1, h2, h3⟩ := decomp_ge hn hrun
  refine ⟨k, h1, h2, ?_⟩
  unfold TUP
  rw [← hlen]
  exact h3

end Spooky
