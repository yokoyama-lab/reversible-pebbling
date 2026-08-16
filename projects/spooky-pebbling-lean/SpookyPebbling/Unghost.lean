/-
# KSS Cor 4.12 — unghosting の分解

$$T_{UG}(n,s)\ =\ \min_{k}\ \bigl[\,2k-1 + T_{UP}(k,s) + T_{UG}(n-k,s-1)\,\bigr]$$

`Decomp.lean` の `decomp_ge_pieces` は始状態について一般化してあるので、
$\ge$ 方向は **`c₀ = sinkGhost n` を入れるだけ**で出る。KSS が Lemma 4.1 の
$P^\bot$ 交換論法で作る性質は、ここでも `k` の取り方（満室時刻の最下位ペブルの最大）
から定義的に出ている。

始状態がゴーストなので、$T_{UP}$ 版より条件が緩い:

- 頭には初期ペブルが**一つも無い**（`sinkGhost` はどこもペブルでない）
- 尻尾側の初期ペブル数が `1` でなく **`0`** なので、掃きの段で要るペブルは
  `2 + 0 = 2`。すなわち $\le$ 方向は **$s\ge2$** で回る（$T_{UP}$ 版は $s\ge3$）

`s† ≥ 2` は「終端のゴーストは unghost されねばならず、それには直前の頂点のペブルが要る」
から出る（`ghost_becomes_pebble` → `two_pebbles_of_clear`）。
-/
import SpookyPebbling.Upper

namespace Spooky

/-! ## `sinkGhost` の成分 -/

theorem sinkGhost_apply (n j : ℕ) :
    sinkGhost n j = if j = n - 1 then Cell.ghost else Cell.empty := by
  unfold sinkGhost sink allEmpty
  rw [Function.update_apply]

theorem sinkGhost_ne_pebble (n j : ℕ) : sinkGhost n j ≠ Cell.pebble := by
  rw [sinkGhost_apply]
  by_cases h : j = n - 1 <;> simp [h]

/-- 尻尾から見た始状態は、長さ `n-k` の鎖の unghosting の始状態と一致する。 -/
theorem shiftC_sinkGhost {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    AgreeOn (n - k) (shiftC k (sinkGhost n)) (sinkGhost (n - k)) := by
  intro t ht
  rw [shiftC_apply, sinkGhost_apply, sinkGhost_apply]
  by_cases h : t = n - k - 1
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-! ## $\ge$ 方向 -/

/-- 終端のゴーストを消すには、途中でペブルを 2 個同時に持つ時刻が要る。 -/
theorem two_pebbles_of_sinkGhost {n s : ℕ} (hn : 2 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∃ d ∈ traj (sinkGhost n) ms, 2 ≤ pcount n d := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hv, _⟩ := (ok_iff ms (sinkGhost n)).mp hok
  have hstart : sinkGhost n (n - 1) = Cell.ghost := by rw [sinkGhost_apply]; simp
  have hend : exec (sinkGhost n) ms (n - 1) = Cell.empty := by
    rw [hagree (n - 1) (by omega)]; rfl
  obtain ⟨l₁, l₂, heq, _, hpp⟩ := ghost_becomes_pebble ms (sinkGhost n) hv hstart hend
  have hv₂ : valid n (exec (sinkGhost n) l₁) l₂ = true :=
    valid_append_right l₁ l₂ (sinkGhost n) (heq ▸ hv)
  have he₂ : exec (exec (sinkGhost n) l₁) l₂ (n - 1) = Cell.empty := by
    rw [← exec_append l₁ l₂ (sinkGhost n), ← heq]; exact hend
  obtain ⟨d, hd, hd2⟩ :=
    two_pebbles_of_clear l₂.length l₂ le_rfl (exec (sinkGhost n) l₁) hv₂
      (by omega) (by omega) hpp he₂
  exact ⟨d, heq ▸ traj_append_subset l₁ (sinkGhost n) l₂ d hd, hd2⟩

/-- **KSS Cor 4.12 の $\ge$ 方向**。交換論法は使わない。 -/
theorem decomp_ug_ge {n s : ℕ} (hn : 2 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) ≤ ms.length := by
  obtain ⟨u, hun1, hlen, hrunT⟩ :=
    decomp_ge_pieces hn (fun j _ => sinkGhost_ne_pebble n j)
      (two_pebbles_of_sinkGhost hn h) h
  have hshift : AgreeOn (n - (u + 1)) (shiftC (u + 1) (sinkGhost n)) (sinkGhost (n - (u + 1))) :=
    shiftC_sinkGhost (by omega) hun1
  obtain ⟨hokT, hagreeT⟩ := hrunT
  have htail : TUG (n - (u + 1)) (s - 1) ≤ (tailMoves u ms).length := by
    refine TUG_le ⟨tailMoves u ms, rfl, ok_congr hshift hokT, ?_⟩
    intro v hv1
    rw [← exec_congr (tailMoves u ms) hshift v hv1]
    exact hagreeT v hv1
  refine ⟨u + 1, by omega, by omega, ?_⟩
  have hk : 2 * (u + 1) - 1 = 2 * u + 1 := by omega
  rw [hk]
  omega

/-- 尻尾の手順そのものも返す版（縮退 `T_UG(m,1)=∞` を使うときに要る）。 -/
theorem decomp_ug_ge' {n s : ℕ} (hn : 2 ≤ n) {ms : List Move}
    (h : Run n s (sinkGhost n) ms allEmpty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) ≤ ms.length ∧
      ∃ msT, Run (n - k) (s - 1) (sinkGhost (n - k)) msT allEmpty := by
  obtain ⟨u, hun1, hlen, hrunT⟩ :=
    decomp_ge_pieces hn (fun j _ => sinkGhost_ne_pebble n j)
      (two_pebbles_of_sinkGhost hn h) h
  have hshift : AgreeOn (n - (u + 1)) (shiftC (u + 1) (sinkGhost n)) (sinkGhost (n - (u + 1))) :=
    shiftC_sinkGhost (by omega) hun1
  obtain ⟨hokT, hagreeT⟩ := hrunT
  have hrunT' : Run (n - (u + 1)) (s - 1) (sinkGhost (n - (u + 1))) (tailMoves u ms) allEmpty := by
    refine ⟨ok_congr hshift hokT, ?_⟩
    intro v hv1
    rw [← exec_congr (tailMoves u ms) hshift v hv1]
    exact hagreeT v hv1
  have htail : TUG (n - (u + 1)) (s - 1) ≤ (tailMoves u ms).length :=
    TUG_le ⟨tailMoves u ms, rfl, hrunT'⟩
  refine ⟨u + 1, by omega, by omega, ?_, tailMoves u ms, hrunT'⟩
  have hk : 2 * (u + 1) - 1 = 2 * u + 1 := by omega
  rw [hk]
  omega

/-- 上限 1 では長さ 2 以上の鎖の unghosting はできない（KSS の `s<2 ∧ s<n → ∞`）。 -/
theorem not_run_ug_cap_one {m : ℕ} (hm : 2 ≤ m) {ms : List Move} :
    ¬ Run m 1 (sinkGhost m) ms allEmpty := by
  intro h
  obtain ⟨d, hd, hd2⟩ := two_pebbles_of_sinkGhost hm h
  obtain ⟨_, hcap⟩ := (ok_iff ms (sinkGhost m)).mp h.1
  have := hcap d hd
  omega

/-- 論文の形: `T_UG(n,s)` そのものについての下界。 -/
theorem TUG_ge_decomp {n s : ℕ} (hn : 2 ≤ n) (hne : (UGLengths n s).Nonempty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) ≤ TUG n s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨k, h1, h2, h3⟩ := decomp_ug_ge hn hrun
  refine ⟨k, h1, h2, ?_⟩
  unfold TUG
  rw [← hlen]
  exact h3

/-! ## $\le$ 方向

`Upper.lean` の `decomp_le_run_gen` に `c₀ = sinkGhost n` を入れる。
尻尾側の初期ペブルが 0 個なので掃きに要るのは 2 個、すなわち **$s\ge2$** で回る。
-/

theorem sinkGhost_above {n v : ℕ} (hn : 0 < n) (h : n ≤ v) : sinkGhost n v = Cell.empty := by
  rw [sinkGhost_apply, if_neg (by omega)]

theorem pcount_shiftC_sinkGhost (n k m : ℕ) : pcount m (shiftC k (sinkGhost n)) = 0 :=
  pcount_eq_zero_iff.mpr fun v _ => by rw [shiftC_apply]; exact sinkGhost_ne_pebble n _

/-- 長さ 1 の鎖の unghosting は 2 手（`unghost` してから `unpebble`）。 -/
theorem run_ug_one {s : ℕ} (hs : 1 ≤ s) :
    Run 1 s (sinkGhost 1) [⟨Op.unghost, 0⟩, ⟨Op.unpebble, 0⟩] allEmpty := by
  have hg : sinkGhost 1 0 = Cell.ghost := by rw [sinkGhost_apply]; simp
  have h1 : step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move) 0 = Cell.pebble :=
    Function.update_self _ _ _
  have h2 : step (step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)) (⟨Op.unpebble, 0⟩ : Move) 0
      = Cell.empty := Function.update_self _ _ _
  refine ⟨(ok_iff _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [valid_cons, valid_nil, Bool.and_true, Bool.and_eq_true]
    constructor
    · unfold legal ready; simp [hg]
    · unfold legal ready; simp [h1]
  · intro d hd
    have hd' : d = sinkGhost 1 ∨ d = step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)
        ∨ d = step (step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)) (⟨Op.unpebble, 0⟩ : Move) := by
      simpa [traj] using hd
    rcases hd' with rfl | rfl | rfl
    · rw [pcount_sinkGhost]; omega
    · have he : pcount 1 (step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)) = 1 := by
        rw [pcount_succ, pcount]; simp [h1]
      omega
    · have he : pcount 1
          (step (step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)) (⟨Op.unpebble, 0⟩ : Move)) = 0 := by
        rw [pcount_succ, pcount]; simp [h2]
      omega
  · intro v hv
    rw [show v = 0 by omega]
    show step (step (sinkGhost 1) (⟨Op.unghost, 0⟩ : Move)) (⟨Op.unpebble, 0⟩ : Move) 0
        = allEmpty 0
    rw [h2]; rfl

/-- **Cor 4.12 の $\le$ 方向の構成**。 -/
theorem decomp_ug_le_run {n s j : ℕ} (hs : 2 ≤ s) (hjn : j + 1 < n)
    {msH msT : List Move}
    (hH : Run (j + 1) s (sinkPebble (j + 1)) msH allEmpty)
    (hT : Run (n - (j + 1)) (s - 1) (sinkGhost (n - (j + 1))) msT allEmpty) :
    ∃ ms : List Move, ms.length = 2 * j + 1 + msT.length + msH.length ∧
      Run n s (sinkGhost n) ms allEmpty := by
  refine decomp_le_run_gen (by omega) hjn ?_ (fun v hv => sinkGhost_above (by omega) hv)
    (shiftC_sinkGhost (by omega) hjn) ?_ hH hT
  · intro i hi; rw [sinkGhost_apply, if_neg (by omega)]
  · rw [pcount_shiftC_sinkGhost]; omega

/-- **到達可能性（unghosting）**: `s ≥ 2` ならどんな長さの鎖もゴーストから片付く。 -/
theorem UGLengths_nonempty {n s : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n) : (UGLengths n s).Nonempty := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨2, _, rfl, run_ug_one (by omega)⟩
  · obtain ⟨j, hj⟩ : ∃ j, n - 1 = j + 1 := ⟨n - 2, by omega⟩
    obtain ⟨_, msH, _, hrunH⟩ :=
      UPLengths_nonempty (n := j + 1) (s := s) (by omega) (by omega)
    have hn1 : n - (j + 1) = 1 := by omega
    have hrunT : Run (n - (j + 1)) (s - 1) (sinkGhost (n - (j + 1)))
        [⟨Op.unghost, 0⟩, ⟨Op.unpebble, 0⟩] allEmpty := by
      rw [hn1]; exact run_ug_one (by omega)
    obtain ⟨ms, _, hrun⟩ := decomp_ug_le_run hs (by omega) hrunH hrunT
    exact ⟨ms.length, ms, rfl, hrun⟩

/-- **Cor 4.12 の $\le$ 方向**（尻尾の到達可能性を仮定に置いた一般形）。 -/
theorem decomp_ug_le {n s k : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k) (hkn : k < n)
    (hTne : (UGLengths (n - k) (s - 1)).Nonempty) :
    TUG n s ≤ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨msH, hlenH, hrunH⟩ :=
    Nat.sInf_mem (UPLengths_nonempty (n := j + 1) (s := s) hs (by omega))
  obtain ⟨msT, hlenT, hrunT⟩ := Nat.sInf_mem hTne
  obtain ⟨ms, hlen, hrun⟩ := decomp_ug_le_run hs hkn hrunH hrunT
  have hb := TUG_le (n := n) (s := s) ⟨ms, rfl, hrun⟩
  rw [hlen] at hb
  unfold TUG at hb
  unfold TUP TUG
  omega

/-- `s ≥ 3` なら尻尾も必ず到達可能なので、仮定は要らない。 -/
theorem decomp_ug_le' {n s k : ℕ} (hs : 3 ≤ s) (hk : 1 ≤ k) (hkn : k < n) :
    TUG n s ≤ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) :=
  decomp_ug_le (by omega) hk hkn (UGLengths_nonempty (by omega) (by omega))

/-- **KSS Cor 4.12（`s ≥ 3`）**: ある `k` で等号が成り立ち、どの `k` も上界を与える。 -/
theorem decomp_ug_exact {n s : ℕ} (hs : 3 ≤ s) (hn : 2 ≤ n) :
    (∃ k, 1 ≤ k ∧ k < n ∧ TUG n s = 2 * k - 1 + TUP k s + TUG (n - k) (s - 1)) ∧
    (∀ k, 1 ≤ k → k < n → TUG n s ≤ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1)) := by
  refine ⟨?_, fun k hk hkn => decomp_ug_le' hs hk hkn⟩
  obtain ⟨k, hk, hkn, hge⟩ :=
    TUG_ge_decomp hn (UGLengths_nonempty (n := n) (s := s) (by omega) (by omega))
  exact ⟨k, hk, hkn, le_antisymm (decomp_ug_le' hs hk hkn) hge⟩

end Spooky
