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
import SpookyPebbling.Reach

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

/-- 論文の形: `T_UG(n,s)` そのものについての下界。 -/
theorem TUG_ge_decomp {n s : ℕ} (hn : 2 ≤ n) (hne : (UGLengths n s).Nonempty) :
    ∃ k, 1 ≤ k ∧ k < n ∧ 2 * k - 1 + TUP k s + TUG (n - k) (s - 1) ≤ TUG n s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  obtain ⟨k, h1, h2, h3⟩ := decomp_ug_ge hn hrun
  refine ⟨k, h1, h2, ?_⟩
  unfold TUG
  rw [← hlen]
  exact h3

end Spooky
