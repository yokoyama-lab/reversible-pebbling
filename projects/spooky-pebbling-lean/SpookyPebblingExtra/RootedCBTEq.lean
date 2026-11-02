/-
# 完全二分木: `RootedTree.TP (cbt h) = SpookyTree.Ttree h` と，系 U2 の `1/ε ∉ ℤ` が外せないこと

`RootedWindowLowerCBT.lean` は SpookyTree の妥当な手順を `cbt h` の手順へ移す向き（`valid_cbt`）だけを持つ．
ここでは逆向き（`valid_of_cbt`：番号 `v` を `dec v` に戻す）と，`ℕ → Move` の妥当な手順からリストの `Run` を作る
`run_of_valid` を足して，

* `PLengths_cbt`: `(cbt h).PLengths cap = SpookyTree.treeLengths h cap`（`h ≥ 1`）
* `TP_cbt`: `(cbt h).TP cap = SpookyTree.Ttree h cap`
* `chs_cbt_card`: 完全二分木の子の数は 2 以下

を示す．系として，`SpookyTree/WindowSqrtNonConv.lean`（完全二分木で `p = ⌊n^{1/2}⌋` なら `T/n` は収束しない）から

* **`cor_U2_fails_half`**: 系 U2（`RootedUniversalUpper.lean` の `cor_U2_limit`）の結論の形
  「子の数 ≤ 2 のすべての根つき木で一様に `|T(t, ⌊n^{1/2}⌋)/n − L| ≤ η`（n ≥ N）」は，**どの実数 `L` でも成り立たない**．
  よって系 U2 の仮定 `1/ε ∉ ℤ` は `ε = 1/2`（`d = 2`）で外せない．
-/
import SpookyPebblingExtra.RootedWindowLowerCBT
import SpookyPebblingExtra.RootedUniversalUpper
import SpookyPebblingExtra.RootedTreeKSS
import SpookyTree.WindowSqrtNonConv

open Filter Topology

namespace Spooky
namespace RootedTree

/-! ## `ℕ → Move` の妥当な手順からリストの `Run` を作る -/

/-- 時刻 `i` から `k` 手を並べたリスト． -/
def seg (ms : ℕ → Move) (i : ℕ) : ℕ → List Move
  | 0 => []
  | k + 1 => ms i :: seg ms (i + 1) k

theorem seg_length (ms : ℕ → Move) : ∀ i k, (seg ms i k).length = k
  | _, 0 => rfl
  | i, k + 1 => by simp [seg, seg_length ms (i + 1) k]

theorem ok_seg {t : RootedTree} {s T : ℕ} {ms : ℕ → Move} (hV : t.Valid s T ms) :
    ∀ k i, i + k ≤ T →
      t.ok s (cfg ms i) (seg ms i k) = true ∧ exec (cfg ms i) (seg ms i k) = cfg ms (i + k)
  | 0, i, hik => by
      refine ⟨?_, by simp [seg, exec]⟩
      simp only [seg, RootedTree.ok, decide_eq_true_eq]
      exact hV.cap_le i (by omega)
  | k + 1, i, hik => by
      obtain ⟨h1, h2⟩ := ok_seg hV k (i + 1) (by omega)
      refine ⟨?_, ?_⟩
      · simp only [seg, RootedTree.ok, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hV.cap_le i (by omega), hV.legal i (by omega)⟩, h1⟩
      · simp only [seg, exec]
        rw [show i + (k + 1) = i + 1 + k by omega]
        exact h2

/-- **妥当な手順（`ℕ → Move`）はリストの `Run` になる．** -/
theorem run_of_valid {t : RootedTree} {s T : ℕ} {ms : ℕ → Move} (hV : t.Valid s T ms) :
    t.Run s allEmpty (seg ms 0 T) t.rootPebble := by
  obtain ⟨h1, h2⟩ := ok_seg hV T 0 (by omega)
  refine ⟨h1, ?_⟩
  intro v hv
  have h2' : exec allEmpty (seg ms 0 T) = cfg ms T := by
    have := h2
    rw [Nat.zero_add] at this
    exact this
  rw [h2']
  exact hV.final v hv

namespace CBT

/-! ## 逆向きの付け替え -/

def opInv : Spooky.Op → SpookyTree.Op
  | .pebble => .pebble
  | .unpebble => .unpebble
  | .ghost => .ghost
  | .unghost => .unghost

def moveInv (m : Spooky.Move) : SpookyTree.Move := ⟨opInv m.op, dec m.v⟩

theorem moveMap_moveInv (m : Spooky.Move) : moveMap (moveInv m) = m := by
  obtain ⟨o, v⟩ := m
  cases o <;> simp [moveMap, moveInv, opMap, opInv]

def msInv (ms : ℕ → Spooky.Move) : ℕ → SpookyTree.Move := fun j => moveInv (ms j)

theorem map_msInv (ms : ℕ → Spooky.Move) : (fun j => moveMap (msInv ms j)) = ms :=
  funext fun j => moveMap_moveInv (ms j)

theorem cfg_msInv (ms : ℕ → Spooky.Move) (i : ℕ) :
    cfg ms i = cfgMap (SpookyTree.st (msInv ms) i) := by
  have := cfg_map (msInv ms) i
  rwa [map_msInv] at this

theorem enc_ne_zero {l : List Bool} (hl : l ≠ []) : enc l ≠ 0 := by
  have hb := (enc_bounds l).1
  have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hl
  have : 2 ≤ 2 ^ l.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) hlen
  omega

/-- **妥当な手順の逆向きの移送**（`h ≥ 1`）． -/
theorem valid_of_cbt {h cap T : ℕ} (hh : 1 ≤ h) {ms : ℕ → Spooky.Move}
    (hV : (cbt h).Valid cap T ms) : SpookyTree.Valid h cap T (msInv ms) where
  legal i hi := by
    have := hV.legal i hi
    rw [cfg_msInv, ← moveMap_moveInv (ms i)] at this
    exact legal_cbt_iff.mp this
  cap_le i hi := by
    have := hV.cap_le i hi
    rw [cfg_msInv] at this
    change pcount (2 ^ h - 1) _ ≤ cap at this
    rwa [pcount_map] at this
  root := by
    have h2 : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    have hf := hV.final 0 (show 0 < 2 ^ h - 1 by omega)
    rw [cfg_msInv] at hf
    simpa [cfgMap, rootPebble, cbt] using hf
  others l hl hne := by
    have hlt : enc l < (cbt h).n := enc_lt_iff.mpr hl
    have hf := hV.final (enc l) hlt
    rw [cfg_msInv, cfgMap_enc] at hf
    have h0 := enc_ne_zero hne
    have : (cbt h).rootPebble (enc l) = Spooky.Cell.empty := by
      simp [rootPebble, cbt, h0, allEmpty]
    rw [this] at hf
    exact cellMap_eq_empty.mp hf

/-- **手数の集合は等しい**（`h ≥ 1`）． -/
theorem PLengths_cbt {h cap : ℕ} (hh : 1 ≤ h) :
    (cbt h).PLengths cap = SpookyTree.treeLengths h cap := by
  ext L
  constructor
  · rintro ⟨ms, hlen, hrun⟩
    refine ⟨msInv (toFun ms), ?_⟩
    rw [← hlen]
    exact valid_of_cbt hh (valid_of_run hrun)
  · rintro ⟨ms, hV⟩
    exact ⟨seg _ 0 L, seg_length _ 0 L, run_of_valid (valid_cbt hV)⟩

/-- **`RootedTree.TP (cbt h) = SpookyTree.Ttree h`**（`h ≥ 1`）． -/
theorem TP_cbt {h cap : ℕ} (hh : 1 ≤ h) : (cbt h).TP cap = SpookyTree.Ttree h cap := by
  unfold RootedTree.TP SpookyTree.Ttree
  rw [PLengths_cbt hh]

/-- 完全二分木の子の数は 2 以下． -/
theorem chs_cbt_card (h v : ℕ) : (UUB.chs (cbt h) v).card ≤ 2 := by
  have hsub : UUB.chs (cbt h) v ⊆ {2 * v + 1, 2 * v + 2} := by
    intro u hu
    simp only [UUB.chs, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨-, hp⟩ := hu
    rw [par_cbt] at hp
    obtain ⟨hu0, hpu⟩ := hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc (UUB.chs (cbt h) v).card ≤ ({2 * v + 1, 2 * v + 2} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ ({2 * v + 2} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

theorem lt_two_pow' : ∀ n : ℕ, n < 2 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have := lt_two_pow' n
    rw [pow_succ]
    omega

/-- **系 U2 の `1/ε ∉ ℤ` は `ε = 1/2` で外せない（子の数 ≤ 2）.**
「子の数 ≤ 2 のすべての根つき木で，`n ≥ N` なら `|T(t, ⌊n^{1/2}⌋)/n − L| ≤ η`」がすべての `η > 0` で
成り立つような実数 `L` は存在しない（完全二分木の列で `T/n` が収束しないため）． -/
theorem cor_U2_fails_half :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TP ⌊(t.n : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) / t.n - L| ≤ η := by
  rintro ⟨L, hL⟩
  apply SpookyTree.Ttree_sqrt_not_tendsto
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hL (ε / 2) (by positivity)
  refine ⟨N + 1, fun h hh => ?_⟩
  have hh1 : 1 ≤ h := by omega
  have hNn : N ≤ (cbt h).n := by
    show N ≤ 2 ^ h - 1
    have := lt_two_pow' h
    omega
  have key := hN (cbt h) (isTree_cbt hh1) (fun v _ => chs_cbt_card h v) hNn
  rw [TP_cbt hh1] at key
  have e : (cbt h).n = 2 ^ h - 1 := rfl
  rw [e] at key
  rw [Real.dist_eq]
  exact lt_of_le_of_lt key (by linarith)

/-- KSS の意味論でも同じ． -/
theorem cor_U2_fails_half_K :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TPK ⌊(t.n : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) / t.n - L| ≤ η := by
  simpa only [TPK_eq_TP] using cor_U2_fails_half

end CBT
end RootedTree
end Spooky
