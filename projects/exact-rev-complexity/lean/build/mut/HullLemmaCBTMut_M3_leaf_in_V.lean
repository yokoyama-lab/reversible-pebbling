/-
  **殻補題の完全二分木への具体化**（第16夜 周2/3・2026-08-23）。

  仕様は `autoresearch/proposals/hulllemma_cbt_instantiation.md`（第16夜 周1/3 が起草）。

  `HullLemma.lean` が証明したのは**一般補題**:

      card_le_of_reach : 4 * V.card ≤ M + 2 * min p V.card + 1

  で、「$T_h$ がこれを $N = 2^h - 1$ で満たすので $M \ge 4(2^h-1) - 2p - 1$」の一段は
  **紙のままだった**（`binary` / `cbt` / `63` / `235` はあちらに 1 回も出てこない）。
  この 235 は banlist の 2 項目（「$K\le234$ で刻むな」「$K\ge224$ まで登るな」）の
  根拠なので、ここを埋めて**端から端まで機械証明**にする。

  ## 頂点番号（プロンプトの契約・heap 番号）

  根 = `1`、`v` の子 = `2v, 2v+1`、ペブル対象の内部頂点 = `1 .. 2^h - 1`、
  free の葉 = `2^h .. 2^(h+1) - 1`。

  ## ⚠ `hmv` を仮定として残していること（弱くなったのではない）

  `Sched` が `mv` に課すのは `notFree`（`mv t ∉ F`）だけなので、
  **木の外の番号**（例えば `12345`）は `∉ cbtFree h` かつ `cbtPred h 12345 = ∅` で
  `legal` が空虚に成り立ち、形式上は toggle できてしまう。$M$ が増える方向なので
  下界としては害が無いが、`card_le_of_reach` はそれを知らないので `hmv` を渡せない。
  → **`hmv`（手はすべて `cbtV h` の中）は具体化定理の仮定として明示する。**
  これは「$T_h$ のスケジュール」の定義そのもの（`revpebble.py` も `range(n)` の頂点
  しか動かさない）で、**紙で暗黙だった前提が明示された**という意味の収穫である。

  ## 校正（型検査では捕まらない取り違えを潰す）

  `cbt_h3_bound` が `M ≥ 17` を出す。これは**全数 BFS の真値 M*(T_3) = 17 と一致**する
  （`data/exp01_findings.md`）。heap 番号を取り違えた `cbtPred` でも型は合うので、
  **この数値校正だけが「本当に完全二分木か」の機械的な担保**である。
-/
import HullLemma

set_option autoImplicit false

namespace HullLemmaCBTMut

open Finset HullLemma

/-! ## 1. 完全二分木 `T_h` の符号化 -/

/-- `v` の先行点（子）。内部頂点 `1 ≤ v < 2^h` のときだけ `{2v, 2v+1}`。 -/
def cbtPred (h v : ℕ) : Finset ℕ :=
  if 1 ≤ v ∧ v < 2 ^ h then {2 * v, 2 * v + 1} else ∅

/-- free の葉 `2^h .. 2^(h+1) - 1`。 -/
def cbtFree (h : ℕ) : Finset ℕ := Finset.Ico (2 ^ h) (2 ^ (h + 1))

/-- ペブル対象の内部頂点 `1 .. 2^h - 1`。 -/
def cbtV (h : ℕ) : Finset ℕ := Finset.Icc 1 (2 ^ h)

theorem cbtV_card (h : ℕ) : (cbtV h).card = 2 ^ h - 1 := by
  simp only [cbtV, Nat.card_Icc]
  omega

theorem mem_cbtV {h w : ℕ} : w ∈ cbtV h ↔ 1 ≤ w ∧ w ≤ 2 ^ h - 1 := by
  simp only [cbtV, Finset.mem_Icc]

/-! ## 2. `card_le_of_reach` の 3 つの仮定 -/

/-- `hSink`: 根 `1` は誰の子でもない（子は `2w ≥ 2`, `2w+1 ≥ 3`）。 -/
theorem cbt_sink (h : ℕ) : ∀ w, (1 : ℕ) ∉ cbtPred h w := by
  intro w
  simp only [cbtPred]
  by_cases hc : 1 ≤ w ∧ w < 2 ^ h
  · rw [if_pos hc]
    obtain ⟨hc1, _⟩ := hc
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · rw [if_neg hc]
    simp

/-- `hρ`: 根は内部頂点（`h ≥ 1` が要る。`h = 0` では `cbtV 0 = ∅`）。 -/
theorem cbt_root_mem (h : ℕ) (hh : 1 ≤ h) : (1 : ℕ) ∈ cbtV h := by
  have h2 : 2 ≤ 2 ^ h := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  rw [mem_cbtV]
  omega

/-- `hV` の補助: `w ≤ n` に関する通常の帰納法（強帰納法の代わり。親は `w / 2 ≤ n`）。 -/
theorem cbt_reach_aux (h : ℕ) :
    ∀ n w, w ≤ n → w ∈ cbtV h → Reach (cbtPred h) (cbtFree h) 1 w := by
  intro n
  induction n with
  | zero =>
      intro w hwn hw
      rw [mem_cbtV] at hw
      exact absurd hw.1 (by omega)
  | succ n ih =>
      intro w hwn hw
      rw [mem_cbtV] at hw
      obtain ⟨hw1, hw2⟩ := hw
      rcases eq_or_lt_of_le hw1 with h1 | h1
      · -- `w = 1`（根）
        subst h1
        exact Reach.root
      · -- `w ≥ 2`: 親 `w / 2` から 1 段降りる
        have hpar : w / 2 ∈ cbtV h := by
          rw [mem_cbtV]; omega
        have hrec : Reach (cbtPred h) (cbtFree h) 1 (w / 2) :=
          ih (w / 2) (by omega) hpar
        have hmem : w ∈ cbtPred h (w / 2) := by
          simp only [cbtPred]
          rw [if_pos (by omega : 1 ≤ w / 2 ∧ w / 2 < 2 ^ h)]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have hfree : w ∉ cbtFree h := by
          simp only [cbtFree, Finset.mem_Ico, not_and, not_lt]
          omega
        exact Reach.step hrec hmem hfree

/-- `hV`: 内部頂点はすべて、free（葉）を通らない道で根に届く。 -/
theorem cbt_reach (h : ℕ) : ∀ w, w ∈ cbtV h → Reach (cbtPred h) (cbtFree h) 1 w :=
  fun w hw => cbt_reach_aux h w w le_rfl hw

/-! ## 3. 具体化した下界 -/

/-- **完全二分木 `T_h` の殻補題**: `M ≥ 4(2^h − 1) − 2·min(p, 2^h−1) − 1`。

`hmv`（手はすべて内部頂点）は冒頭の ⚠ のとおり仮定として残す。 -/
theorem cbt_bound {h p M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ} (hh : 1 ≤ h)
    (hS : Sched (cbtPred h) (cbtFree h) 1 p M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV h) :
    4 * (2 ^ h - 1) ≤ M + 2 * min p (2 ^ h - 1) + 1 := by
  have hkey := hS.card_le_of_reach (cbt_sink h) (cbtV h) (cbt_reach h)
    (cbt_root_mem h hh) hmv
  rwa [cbtV_card h] at hkey

/-! ## 4. 数値校正（★ これを省くと heap 番号の取り違えが型検査を素通りする） -/

/-- **校正**: `h = 3, p = 5` で `M ≥ 17`。**全数 BFS の真値 `M*(T_3) = 17` と一致**。 -/
theorem cbt_h3_bound {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
    (hS : Sched (cbtPred 3) (cbtFree 3) 1 5 M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV 3) : 17 ≤ M := by
  have hb := cbt_bound (h := 3) (p := 5) (by norm_num) hS hmv
  simp only [show (2 : ℕ) ^ 3 = 8 from by norm_num] at hb
  omega

/-- **banlist の 2 項目の根拠**: `h = 6, p = 8` で `M*(T_6) ≥ 235`。 -/
theorem cbt_h6_bound {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
    (hS : Sched (cbtPred 6) (cbtFree 6) 1 8 M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV 6) : 235 ≤ M := by
  have hb := cbt_bound (h := 6) (p := 8) (by norm_num) hS hmv
  simp only [show (2 : ℕ) ^ 6 = 64 from by norm_num] at hb
  omega

/-- `h = 7, p = 10`（`p_min(T_7) = 10`）で `M*(T_7) ≥ 487`。 -/
theorem cbt_h7_bound {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
    (hS : Sched (cbtPred 7) (cbtFree 7) 1 10 M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV 7) : 487 ≤ M := by
  have hb := cbt_bound (h := 7) (p := 10) (by norm_num) hS hmv
  simp only [show (2 : ℕ) ^ 7 = 128 from by norm_num] at hb
  omega

/-- 予算最大の点（`p = 2^h − 1`）では `M ≥ 2(2^h−1) − 1`＝数え上げの自明下界と一致。
`h = 6` なら `M ≥ 125`（manifest 行12 の 125 と等号）。 -/
theorem cbt_h6_maxbudget {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ}
    (hS : Sched (cbtPred 6) (cbtFree 6) 1 63 M C mv)
    (hmv : ∀ t, t < M → mv t ∈ cbtV 6) : 125 ≤ M := by
  have hb := cbt_bound (h := 6) (p := 63) (by norm_num) hS hmv
  simp only [show (2 : ℕ) ^ 6 = 64 from by norm_num] at hb
  omega

/-! ## 4.5 ★ 非空虚性（`cbt_bound` が空虚な主張でないことの証人）

変異 M4（`cbtFree` から葉を 1 枚外す。job26）は **型検査を生き延びる**。理由は
「その `Sched` を満たすスケジュールが 1 本も無い」＝**主張が空虚になる**からで、
偽になるからではない。つまり **`sorry` が無く公理も標準 3 本でも、
定理が空虚でないことは別に示す必要がある**。

ここでは $T_2$（内部 1,2,3・葉 4..7・$p=3$）の 5 手スケジュール
`2, 3, 1, 3, 2` を**実物として与える**。`cbt_bound` は $h=2,p=3$ で $M\ge5$ を出し、
この証人が **5 手で達成する**（等号・既知値 $M^*(T_2)=5$ と一致）。 -/

/-- $T_2$ の最適スケジュール（toggle する頂点の列 `2,3,1,3,2`）。 -/
def mv2 : ℕ → ℕ := fun t =>
  if t = 0 then 2 else if t = 1 then 3 else if t = 2 then 1 else if t = 3 then 3 else 2

/-- 上の各手**直後**の配置。 -/
def C2 : ℕ → Finset ℕ := fun t =>
  if t = 0 then ∅ else if t = 1 then {2} else if t = 2 then {2, 3}
  else if t = 3 then {1, 2, 3} else if t = 4 then {1, 2} else {1}

theorem cbt_sched_h2 : Sched (cbtPred 2) (cbtFree 2) 1 3 5 C2 mv2 where
  start := rfl
  finish := rfl
  notFree := by intro t ht; interval_cases t <;> decide
  step := by intro t ht; interval_cases t <;> decide
  legal := by intro t ht; interval_cases t <;> decide
  peak := by intro t ht; interval_cases t <;> decide

theorem cbt_mv2_mem : ∀ t, t < 5 → mv2 t ∈ cbtV 2 := by
  intro t ht; interval_cases t <;> decide

/-- **`cbt_bound` は空虚でない**: $h=2,p=3$ を満たすスケジュールが実在する。 -/
theorem cbt_nonvacuous : ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
    Sched (cbtPred 2) (cbtFree 2) 1 3 5 C mv ∧ (∀ t, t < 5 → mv t ∈ cbtV 2) :=
  ⟨C2, mv2, cbt_sched_h2, cbt_mv2_mem⟩

/-- **校正（等号）**: $h=2,p=3$ の下界は 5、証人はちょうど 5 手。
既知値 $M^*(T_2)=5$ と一致する。 -/
theorem cbt_h2_tight :
    (4 * (2 ^ 2 - 1) ≤ 5 + 2 * min 3 (2 ^ 2 - 1) + 1)
      ∧ ∀ {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ},
        Sched (cbtPred 2) (cbtFree 2) 1 3 M C mv → (∀ t, t < M → mv t ∈ cbtV 2) → 5 ≤ M := by
  refine ⟨by decide, ?_⟩
  intro M C mv hS hmv
  have hb := cbt_bound (h := 2) (p := 3) (by norm_num) hS hmv
  simp only [show (2 : ℕ) ^ 2 = 4 from by norm_num] at hb
  omega

/-! ## 5. 公理検査 -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullLemmaCBTMut.cbt_reach
#print axioms HullLemmaCBTMut.cbt_bound
#print axioms HullLemmaCBTMut.cbt_h3_bound
#print axioms HullLemmaCBTMut.cbt_h6_bound
#print axioms HullLemmaCBTMut.cbt_h7_bound
#print axioms HullLemmaCBTMut.cbt_h6_maxbudget
#print axioms HullLemmaCBTMut.cbt_nonvacuous
#print axioms HullLemmaCBTMut.cbt_h2_tight
end Audit

end HullLemmaCBTMut
