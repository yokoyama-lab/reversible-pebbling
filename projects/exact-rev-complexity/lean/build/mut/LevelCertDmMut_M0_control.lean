/-
  **レベル束の証明書から `hDmA` / `hDmB` の形へ**（第59夜 周3/3 2026-09-13）。

  周2/3 の残る穴 1 の Lean 側。第59夜 周1/3 で `split_lemma_strong_num`（橋）が
  入ったあと、$M^*(T_8,11)\ge 1819$ / $M^*(T_8,12)\ge 1589$ の根拠のうち機械の外に
  残っているのは **`hDmA` / `hDmB` の 2 点だけ**だった:

      hDmA : ∀ q Y, Y ⊆ A → a ∈ Y → Dm q Y.card ≤ D q A ∅ Y

  ——「表 `Dm q s` が、大きさ `s` で部分木の根 `a` を含む**すべての** `Y` を下から
  押さえる」。これは**下界**なので証人（具体スケジュール）では出ない。要るのは
  「掃いた中に無かった」ではなく「**掃きが全数だった**」という主張である。

  周2/3 で `Dcert_ge_of_levels`（閉包性を満たすレベル束の外への距離は `T+1` 以上）を
  入れた。ここではそれを **`s` について量化**して `hDmA` とちょうど同じ形にする
  （§1 の `Dm_le_Dcert_of_levels`）。済めば $1819$ / $1589$ の外部入力は**ゼロ**になる。

  ## 設計 — `Tf : ℕ → ℕ` を渡し、束は 1 つで済ます

  * 束 `Lv` は `q` にも `s` にも依存させない。閉包性からピーク条件
    `(toggleAt C m).card ≤ q` を**落として**要求する（＝どの `q` でも通る強い閉包性）。
    部分木が小さいときはピーク条件が束縛しないので、これで損をしない。
  * 深さは `Tf s`（`s` ごとに違う打ち切り深さ）。`Tf s ≤ M` で 1 つの閉包性に相乗りする。
  * `s` の範囲を `1 ≤ s ≤ N`（`A.card ≤ N`）に絞る。`a ∈ Y ⊆ A` からこの範囲は自動で
    従うので**仮定を弱めていない**。絞る理由は証人側で `interval_cases s` が使えること。

  ⚠ **何が機械の外に残るか**: 模型（`toggleAt` / `Legal` / `Peak` / `predT3` / `FT3`）。
  束を作る側と検査する側で共有しているので、模型が間違っていれば両方が同じ間違いを
  する。ここは `scripts/revpebble.py` との突き合わせ（数値側 `job111`）が受け持つ層。

  ## 証人 — $T_3$ で**パイプライン全体**を既知値に当てる（校正）

  $T_8$ の $1819$ を出したのと**同じ経路**（レベル束の証明書 → 表 → 強化版分割補題 →
  対ごとの不等式）を $h=3$ で走らせ、既知値 $M^*(T_3)=17$ が出るかを見る。

  * 部分木 $A=\{2,4,5\}$（根 $a=2$）・$B=\{3,6,7\}$（根 $b=3$）、$\rho=1$、$p=p_{\min}(T_3)=5$。
  * 証明書から出る表: $D_m(q,1)=5$・$D_m(q,2)=4$・$D_m(q,3)=3$（`TfA3 s + 1`）。
  * 対ごとの min は **17**（$(s_A,s_B)=(1,3),(2,2),(3,1)$ の 3 点で同時に達成）。
  * ⇒ `split_h3_num_cert : 17 ≤ l.length`。**`schedT3.length = 17` なので緊密**
    （`split_h3_num_cert_tight`）。表も下界も 1 も捨てていない。

  ⚠ $17$ は新しい数ではない（`HullLemmaCBT.cbt_h3_bound` が別経路で既に出している。
  manifest では `exact` ＋ DRAT）。**ここで新しいのは経路**で、$1819$ を出した経路に
  外部の数値入力が 1 つも無い形が立つことである。

  ## 事前登録（変異注入。**走らせる前に書いた**。採点は `job112`）

  危ない向き = 表を過大にする／束を小さくする／閉包の主張範囲を広げる。

  | 変異 | 種別 | 予測 |
  |---|---|---|
  | `M1_tf_s3_up`（`TfA3 3` を 2→3。表を 1 上げる） | stmt | 落ちる（`LvA3_miss` が破れる） |
  | `M2_bnd_18`（結論を 17→18） | stmt | 落ちる（`hpairT3` の min は 17） |
  | `M3_drop_state`（束から `{4,5}` を落とす） | stmt | 落ちる（`LvA3_closed` が破れる） |
  | `M4_closure_slack`（閉包の範囲を `i<4`→`i<5`） | stmt | 落ちる（`{2}` が束の外） |
  | `C1_unused_branch`（`TfA3` の `s ≥ 4` 用の枝を 0→7・対照） | ctrl | 通る |
  | `C2_reorder`（`LvlA3` のレベル内の順序・対照） | ctrl | 通る |

  ⚠ 対照は banlist（第59夜「弱める変異は中立でない」）の条件を満たす形にした——
  **下流の証人が受け取る引数の形を変えない**（`C1` は到達しない枝の値だけ、
  `C2` は `Finset` の要素の並びだけ）。
  ⚠ 最初は対照を「`B` を 5→9」にしていたが、**`hDmA3` の宣言した型に `Dcert … 5` が
  現れるので引数の形が変わってしまい、中立にならない**（走らせる前に気づいて差し替えた）。
  ★ `C1` は同時に「`1 ≤ s ≤ N` の範囲制限が実際に効いていて、使われない枝が
  下界に漏れていない」ことの検査にもなっている。
-/
import LevelCert
import SplitLemmaNum

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 証明書から `hDmA` の形へ -/

/-- ★ **レベル束の証明書から `hDmA` / `hDmB` の形へ。**

`Lv` は（`q` にも `s` にも依存しない）レベル束、`Tf s` は大きさ `s` 用の打ち切り深さ。
結論は `split_lemma_strong_num` の `hDmA` と**同じ形**（`Dm := fun _ s => Tf s + 1`）。

仮定の読み:
* `h0` — 束の 0 段目に初期配置がある。
* `hcl` — **閉包性**（`i < M` の各段の各配置の合法な後続が段 `≤ i+1` にある）。
  ピーク条件を課していないので、どの `q` でも使える。
* `hN` / `hT` / `hmiss` / `hB` — `1 ≤ s ≤ N` の範囲でだけ要求する。`a ∈ Y ⊆ A` から
  `Y.card` はこの範囲に入るので、仮定を弱めてはいない。
* `hmiss` — ★ **全数性**。「段 `≤ Tf s` に、`a` を含む大きさ `s` の配置が 1 つも無い」。 -/
theorem Dm_le_Dcert_of_levels {pred : ℕ → Finset ℕ} {F A : Finset ℕ} {a B M N : ℕ}
    {Lv : ℕ → Finset ℕ → Prop} {Tf : ℕ → ℕ}
    (h0 : Lv 0 ∅)
    (hcl : ∀ i, i < M → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ A, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m))
    (hN : A.card ≤ N)
    (hT : ∀ s, 1 ≤ s → s ≤ N → Tf s ≤ M)
    (hmiss : ∀ s, 1 ≤ s → s ≤ N → ∀ j, j ≤ Tf s → ∀ C : Finset ℕ, Lv j C →
      a ∈ C → C.card ≠ s)
    (hB : ∀ s, 1 ≤ s → s ≤ N → Tf s + 1 ≤ B) :
    ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ A → a ∈ Y →
      (fun (_ s : ℕ) => Tf s + 1) q Y.card ≤ Dcert pred F B q A ∅ Y := by
  intro q Y hYA haY
  have h1 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨a, haY⟩
  have h2 : Y.card ≤ N := le_trans (Finset.card_le_card hYA) hN
  exact Dcert_ge_of_levels (T := Tf Y.card) h0
    (fun i hi C hC m hm hmF hpred _ =>
      hcl i (lt_of_lt_of_le hi (hT Y.card h1 h2)) C hC m hm hmF hpred)
    (fun j hj hLv => hmiss Y.card h1 h2 j hj Y hLv haY rfl) (hB Y.card h1 h2)

/-! ## 2. 証人 — `T_3`（heap 番号。内部頂点 1..7、free の葉 8..15） -/

/-- `T_3` の先行関係（heap 番号。`v` の子は `2v, 2v+1`）。 -/
def predT3 : ℕ → Finset ℕ := fun v =>
  if v = 1 then {2, 3} else if v = 2 then {4, 5} else if v = 3 then {6, 7}
  else if v = 4 then {8, 9} else if v = 5 then {10, 11}
  else if v = 6 then {12, 13} else if v = 7 then {14, 15} else ∅

/-- free の葉。 -/
def FT3 : Finset ℕ := {8, 9, 10, 11, 12, 13, 14, 15}

/-- `M*(T_3) = 17` を達成するスケジュール（`t3_m17.json` = BFS の出力。
`HullLemmaCBTWitness.mvLh3` と同じ列。手書きではない）。 -/
def schedT3 : List ℕ := [4, 5, 2, 4, 5, 6, 7, 3, 1, 3, 4, 6, 5, 2, 4, 5, 7]

theorem predT3_irrefl : ∀ v : ℕ, v ∉ predT3 v := by
  intro v
  simp only [predT3]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · subst h1; decide
  · subst h2; decide
  · subst h3; decide
  · subst h4; decide
  · subst h5; decide
  · subst h6; decide
  · subst h7; decide
  · simp

-- ⚠ 2 つ罠を踏んだので書いておく（どちらも第59夜 周3/3 に実測。`probe_n59r3_legal.lean`）:
--   ① `predT3` / `FT3` / `toggleAt` を `simp only` に**入れない**こと。`4 = 4` が `True` へ
--      書き換わった `ite` が残り（`instDecidableEqNat` のままなので `if_true` が当たらない）、
--      `decide` の `Decidable` 合成が落ちる。`Legal` / `Peak` / `run` の展開だけでよい。
--   ② 17 手だと `Decidable` の合成が **`synthInstance.maxSize`（既定 128）** を超える。
--      `maxRecDepth` ではない（10 万にしても落ちた。3 手なら既定で通る）。
--      ⇒ 落ちるのは「証明の不備」ではなく合成の上限。T_2（5 手）で見えなかったのはこれ。
set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
theorem schedT3_legal : Legal predT3 FT3 schedT3 ∅ := by
  simp only [schedT3, Legal]
  decide

set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
theorem schedT3_peak : Peak 5 schedT3 ∅ := by
  simp only [schedT3, Peak]
  decide

set_option maxRecDepth 4000 in
set_option synthInstance.maxSize 4000 in
theorem schedT3_clean : run schedT3 ∅ = {1} := by
  simp only [schedT3, run]
  decide

/-! ## 3. 部分木 `A = {2,4,5}` のレベル束と証明書 -/

/-- `A` に閉じたゲームの BFS レベル束（数値側 `job111` が独立に測ったものと同じ）。 -/
def LvlA3 : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then {∅} else if i = 1 then {{4}, {5}} else if i = 2 then {{4, 5}}
  else if i = 3 then {{2, 4, 5}} else if i = 4 then {{2, 4}, {2, 5}} else ∅

abbrev LvA3 (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlA3 i

/-- 大きさ `s` 用の打ち切り深さ。表は `Tf s + 1` ＝ `5, 4, 3`。
⚠ 末尾の `else 0` は **`s ≥ 4` 用で、下界の計算には一度も出てこない**
（`a ∈ Y ⊆ A` かつ `|A| = 3` なので `1 ≤ s ≤ 3`）。対照変異 `C1_unused_branch` が
「使われないことを確かめる」ために触るのはここ。 -/
def TfA3 : ℕ → ℕ := fun s =>
  if s = 1 then 4 else if s = 2 then 3 else if s = 3 then 2 else 0

theorem LvA3_zero : LvA3 0 ∅ := by decide

theorem LvA3_closed : ∀ i, i < 4 → ∀ C : Finset ℕ, LvA3 i C →
    ∀ m ∈ ({2, 4, 5} : Finset ℕ), m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ C ∨ c ∈ FT3) → ∃ j, j ≤ i + 1 ∧ LvA3 j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred
  have hC' : C ∈ LvlA3 i := hC
  interval_cases i <;>
    simp only [LvlA3] at hC' <;>
    fin_cases hC' <;>
    fin_cases hm <;>
    first
      | (refine ⟨0, by omega, ?_⟩; decide)
      | (refine ⟨1, by omega, ?_⟩; decide)
      | (refine ⟨2, by omega, ?_⟩; decide)
      | (refine ⟨3, by omega, ?_⟩; decide)
      | (refine ⟨4, by omega, ?_⟩; decide)
      | (exact absurd (hpred 4 (by decide)) (by decide))
      | (exact absurd (hpred 5 (by decide)) (by decide))

/-- ★ **全数性**: 段 `≤ TfA3 s` に、`2` を含む大きさ `s` の配置は 1 つも無い。 -/
theorem LvA3_miss : ∀ s, 1 ≤ s → s ≤ 3 → ∀ j, j ≤ TfA3 s → ∀ C : Finset ℕ,
    LvA3 j C → 2 ∈ C → C.card ≠ s := by
  intro s h1 h3 j hj C hC h2
  have hC' : C ∈ LvlA3 j := hC
  interval_cases s <;>
    simp only [TfA3] at hj <;>
    norm_num at hj <;>
    interval_cases j <;>
      simp only [LvlA3] at hC' <;>
      fin_cases hC' <;>
      revert h2 <;>
      decide

theorem hDmA3 : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ ({2, 4, 5} : Finset ℕ) → 2 ∈ Y →
    (fun (_ s : ℕ) => TfA3 s + 1) q Y.card ≤ Dcert predT3 FT3 5 q ({2, 4, 5} : Finset ℕ) ∅ Y :=
  Dm_le_Dcert_of_levels (pred := predT3) (F := FT3) (A := ({2, 4, 5} : Finset ℕ))
    (a := 2) (B := 5) (M := 4) (N := 3) (Lv := LvA3) (Tf := TfA3)
    LvA3_zero LvA3_closed (by decide)
    (by intro s h1 h3; interval_cases s <;> simp only [TfA3] <;> norm_num)
    LvA3_miss
    (by intro s h1 h3; interval_cases s <;> simp only [TfA3] <;> norm_num)

/-! ## 4. 部分木 `B = {3,6,7}` — 同じ形（左右対称） -/

def LvlB3 : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then {∅} else if i = 1 then {{6}, {7}} else if i = 2 then {{6, 7}}
  else if i = 3 then {{3, 6, 7}} else if i = 4 then {{3, 6}, {3, 7}} else ∅

abbrev LvB3 (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlB3 i

theorem LvB3_zero : LvB3 0 ∅ := by decide

theorem LvB3_closed : ∀ i, i < 4 → ∀ C : Finset ℕ, LvB3 i C →
    ∀ m ∈ ({3, 6, 7} : Finset ℕ), m ∉ FT3 →
    (∀ c ∈ predT3 m, c ∈ C ∨ c ∈ FT3) → ∃ j, j ≤ i + 1 ∧ LvB3 j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred
  have hC' : C ∈ LvlB3 i := hC
  interval_cases i <;>
    simp only [LvlB3] at hC' <;>
    fin_cases hC' <;>
    fin_cases hm <;>
    first
      | (refine ⟨0, by omega, ?_⟩; decide)
      | (refine ⟨1, by omega, ?_⟩; decide)
      | (refine ⟨2, by omega, ?_⟩; decide)
      | (refine ⟨3, by omega, ?_⟩; decide)
      | (refine ⟨4, by omega, ?_⟩; decide)
      | (exact absurd (hpred 6 (by decide)) (by decide))
      | (exact absurd (hpred 7 (by decide)) (by decide))

theorem LvB3_miss : ∀ s, 1 ≤ s → s ≤ 3 → ∀ j, j ≤ TfA3 s → ∀ C : Finset ℕ,
    LvB3 j C → 3 ∈ C → C.card ≠ s := by
  intro s h1 h3 j hj C hC h2
  have hC' : C ∈ LvlB3 j := hC
  interval_cases s <;>
    simp only [TfA3] at hj <;>
    norm_num at hj <;>
    interval_cases j <;>
      simp only [LvlB3] at hC' <;>
      fin_cases hC' <;>
      revert h2 <;>
      decide

theorem hDmB3 : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ ({3, 6, 7} : Finset ℕ) → 3 ∈ Y →
    (fun (_ s : ℕ) => TfA3 s + 1) q Y.card ≤ Dcert predT3 FT3 5 q ({3, 6, 7} : Finset ℕ) ∅ Y :=
  Dm_le_Dcert_of_levels (pred := predT3) (F := FT3) (A := ({3, 6, 7} : Finset ℕ))
    (a := 3) (B := 5) (M := 4) (N := 3) (Lv := LvB3) (Tf := TfA3)
    LvB3_zero LvB3_closed (by decide)
    (by intro s h1 h3; interval_cases s <;> simp only [TfA3] <;> norm_num)
    LvB3_miss
    (by intro s h1 h3; interval_cases s <;> simp only [TfA3] <;> norm_num)

/-! ## 5. 対ごとの不等式（数値側の二重ループそのもの）と結論 -/

/-- ★ **対ごとの min が 17**（$(1,3),(2,2),(3,1)$ の 3 点で同時に達成＝緊密）。 -/
theorem hpairT3 : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 5 →
    17 ≤ ((fun (_ s : ℕ) => TfA3 s + 1) 5 sA + (fun (_ s : ℕ) => TfA3 s + 1) (5 - 1) sA)
      + 2 * (fun (_ s : ℕ) => TfA3 s + 1) (5 - 1) sB + 1 := by
  intro sA sB hA hB hsum
  have hA3 : sA ≤ 3 := by omega
  have hB3 : sB ≤ 3 := by omega
  interval_cases sA <;> interval_cases sB <;>
    first
      | omega
      | (simp only [TfA3]; norm_num)

/-- ★ **$T_3$ でパイプライン全体を既知値に当てた**: レベル束の証明書 → 表 →
強化版分割補題 → 対ごとの不等式で $M^*(T_3,5) \ge 17$。**外部の数値入力は無い。** -/
theorem split_h3_num_cert (l : List ℕ)
    (hL : Legal predT3 FT3 l ∅) (hP : Peak 5 l ∅) (hfin : run l ∅ = {1}) :
    17 ≤ l.length :=
  split_lemma_strong_num (pred := predT3) (F := FT3) (ρ := 1) (p := 5)
    (A := ({2, 4, 5} : Finset ℕ)) (B := ({3, 6, 7} : Finset ℕ))
    (D := Dcert predT3 FT3 5)
    predT3_irrefl (Dcert_valid predT3 FT3 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun (_ s : ℕ) => TfA3 s + 1) 17 hDmA3 hDmB3 hpairT3
    l hL hP hfin

/-- ★ **緊密**: 下界 17 に 17 手の実スケジュールが当たる。⇒ 証明書も橋も
下界を 1 も捨てていない（`M*(T_3) = 17` にちょうど一致）。 -/
theorem split_h3_num_cert_tight :
    17 ≤ schedT3.length ∧ schedT3.length = 17 :=
  ⟨split_h3_num_cert schedT3 schedT3_legal schedT3_peak schedT3_clean, rfl⟩

#print axioms Dm_le_Dcert_of_levels
#print axioms predT3_irrefl
#print axioms schedT3_legal
#print axioms schedT3_peak
#print axioms schedT3_clean
#print axioms LvA3_closed
#print axioms LvA3_miss
#print axioms hDmA3
#print axioms LvB3_closed
#print axioms LvB3_miss
#print axioms hDmB3
#print axioms hpairT3
#print axioms split_h3_num_cert
#print axioms split_h3_num_cert_tight

end SplitLemma
