/-
  **証書が使っている鍵そのものを Lean 側に書き、単射性を機械で示す**
  （第 81 夜 周 3・2026-10-12）。

  ## どの穴を埋めるか

  第 81 夜 周 1 の `night81r1_gapcount.py` が数えた「層 1 までに残る紙 3 本」の ① は、
  周 2 の `TreeAutCBTKey.lean`（鍵の一般化）で

      ① 証書の `canon` は **ある単射な鍵**についての軌道最小元である

  に弱まった。本ファイルはその「ある鍵」を**名指しで書き下す**:

      `keyCert h C := bitkey (C.image (relabCert h))`,
      `relabCert h v := if 0 < v ∧ v < 2^h then preIdx h v + 1 else v`

  ここで `preIdx h v` は **heap 番号 v の preorder 番号**（証書 `night76_cert_spec.md` §1.1 の
  番号づけ。`night76_certcheck_ref.py:layout` と同じもの）である。
  証書の `canon`（同 §1.2）は各節点で部分木コードの max を下位・min を上位に置くので、
  **preorder ビットマスクを最小にする軌道の元**を選んでいる。それがこの鍵である。
  （`relabCert` の「+1」は値を 2 倍するだけなので argmin を変えない。全数で実測もした。）

  ## ここで示すこと / 示さないこと

  - ★ 示す: **`keyCert h` は単射**（`hkey` が立つ）。したがって周 2 の
    `length_ge_of_quot_levels_cbt_key` は **証書の鍵のまま**使える。
    単射性は $h$ ごとに `decide` で閉じる（$h\le5$ を本ファイルに、$h=7$ は `KeyCertH7.lean`）。
  - ✗ 示さない: 「証書の `canon` 関数がこの鍵の軌道最小元である」こと自体。
    これは $h\le4$ の**全配置**（$2^{15}$ 個）で `night81r3_keycert.py` が確かめた
    （プログラムの層）。Lean で言うには `autB h` の軌道を計算する必要があり、
    $h=7$ では $2^{128}$ 本なので計算では閉じない。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。

  ## 非空虚性（鍵の一般化は飾りではなかった）

  `night81r3_keycert.py` の全数: $h\le3$ では `bitkey` の軌道最小元と `keyCert` の軌道最小元は
  **全配置で一致する**が、$h=4$ では **32,768 配置のうち 1,216 で食い違う**。
  すなわち周 2 以前の `canonCbt`（`bitkey`）は証書の代表と**別の元**を選んでおり、
  残る紙 ① は実在の隙間だった。小さい $h$ だけを見ていると見えない。
-/
import TreeAutCBTKey

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. heap 番号 → preorder 番号（燃料つきの再帰。`decide` が通るように） -/

/-- 根からの深さ。`f` は燃料（`Nat.log` を使わないのは `decide` で潰すため）。 -/
def depF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, v => if v ≤ 1 then 0 else depF f (v / 2) + 1

/-- heap 番号 `v` の preorder 番号（高さ `h` の完全二分木）。

左の子は親の直後（+1）、右の子は親の直後から左部分木の大きさ
$S_{m-1} = 2^{m-1}-1$ だけ先（+ $2^{m-1}$）。ここで $m$ は部分木の高さ。 -/
def preF (h : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, v =>
      if v ≤ 1 then 0
      else preF h f (v / 2) + (if v % 2 = 0 then 1 else 2 ^ (h - 1 - depF f (v / 2)))

/-- 燃料を `h` に固定したもの（`v < 2^h` なら深さ $\le h-1$ なので足りる）。 -/
def preIdx (h v : ℕ) : ℕ := preF h h v

/-! ## 2. 「区間 $[1,N)$ の中だけ入れ替える」写像は、そこで単射なら全体で単射 -/

/-- `f` を $[1,N)$ の上だけで使い、外側は恒等にした写像。 -/
def relabOf (N : ℕ) (f : ℕ → ℕ) (v : ℕ) : ℕ := if 0 < v ∧ v < N then f v else v

/-- ★ **有界な単射 → 全体の単射。** 仮定は 2 つとも `∀ v < N` の形なので
`decide` で閉じられる（`Nat.decidableBallLT`）。 -/
theorem relabOf_injective {N : ℕ} {f : ℕ → ℕ}
    (hb : ∀ v, v < N → 0 < v → 0 < f v ∧ f v < N)
    (hi : ∀ v, v < N → ∀ w, w < N → 0 < v → 0 < w → f v = f w → v = w) :
    Function.Injective (relabOf N f) := by
  intro a b hab
  simp only [relabOf] at hab
  by_cases ha : 0 < a ∧ a < N
  · by_cases hbb : 0 < b ∧ b < N
    · rw [if_pos ha, if_pos hbb] at hab
      exact hi a ha.2 b hbb.2 ha.1 hbb.1 hab
    · rw [if_pos ha, if_neg hbb] at hab
      have h1 := hb a ha.2 ha.1
      omega
  · by_cases hbb : 0 < b ∧ b < N
    · rw [if_neg ha, if_pos hbb] at hab
      have h1 := hb b hbb.2 hbb.1
      omega
    · rw [if_neg ha, if_neg hbb] at hab
      exact hab

/-! ## 3. 証書の鍵 -/

/-- 証書の番号づけへの貼り替え（$[1,2^h)$ の中だけ動く）。 -/
def relabCert (h : ℕ) : ℕ → ℕ := relabOf (2 ^ h) (fun v => preIdx h v + 1)

/-- ★ **証書が最小化している鍵**: preorder ビットマスク（を 2 倍したもの）。 -/
def keyCert (h : ℕ) (C : Finset ℕ) : ℕ := bitkey (C.image (relabCert h))

/-- 鍵の単射性は貼り替えの単射性から出る。 -/
theorem keyCert_injective {h : ℕ} (hrel : Function.Injective (relabCert h)) :
    Function.Injective (keyCert h) := by
  intro A B hAB
  exact Finset.image_injective hrel (bitkey_inj hAB)

/-- 貼り替えの単射性を `decide` 可能な 2 条件に落とす。 -/
theorem relabCert_injective (h : ℕ)
    (hb : ∀ v, v < 2 ^ h → 0 < v → 0 < preIdx h v + 1 ∧ preIdx h v + 1 < 2 ^ h)
    (hi : ∀ v, v < 2 ^ h → ∀ w, w < 2 ^ h → 0 < v → 0 < w →
      preIdx h v + 1 = preIdx h w + 1 → v = w) :
    Function.Injective (relabCert h) :=
  relabOf_injective hb hi

/-! ## 4. $h$ ごとの実例（`decide` で閉じる） -/

theorem relabCert_inj_1 : Function.Injective (relabCert 1) :=
  relabCert_injective 1 (by decide) (by decide)
theorem relabCert_inj_2 : Function.Injective (relabCert 2) :=
  relabCert_injective 2 (by decide) (by decide)
theorem relabCert_inj_3 : Function.Injective (relabCert 3) :=
  relabCert_injective 3 (by decide) (by decide)
theorem relabCert_inj_4 : Function.Injective (relabCert 4) :=
  relabCert_injective 4 (by decide) (by decide)
theorem relabCert_inj_5 : Function.Injective (relabCert 5) :=
  relabCert_injective 5 (by decide) (by decide)

theorem keyCert_inj_4 : Function.Injective (keyCert 4) := keyCert_injective relabCert_inj_4

/-! ## 5. ★ 証書の鍵のままの下界（周 2 の一般形へ差し込むだけ） -/

/-- $T_h$ の、**証書の鍵**による正準形。 -/
def canonCbtCert (h : ℕ) : Finset ℕ → Finset ℕ := canonCbtK (keyCert h) h

/-- ★★ **商レベル集合証書 → 手数の下界（鍵は証書のもの）。**

仮定は **貼り替えの単射性（$h$ ごとに `decide`）＋ 証書の 3 検査**だけである。
木ごとの `decide`（配置の全数）は 0 個。 -/
theorem length_ge_of_quot_levels_cbt_cert
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h q T : ℕ) (hrel : Function.Injective (relabCert h))
    (hcanon0 : Lq 0 (canonCbtCert h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ HullLemmaCBT.cbtV h,
      m ∉ HullLemmaCBT.cbtFree h →
      (∀ c ∈ HullLemmaCBT.cbtPred h m, c ∈ s ∨ c ∈ HullLemmaCBT.cbtFree h) →
      (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbtCert h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbtCert h Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ HullLemmaCBT.cbtV h)
    (hL : Legal (HullLemmaCBT.cbtPred h) (HullLemmaCBT.cbtFree h) l ∅)
    (hP : Peak q l ∅) (hrun : run l ∅ = Y) : T + 1 ≤ l.length :=
  length_ge_of_quot_levels_cbt_key (keyCert_injective hrel) h q T hcanon0 hqcl hY l hS hL hP hrun

/-- 同じものを `Dcert`（証明書つき真の距離）の下界として。 -/
theorem Dcert_ge_of_quot_levels_cbt_cert
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h q T Bd : ℕ) (hrel : Function.Injective (relabCert h))
    (hcanon0 : Lq 0 (canonCbtCert h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ HullLemmaCBT.cbtV h,
      m ∉ HullLemmaCBT.cbtFree h →
      (∀ c ∈ HullLemmaCBT.cbtPred h m, c ∈ s ∨ c ∈ HullLemmaCBT.cbtFree h) →
      (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbtCert h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbtCert h Y))
    (hB : T + 1 ≤ Bd) :
    T + 1 ≤ Dcert (HullLemmaCBT.cbtPred h) (HullLemmaCBT.cbtFree h) Bd q
      (HullLemmaCBT.cbtV h) ∅ Y :=
  Dcert_ge_of_quot_levels_cbt_key (keyCert_injective hrel) h q T Bd hcanon0 hqcl hY hB

#print axioms relabOf_injective
#print axioms keyCert_injective
#print axioms relabCert_inj_4
#print axioms relabCert_inj_5
#print axioms length_ge_of_quot_levels_cbt_cert
#print axioms Dcert_ge_of_quot_levels_cbt_cert

end SplitLemma
