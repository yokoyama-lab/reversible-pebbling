/-
  **完全二分木 $T_h$ の `hstep` を $h$ 一般に出す**（第81夜 周1・2026-10-11）。

  第79夜 周3〜5 は次の 3 つを別々に作ったまま、**繋いでいなかった**:

  - 周 3 `hstep_of_aut` … 置換の族から `hstep` を出す一般の十分条件（6 仮定）
  - 周 4 `hstep_of_group` … `canon = canonOf G`（軌道のキー最小元）に固定して
    仮定を「`G` が群」＋「木ごとの有限検査 3 つ（`hSg` `hFg` `hpredg`）」へ減らす
  - 周 5 `TreeAut.swapAct` … 自己同型をビット関数で与え、合成・逆元・深さの保存・
    子の集合の**厳密な**同変を $h$ に依らず証明（**ただし誰も使っていなかった**）

  木ごとの有限検査は `decide` で済ませていたので、周 4 の `LevelCertT3.lean` は
  表 $2^{2^{h-1}-1}$ 本に対する二重指数の壁にぶつかっていた（$h=5$ で $10^{10}$ 点）。

  ここでは周 5 の道具で**その 3 つの検査を $h$ 一般の定理にする**。`decide` は 1 つも使わない。
  得られるのは

      `hstep_cbt_of_group` … $T_h$ の `hstep`（$h$ は任意・証明は $h$ に依らない）

  で、`LevelCertQuot.lean` の `length_ge_of_quot_levels` と繋いだ
  `length_ge_of_quot_levels_cbt` / `Dcert_ge_of_quot_levels_cbt` が最終形である。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままで、
  5.44 GB の証書を Lean に通したのではない。閉じたのは**論証の段**である。

  符号化は `HullLemmaCBT.lean` の正本（`cbtPred` / `cbtFree` / `cbtV`）をそのまま使う。
-/
import LevelCertGrp
import HullLemmaCBT
import TreeAut

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma TreeAut HullLemmaCBT

/-! ## 1. `swapAct` は heap 番号の段を保つ（`swapAct_depth` の使いやすい形） -/

theorem swapAct_zero (b : ℕ → Bool) : swapAct b 0 = 0 := swapAct_le_one b 0 (by omega)

theorem swapAct_inj (b : ℕ → Bool) : Function.Injective (swapAct b) :=
  Function.LeftInverse.injective (invAct_swapAct b)

theorem swapAct_pos_iff (b : ℕ → Bool) (v : ℕ) : 1 ≤ swapAct b v ↔ 1 ≤ v := by
  constructor
  · intro hs
    by_contra hcon
    have hv : v = 0 := by omega
    rw [hv, swapAct_zero] at hs
    omega
  · intro hv
    exact swapAct_pos b v hv

/-- ★ **像は同じ段に留まるので「$2^k$ 未満か」は像で変わらない。** -/
theorem swapAct_lt_two_pow (b : ℕ → Bool) (k : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    swapAct b v < 2 ^ k ↔ v < 2 ^ k := by
  have h1 : 2 ^ (Nat.log 2 v) ≤ v := Nat.pow_log_le_self 2 (by omega)
  have h2 : v < 2 ^ (Nat.log 2 v + 1) := Nat.lt_pow_succ_log_self (by norm_num) v
  obtain ⟨g1, g2⟩ := swapAct_depth b (Nat.log 2 v) v h1 h2
  have key : ∀ w : ℕ, 2 ^ (Nat.log 2 v) ≤ w → w < 2 ^ (Nat.log 2 v + 1) →
      (w < 2 ^ k ↔ Nat.log 2 v < k) := by
    intro w hw1 hw2
    constructor
    · intro hlt
      by_contra hcon
      have : (2 : ℕ) ^ k ≤ 2 ^ (Nat.log 2 v) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · intro hdk
      have : (2 : ℕ) ^ (Nat.log 2 v + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [key _ g1 g2, key v h1 h2]

/-! ## 2. 木ごとの有限検査 3 つが $h$ 一般の定理になる -/

/-- (b) 内部頂点（toggle 対象）は保たれる。 -/
theorem swapAct_mem_cbtV (b : ℕ → Bool) (h v : ℕ) :
    swapAct b v ∈ cbtV h ↔ v ∈ cbtV h := by
  have hp : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  simp only [mem_cbtV]
  constructor
  · intro hc
    have hv : 1 ≤ v := (swapAct_pos_iff b v).mp hc.1
    have hlt : v < 2 ^ h := (swapAct_lt_two_pow b h hv).mp (by omega)
    exact ⟨hv, by omega⟩
  · intro hc
    have hs : 1 ≤ swapAct b v := swapAct_pos b v hc.1
    have hlt : swapAct b v < 2 ^ h := (swapAct_lt_two_pow b h hc.1).mpr (by omega)
    exact ⟨hs, by omega⟩

/-- (c) free の葉は保たれる（**両方向**）。 -/
theorem swapAct_mem_cbtFree (b : ℕ → Bool) (h v : ℕ) :
    swapAct b v ∈ cbtFree h ↔ v ∈ cbtFree h := by
  have hp : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  simp only [cbtFree, Finset.mem_Ico]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [swapAct_zero]
  · constructor
    · intro hc
      have h2 : ¬ (v < 2 ^ h) := fun hlt =>
        absurd ((swapAct_lt_two_pow b h hv).mpr hlt) (by omega)
      have h3 : v < 2 ^ (h + 1) := (swapAct_lt_two_pow b (h + 1) hv).mp hc.2
      omega
    · intro hc
      have h2 : ¬ (swapAct b v < 2 ^ h) := fun hlt =>
        absurd ((swapAct_lt_two_pow b h hv).mp hlt) (by omega)
      have h3 : swapAct b v < 2 ^ (h + 1) := (swapAct_lt_two_pow b (h + 1) hv).mpr hc.2
      omega

/-- (d) 先行点（子の組）は**厳密に**同変。周 3 の「像か、さもなくば free」の弱い形は要らない
（周 5 の `swapAct_children` が葉まで動かす作用で厳密な同変を与えるため）。 -/
theorem image_cbtPred (b : ℕ → Bool) (h v : ℕ) :
    (cbtPred h v).image (swapAct b) = cbtPred h (swapAct b v) := by
  by_cases hv : 1 ≤ v ∧ v < 2 ^ h
  · have hs : 1 ≤ swapAct b v ∧ swapAct b v < 2 ^ h :=
      ⟨swapAct_pos b v hv.1, (swapAct_lt_two_pow b h hv.1).mpr hv.2⟩
    simp only [cbtPred, if_pos hv, if_pos hs]
    exact swapAct_children b v hv.1
  · have hs : ¬ (1 ≤ swapAct b v ∧ swapAct b v < 2 ^ h) := by
      intro hc
      have hv1 : 1 ≤ v := (swapAct_pos_iff b v).mp hc.1
      exact hv ⟨hv1, (swapAct_lt_two_pow b h hv1).mp hc.2⟩
    simp only [cbtPred, if_neg hv, if_neg hs]
    simp

theorem cbtPred_lift (b : ℕ → Bool) (h v : ℕ) :
    ∀ c ∈ cbtPred h (swapAct b v), ∃ c₀ ∈ cbtPred h v, c = swapAct b c₀ := by
  intro c hc
  rw [← image_cbtPred b h v] at hc
  obtain ⟨c₀, hc₀, hce⟩ := Finset.mem_image.mp hc
  exact ⟨c₀, hc₀, hce.symm⟩

/-! ## 3. ★ $T_h$ の `hstep`（$h$ 一般・`decide` を 1 つも使わない） -/

/-- 置換の有限族をビット関数の一覧で与える。 -/
def swapGroup (B : List (ℕ → Bool)) : List (ℕ → ℕ) := B.map swapAct

theorem mem_swapGroup {B : List (ℕ → Bool)} {g : ℕ → ℕ} :
    g ∈ swapGroup B ↔ ∃ b ∈ B, swapAct b = g := List.mem_map

/-- ★ **$T_h$ の `hstep`。** 仮定は「ビット関数の族 `B` が定める置換の集まりが群であること」
だけで、木ごとの有限検査（周 4 の `decide` 3 つ）は**全部定理に置き換わっている**。 -/
theorem hstep_cbt_of_group {B : List (ℕ → Bool)} (h q : ℕ)
    (hG : IsPermGroup (swapGroup B)) :
    ∀ C : Finset ℕ, ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ C ∨ c ∈ cbtFree h) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ cbtV h ∧ m' ∉ cbtFree h ∧
        (∀ c ∈ cbtPred h m', c ∈ canonOf (swapGroup B) C ∨ c ∈ cbtFree h) ∧
        (toggleAt (canonOf (swapGroup B) C) m').card ≤ q ∧
        canonOf (swapGroup B) (toggleAt C m)
          = canonOf (swapGroup B) (toggleAt (canonOf (swapGroup B) C) m') :=
  hstep_of_group (pred := cbtPred h) (F := cbtFree h) (S := cbtV h) (q := q) hG
    (fun g hg m hm => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact (swapAct_mem_cbtV b h m).mpr hm)
    (fun g hg x => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact swapAct_mem_cbtFree b h x)
    (fun g hg v c hc => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact Or.inl (cbtPred_lift b h v c hc))

/-! ## 4. 商レベル集合証書 → 下界（$h$ 一般） -/

/-- ★ **$T_h$ の商レベル集合証書から手数の下界へ。**
残る義務は証書そのものの 3 検査（`hcanon0` = 検査 3・`hqcl` = 検査 4・`hY` = 検査 5）と、
`B` が群であることだけである。 -/
theorem length_ge_of_quot_levels_cbt {B : List (ℕ → Bool)}
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ} (h q T : ℕ)
    (hG : IsPermGroup (swapGroup B))
    (hcanon0 : Lq 0 (canonOf (swapGroup B) ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonOf (swapGroup B) (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonOf (swapGroup B) Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ cbtV h) (hL : Legal (cbtPred h) (cbtFree h) l ∅)
    (hP : Peak q l ∅) (hrun : run l ∅ = Y) : T + 1 ≤ l.length :=
  length_ge_of_quot_levels hcanon0
    (fun _ _ C _ m hmS hmF hpred hcard =>
      hstep_cbt_of_group h q hG C m hmS hmF hpred hcard)
    hqcl hY l hS hL hP hrun

/-- 同じものを `Dcert`（証明書つき真の距離）の下界として。 -/
theorem Dcert_ge_of_quot_levels_cbt {B : List (ℕ → Bool)}
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ} (h q T Bd : ℕ)
    (hG : IsPermGroup (swapGroup B))
    (hcanon0 : Lq 0 (canonOf (swapGroup B) ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonOf (swapGroup B) (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonOf (swapGroup B) Y))
    (hB : T + 1 ≤ Bd) :
    T + 1 ≤ Dcert (cbtPred h) (cbtFree h) Bd q (cbtV h) ∅ Y :=
  Dcert_ge_of_quot_levels hcanon0
    (fun _ _ C _ m hmS hmF hpred hcard =>
      hstep_cbt_of_group h q hG C m hmS hmF hpred hcard)
    hqcl hY hB

/-! ## 5. 仮定が空虚でないことの最小の確認（自明群） -/

/-- 自明群 `{id}`（ビット関数は恒偽の 1 本）。 -/
def trivB : List (ℕ → Bool) := [fun _ => false]

theorem trivB_group : IsPermGroup (swapGroup trivB) := by
  have hmem : swapAct (fun _ => false) ∈ swapGroup trivB := by
    simp [swapGroup, trivB]
  refine ⟨⟨_, hmem, fun x => swapAct_id x⟩, ?_, ?_⟩
  · intro g hg k hk
    obtain ⟨b, hb, rfl⟩ := mem_swapGroup.mp hg
    obtain ⟨c, hc, rfl⟩ := mem_swapGroup.mp hk
    have hb' : b = fun _ => false := by simpa [trivB] using hb
    have hc' : c = fun _ => false := by simpa [trivB] using hc
    subst hb'; subst hc'
    -- `rw` は同じ具体化の出現をまとめて書き換えるので 2 回で閉じる
    -- （3 回目は対象が `x = x` になっており `rewrite` が失敗する。第 81 夜 周 1 の実測）
    exact ⟨_, hmem, fun x => by rw [swapAct_id, swapAct_id]⟩
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := mem_swapGroup.mp hg
    have hb' : b = fun _ => false := by simpa [trivB] using hb
    subst hb'
    exact ⟨_, hmem, fun x => by rw [swapAct_id, swapAct_id]⟩

#print axioms swapAct_lt_two_pow
#print axioms swapAct_mem_cbtV
#print axioms swapAct_mem_cbtFree
#print axioms image_cbtPred
#print axioms hstep_cbt_of_group
#print axioms length_ge_of_quot_levels_cbt
#print axioms Dcert_ge_of_quot_levels_cbt
#print axioms trivB_group

end SplitLemma
