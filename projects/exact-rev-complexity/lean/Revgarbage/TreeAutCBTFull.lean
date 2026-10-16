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
    -- `rw` は同じ具体化の出現をまとめて書き換えるので 2 回で閉じる（第 81 夜 周 2）
    exact ⟨_, hmem, fun x => by rw [swapAct_id, swapAct_id]⟩
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := mem_swapGroup.mp hg
    have hb' : b = fun _ => false := by simpa [trivB] using hb
    subst hb'
    exact ⟨_, hmem, fun x => by rw [swapAct_id, swapAct_id]⟩
/-! ## 6. ★ Aut($T_h$) そのものを与える — 表ではなくビット関数の一覧 -/

/-- 台が `[0, K)` に収まるビット関数の一覧（$2^K$ 本）。**項として書くだけで、評価しない。** -/
def bitFns : ℕ → List (ℕ → Bool)
  | 0 => [fun _ => false]
  | K + 1 => (bitFns K).flatMap (fun f => [f, fun u => if u = K then true else f u])

theorem bitFns_support : ∀ (K : ℕ), ∀ f ∈ bitFns K, ∀ u, K ≤ u → f u = false := by
  intro K
  induction K with
  | zero =>
    intro f hf u _
    have : f = fun _ => false := by simpa [bitFns] using hf
    rw [this]
  | succ K ih =>
    intro f hf u hu
    simp only [bitFns, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hf
    obtain ⟨g, hg, hfg⟩ := hf
    rcases hfg with rfl | rfl
    -- この枝では `rfl` が `g` を消して `f` に同一化するので、名前で呼ばず `_` にする
    · exact ih _ hg u (by omega)
    · have hk : u ≠ K := by omega
      simp only [hk, if_false]
      exact ih g hg u (by omega)

theorem bitFns_mem : ∀ (K : ℕ) (d : ℕ → Bool), (∀ u, K ≤ u → d u = false) → d ∈ bitFns K := by
  intro K
  induction K with
  | zero =>
    intro d hd
    have : d = fun _ => false := funext (fun u => hd u (by omega))
    simp [bitFns, this]
  | succ K ih =>
    intro d hd
    have hd0s : ∀ u, K ≤ u → (fun w => if w = K then false else d w) u = false := by
      intro u hu
      by_cases hk : u = K
      · simp [hk]
      · simp only [hk, if_false]
        exact hd u (by omega)
    have hmem0 : (fun w => if w = K then false else d w) ∈ bitFns K := ih _ hd0s
    simp only [bitFns, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨_, hmem0, ?_⟩
    cases hdk : d K
    · left
      funext u
      by_cases hk : u = K
      · simp [hk, hdk]
      · simp [hk]
    · right
      funext u
      by_cases hk : u = K
      · simp [hk, hdk]
      · simp [hk]

/-! ### 逆元のために `invAct` も段を保つことを示す（`swapAct` 側と同じ帰納） -/

theorem invAct_pos (b : ℕ → Bool) (w : ℕ) (h : 1 ≤ w) : 1 ≤ invAct b w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w 2 with hw | hw
    · rw [invAct_le_one b w (by omega)]; omega
    · obtain ⟨x, s, hx, hs, rfl⟩ := split_two hw
      have hix := ih x (by omega) hx
      rw [invAct_eq b x s hx hs]
      omega

theorem invAct_depth (b : ℕ → Bool) (d : ℕ) : ∀ w, 2 ^ d ≤ w → w < 2 ^ (d + 1) →
    2 ^ d ≤ invAct b w ∧ invAct b w < 2 ^ (d + 1) := by
  induction d with
  | zero =>
    intro w h1 h2
    have hw : w = 1 := by simp at h1 h2; omega
    subst hw
    rw [invAct_le_one b 1 (by omega)]
    simp
  | succ d ih =>
    intro w h1 h2
    have e1 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have e2 : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    have hw : 2 ≤ w := by
      have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      omega
    obtain ⟨x, s, hx, hs, rfl⟩ := split_two hw
    have hx1 : 2 ^ d ≤ x := by omega
    have hx2 : x < 2 ^ (d + 1) := by omega
    obtain ⟨g1, g2⟩ := ih x hx1 hx2
    have hss : (if b (invAct b x) then 1 - s else s) < 2 := by
      cases b (invAct b x) <;> simp <;> omega
    rw [invAct_eq b x s hx hs]
    omega

theorem invAct_lt_two_pow (b : ℕ → Bool) (k : ℕ) {w : ℕ} (hw : 1 ≤ w) :
    invAct b w < 2 ^ k ↔ w < 2 ^ k := by
  have h1 : 2 ^ (Nat.log 2 w) ≤ w := Nat.pow_log_le_self 2 (by omega)
  have h2 : w < 2 ^ (Nat.log 2 w + 1) := Nat.lt_pow_succ_log_self (by norm_num) w
  obtain ⟨g1, g2⟩ := invAct_depth b (Nat.log 2 w) w h1 h2
  have key : ∀ y : ℕ, 2 ^ (Nat.log 2 w) ≤ y → y < 2 ^ (Nat.log 2 w + 1) →
      (y < 2 ^ k ↔ Nat.log 2 w < k) := by
    intro y hy1 hy2
    constructor
    · intro hlt
      by_contra hcon
      have : (2 : ℕ) ^ k ≤ 2 ^ (Nat.log 2 w) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · intro hdk
      have : (2 : ℕ) ^ (Nat.log 2 w + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [key _ g1 g2, key w h1 h2]

/-! ### ★ 群であること — `h` にも族の本数にも依らない 1 本の証明 -/

/-- $T_h$ の自己同型（子の入れ替えビットは `[0, 2^h)` に台を持つ）。 -/
def autB (h : ℕ) : List (ℕ → Bool) := bitFns (2 ^ h)

theorem autB_group (h : ℕ) : IsPermGroup (swapGroup (autB h)) := by
  have hK : ∀ b ∈ autB h, ∀ u, 2 ^ h ≤ u → b u = false := bitFns_support (2 ^ h)
  have hpow : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hfalse : (fun _ : ℕ => false) ∈ autB h := bitFns_mem (2 ^ h) _ (fun _ _ => rfl)
  constructor
  · exact ⟨swapAct (fun _ => false), mem_swapGroup.mpr ⟨_, hfalse, rfl⟩, fun x => swapAct_id x⟩
  · intro g hg k hk
    obtain ⟨b, hb, rfl⟩ := mem_swapGroup.mp hg
    obtain ⟨c, hc, rfl⟩ := mem_swapGroup.mp hk
    refine ⟨swapAct (fun u => xor (b u) (c (swapAct b u))), ?_, ?_⟩
    · refine mem_swapGroup.mpr ⟨_, bitFns_mem _ _ ?_, rfl⟩
      intro u hu
      have hu1 : 1 ≤ u := by omega
      have h1 : b u = false := hK b hb u hu
      have h2 : ¬ (swapAct b u < 2 ^ h) := fun hlt =>
        absurd ((swapAct_lt_two_pow b h hu1).mp hlt) (by omega)
      have h3 : c (swapAct b u) = false := hK c hc _ (by omega)
      simp [h1, h3]
    · intro x
      exact (swapAct_comp c b x).symm
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := mem_swapGroup.mp hg
    refine ⟨swapAct (fun w => b (invAct b w)), ?_, ?_⟩
    · refine mem_swapGroup.mpr ⟨_, bitFns_mem _ _ ?_, rfl⟩
      intro w hw
      have hw1 : 1 ≤ w := by omega
      have h2 : ¬ (invAct b w < 2 ^ h) := fun hlt =>
        absurd ((invAct_lt_two_pow b h hw1).mp hlt) (by omega)
      exact hK b hb _ (by omega)
    · intro x
      have hfun : (fun u => xor (b u) ((fun w => b (invAct b w)) (swapAct b u)))
          = (fun _ : ℕ => false) := by
        funext u
        simp only [invAct_swapAct, Bool.xor_self]
      rw [swapAct_comp, hfun, swapAct_id]

/-! ## 7. ★★ $T_h$ の `hstep` が、仮定なしで、すべての $h$ について成り立つ -/

/-- $T_h$ の正準形（$\mathrm{Aut}(T_h)$ 軌道の `bitkey` 最小元）。 -/
def canonCbt (h : ℕ) : Finset ℕ → Finset ℕ := canonOf (swapGroup (autB h))

/-- ★★ **仮定なしの `hstep`。** 周 4 の $T_3$ 版（表 8 本の `decide`）と違い、
$h$ は任意で、`decide` は 1 つも使っていない。 -/
theorem hstep_cbt (h q : ℕ) :
    ∀ C : Finset ℕ, ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ C ∨ c ∈ cbtFree h) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ cbtV h ∧ m' ∉ cbtFree h ∧
        (∀ c ∈ cbtPred h m', c ∈ canonCbt h C ∨ c ∈ cbtFree h) ∧
        (toggleAt (canonCbt h C) m').card ≤ q ∧
        canonCbt h (toggleAt C m) = canonCbt h (toggleAt (canonCbt h C) m') :=
  hstep_cbt_of_group h q (autB_group h)

/-- ★★ **$T_h$ の商レベル集合証書から下界へ（仮定は証書の 3 検査だけ）。** -/
theorem length_ge_of_quot_levels_cbt_aut {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h q T : ℕ)
    (hcanon0 : Lq 0 (canonCbt h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbt h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbt h Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ cbtV h) (hL : Legal (cbtPred h) (cbtFree h) l ∅)
    (hP : Peak q l ∅) (hrun : run l ∅ = Y) : T + 1 ≤ l.length :=
  length_ge_of_quot_levels_cbt h q T (autB_group h) hcanon0 hqcl hY l hS hL hP hrun

/-- 同じものを `Dcert` の下界として。 -/
theorem Dcert_ge_of_quot_levels_cbt_aut {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h q T Bd : ℕ)
    (hcanon0 : Lq 0 (canonCbt h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbt h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbt h Y))
    (hB : T + 1 ≤ Bd) :
    T + 1 ≤ Dcert (cbtPred h) (cbtFree h) Bd q (cbtV h) ∅ Y :=
  Dcert_ge_of_quot_levels_cbt h q T Bd (autB_group h) hcanon0 hqcl hY hB

#print axioms bitFns_support
#print axioms bitFns_mem
#print axioms invAct_depth
#print axioms autB_group
#print axioms hstep_cbt
#print axioms length_ge_of_quot_levels_cbt_aut
#print axioms Dcert_ge_of_quot_levels_cbt_aut
#print axioms swapAct_lt_two_pow
#print axioms swapAct_mem_cbtV
#print axioms swapAct_mem_cbtFree
#print axioms image_cbtPred
#print axioms hstep_cbt_of_group
#print axioms length_ge_of_quot_levels_cbt
#print axioms Dcert_ge_of_quot_levels_cbt
#print axioms trivB_group

end SplitLemma
