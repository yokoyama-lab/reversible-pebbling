/-
# 消去ペブリング: 解体順序 DP と補題 A♮

`data/conj_g_proof_attempt.md` §2.3・§4・§6 の機械証明。
ペブリングのモデルは**必要としない**（`List ℕ` 上の有限組合せ論だけで閉じる）。

  cst g q : 自由ペブル q 本でギャップ g を跳ぶ最小消去数（ℕ∞）
  cost p D : 解体順序 D（先頭が最初に取り除かれる）の総費用
-/
import Revgarbage.PebbleArith

namespace PebbleDP

open PebbleArith

/-- 足場からギャップ `g` を自由ペブル `q` 本で跳ぶ最小消去数。
`q = 0` は不可能、`q = 1` は `g = 1` のみ、`q ≥ 2` は `psi g 2^(q-2)`。 -/
def cst (g q : ℕ) : ℕ∞ :=
  match q with
  | 0 => ⊤
  | 1 => if g = 1 then 0 else ⊤
  | (n + 2) => (psi g (2 ^ n) : ℕ)

@[simp] lemma cst_zero (g : ℕ) : cst g 0 = ⊤ := rfl
@[simp] lemma cst_one (g : ℕ) : cst g 1 = if g = 1 then 0 else ⊤ := rfl
lemma cst_succ_succ (g n : ℕ) : cst g (n + 2) = ((psi g (2 ^ n) : ℕ) : ℕ∞) := rfl

/-- 自由ペブルが 1 本増えれば費用は増えない。 -/
lemma cst_mono_q (g q : ℕ) : cst g (q + 1) ≤ cst g q := by
  match q with
  | 0 => simp
  | 1 =>
    simp only [cst_one, cst_succ_succ, pow_zero]
    split
    · next h => subst h; norm_num [psi, Nat.ceilDiv_eq_add_pred_div]
    · exact le_top
  | (n + 2) =>
    simp only [cst_succ_succ]
    exact_mod_cast psi_mono_m g (2 ^ n) (2 ^ (n + 1)) (by positivity)
      (by simpa using Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))

/-- ギャップについて単調（`0 < a` が要る: `q=1` の縮退のため）。 -/
lemma cst_mono_g {a b q : ℕ} (ha : 0 < a) (h : a ≤ b) : cst a q ≤ cst b q := by
  match q with
  | 0 => simp
  | 1 =>
    simp only [cst_one]
    split
    · next h1 =>
      subst h1
      split
      · exact le_rfl
      · exact le_top
    · next h1 =>
      have : b ≠ 1 := by omega
      simp [this]
  | (n + 2) =>
    simp only [cst_succ_succ]
    exact_mod_cast psi_mono_g (2 ^ n) (by positivity) h

/-- **補題 S の持ち上げ**（補題 A♮ の (★) の実体）。 -/
lemma cst_S (a b q : ℕ) (ha : 0 < a) (hb : 0 < b) :
    cst (a + b) (q + 1) + cst b (q + 1) ≤ cst a q + cst b q := by
  match q with
  | 0 => simp
  | 1 =>
    by_cases hb1 : b = 1
    · by_cases ha1 : a = 1
      · subst ha1; subst hb1
        norm_num [cst_succ_succ, psi, Nat.ceilDiv_eq_add_pred_div]
      · simp [cst_one, ha1]
    · simp [cst_one, hb1]
  | (n + 2) =>
    simp only [cst_succ_succ, ← Nat.cast_add, Nat.cast_le, pow_succ]
    have := psi_S a b (2 ^ n) ha hb (by positivity)
    calc psi (a + b) (2 ^ n * 2) + psi b (2 ^ n * 2)
        = psi (a + b) (2 * 2 ^ n) + psi b (2 * 2 ^ n) := by ring_nf
      _ ≤ psi a (2 ^ n) + psi b (2 ^ n) := this

/-- **補題 S2 の持ち上げ**（補題 B♮ の実体）。 -/
lemma cst_S2 (a b q : ℕ) (ha : 0 < a) (hb : 0 < b) :
    cst (a + b) (q + 1) ≤ cst a (q + 1) + cst b q + 1 := by
  match q with
  | 0 => simp
  | 1 =>
    by_cases hb1 : b = 1
    · subst hb1
      have h1 : cst 1 1 = (0 : ℕ∞) := by simp
      rw [h1, add_zero]
      simp only [cst_succ_succ, pow_zero]
      have h2 : psi (a + 1) 1 ≤ psi a 1 + 1 := by
        simp only [psi, Nat.ceilDiv_eq_add_pred_div]
        omega
      exact_mod_cast h2
    · simp [cst_one, hb1]
  | (n + 2) =>
    simp only [cst_succ_succ, pow_succ]
    have := psi_S2 a b (2 ^ n) ha hb (by positivity)
    have h2 : psi (a + b) (2 ^ n * 2) ≤ psi a (2 ^ n * 2) + psi b (2 ^ n) + 1 := by
      calc psi (a + b) (2 ^ n * 2) = psi (a + b) (2 * 2 ^ n) := by ring_nf
        _ ≤ psi a (2 * 2 ^ n) + psi b (2 ^ n) + 1 := this
        _ = psi a (2 ^ n * 2) + psi b (2 ^ n) + 1 := by ring_nf
    exact_mod_cast h2

/-! ### `pred`: 現在の集合の中で `y` の直下にある要素 -/

lemma le_foldr_max {l : List ℕ} {w : ℕ} (h : w ∈ l) : w ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma foldr_max_zero_or_mem (l : List ℕ) : l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => left; rfl
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases le_total a (t.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem _ hm)
    · rw [max_eq_left h]
      exact Or.inr (List.mem_cons_self ..)

/-- `L` の要素のうち `y` 未満の最大値（無ければ 0）。 -/
def pred (L : List ℕ) (y : ℕ) : ℕ := (L.filter (fun w => decide (w < y))).foldr max 0

lemma pred_le {L : List ℕ} {y w : ℕ} (hw : w ∈ L) (hlt : w < y) : w ≤ pred L y :=
  le_foldr_max (List.mem_filter.2 ⟨hw, by simpa using hlt⟩)

lemma pred_zero_or (L : List ℕ) (y : ℕ) : pred L y = 0 ∨ (pred L y ∈ L ∧ pred L y < y) := by
  unfold pred
  rcases foldr_max_zero_or_mem (L.filter (fun w => decide (w < y))) with h | h
  · exact Or.inl h
  · have h2 := List.mem_filter.1 h
    exact Or.inr ⟨h2.1, by simpa using h2.2⟩

lemma pred_lt {L : List ℕ} {y : ℕ} (hy : 0 < y) : pred L y < y := by
  rcases pred_zero_or L y with h | h
  · rw [h]; exact hy
  · exact h.2

/-- 同じ集合の上ではフィルタが一致すれば `pred` も一致する。 -/
lemma pred_congr {L : List ℕ} {y z : ℕ}
    (h : ∀ w ∈ L, (w < y) ↔ (w < z)) : pred L y = pred L z := by
  unfold pred
  congr 1
  refine List.filter_congr ?_
  intro w hw
  simp only [decide_eq_decide]
  exact h w hw

/-- **L2**: `pred L y ≠ x` なら `x` を除いても `pred` は変わらない。 -/
lemma pred_erase_of_ne {L : List ℕ} {y x : ℕ} (h : pred L y ≠ x) :
    pred (L.erase x) y = pred L y := by
  refine le_antisymm ?_ ?_
  · rcases pred_zero_or (L.erase x) y with h0 | h1
    · simp [h0]
    · exact pred_le (List.mem_of_mem_erase h1.1) h1.2
  · rcases pred_zero_or L y with h0 | h1
    · simp [h0]
    · exact pred_le ((List.mem_erase_of_ne (by simpa using h)).2 h1.1) h1.2

/-- **L3**: `pred L y = x` なら、`x` を除いた後の `y` の pred は `x` の pred に等しい。 -/
lemma pred_erase_of_eq {L : List ℕ} {y x : ℕ} (hL : L.Nodup) (hx : 0 < x) (h : pred L y = x) :
    pred (L.erase x) y = pred (L.erase x) x := by
  have hxy : x < y := by
    rcases pred_zero_or L y with h0 | h1
    · rw [h0] at h; omega
    · rw [h] at h1; exact h1.2
  refine pred_congr ?_
  intro w hw
  obtain ⟨hwx, hwL⟩ := (List.Nodup.mem_erase_iff hL).1 hw
  constructor
  · intro hy
    have : w ≤ x := h ▸ pred_le hwL hy
    omega
  · intro hlt
    omega

lemma pred_cons_of_not_lt {M : List ℕ} {y x : ℕ} (h : ¬ y < x) :
    pred (y :: M) x = pred M x := by
  unfold pred
  rw [List.filter_cons]
  simp [h]

lemma pred_cons_of_lt {M : List ℕ} {y x : ℕ} (h : y < x) :
    pred (y :: M) x = max y (pred M x) := by
  unfold pred
  rw [List.filter_cons]
  simp [h]

/-! ### 解体順序の費用 -/

/-- 解体順序 `D`（先頭が最初に取り除かれる）の総費用。
残りが `j` 個のとき自由ペブルは `p - j + 1` 本。 -/
def cost (p : ℕ) : List ℕ → ℕ∞
  | [] => 0
  | y :: L => cst (y - pred L y) (p - L.length) + cost p L

@[simp] lemma cost_nil (p : ℕ) : cost p [] = 0 := rfl
lemma cost_cons (p y : ℕ) (L : List ℕ) :
    cost p (y :: L) = cst (y - pred L y) (p - L.length) + cost p L := rfl


/-- ギャップ 1 は無料（自由ペブルが 1 本以上あれば）。 -/
lemma cst_gap_one {q : ℕ} (hq : 0 < q) : cst 1 q = 0 := by
  match q with
  | 0 => omega
  | 1 => simp
  | (n + 2) => simp [cst_succ_succ, psi, Nat.ceilDiv_eq_add_pred_div]

lemma star_mono (a b q : ℕ) : cst a (q + 1) + cst b (q + 1) ≤ cst a q + cst b q :=
  add_le_add (cst_mono_q a q) (cst_mono_q b q)

/-- **補題 A♮**（`data/conj_g_proof_attempt.md` §4）。 -/
theorem Anat (p : ℕ) : ∀ (D : List ℕ), D.Nodup → (∀ w ∈ D, 0 < w) → ∀ x, x ∈ D →
    cost p (D.erase x) ≤ cost p D + cst (x - pred (D.erase x) x) (p + 1 - D.length) := by
  intro D
  induction D with
  | nil => intro _ _ x hx; cases hx
  | cons y L ih =>
    intro hnd hpos x hx
    by_cases hyx : y = x
    · subst hyx
      rw [List.erase_cons_head, cost_cons]
      calc cost p L ≤ cst (y - pred L y) (p - L.length) + cost p L := le_add_self
        _ ≤ _ := le_self_add
    · have hxL : x ∈ L := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      have hndL : L.Nodup := hnd.of_cons
      have hposL : ∀ w ∈ L, 0 < w := fun w hw => hpos w (List.mem_cons_of_mem _ hw)
      have hx0 : 0 < x := hpos x hx
      have hy0 : 0 < y := hpos y (List.mem_cons_self ..)
      have herase : (y :: L).erase x = y :: L.erase x :=
        List.erase_cons_tail (by simpa using hyx)
      have hlen : (L.erase x).length = L.length - 1 := List.length_erase_of_mem hxL
      have hLpos : 0 < L.length := List.length_pos_of_mem hxL
      have hIH := ih hndL hposL x hxL
      rw [herase, cost_cons, cost_cons, hlen]
      simp only [List.length_cons]
      -- L.length ≥ p なら右辺に ⊤ が出るので自明
      rcases Nat.lt_or_ge L.length p with hlt | hge
      swap
      · have : p - L.length = 0 := by omega
        rw [this]
        simp
      -- 以下 L.length < p。レベルを q, q+1 に正規化する
      set q := p - L.length with hqdef
      have e1 : p - (L.length - 1) = q + 1 := by omega
      have e2 : p + 1 - L.length = q + 1 := by omega
      have e3 : p + 1 - (L.length + 1) = q := by omega
      rw [e1, e3] at *
      rw [e2] at hIH
      -- 記号
      set γ := y - pred L y with hγ
      set γs := y - pred (L.erase x) y with hγs
      set δ := x - pred (y :: L.erase x) x with hδ
      set δ' := x - pred (L.erase x) x with hδ'
      have hpredx : pred (L.erase x) x < x := pred_lt hx0
      have hδ'pos : 0 < δ' := by omega
      -- (★)
      have star : cst γs (q + 1) + cst δ' (q + 1) ≤ cst γ q + cst δ q := by
        rcases Nat.lt_or_ge x y with hxy | hyx'
        · -- y > x
          have hδeq : δ = δ' := by
            rw [hδ, hδ', pred_cons_of_not_lt (by omega)]
          by_cases hpy : pred L y = x
          · -- 場合 (b2)
            have h1 : pred (L.erase x) y = pred (L.erase x) x :=
              pred_erase_of_eq hndL hx0 hpy
            have hγv : γ = y - x := by rw [hγ, hpy]
            have hγspos : γs = γ + δ' := by
              rw [hγs, h1, hγv, hδ']; omega
            rw [hγspos, hδeq]
            exact cst_S γ δ' q (by omega) hδ'pos
          · -- 場合 (b1)
            have h1 : pred (L.erase x) y = pred L y := pred_erase_of_ne hpy
            have : γs = γ := by rw [hγs, h1, hγ]
            rw [this, hδeq]
            exact star_mono γ δ' q
        · -- y < x
          have hyxlt : y < x := by omega
          have hpy : pred L y ≠ x := by
            have := pred_lt (L := L) (y := y) hy0
            omega
          have hγeq : γs = γ := by
            rw [hγs, pred_erase_of_ne hpy, hγ]
          have hcons : pred (y :: L.erase x) x = max y (pred (L.erase x) x) :=
            pred_cons_of_lt hyxlt
          rcases Nat.lt_or_ge (pred (L.erase x) x) y with hlt2 | hge2
          · -- 場合 (b4): y が x の直下
            have hmax : pred (y :: L.erase x) x = y := by
              rw [hcons]; omega
            have hδv : δ = x - y := by rw [hδ, hmax]
            -- pred L x = pred L y
            have hpx : pred (L.erase x) x = pred L x := pred_erase_of_ne (by
              have := pred_lt (L := L) (y := x) hx0
              omega)
            have hkey : pred L x = pred L y := by
              refine pred_congr ?_
              intro w hw
              constructor
              · intro hwx
                have : w ≤ pred L x := pred_le hw hwx
                omega
              · intro hwy; omega
            have hδ'v : δ' = δ + γ := by
              rw [hδ', hpx, hkey, hδv, hγ]
              have := pred_lt (L := L) (y := y) hy0
              omega
            rw [hγeq, hδ'v]
            have hγpos : 0 < γ := by
              have := pred_lt (L := L) (y := y) hy0
              omega
            have := cst_S δ γ q (by omega) hγpos
            calc cst γ (q + 1) + cst (δ + γ) (q + 1)
                = cst (δ + γ) (q + 1) + cst γ (q + 1) := by ring
              _ ≤ cst δ q + cst γ q := this
              _ = cst γ q + cst δ q := by ring
          · -- 場合 (b3)
            have hmax : pred (y :: L.erase x) x = pred (L.erase x) x := by
              rw [hcons]; omega
            have hδeq : δ = δ' := by rw [hδ, hmax, hδ']
            rw [hγeq, hδeq]
            exact star_mono γ δ' q
      -- 組み立て
      calc cst γs (q + 1) + cost p (L.erase x)
          ≤ cst γs (q + 1) + (cost p L + cst δ' (q + 1)) := add_le_add le_rfl hIH
        _ = (cst γs (q + 1) + cst δ' (q + 1)) + cost p L := by ring
        _ ≤ (cst γ q + cst δ q) + cost p L := add_le_add star le_rfl
        _ = cst γ q + cost p L + cst δ q := by ring

/-- **補題 A（スケジュール単位）**: `x` の直下が埋まっている（`pred = x-1`）なら、
`x` の段を落としても費用は増えない。`|D| ≤ p` が必要。 -/
theorem cost_erase_le_of_supported (p : ℕ) (D : List ℕ) (hnd : D.Nodup)
    (hpos : ∀ w ∈ D, 0 < w) (x : ℕ) (hx : x ∈ D) (hlen : D.length ≤ p)
    (hsup : x - pred (D.erase x) x = 1) :
    cost p (D.erase x) ≤ cost p D := by
  have h := Anat p D hnd hpos x hx
  rw [hsup, cst_gap_one (by omega)] at h
  simpa using h


/-! ### `List.replace` の基本 -/

lemma length_replace (l : List ℕ) (x y : ℕ) : (l.replace x y).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.replace_cons]
    cases h : (x == a) with
    | true => simp
    | false => simp [ih]

lemma mem_replace_of_mem_of_ne {l : List ℕ} {z x y : ℕ} (hz : z ∈ l) (hne : z ≠ x) :
    z ∈ l.replace x y := by
  induction l with
  | nil => cases hz
  | cons a t ih =>
    rw [List.replace_cons]
    cases h : (x == a) with
    | true =>
      have hax : a = x := by simpa using (beq_iff_eq).1 h |>.symm
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact absurd hax hne
      · exact List.mem_cons_of_mem _ hz'
    | false =>
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hz')

lemma mem_replace_self {l : List ℕ} {x y : ℕ} (hx : x ∈ l) : y ∈ l.replace x y := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.replace_cons]
    cases h : (x == a) with
    | true => simp
    | false =>
      have hax : x ≠ a := by simpa using h
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd rfl hax
      · exact List.mem_cons_of_mem _ (ih hx')

lemma replace_cons_head (t : List ℕ) (x y : ℕ) : (x :: t).replace x y = y :: t := by
  rw [List.replace_cons]; simp

lemma replace_cons_tail {t : List ℕ} {a x y : ℕ} (h : x ≠ a) :
    (a :: t).replace x y = a :: t.replace x y := by
  have hb : (x == a) = false := by simpa using h
  rw [List.replace_cons, hb]

/-! ### `pred` は replace で下がらない -/

lemma pred_replace_ge {t : List ℕ} {x y w : ℕ} (hx : x ∈ t) (hxy : x < y)
    (hw : ¬ (x < w ∧ w < y)) (hwy : w ≠ y) :
    pred t w ≤ pred (t.replace x y) w := by
  rcases pred_zero_or t w with h0 | ⟨hmem, hlt⟩
  · rw [h0]; exact Nat.zero_le _
  · by_cases hzx : pred t w = x
    · have hxw : x < w := by rw [← hzx]; exact hlt
      have hyw : y < w := by
        rcases Nat.lt_or_ge w y with h | h
        · exact absurd ⟨hxw, h⟩ hw
        · omega
      have : y ≤ pred (t.replace x y) w := pred_le (mem_replace_self hx) hyw
      omega
    · exact pred_le (mem_replace_of_mem_of_ne hmem hzx) hlt

/-- `L` の `x` を `y` に置き換えた列は `y :: (L∖x)` の並べ替え。 -/
lemma replace_perm {L : List ℕ} {x y : ℕ} (hx : x ∈ L) :
    (L.replace x y).Perm (y :: L.erase x) := by
  induction L with
  | nil => cases hx
  | cons a t ih =>
    by_cases hax : x = a
    · subst hax
      rw [replace_cons_head, List.erase_cons_head]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h hax
        · exact h
      rw [replace_cons_tail hax, List.erase_cons_tail (by simpa using Ne.symm hax)]
      exact ((ih hxt).cons a).trans (List.Perm.swap _ _ _)

/-! ### 補題 B♮ の中核: x を y に置き換える -/

lemma cost_replace (p : ℕ) : ∀ (L : List ℕ), L.Nodup → (∀ w ∈ L, 0 < w) →
    ∀ x y : ℕ, x ∈ L → y ∉ L → x < y →
    (∀ w ∈ L, ¬ (x < w ∧ w < y)) → 0 < x →
    cost p (L.replace x y) ≤ cost p L + cst (y - x) (p - L.length) + 1 := by
  intro L
  induction L with
  | nil => intro _ _ x y hx; cases hx
  | cons a t ih =>
    intro hnd hpos x y hx hy hxy hgap hx0
    have hndt : t.Nodup := hnd.of_cons
    have hpost : ∀ w ∈ t, 0 < w := fun w hw => hpos w (List.mem_cons_of_mem _ hw)
    have ha0 : 0 < a := hpos a (List.mem_cons_self ..)
    have hat : a ∉ t := (List.nodup_cons.1 hnd).1
    by_cases hax : x = a
    · -- x が先頭
      subst hax
      rw [replace_cons_head, cost_cons, cost_cons, List.length_cons]
      set M := p - t.length with hM
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · rw [hM0]; simp
      -- pred t y = pred t x
      have hpe : pred t y = pred t x := by
        refine pred_congr ?_
        intro w hw
        have hwmem : w ∈ x :: t := List.mem_cons_of_mem _ hw
        have hng := hgap w hwmem
        have hwx : w ≠ x := by rintro rfl; exact hat hw
        constructor
        · intro h; omega
        · intro h; omega
      have hpx : pred t x < x := pred_lt hx0
      have hsplit : y - pred t x = (x - pred t x) + (y - x) := by omega
      obtain ⟨q, hq⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
      have hlev : p - (t.length + 1) = q := by omega
      rw [hpe, hsplit, hq, hlev]
      have hS2 := cst_S2 (x - pred t x) (y - x) q (by omega) (by omega)
      calc cst (x - pred t x + (y - x)) (q + 1) + cost p t
          ≤ (cst (x - pred t x) (q + 1) + cst (y - x) q + 1) + cost p t :=
            add_le_add hS2 le_rfl
        _ = cst (x - pred t x) (q + 1) + cost p t + cst (y - x) q + 1 := by ring
    · -- x は先頭でない
      have hxt : x ∈ t := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h hax
        · exact h
      have hyt : y ∉ t := fun h => hy (List.mem_cons_of_mem _ h)
      have hgapt : ∀ w ∈ t, ¬ (x < w ∧ w < y) := fun w hw => hgap w (List.mem_cons_of_mem _ hw)
      have hIH := ih hndt hpost x y hxt hyt hxy hgapt hx0
      rw [replace_cons_tail hax, cost_cons, cost_cons,
        length_replace, List.length_cons]
      set M := p - t.length with hM
      have hay : a ≠ y := by rintro rfl; exact hy (List.mem_cons_self ..)
      have hmono : pred t a ≤ pred (t.replace x y) a :=
        pred_replace_ge hxt hxy (hgap a (List.mem_cons_self ..)) hay
      have hpa : pred (t.replace x y) a < a := pred_lt ha0
      have hhead : cst (a - pred (t.replace x y) a) M ≤ cst (a - pred t a) M :=
        cst_mono_g (by omega) (by omega)
      have hlev : cst (y - x) M ≤ cst (y - x) (p - (t.length + 1)) := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · have : p - (t.length + 1) = 0 := by omega
          rw [hM0, this]
        · obtain ⟨q, hq⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
          have : p - (t.length + 1) = q := by omega
          rw [hq, this]
          exact cst_mono_q _ _
      calc cst (a - pred (t.replace x y) a) M + cost p (t.replace x y)
          ≤ cst (a - pred (t.replace x y) a) M + (cost p t + cst (y - x) M + 1) :=
            add_le_add le_rfl hIH
        _ = (cst (a - pred (t.replace x y) a) M + cst (y - x) M) + cost p t + 1 := by ring
        _ ≤ (cst (a - pred t a) M + cst (y - x) (p - (t.length + 1))) + cost p t + 1 :=
            add_le_add (add_le_add (add_le_add hhead hlev) le_rfl) le_rfl
        _ = cst (a - pred t a) M + cost p t + cst (y - x) (p - (t.length + 1)) + 1 := by ring

/-- `pred` は集合だけで決まる（並べ替えで不変）。 -/
lemma pred_perm {L L' : List ℕ} (h : L.Perm L') (y : ℕ) : pred L y = pred L' y := by
  unfold pred
  have : LeftCommutative (max : ℕ → ℕ → ℕ) := ⟨fun a b c => max_left_comm a b c⟩
  exact List.Perm.foldr_eq (h.filter _) 0

/-- **補題 B♮**（`data/conj_g_proof_attempt.md` §6）。
どんな解体順序 `D` からでも、`x` を除いた集合の解体順序 `E` が取れて費用は高々 `+1`。 -/
theorem Bnat (p : ℕ) : ∀ (D : List ℕ), D.Nodup → (∀ w ∈ D, 0 < w) → ∀ x, x ∈ D →
    ∃ E : List ℕ, E.Perm (D.erase x) ∧ cost p E ≤ cost p D + 1 := by
  intro D
  induction D with
  | nil => intro _ _ x hx; cases hx
  | cons y L ih =>
    intro hnd hpos x hx
    have hndL : L.Nodup := hnd.of_cons
    have hposL : ∀ w ∈ L, 0 < w := fun w hw => hpos w (List.mem_cons_of_mem _ hw)
    have hyL : y ∉ L := (List.nodup_cons.1 hnd).1
    have hy0 : 0 < y := hpos y (List.mem_cons_self ..)
    by_cases hyx : y = x
    · -- (a) 先頭が x
      subst hyx
      refine ⟨L, by rw [List.erase_cons_head], ?_⟩
      rw [cost_cons]
      calc cost p L ≤ cst (y - pred L y) (p - L.length) + cost p L := le_add_self
        _ ≤ _ := le_self_add
    · have hxL : x ∈ L := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      have hx0 : 0 < x := hpos x hx
      have herase : (y :: L).erase x = y :: L.erase x :=
        List.erase_cons_tail (by simpa using hyx)
      have hlen : (L.erase x).length = L.length - 1 := List.length_erase_of_mem hxL
      have hLpos : 0 < L.length := List.length_pos_of_mem hxL
      by_cases hIII : x < y ∧ pred L y = x
      · -- (III) y が x の直上で、しかも最初に消される
        obtain ⟨hxy, hpy⟩ := hIII
        have hgap : ∀ w ∈ L, ¬ (x < w ∧ w < y) := by
          intro w hw ⟨h1, h2⟩
          have : w ≤ pred L y := pred_le hw h2
          omega
        refine ⟨L.replace x y, ?_, ?_⟩
        · rw [herase]
          exact replace_perm hxL
        · have h := cost_replace p L hndL hposL x y hxL hyL hxy hgap hx0
          rw [cost_cons, hpy]
          calc cost p (L.replace x y) ≤ cost p L + cst (y - x) (p - L.length) + 1 := h
            _ = cst (y - x) (p - L.length) + cost p L + 1 := by ring
      · -- (I)(II) 相当: 先頭 y を残して再帰
        have hpy : pred L y ≠ x := by
          rcases Nat.lt_or_ge y x with h | h
          · have := pred_lt (L := L) (y := y) hy0
            omega
          · have hyx' : x < y := by
              rcases Nat.lt_or_eq_of_le h with h' | h'
              · exact h'
              · exact absurd h'.symm hyx
            intro hc
            exact hIII ⟨hyx', hc⟩
        obtain ⟨E, hEperm, hEcost⟩ := ih hndL hposL x hxL
        refine ⟨y :: E, ?_, ?_⟩
        · rw [herase]; exact hEperm.cons y
        · rw [cost_cons, cost_cons]
          have hlenE : E.length = L.length - 1 := by
            rw [hEperm.length_eq, hlen]
          have hpE : pred E y = pred L y := by
            rw [pred_perm hEperm, pred_erase_of_ne hpy]
          rw [hlenE, hpE]
          have hmono : cst (y - pred L y) (p - (L.length - 1))
              ≤ cst (y - pred L y) (p - L.length) := by
            rcases Nat.lt_or_ge L.length p with h | h
            · have e1 : p - (L.length - 1) = (p - L.length) + 1 := by omega
              rw [e1]
              exact cst_mono_q _ _
            · have : p - L.length = 0 := by omega
              rw [this]
              exact le_top
          calc cst (y - pred L y) (p - (L.length - 1)) + cost p E
              ≤ cst (y - pred L y) (p - L.length) + (cost p L + 1) :=
                add_le_add hmono hEcost
            _ = cst (y - pred L y) (p - L.length) + cost p L + 1 := by ring

end PebbleDP
