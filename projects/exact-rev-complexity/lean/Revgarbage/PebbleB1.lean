/-
# 定理 B1（構成側）と定理 B2（等号）

`data/conj_g_proof_attempt.md` §7.1・§12.6 の機械証明。
`Revgarbage.PebbleModel`（上界側）の上に、区間に閉じた相対到達 `StepsIn`、
フレーム補題、Bennett の再帰、消去前進を置き、**定理 B2 の等号**を得る。
-/
import Revgarbage.PebbleModel

namespace PebbleDP

open Finset


/-! ### 区間に閉じた相対到達 -/

/-- 足場 `a`（`a = 0` なら源）から、区間 `(a, b]` の中だけを使って
配置 `S` から `T` へ、ピーク `p`・消去 `u` 回で移る。 -/
inductive StepsIn (p a b : ℕ) : Finset ℕ → Finset ℕ → ℕ → Prop
  | refl (S) : StepsIn p a b S S 0
  | put {S T u v} : StepsIn p a b S T u → a < v → v ≤ b → v ∉ T →
      (v = a + 1 ∨ v - 1 ∈ T) → T.card < p → StepsIn p a b S (insert v T) u
  | take {S T u v} : StepsIn p a b S T u → a < v → v ≤ b → v ∈ T →
      (v = a + 1 ∨ v - 1 ∈ T) → StepsIn p a b S (T.erase v) u
  | erase {S T u v} : StepsIn p a b S T u → a < v → v ≤ b → v ∈ T →
      ¬(v = a + 1 ∨ v - 1 ∈ T) → StepsIn p a b S (T.erase v) (u + 1)

lemma StepsIn.card_le {p a b S T u} (h : StepsIn p a b S T u) (hS : S.card ≤ p) :
    T.card ≤ p := by
  induction h with
  | refl => exact hS
  | put _ _ _ hv _ hc ih => rw [Finset.card_insert_of_notMem hv]; omega
  | take _ _ _ _ _ ih => exact le_trans Finset.card_erase_le ih
  | erase _ _ _ _ _ ih => exact le_trans Finset.card_erase_le ih

lemma StepsIn.mem_range {p a b S T u} (h : StepsIn p a b S T u)
    (hS : ∀ w ∈ S, a < w ∧ w ≤ b) : ∀ w ∈ T, a < w ∧ w ≤ b := by
  induction h with
  | refl => exact hS
  | put _ hlo hhi _ _ _ ih =>
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hlo, hhi⟩
    · exact ih w hw
  | take _ _ _ _ _ ih => intro w hw; exact ih w (Finset.mem_of_mem_erase hw)
  | erase _ _ _ _ _ ih => intro w hw; exact ih w (Finset.mem_of_mem_erase hw)

lemma StepsIn.trans {p a b S T U u u'} (h : StepsIn p a b S T u)
    (h' : StepsIn p a b T U u') : StepsIn p a b S U (u + u') := by
  induction h' with
  | refl => simpa using h
  | put _ h1 h2 h3 h4 h5 ih => exact StepsIn.put ih h1 h2 h3 h4 h5
  | take _ h1 h2 h3 h4 ih => exact StepsIn.take ih h1 h2 h3 h4
  | @erase T' u'' v _ h1 h2 h3 h4 ih =>
    have := StepsIn.erase ih h1 h2 h3 h4
    simpa [Nat.add_assoc] using this

lemma StepsIn.mono_p {p p' a b S T u} (h : StepsIn p a b S T u) (hp : p ≤ p') :
    StepsIn p' a b S T u := by
  induction h with
  | refl => exact StepsIn.refl _
  | put _ h1 h2 h3 h4 h5 ih => exact StepsIn.put ih h1 h2 h3 h4 (by omega)
  | take _ h1 h2 h3 h4 ih => exact StepsIn.take ih h1 h2 h3 h4
  | erase _ h1 h2 h3 h4 ih => exact StepsIn.erase ih h1 h2 h3 h4

lemma StepsIn.mono_b {p a b b' S T u} (h : StepsIn p a b S T u) (hb : b ≤ b') :
    StepsIn p a b' S T u := by
  induction h with
  | refl => exact StepsIn.refl _
  | put _ h1 h2 h3 h4 h5 ih => exact StepsIn.put ih h1 (by omega) h3 h4 h5
  | take _ h1 h2 h3 h4 ih => exact StepsIn.take ih h1 (by omega) h3 h4
  | erase _ h1 h2 h3 h4 ih => exact StepsIn.erase ih h1 (by omega) h3 h4

/-- 消去を使わない走行は逆再生できる。 -/
lemma StepsIn.reverse {p a b S T u} (h : StepsIn p a b S T u) (hu : u = 0) (hS : S.card ≤ p) :
    StepsIn p a b T S 0 := by
  induction h with
  | refl => exact StepsIn.refl _
  | @put T u v hst h1 h2 h3 h4 h5 ih =>
    have hback : StepsIn p a b (insert v T) T 0 := by
      have hsup : v = a + 1 ∨ v - 1 ∈ insert v T := by
        rcases h4 with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
      have := StepsIn.take (StepsIn.refl (p := p) (a := a) (b := b) (insert v T)) h1 h2
        (Finset.mem_insert_self v T) hsup
      rwa [Finset.erase_insert h3] at this
    simpa using hback.trans (ih hu)
  | @take T u v hst h1 h2 h3 h4 ih =>
    have hcard : (T.erase v).card < p := by
      have hc1 := hst.card_le hS
      have hc2 := Finset.card_erase_of_mem h3
      have hc3 : 0 < T.card := Finset.card_pos.2 ⟨v, h3⟩
      omega
    have hback : StepsIn p a b (T.erase v) T 0 := by
      have hsup : v = a + 1 ∨ v - 1 ∈ T.erase v := by
        rcases h4 with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_erase.2 ⟨by omega, h⟩)
      have := StepsIn.put (StepsIn.refl (p := p) (a := a) (b := b) (T.erase v)) h1 h2
        (by simp) hsup hcard
      rwa [Finset.insert_erase h3] at this
    simpa using hback.trans (ih hu)
  | erase _ _ _ _ _ _ => omega


/-- **フレーム補題**: 区間 `(a,b]` に閉じた走行は、その外側にある静止配置 `B` を
そのまま保ったまま、より広い区間 `(a',b']` の走行として実行できる。ピークは `B.card` 増える。
`B` が足場 `a` を含む（または `a = a'`）ことが、下端での支持の条件になる。 -/
lemma StepsIn.frame {p a b a' b' : ℕ} {S T : Finset ℕ} {u : ℕ}
    (h : StepsIn p a b S T u) (B : Finset ℕ)
    (hS : ∀ w ∈ S, a < w ∧ w ≤ b)
    (hBdisj : ∀ w ∈ B, w ≤ a ∨ b < w)
    (hbot : a = a' ∨ a ∈ B) (ha' : a' ≤ a) (hb' : b ≤ b') :
    StepsIn (p + B.card) a' b' (S ∪ B) (T ∪ B) u := by
  induction h with
  | refl => exact StepsIn.refl _
  | @put T u v hst h1 h2 h3 h4 h5 ih =>
    have hrange := hst.mem_range hS
    have hvB : v ∉ B := by
      intro hc; rcases hBdisj v hc with h | h <;> omega
    have hdisj : Disjoint T B := by
      rw [Finset.disjoint_left]
      intro w hw hwB
      rcases hBdisj w hwB with h | h
      · exact absurd (hrange w hw).1 (by omega)
      · exact absurd (hrange w hw).2 (by omega)
    have hcard : (T ∪ B).card < p + B.card := by
      rw [Finset.card_union_of_disjoint hdisj]; omega
    have hsup : v = a' + 1 ∨ v - 1 ∈ T ∪ B := by
      rcases h4 with h | h
      · rcases hbot with rfl | hmem
        · exact Or.inl h
        · exact Or.inr (Finset.mem_union_right _ (by rw [h]; simpa using hmem))
      · exact Or.inr (Finset.mem_union_left _ h)
    have := StepsIn.put ih (by omega) (by omega)
      (by simp [h3, hvB]) hsup hcard
    rw [Finset.insert_union]
    exact this
  | @take T u v hst h1 h2 h3 h4 ih =>
    have hvB : v ∉ B := by
      intro hc; rcases hBdisj v hc with h | h <;> omega
    have hsup : v = a' + 1 ∨ v - 1 ∈ T ∪ B := by
      rcases h4 with h | h
      · rcases hbot with rfl | hmem
        · exact Or.inl h
        · exact Or.inr (Finset.mem_union_right _ (by rw [h]; simpa using hmem))
      · exact Or.inr (Finset.mem_union_left _ h)
    have heq : (T ∪ B).erase v = (T.erase v) ∪ B := by
      ext w
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hw⟩
        rcases hw with hw | hw
        · exact Or.inl ⟨hne, hw⟩
        · exact Or.inr hw
      · rintro (⟨hne, hw⟩ | hw)
        · exact ⟨hne, Or.inl hw⟩
        · exact ⟨by rintro rfl; exact hvB hw, Or.inr hw⟩
    have := StepsIn.take ih (by omega) (by omega)
      (Finset.mem_union_left _ h3) hsup
    rwa [heq] at this
  | @erase T u v hst h1 h2 h3 h4 ih =>
    have hvB : v ∉ B := by
      intro hc; rcases hBdisj v hc with h | h <;> omega
    have hv1 : v ≠ a + 1 := fun hc => h4 (Or.inl hc)
    have hvT : v - 1 ∉ T := fun hc => h4 (Or.inr hc)
    have hv1B : v - 1 ∉ B := by
      intro hc
      rcases hBdisj (v - 1) hc with h | h <;> omega
    have hsup : ¬(v = a' + 1 ∨ v - 1 ∈ T ∪ B) := by
      rintro (hc | hc)
      · have : a = a' := by
          rcases hbot with h | hmem
          · exact h
          · rcases hBdisj a hmem with h | h
            · omega
            · omega
        omega
      · rcases Finset.mem_union.1 hc with h | h
        · exact hvT h
        · exact hv1B h
    have heq : (T ∪ B).erase v = (T.erase v) ∪ B := by
      ext w
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hne, hw⟩
        rcases hw with hw | hw
        · exact Or.inl ⟨hne, hw⟩
        · exact Or.inr hw
      · rintro (⟨hne, hw⟩ | hw)
        · exact ⟨hne, Or.inl hw⟩
        · exact ⟨by rintro rfl; exact hvB hw, Or.inr hw⟩
    have := StepsIn.erase ih (by omega) (by omega)
      (Finset.mem_union_left _ h3) hsup
    rwa [heq] at this


/-- **Bennett の再帰スケジュール**: 足場 `a`・ペブル `q+1` 本で、区間 `(a, a+2^q]` の
中だけを使い、消去 0 回で `∅` から `{a + 2^q}` へ到達する。 -/
theorem bennett : ∀ (q a : ℕ), StepsIn (q + 1) a (a + 2 ^ q) ∅ {a + 2 ^ q} 0 := by
  intro q
  induction q with
  | zero =>
    intro a
    have := StepsIn.put (v := a + 1)
      (StepsIn.refl (p := 1) (a := a) (b := a + 2 ^ 0) (∅ : Finset ℕ))
      (by omega) (by simp) (by simp) (by omega) (by simp)
    simpa using this
  | succ n ih =>
    intro a
    set h := 2 ^ n with hh
    have hh1 : 1 ≤ h := Nat.one_le_two_pow
    have harith : a + 2 ^ (n + 1) = a + h + h := by rw [hh, pow_succ]; ring
    -- 第1段: ∅ → {a+h}
    have s1 : StepsIn (n + 2) a (a + h + h) ∅ {a + h} 0 :=
      ((ih a).mono_p (by omega)).mono_b (by omega)
    -- 第2段: {a+h} → {a+h+h, a+h}（足場 a+h の上で再帰し、a+h を静止させる）
    have s2 : StepsIn (n + 2) a (a + h + h) {a + h} {a + h, a + h + h} 0 := by
      have := (ih (a + h)).frame (a' := a) (b' := a + h + h) {a + h} (by simp)
        (by intro w hw; left; simp at hw; omega) (Or.inr (by simp))
        (by omega) (by omega)
      simpa [Finset.union_comm] using this
    -- 第3段: 第1段の逆再生（a+h+h を静止させる）
    have s3 : StepsIn (n + 2) a (a + h + h) {a + h, a + h + h} {a + h + h} 0 := by
      have hrev : StepsIn (n + 1) a (a + h) {a + h} ∅ 0 :=
        (ih a).reverse rfl (by simp)
      have hfr := hrev.frame (a' := a) (b' := a + h + h) {a + h + h}
        (by intro w hw; simp at hw; omega)
        (by intro w hw; right; simp at hw; omega) (Or.inl rfl) (by omega) (by omega)
      have heq1 : ({a + h} : Finset ℕ) ∪ {a + h + h} = {a + h, a + h + h} := by
        ext w; simp
      have heq2 : (∅ : Finset ℕ) ∪ {a + h + h} = {a + h + h} := by simp
      rw [heq1, heq2] at hfr
      exact hfr
    have hcomb := (s1.trans s2).trans s3
    rw [harith]
    simpa using hcomb


/-- 足場が源（`a = 0`）の区間走行は、そのまま `Reach` になる。 -/
lemma StepsIn.toReach {p b S u} (h : StepsIn p 0 b ∅ S u) : Reach p S u := by
  induction h with
  | refl => exact Reach.empty
  | put _ h1 _ h3 h4 h5 ih => exact Reach.put ih (by omega) h3 (by simpa using h4) h5
  | take _ _ _ h3 h4 ih => exact Reach.take ih h3 (by simpa using h4)
  | erase _ _ _ h3 h4 ih => exact Reach.erase ih h3 (by simpa using h4)

/-- **消去前進**: 単独ペブル `{x}` から `{x + 2^m}` へ、ペブル `m+2` 本・消去 1 回。 -/
lemma advance (m x : ℕ) (hx : 2 ≤ x) :
    StepsIn (m + 2) 0 (x + 2 ^ m) {x} {x + 2 ^ m} 1 := by
  have hb := (bennett m x).frame (a' := 0) (b' := x + 2 ^ m) {x}
    (by simp) (by intro w hw; left; simp at hw; omega) (Or.inr (by simp))
    (by omega) (by omega)
  have heq1 : (∅ : Finset ℕ) ∪ {x} = {x} := by simp
  have heq2 : ({x + 2 ^ m} : Finset ℕ) ∪ {x} = {x, x + 2 ^ m} := by ext w; simp; tauto
  rw [heq1, heq2, Finset.card_singleton] at hb
  have h2 : (2 : ℕ) ^ m ≥ 1 := Nat.one_le_two_pow
  have hstep := StepsIn.erase (v := x) hb (by omega) (by omega)
    (by simp) (by
      rintro (hc | hc)
      · omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hc <;> omega)
  have heq3 : ({x, x + 2 ^ m} : Finset ℕ).erase x = {x + 2 ^ m} := by
    ext w; simp
  rw [heq3] at hstep
  simpa using hstep

/-- **定理 B1（構成側）**: ピーク `m+2`・消去 `e` 回で `{(e+2)·2^m}` に到達できる。 -/
theorem b1_steps (m : ℕ) : ∀ e : ℕ, ∃ b, StepsIn (m + 2) 0 b ∅ {(e + 2) * 2 ^ m} e := by
  intro e
  induction e with
  | zero =>
    refine ⟨0 + 2 ^ (m + 1), ?_⟩
    have := bennett (m + 1) 0
    have harith : (0 + 2) * 2 ^ m = 0 + 2 ^ (m + 1) := by rw [pow_succ]; ring
    rw [harith]
    exact this.mono_p (by omega)
  | succ e ih =>
    obtain ⟨b, hb⟩ := ih
    set x := (e + 2) * 2 ^ m with hx
    have hx2 : 2 ≤ x := by
      have : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
      rw [hx]; nlinarith
    have hadv := advance m x hx2
    refine ⟨b + x + 2 ^ m, ?_⟩
    have harith : (e + 1 + 2) * 2 ^ m = x + 2 ^ m := by rw [hx]; ring
    rw [harith]
    have h1 := hb.mono_b (b' := b + x + 2 ^ m) (by omega)
    have h2 := hadv.mono_b (b' := b + x + 2 ^ m) (by omega)
    simpa using h1.trans h2

/-- **定理 B2**: `reach(p,e) = (e+2)·2^{p-2}`（`p ≥ 2`）。
上界（`reach_singleton_le`）と下界（構成）の両方。 -/
theorem reach_eq (p e : ℕ) (hp : 2 ≤ p) :
    Reach p {(e + 2) * 2 ^ (p - 2)} e ∧
    (∀ n u, u ≤ e → Reach p {n} u → n ≤ (e + 2) * 2 ^ (p - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor
  · obtain ⟨b, hb⟩ := b1_steps m e
    exact hb.toReach
  · intro n u hu h
    have := reach_singleton_le (p := m + 2) (n := n) (u := u) (by omega) h
    simp only [Nat.add_sub_cancel] at this
    calc n ≤ (u + 2) * 2 ^ m := this
      _ ≤ (e + 2) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)

/-! ### リポジトリの数表との突き合わせ（`data/exp03_results.md` §B.2 の ✅ 行） -/

/-- `reach(3,0) = 4` -/
example : Reach 3 {4} 0 := by have := (reach_eq 3 0 (by norm_num)).1; norm_num at this; exact this
/-- `reach(3,1) = 6` -/
example : Reach 3 {6} 1 := by have := (reach_eq 3 1 (by norm_num)).1; norm_num at this; exact this
/-- `reach(4,0) = 8` -/
example : Reach 4 {8} 0 := by have := (reach_eq 4 0 (by norm_num)).1; norm_num at this; exact this
/-- `reach(4,2) = 16` -/
example : Reach 4 {16} 2 := by have := (reach_eq 4 2 (by norm_num)).1; norm_num at this; exact this
/-- `reach(5,4) = 48` -/
example : Reach 5 {48} 4 := by have := (reach_eq 5 4 (by norm_num)).1; norm_num at this; exact this
/-- `reach(6,2) = 64`（Fable5 側が全 mask で確認した点） -/
example : Reach 6 {64} 2 := by have := (reach_eq 6 2 (by norm_num)).1; norm_num at this; exact this

/-- 上界側も数表と合う: `p=5, e=4` では 49 に到達できない。 -/
example : ¬ Reach 5 {49} 4 := by
  intro h
  have := (reach_eq 5 4 (by norm_num)).2 49 4 le_rfl h
  norm_num at this


end PebbleDP
