/-
  # 時間対称性は WLOG — 時間最適ペブリングは片道の「降下問題」に帰着する（2026-08-18）

  時間最適 `T = 2D+1` の合法なペブリング `P`（終状態 `{sink}`）を 1 つ取る。
  その**上り（`t ≥ D+1`）を時間反転して sink を除いた列**

      Q j := (P (T - j)).erase sink        (j = 0..D)

  は `∅` から始まる合法な列で、上りでは sink が常在するから `|Q j| ≤ p - 1`。
  `Q` を下りに使い、時刻 `D+1` で sink を置き、`Q` を逆順に上ればピーク `≤ p` の
  **時間対称な**ペブリングになる（`sym_wlog`）。

  さらに `Q` は「降下」`Descent`（空から始まる合法列で、時間最適性が強制する
  「層 `k` は時刻 `k+1, k+2` に全部居る」を満たすもの）であり（`descent_of_pebbling`）、
  逆に任意の降下からピーク `+1` のペブリングが作れる（`pebbling_of_descent`）。
  したがって

      p_min = 1 + d,   d := min over descents of max_{t ≤ D} |Q t|     (`pmin_iff_descent`)

  **これで問題は「終状態が自由な片道の降下」になり、SAT/CP の地平線が半分になる**
  （`scripts/q2_descent_cnf.py`）。

  仮定は `ParPebbleWindow` の深さ関数版と同じ（`hclosed`/`hdown`/`hmax`/`huniq`/`hup`）に
  `hpa1`（親は深さがちょうど 1 小さい。`lift_pebbling` と同じ）と
  `hnochild`（sink は誰の親でもない）を足したもの。鎖・ピラミッドは満たす。
-/
import Revgarbage.ParPebbleWindow

namespace ParPebbleDAG

variable {pa : ℕ → Finset ℕ}

/-! ## 0. 1 ステップの補題: 反転・sink の除去・sink の付加 -/

/-- 合法なステップは逆向きも合法（`Changed` が対称なので）。 -/
theorem legalStep_symm {P Q : Finset ℕ} (h : LegalStep pa P Q) : LegalStep pa Q P := by
  intro v hv u hu
  have hv' : Changed P Q v := by
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  exact ⟨(h v hv' u hu).2, (h v hv' u hu).1⟩

/-- 誰の親でもない頂点 `s` は、両側から消しても合法性を壊さない。 -/
theorem legalStep_erase {P Q : Finset ℕ} {s : ℕ}
    (hns : ∀ v, s ∉ pa v) (h : LegalStep pa P Q) :
    LegalStep pa (P.erase s) (Q.erase s) := by
  intro v hv u hu
  have hvs : v ≠ s := by
    intro he; subst he
    rcases hv with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact (Finset.notMem_erase _ _) h1
    · exact (Finset.notMem_erase _ _) h2
  have hv' : Changed P Q v := by
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(Finset.mem_erase.mp h1).2, fun hq => h2 (Finset.mem_erase.mpr ⟨hvs, hq⟩)⟩
    · exact Or.inr ⟨fun hp => h1 (Finset.mem_erase.mpr ⟨hvs, hp⟩), (Finset.mem_erase.mp h2).2⟩
  have hus : u ≠ s := by intro he; subst he; exact hns v hu
  obtain ⟨h1, h2⟩ := h v hv' u hu
  exact ⟨Finset.mem_erase.mpr ⟨hus, h1⟩, Finset.mem_erase.mpr ⟨hus, h2⟩⟩

/-- 誰の親でもない頂点 `s` は、両側に足しても合法性を壊さない（`s` は元の両側に無いとする）。 -/
theorem legalStep_insert {P Q : Finset ℕ} {s : ℕ}
    (hns : ∀ v, s ∉ pa v) (hsP : s ∉ P) (hsQ : s ∉ Q) (h : LegalStep pa P Q) :
    LegalStep pa (insert s P) (insert s Q) := by
  intro v hv u hu
  have hvs : v ≠ s := by
    intro he; subst he
    rcases hv with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 (Finset.mem_insert_self _ _)
    · exact h1 (Finset.mem_insert_self _ _)
  have hv' : Changed P Q v := by
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(Finset.mem_insert.mp h1).resolve_left hvs,
        fun hq => h2 (Finset.mem_insert_of_mem hq)⟩
    · exact Or.inr ⟨fun hp => h1 (Finset.mem_insert_of_mem hp),
        (Finset.mem_insert.mp h2).resolve_left hvs⟩
  obtain ⟨h1, h2⟩ := h v hv' u hu
  exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩

/-! ## 1. 降下 -/

/-- **降下**: `∅` から `D` ステップの合法列で、`V` の頂点 `v` は時刻 `dep v + 1` と
    `dep v + 2`（`≤ D` の範囲で）に必ず居る。終状態は自由。 -/
structure Descent (pa : ℕ → Finset ℕ) (V : Finset ℕ) (dep : ℕ → ℕ) (D : ℕ)
    (Q : ℕ → Finset ℕ) : Prop where
  peb : Pebbling pa Q D
  forced1 : ∀ v ∈ V, dep v + 1 ≤ D → v ∈ Q (dep v + 1)
  forced2 : ∀ v ∈ V, dep v + 2 ≤ D → v ∈ Q (dep v + 2)

section Reduction

variable {P Q : ℕ → Finset ℕ} {V : Finset ℕ} {dep : ℕ → ℕ} {sink D : ℕ}

/-- **上りの時間反転は降下である**（sink を除く）。ピークは元の `p` から 1 減る。 -/
theorem descent_of_pebbling
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1)
    (hnochild : ∀ v, sink ∉ pa v)
    (hend : P (2 * D + 1) = {sink}) :
    Descent pa V dep D (fun j => (P (2 * D + 1 - j)).erase sink) ∧
    ∀ j, j ≤ D → ((P (2 * D + 1 - j)).erase sink).card + 1 = (P (2 * D + 1 - j)).card := by
  have hgone : ∀ v ∈ V, v ≠ sink → v ∉ P (2 * D + 1) := by
    intro v _ hvs hc; rw [hend] at hc; exact hvs (Finset.mem_singleton.mp hc)
  have hsin : sink ∈ P (2 * D + 1) := by rw [hend]; exact Finset.mem_singleton_self _
  have hstay := sink_at_and_stays_dep hp hclosed hdown hmax hgone hsV hds hD hsin
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · -- start
    show (P (2 * D + 1 - 0)).erase sink = ∅
    simp [hend]
  · -- legal: 上りの各ステップの反転
    intro t ht
    have h1 : 2 * D + 1 - t = (2 * D + 1 - (t + 1)) + 1 := by omega
    have hleg := hp.legal (2 * D + 1 - (t + 1)) (by omega)
    rw [← h1] at hleg
    exact legalStep_erase hnochild (legalStep_symm hleg)
  · -- forced1: 窓の右端 `2D - dep v`
    intro v hvV h1
    have hvs : v ≠ sink := by intro he; subst he; omega
    have hpe := (present_at_end_dep hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup v hvV hvs).1
    have he : 2 * D + 1 - (dep v + 1) = 2 * D - dep v := by omega
    show v ∈ (P (2 * D + 1 - (dep v + 1))).erase sink
    rw [he]; exact Finset.mem_erase.mpr ⟨hvs, hpe⟩
  · -- forced2: 窓の右端の 1 つ内側 `2D - dep v - 1`
    intro v hvV h2
    have hvs : v ≠ sink := by intro he; subst he; omega
    have hpe := (present_at_end_dep hp hclosed hdown hmax huniq hgone hsV hds hD hsin hup v hvV hvs).2
    have he : 2 * D + 1 - (dep v + 2) = 2 * D - dep v - 1 := by omega
    show v ∈ (P (2 * D + 1 - (dep v + 2))).erase sink
    rw [he]; exact Finset.mem_erase.mpr ⟨hvs, hpe⟩
  · -- カード: 上りでは sink が常在
    intro j hj
    have hs : sink ∈ P (2 * D + 1 - j) := hstay _ (by omega) (by omega)
    exact Finset.card_erase_add_one hs

/-- 降下から作る対称なペブリング: 下りは `Q`、時刻 `D+1` で sink を置き、上りは `Q` の逆順。 -/
def symOfDescent (Q : ℕ → Finset ℕ) (sink D : ℕ) : ℕ → Finset ℕ := fun t =>
  if t ≤ D then Q t else insert sink (Q (2 * D + 1 - t))

/-- **任意の降下はピーク `+1` の時間最適ペブリングに伸びる**（終状態 `{sink}`）。 -/
theorem pebbling_of_descent
    (hQ : Descent pa V dep D Q)
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v)
    (hsV : sink ∈ V) (hds : dep sink = D)
    (hnochild : ∀ v, sink ∉ pa v) :
    Pebbling pa (symOfDescent Q sink D) (2 * D + 1) ∧
    symOfDescent Q sink D (2 * D + 1) = {sink} ∧
    (∀ t, t ≤ D → symOfDescent Q sink D t = Q t) ∧
    (∀ t, D + 1 ≤ t → t ≤ 2 * D + 1 →
      (symOfDescent Q sink D t).card = (Q (2 * D + 1 - t)).card + 1) := by
  -- sink は降下のどの時刻にも居ない（深さの下界）
  have hnos : ∀ t, t ≤ D → sink ∉ Q t := by
    intro t ht hc
    have := depth_bound_dep hQ.peb hclosed hdown t ht sink hsV hc
    omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- start
    show (if 0 ≤ D then Q 0 else _) = ∅
    simp [hQ.peb.start]
  · -- legal
    intro t ht
    unfold symOfDescent
    by_cases h1 : t + 1 ≤ D
    · -- 下り
      have h0 : t ≤ D := by omega
      simp only [h0, h1, if_true]
      exact hQ.peb.legal t (by omega)
    · by_cases h0 : t ≤ D
      · -- `t = D`: sink を置く。親は層 `D-1` にあり、`forced1` で `Q D` に居る
        have htD : t = D := by omega
        have hR : 2 * D + 1 - (t + 1) = t := by omega
        simp only [h0, if_true, h1, if_false, hR]
        intro v hv u hu
        have hvs : v = sink := by
          by_contra hne
          rcases hv with ⟨hin, hout⟩ | ⟨hin, hout⟩
          · exact hout (Finset.mem_insert_of_mem hin)
          · exact hin ((Finset.mem_insert.mp hout).resolve_left hne)
        subst hvs
        have huV : u ∈ V := hclosed v hsV u hu
        have hdu : dep u + 1 = t := by have := hpa1 v hsV u hu; omega
        have huQ : u ∈ Q t := by
          have := hQ.forced1 u huV (by omega)
          rw [hdu] at this; exact this
        exact ⟨huQ, Finset.mem_insert_of_mem huQ⟩
      · -- 上り: `Q` の逆順に sink を足したもの
        have hj : 2 * D + 1 - t = (2 * D + 1 - (t + 1)) + 1 := by omega
        simp only [h0, h1, if_false]
        have hleg := hQ.peb.legal (2 * D + 1 - (t + 1)) (by omega)
        rw [← hj] at hleg
        exact legalStep_insert hnochild (hnos _ (by omega)) (hnos _ (by omega))
          (legalStep_symm hleg)
  · -- 終状態
    unfold symOfDescent
    have h : ¬ (2 * D + 1 ≤ D) := by omega
    simp only [h, if_false]
    have hz : 2 * D + 1 - (2 * D + 1) = 0 := by omega
    rw [hz, hQ.peb.start]; rfl
  · intro t ht; unfold symOfDescent; simp [ht]
  · intro t ht1 ht2
    unfold symOfDescent
    have h : ¬ (t ≤ D) := by omega
    simp only [h, if_false]
    exact Finset.card_insert_of_notMem (hnos _ (by omega))

/-- **`p_min = 1 + d`**: ピーク `≤ p` の時間最適ペブリング（終状態 `{sink}`）が存在することと、
    ピーク `≤ p - 1` の降下が存在することは同値（`1 ≤ p`）。

    左→右は上りの反転（`descent_of_pebbling`）、右→左は対称化（`pebbling_of_descent`）。 -/
theorem pmin_iff_descent {p : ℕ}
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1)
    (hnochild : ∀ v, sink ∉ pa v) :
    (∃ P : ℕ → Finset ℕ, Pebbling pa P (2 * D + 1) ∧ P (2 * D + 1) = {sink} ∧
        (∀ t, t ≤ 2 * D + 1 → P t ⊆ V) ∧ (∀ t, t ≤ 2 * D + 1 → (P t).card ≤ p)) ↔
    (∃ Q : ℕ → Finset ℕ, Descent pa V dep D Q ∧ (∀ t, t ≤ D → Q t ⊆ V) ∧
        (∀ t, t ≤ D → (Q t).card + 1 ≤ p)) := by
  constructor
  · rintro ⟨P, hp, hend, hsub, hpk⟩
    obtain ⟨hdesc, hcard⟩ := descent_of_pebbling hp hclosed hdown hmax huniq hsV hds hD hup
      hnochild hend
    refine ⟨fun j => (P (2 * D + 1 - j)).erase sink, hdesc, ?_, ?_⟩
    · intro t _ v hv
      exact hsub _ (by omega) (Finset.mem_erase.mp hv).2
    · intro t ht
      show ((P (2 * D + 1 - t)).erase sink).card + 1 ≤ p
      have := hcard t ht
      have := hpk (2 * D + 1 - t) (by omega)
      omega
  · rintro ⟨Q, hQ, hsub, hpk⟩
    obtain ⟨hpeb, hend, hdown', hup'⟩ := pebbling_of_descent hQ hclosed hdown hpa1 hsV hds
      hnochild
    refine ⟨symOfDescent Q sink D, hpeb, hend, ?_, ?_⟩
    · intro t ht
      by_cases h : t ≤ D
      · rw [hdown' t h]; exact hsub t h
      · unfold symOfDescent
        simp only [h, if_false]
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hsV
        · exact hsub _ (by omega) hv'
    · intro t ht
      by_cases h : t ≤ D
      · rw [hdown' t h]; have := hpk t h; omega
      · rw [hup' t (by omega) ht]; have := hpk (2 * D + 1 - t) (by omega); omega

/-- **時間対称な最適解が常に存在する。** ピーク `≤ p` のペブリングがあれば、
    `Q t = (Q (T - t)).erase sink`（`t ≤ D`）を満たすピーク `≤ p` のペブリングもある。 -/
theorem sym_wlog {p : ℕ}
    (hp : Pebbling pa P (2 * D + 1))
    (hclosed : ∀ v ∈ V, ∀ u ∈ pa v, u ∈ V)
    (hdown : ∀ v ∈ V, dep v ≠ 0 → ∃ u ∈ pa v, dep u + 1 = dep v)
    (hpa1 : ∀ v ∈ V, ∀ u ∈ pa v, dep u + 1 = dep v)
    (hmax : ∀ v ∈ V, dep v ≤ dep sink)
    (huniq : ∀ v ∈ V, dep v = D → v = sink)
    (hsV : sink ∈ V) (hds : dep sink = D) (hD : 1 ≤ D)
    (hup : ∀ v ∈ V, v ≠ sink → ∃ c ∈ V, v ∈ pa c ∧ dep c = dep v + 1)
    (hnochild : ∀ v, sink ∉ pa v)
    (hend : P (2 * D + 1) = {sink})
    (hpk : ∀ t, t ≤ 2 * D + 1 → (P t).card ≤ p) :
    ∃ P' : ℕ → Finset ℕ, Pebbling pa P' (2 * D + 1) ∧ P' (2 * D + 1) = {sink} ∧
      (∀ t, t ≤ 2 * D + 1 → (P' t).card ≤ p) ∧
      (∀ t, t ≤ D → P' t = (P' (2 * D + 1 - t)).erase sink) := by
  obtain ⟨hdesc, hcard⟩ := descent_of_pebbling hp hclosed hdown hmax huniq hsV hds hD hup
    hnochild hend
  obtain ⟨hpeb, hend', hdown', hup'⟩ := pebbling_of_descent hdesc hclosed hdown hpa1 hsV hds
    hnochild
  refine ⟨symOfDescent (fun j => (P (2 * D + 1 - j)).erase sink) sink D, hpeb, hend', ?_, ?_⟩
  · intro t ht
    by_cases h : t ≤ D
    · rw [hdown' t h]
      show ((P (2 * D + 1 - t)).erase sink).card ≤ p
      have := hcard t h
      have := hpk (2 * D + 1 - t) (by omega)
      omega
    · rw [hup' t (by omega) ht]
      show ((P (2 * D + 1 - (2 * D + 1 - t))).erase sink).card + 1 ≤ p
      have := hcard (2 * D + 1 - t) (by omega)
      have := hpk (2 * D + 1 - (2 * D + 1 - t)) (by omega)
      omega
  · intro t ht
    rw [hdown' t ht]
    unfold symOfDescent
    have h : ¬ (2 * D + 1 - t ≤ D) := by omega
    simp only [h, if_false]
    have e : 2 * D + 1 - (2 * D + 1 - t) = t := by omega
    rw [e, Finset.erase_insert (Finset.notMem_erase _ _)]

end Reduction

end ParPebbleDAG

namespace ParPebbleDAG

/-! ## 2. 非空虚性: ピラミッド `h = 5`（`paP5`）に実際に適用できる -/

/-- `pmin_iff_descent` の仮定はピラミッド `h=5` で `decide` により満たされる。
    したがって $p_{\min}(\mathrm{pyr}\,5) = 10$ は「降下 4 ステップでピーク 9」と同値。 -/
theorem pyr5_pmin_iff_descent (p : ℕ) :
    (∃ P : ℕ → Finset ℕ, Pebbling paP5 P (2 * 4 + 1) ∧ P (2 * 4 + 1) = {14} ∧
        (∀ t, t ≤ 2 * 4 + 1 → P t ⊆ VP5) ∧ (∀ t, t ≤ 2 * 4 + 1 → (P t).card ≤ p)) ↔
    (∃ Q : ℕ → Finset ℕ, Descent paP5 VP5 depP5 4 Q ∧ (∀ t, t ≤ 4 → Q t ⊆ VP5) ∧
        (∀ t, t ≤ 4 → (Q t).card + 1 ≤ p)) :=
  pmin_iff_descent (pa := paP5) (V := VP5) (dep := depP5) (sink := 14) (D := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by intro v; unfold paP5; split_ifs <;> decide)

end ParPebbleDAG
