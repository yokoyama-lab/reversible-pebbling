/-
# 一般の根つき木で，KSS の意味論と LLJ の規則の手数の集合が一致する

`RootedTree.lean` の `legal` は LLJ arXiv:2610.09434 §2.2 の規則（`ghost` は前提なし）を任意の根つき木へ
同じ式で広げたもので，`legalK` は KSS Def 2.6/2.7 の意味論（`ghost` は子が揃っていないときだけ）である．
これまで両者の手数の集合が等しいことは，鎖（`KSSModel.lean` の `PLengthsK_eq`）と
完全二分木（`SpookyTree/WindowLowerLimit.lean` の `treeLengths_eq_K`）でしか示していなかった．

このファイルは鎖の読み替え（`KSSModel.lean` の `tweakK`／`stripK`）を `RootedTree.ready` に置き換えて，
**すべての根つき木**（`isTree` も子の数の上限も仮定しない）で

* `PLengthsK_eq : t.PLengthsK s = t.PLengths s`
* `TPK_eq_TP : t.TPK s = t.TP s`

を示す．読み替えは「子が揃っているときの `ghost v` を `unpebble v` に，その結果ゴーストが無くなった頂点への
`unghost v` を `pebble v` に」で，手数もペブル数も変えない．不変条件は `Ghost.lean` の `Dom`
（各頂点で一致しているか，新しい側は空・元の側はゴースト）．

系として，普遍上界 `UUB.cor_U1`・`UUB.cor_U2_limit`（`RootedUniversalUpper.lean`）を KSS の意味論で述べ直す
（`cor_U1_K`・`cor_U2_limit_K`）．

注意: 読み替えは手数を保つが**仕事量（LLJ の W）は保たない**（`unpebble` は仕事 1，`ghost` は 0）．
仕事量の議論にここの結果を使ってはいけない．

名前は `TreeN24.lean` の `tweakKT`／`stripKT`（同じ読み替えを証人の検査に使う）と衝突しないよう `tweakKR`／`stripKR` とした．
-/
import SpookyPebblingExtra.RootedUniversalUpper

namespace Spooky
namespace RootedTree

variable (t : RootedTree)

/-- `Dom` はペブルの位置を保つので，`ready` も保つ． -/
theorem ready_of_Dom {c a : Config} (h : Dom c a) (v : ℕ) : t.ready c v = t.ready a v := by
  unfold RootedTree.ready
  simp [Dom_pebble h]

theorem legal_lt_n {c : Config} {m : Move} (h : t.legal c m = true) : m.v < t.n := by
  unfold RootedTree.legal at h
  exact of_decide_eq_true (Bool.and_elim_left h)

/-- 読み替え: `ready` が真のときの `ghost` は `unpebble` に，
新しい走りで対象がゴーストでないときの `unghost` は `pebble` に． -/
def tweakKR (c : Config) (m : Move) : Move :=
  if m.op = Op.ghost ∧ t.ready c m.v = true then ⟨Op.unpebble, m.v⟩
  else if m.op = Op.unghost ∧ c m.v ≠ Cell.ghost then ⟨Op.pebble, m.v⟩
  else m

def stripKR (t : RootedTree) : Config → List Move → List Move
  | _, [] => []
  | c, m :: ms => t.tweakKR c m :: stripKR t (step c (t.tweakKR c m)) ms

@[simp] theorem stripKR_nil (c : Config) : t.stripKR c [] = [] := rfl

@[simp] theorem stripKR_cons (c : Config) (m : Move) (ms : List Move) :
    t.stripKR c (m :: ms) = t.tweakKR c m :: t.stripKR (step c (t.tweakKR c m)) ms := rfl

theorem stripKR_length (c : Config) (ms : List Move) : (t.stripKR c ms).length = ms.length := by
  induction ms generalizing c with
  | nil => simp
  | cons m ms ih => simp [ih]

/-- `legalK` を作る補助． -/
theorem legalK_of_legal {c : Config} {m : Move} (h1 : t.legal c m = true)
    (h2 : m.op = Op.ghost → t.ready c m.v = false) : t.legalK c m = true := by
  unfold RootedTree.legalK
  rw [h1, Bool.true_and]
  cases hop : m.op with
  | pebble => rfl
  | unpebble => rfl
  | ghost => rw [h2 hop]; rfl
  | unghost => rfl

/-- **正規化の核**: `Dom` を保ちながら KSS の意味論の手順に読み替えられる． -/
theorem stripKR_ok {s : ℕ} : ∀ (ms : List Move) (c a : Config), Dom c a → t.ok s a ms = true →
    t.okK s c (t.stripKR c ms) = true ∧ Dom (exec c (t.stripKR c ms)) (exec a ms) := by
  intro ms
  induction ms with
  | nil =>
      intro c a hd h
      refine ⟨?_, hd⟩
      simp only [stripKR_nil, RootedTree.okK, RootedTree.ok, decide_eq_true_eq] at *
      rw [Dom_pcount hd]
      exact h
  | cons m ms ih =>
      obtain ⟨op, mv⟩ := m
      intro c a hd h
      unfold RootedTree.ok at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hcap, hleg⟩, htail⟩ := h
      have hlt : mv < t.n := t.legal_lt_n hleg
      have hrd : t.ready c mv = t.ready a mv := t.ready_of_Dom hd mv
      have hlegm := Bool.and_elim_right (by unfold RootedTree.legal at hleg; exact hleg)
      have hdstep : ∀ (x : Move), x.v = mv → result x.op = result op →
          Dom (step c x) (step a ⟨op, mv⟩) := by
        intro x hxv hxr v
        by_cases hv : v = mv
        · refine Or.inl ?_
          have h1 : step c x v = result x.op := by rw [hv, ← hxv]; exact step_self c x
          have h2 : step a ⟨op, mv⟩ v = result op := by rw [hv]; exact step_self a ⟨op, mv⟩
          rw [h1, h2]; exact hxr
        · rw [step_ne_of_ne (by omega : x.v ≠ v), step_ne_of_ne (by omega : mv ≠ v)]
          exact hd v
      have key : t.legalK c (t.tweakKR c ⟨op, mv⟩) = true
          ∧ Dom (step c (t.tweakKR c ⟨op, mv⟩)) (step a ⟨op, mv⟩) := by
        cases op with
        | pebble =>
            have hae : a mv = Cell.empty := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hra : t.ready a mv = true := Bool.and_elim_right hlegm
            have hce : c mv = Cell.empty := by
              rcases hd mv with he | ⟨_, h2⟩
              · rw [he]; exact hae
              · rw [hae] at h2; exact absurd h2 (by simp)
            have ht : t.tweakKR c ⟨Op.pebble, mv⟩ = ⟨Op.pebble, mv⟩ := by simp [tweakKR]
            rw [ht]
            refine ⟨t.legalK_of_legal ?_ (by simp), hdstep _ rfl rfl⟩
            show (decide (mv < t.n) && (decide (c mv = Cell.empty) && t.ready c mv)) = true
            rw [hce, hrd, hra]; simp [hlt]
        | unpebble =>
            have hap : a mv = Cell.pebble := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hra : t.ready a mv = true := Bool.and_elim_right hlegm
            have hcp : c mv = Cell.pebble := (Dom_pebble hd mv).mpr hap
            have ht : t.tweakKR c ⟨Op.unpebble, mv⟩ = ⟨Op.unpebble, mv⟩ := by simp [tweakKR]
            rw [ht]
            refine ⟨t.legalK_of_legal ?_ (by simp), hdstep _ rfl rfl⟩
            show (decide (mv < t.n) && (decide (c mv = Cell.pebble) && t.ready c mv)) = true
            rw [hcp, hrd, hra]; simp [hlt]
        | ghost =>
            have hap : a mv = Cell.pebble := of_decide_eq_true hlegm
            have hcp : c mv = Cell.pebble := (Dom_pebble hd mv).mpr hap
            by_cases hr : t.ready c mv = true
            · -- KSS が許さない手．`unpebble` に読み替える（長さもペブル数も同じ）
              have ht : t.tweakKR c ⟨Op.ghost, mv⟩ = ⟨Op.unpebble, mv⟩ := by simp [tweakKR, hr]
              rw [ht]
              refine ⟨t.legalK_of_legal ?_ (by simp), ?_⟩
              · show (decide (mv < t.n) && (decide (c mv = Cell.pebble) && t.ready c mv)) = true
                rw [hcp, hr]; simp [hlt]
              · intro v
                by_cases hv : v = mv
                · refine Or.inr ⟨?_, ?_⟩
                  · have h1 : step c ⟨Op.unpebble, mv⟩ mv = result Op.unpebble :=
                      step_self c ⟨Op.unpebble, mv⟩
                    rw [hv, h1]; rfl
                  · have h2 : step a ⟨Op.ghost, mv⟩ mv = result Op.ghost :=
                      step_self a ⟨Op.ghost, mv⟩
                    rw [hv, h2]; rfl
                · rw [step_ne_of_ne (by omega : mv ≠ v), step_ne_of_ne (by omega : mv ≠ v)]
                  exact hd v
            · -- KSS でも打てる手
              have ht : t.tweakKR c ⟨Op.ghost, mv⟩ = ⟨Op.ghost, mv⟩ := by simp [tweakKR, hr]
              rw [ht]
              refine ⟨t.legalK_of_legal ?_ (fun _ => by simpa using hr), hdstep _ rfl rfl⟩
              show (decide (mv < t.n) && decide (c mv = Cell.pebble)) = true
              rw [hcp]; simp [hlt]
        | unghost =>
            have hag : a mv = Cell.ghost := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hrdy : t.ready c mv = true := by rw [hrd]; exact Bool.and_elim_right hlegm
            by_cases hcg : c mv = Cell.ghost
            · have ht : t.tweakKR c ⟨Op.unghost, mv⟩ = ⟨Op.unghost, mv⟩ := by simp [tweakKR, hcg]
              rw [ht]
              refine ⟨t.legalK_of_legal ?_ (by simp), hdstep _ rfl rfl⟩
              show (decide (mv < t.n) && (decide (c mv = Cell.ghost) && t.ready c mv)) = true
              rw [hcg, hrdy]; simp [hlt]
            · -- 新しい走りでは空．`pebble` に読み替える
              have hce : c mv = Cell.empty := by
                rcases hd mv with he | ⟨h1, _⟩
                · rw [he] at hcg; exact absurd hag hcg
                · exact h1
              have ht : t.tweakKR c ⟨Op.unghost, mv⟩ = ⟨Op.pebble, mv⟩ := by simp [tweakKR, hcg]
              rw [ht]
              refine ⟨t.legalK_of_legal ?_ (by simp), hdstep _ rfl rfl⟩
              show (decide (mv < t.n) && (decide (c mv = Cell.empty) && t.ready c mv)) = true
              rw [hce, hrdy]; simp [hlt]
      obtain ⟨hlegK, hd'⟩ := key
      obtain ⟨hok', hdom'⟩ := ih (step c (t.tweakKR c ⟨op, mv⟩)) (step a ⟨op, mv⟩) hd' htail
      refine ⟨?_, hdom'⟩
      show (decide (pcount t.n c ≤ s) && t.legalK c (t.tweakKR c ⟨op, mv⟩)
        && t.okK s (step c (t.tweakKR c ⟨op, mv⟩))
          (t.stripKR (step c (t.tweakKR c ⟨op, mv⟩)) ms)) = true
      rw [hlegK, hok']
      simp only [Bool.and_true, decide_eq_true_eq]
      rw [Dom_pcount hd]
      exact of_decide_eq_true hcap

/-- **正規化**: 広いモデル（LLJ の規則）の手順は，同じ手数の KSS の手順に読み替えられる
（終状態にゴーストが無ければ）． -/
theorem RunK_of_Run_R {s : ℕ} {a b : Config} (hb : ∀ v, v < t.n → b v ≠ Cell.ghost)
    {ms : List Move} (h : t.Run s a ms b) :
    ∃ ms', ms'.length = ms.length ∧ t.RunK s a ms' b := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hok', hdom'⟩ := t.stripKR_ok ms a a (Dom_refl a) hok
  refine ⟨t.stripKR a ms, t.stripKR_length a ms, hok', ?_⟩
  intro v hv
  rcases hdom' v with he | ⟨h1, h2⟩
  · rw [he]; exact hagree v hv
  · rw [hagree v hv] at h2
    exact absurd h2 (hb v hv)

theorem rootPebble_no_ghost : ∀ v, v < t.n → t.rootPebble v ≠ Cell.ghost := by
  intro v _
  unfold RootedTree.rootPebble
  by_cases h : v = t.root
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [allEmpty]

/-- **手数の集合は 2 つの意味論で同じ（すべての根つき木・すべての `s`）．** -/
theorem PLengthsK_eq (s : ℕ) : t.PLengthsK s = t.PLengths s := by
  ext L
  constructor
  · rintro ⟨ms, hlen, hrun⟩; exact ⟨ms, hlen, t.Run_of_RunK hrun⟩
  · rintro ⟨ms, hlen, hrun⟩
    obtain ⟨ms', hlen', hrun'⟩ := t.RunK_of_Run_R t.rootPebble_no_ghost hrun
    exact ⟨ms', by rw [hlen', hlen], hrun'⟩

/-- **最小手数は 2 つの意味論で同じ．** -/
theorem TPK_eq_TP (s : ℕ) : t.TPK s = t.TP s := by
  unfold RootedTree.TPK RootedTree.TP
  rw [t.PLengthsK_eq s]

namespace UUB

/-- **系 U1 の KSS 版**: 同じ範囲で，KSS の意味論でも妥当な手順があり `T_KSS ≤ 2⌈1/ε⌉n − 1`． -/
theorem cor_U1_K {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε) (d : ℕ) :
    ∃ n₀ : ℕ, ∀ t : RootedTree, t.isTree = true → (∀ v, v < t.n → (chs t v).card ≤ d) →
      n₀ ≤ t.n → (t.PLengthsK ⌊(t.n : ℝ) ^ ε⌋₊).Nonempty ∧
        t.TPK ⌊(t.n : ℝ) ^ ε⌋₊ ≤ 2 * ⌈1 / ε⌉₊ * t.n - 1 := by
  obtain ⟨n₀, h⟩ := cor_U1 hε0 hε1 hint d
  refine ⟨n₀, fun t ht hd hn => ?_⟩
  rw [t.PLengthsK_eq, t.TPK_eq_TP]
  exact h t ht hd hn

/-- **系 U2 の極限の KSS 版**: `|T_KSS/n − 2⌈1/ε⌉| ≤ η` が `n ≥ N(η)` のすべての木で一様． -/
theorem cor_U2_limit_K {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε)
    (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true → (∀ v, v < t.n → (chs t v).card ≤ d) → N ≤ t.n →
      |(t.TPK ⌊(t.n : ℝ) ^ ε⌋₊ : ℝ) / t.n - 2 * (⌈1 / ε⌉₊ : ℝ)| ≤ η := by
  obtain ⟨N, h⟩ := cor_U2_limit hε0 hε1 hint d hη
  refine ⟨N, fun t ht hd hn => ?_⟩
  rw [t.TPK_eq_TP]
  exact h t ht hd hn

end UUB

end RootedTree
end Spooky
