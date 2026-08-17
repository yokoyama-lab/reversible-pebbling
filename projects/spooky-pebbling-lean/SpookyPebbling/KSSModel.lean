/-
# KSS の意味論との同値性

`Defs.lean` の `legal` は、KSS Def 2.6/2.7 に対して **1 点だけ広い**。

> **KSS Def 2.6**: $G_{i+1} = \bigl(G_i \cup \{v\in P_i : \mathrm{parents}(v)\not\subseteq P_i\}\bigr)\setminus P_{i+1}$
>
> **KSS Def 2.7**: $\|P_i \triangle P_{i+1}\|=1$、$v\in P_{i+1}\setminus P_i \Rightarrow \mathrm{parents}(v)\subseteq P_i$、$G_\tau=\emptyset$

KSS では **ゴーストは導出であって選択ではない**。`v` からペブルを外すとき、
`parents(v) ⊆ P` ならゴーストは**生じず**、そうでなければ**必ず**生じる。
一方 `Defs.lean` の `ghost` は前提条件を持たないので、`ready c v` が真でも打てる
（＝ KSS が許さない「わざとゴーストを作る手」）。

したがって素朴には

* **下界はそのまま KSS へ移る**（手が多いほど最小値は小さいので $T_{\text{本形式化}} \le T_{KSS}$）
* **上界は自動では移らない**

**このファイルはその差を潰す。** `ready` が真のときの `ghost v` を `unpebble v` に、
その後の `unghost v` を `pebble v` に読み替える正規化を与え、**手数もペブル数も変えずに**
KSS の意味論の手順へ移せることを示す。よって

$$T_{KSS}(n,s) \;=\; T_{\text{本形式化}}(n,s)$$

であり、**本リポジトリの上界・下界はすべて KSS の意味論の定理**である。

読み替えの道具は `Ghost.lean` の `Dom` / `tweak` / `strip` の親戚で、
不変条件も同じ「ペブルの位置は一致・ゴーストは高々元の分だけ」。
-/
import SpookyPebbling.Decomp

namespace Spooky

/-! ## KSS の意味論 -/

/-- **KSS Def 2.6/2.7 の意味論**。`ghost` は `ready` が偽のときしか打てない
（＝ペブルを外すとき、親が揃っていればゴーストは生じない）。 -/
def legalK (n : ℕ) (c : Config) (m : Move) : Bool :=
  legal n c m && (match m.op with | .ghost => !ready c m.v | _ => true)

theorem legalK_legal {n : ℕ} {c : Config} {m : Move} (h : legalK n c m = true) :
    legal n c m = true := Bool.and_elim_left h

def okK (n s : ℕ) (c : Config) : List Move → Bool
  | [] => decide (pcount n c ≤ s)
  | m :: ms => decide (pcount n c ≤ s) && legalK n c m && okK n s (step c m) ms

def RunK (n s : ℕ) (a : Config) (ms : List Move) (b : Config) : Prop :=
  okK n s a ms = true ∧ AgreeOn n (exec a ms) b

/-- KSS の手順は本形式化の手順でもある（自明な向き）。 -/
theorem ok_of_okK {n s : ℕ} : ∀ (ms : List Move) (c : Config),
    okK n s c ms = true → ok n s c ms = true := by
  intro ms
  induction ms with
  | nil => intro c h; unfold okK at h; unfold ok; exact h
  | cons m ms ih =>
      intro c h
      unfold okK at h
      unfold ok
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, legalK_legal h.1.2⟩, ih (step c m) h.2⟩

theorem Run_of_RunK {n s : ℕ} {a b : Config} {ms : List Move} (h : RunK n s a ms b) :
    Run n s a ms b := ⟨ok_of_okK ms a h.1, h.2⟩

/-! ## 正規化 -/

/-- 読み替え: `ready` が真のときの `ghost` は `unpebble` に、
新しい走りで対象がゴーストでないときの `unghost` は `pebble` に。 -/
def tweakK (c : Config) (m : Move) : Move :=
  if m.op = Op.ghost ∧ ready c m.v = true then ⟨Op.unpebble, m.v⟩
  else if m.op = Op.unghost ∧ c m.v ≠ Cell.ghost then ⟨Op.pebble, m.v⟩
  else m

@[simp] theorem tweakK_v (c : Config) (m : Move) : (tweakK c m).v = m.v := by
  unfold tweakK; split <;> [rfl; split <;> rfl]

def stripK (c : Config) : List Move → List Move
  | [] => []
  | m :: ms => tweakK c m :: stripK (step c (tweakK c m)) ms

@[simp] theorem stripK_nil (c : Config) : stripK c [] = [] := rfl

@[simp] theorem stripK_cons (c : Config) (m : Move) (ms : List Move) :
    stripK c (m :: ms) = tweakK c m :: stripK (step c (tweakK c m)) ms := rfl

theorem stripK_length (c : Config) (ms : List Move) : (stripK c ms).length = ms.length := by
  induction ms generalizing c with
  | nil => simp
  | cons m ms ih => simp [ih]

/-- `legalK` を作る補助。 -/
theorem legalK_of {n : ℕ} {c : Config} {m : Move} (h1 : legal n c m = true)
    (h2 : m.op = Op.ghost → ready c m.v = false) : legalK n c m = true := by
  unfold legalK
  rw [h1, Bool.true_and]
  cases hop : m.op with
  | pebble => rfl
  | unpebble => rfl
  | ghost => rw [h2 hop]; rfl
  | unghost => rfl

/-- **正規化の核**: `Dom` を保ちながら KSS の意味論の手順に読み替えられる。 -/
theorem stripK_ok {n s : ℕ} : ∀ (ms : List Move) (c a : Config), Dom c a → ok n s a ms = true →
    okK n s c (stripK c ms) = true ∧ Dom (exec c (stripK c ms)) (exec a ms) := by
  intro ms
  induction ms with
  | nil =>
      intro c a hd h
      refine ⟨?_, hd⟩
      simp only [stripK_nil, okK, ok, decide_eq_true_eq] at *
      rw [Dom_pcount hd]
      exact h
  | cons m ms ih =>
      obtain ⟨op, mv⟩ := m
      intro c a hd h
      unfold ok at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hcap, hleg⟩, htail⟩ := h
      have hlt : mv < n := legal_lt hleg
      have hrd : ready c mv = ready a mv := Dom_ready hd mv
      have hlegm := Bool.and_elim_right (by unfold legal at hleg; exact hleg)
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
      have key : legalK n c (tweakK c ⟨op, mv⟩) = true
          ∧ Dom (step c (tweakK c ⟨op, mv⟩)) (step a ⟨op, mv⟩) := by
        cases op with
        | pebble =>
            have hae : a mv = Cell.empty := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hra : ready a mv = true := Bool.and_elim_right hlegm
            have hce : c mv = Cell.empty := by
              rcases hd mv with he | ⟨_, h2⟩
              · rw [he]; exact hae
              · rw [hae] at h2; exact absurd h2 (by simp)
            have ht : tweakK c ⟨Op.pebble, mv⟩ = ⟨Op.pebble, mv⟩ := by simp [tweakK]
            rw [ht]
            refine ⟨legalK_of ?_ (by simp), hdstep _ rfl rfl⟩
            show (decide (mv < n) && (decide (c mv = Cell.empty) && ready c mv)) = true
            rw [hce, hrd, hra]; simp [hlt]
        | unpebble =>
            have hap : a mv = Cell.pebble := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hra : ready a mv = true := Bool.and_elim_right hlegm
            have hcp : c mv = Cell.pebble := (Dom_pebble hd mv).mpr hap
            have ht : tweakK c ⟨Op.unpebble, mv⟩ = ⟨Op.unpebble, mv⟩ := by simp [tweakK]
            rw [ht]
            refine ⟨legalK_of ?_ (by simp), hdstep _ rfl rfl⟩
            show (decide (mv < n) && (decide (c mv = Cell.pebble) && ready c mv)) = true
            rw [hcp, hrd, hra]; simp [hlt]
        | ghost =>
            have hap : a mv = Cell.pebble := of_decide_eq_true hlegm
            have hcp : c mv = Cell.pebble := (Dom_pebble hd mv).mpr hap
            by_cases hr : ready c mv = true
            · -- KSS が許さない手。`unpebble` に読み替える（長さもペブル数も同じ）
              have ht : tweakK c ⟨Op.ghost, mv⟩ = ⟨Op.unpebble, mv⟩ := by simp [tweakK, hr]
              rw [ht]
              refine ⟨legalK_of ?_ (by simp), ?_⟩
              · show (decide (mv < n) && (decide (c mv = Cell.pebble) && ready c mv)) = true
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
              have ht : tweakK c ⟨Op.ghost, mv⟩ = ⟨Op.ghost, mv⟩ := by simp [tweakK, hr]
              rw [ht]
              refine ⟨legalK_of ?_ (fun _ => by simpa using hr), hdstep _ rfl rfl⟩
              show (decide (mv < n) && decide (c mv = Cell.pebble)) = true
              rw [hcp]; simp [hlt]
        | unghost =>
            have hag : a mv = Cell.ghost := of_decide_eq_true (Bool.and_elim_left hlegm)
            have hrdy : ready c mv = true := by rw [hrd]; exact Bool.and_elim_right hlegm
            by_cases hcg : c mv = Cell.ghost
            · have ht : tweakK c ⟨Op.unghost, mv⟩ = ⟨Op.unghost, mv⟩ := by simp [tweakK, hcg]
              rw [ht]
              refine ⟨legalK_of ?_ (by simp), hdstep _ rfl rfl⟩
              show (decide (mv < n) && (decide (c mv = Cell.ghost) && ready c mv)) = true
              rw [hcg, hrdy]; simp [hlt]
            · -- 新しい走りでは空。`pebble` に読み替える
              have hce : c mv = Cell.empty := by
                rcases hd mv with he | ⟨h1, _⟩
                · rw [he] at hcg; exact absurd hag hcg
                · exact h1
              have ht : tweakK c ⟨Op.unghost, mv⟩ = ⟨Op.pebble, mv⟩ := by simp [tweakK, hcg]
              rw [ht]
              refine ⟨legalK_of ?_ (by simp), hdstep _ rfl rfl⟩
              show (decide (mv < n) && (decide (c mv = Cell.empty) && ready c mv)) = true
              rw [hce, hrdy]; simp [hlt]
      obtain ⟨hlegK, hd'⟩ := key
      obtain ⟨hok', hdom'⟩ := ih (step c (tweakK c ⟨op, mv⟩)) (step a ⟨op, mv⟩) hd' htail
      refine ⟨?_, hdom'⟩
      show (decide (pcount n c ≤ s) && legalK n c (tweakK c ⟨op, mv⟩)
        && okK n s (step c (tweakK c ⟨op, mv⟩)) (stripK (step c (tweakK c ⟨op, mv⟩)) ms)) = true
      rw [hlegK, hok']
      simp only [Bool.and_true, decide_eq_true_eq]
      rw [Dom_pcount hd]
      exact of_decide_eq_true hcap

/-- **正規化**: 本形式化の手順は、同じ手数の KSS の手順に読み替えられる
（終状態にゴーストが無ければ）。 -/
theorem RunK_of_Run {n s : ℕ} {a b : Config} (hb : ∀ v, v < n → b v ≠ Cell.ghost)
    {ms : List Move} (h : Run n s a ms b) :
    ∃ ms', ms'.length = ms.length ∧ RunK n s a ms' b := by
  obtain ⟨hok, hagree⟩ := h
  obtain ⟨hok', hdom'⟩ := stripK_ok ms a a (Dom_refl a) hok
  refine ⟨stripK a ms, stripK_length a ms, hok', ?_⟩
  intro v hv
  rcases hdom' v with he | ⟨h1, h2⟩
  · rw [he]; exact hagree v hv
  · rw [hagree v hv] at h2
    exact absurd h2 (hb v hv)

/-! ## 3 つの量が一致する -/

def PLengthsK (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ RunK n s allEmpty ms (sinkPebble n) }

def UPLengthsK (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ RunK n s (sinkPebble n) ms allEmpty }

def UGLengthsK (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ RunK n s (sinkGhost n) ms allEmpty }

theorem allEmpty_no_ghost (n : ℕ) : ∀ v, v < n → allEmpty v ≠ Cell.ghost := by
  intro v _; simp [allEmpty]

theorem sinkPebble_no_ghost (n : ℕ) : ∀ v, v < n → sinkPebble n v ≠ Cell.ghost := by
  intro v _
  rw [sinkPebble_apply]
  by_cases h : v = n - 1 <;> simp [h]


theorem UPLengthsK_eq (n s : ℕ) : UPLengthsK n s = UPLengths n s := by
  ext L
  constructor
  · rintro ⟨ms, hlen, hrun⟩; exact ⟨ms, hlen, Run_of_RunK hrun⟩
  · rintro ⟨ms, hlen, hrun⟩
    obtain ⟨ms', hlen', hrun'⟩ := RunK_of_Run (allEmpty_no_ghost n) hrun
    exact ⟨ms', by rw [hlen', hlen], hrun'⟩

theorem UGLengthsK_eq (n s : ℕ) : UGLengthsK n s = UGLengths n s := by
  ext L
  constructor
  · rintro ⟨ms, hlen, hrun⟩; exact ⟨ms, hlen, Run_of_RunK hrun⟩
  · rintro ⟨ms, hlen, hrun⟩
    obtain ⟨ms', hlen', hrun'⟩ := RunK_of_Run (allEmpty_no_ghost n) hrun
    exact ⟨ms', by rw [hlen', hlen], hrun'⟩

theorem PLengthsK_eq (n s : ℕ) : PLengthsK n s = PLengths n s := by
  ext L
  constructor
  · rintro ⟨ms, hlen, hrun⟩; exact ⟨ms, hlen, Run_of_RunK hrun⟩
  · rintro ⟨ms, hlen, hrun⟩
    obtain ⟨ms', hlen', hrun'⟩ := RunK_of_Run (sinkPebble_no_ghost n) hrun
    exact ⟨ms', by rw [hlen', hlen], hrun'⟩

/-- **本形式化の 3 つの量は KSS の意味論の量と一致する。**
したがって上界・下界のどちらも KSS の定理として読んでよい。 -/
theorem TUP_eq_K (n s : ℕ) : sInf (UPLengthsK n s) = TUP n s := by
  rw [UPLengthsK_eq]; rfl

theorem TUG_eq_K (n s : ℕ) : sInf (UGLengthsK n s) = TUG n s := by
  rw [UGLengthsK_eq]; rfl

theorem TP_eq_K (n s : ℕ) : sInf (PLengthsK n s) = TP n s := by
  rw [PLengthsK_eq]; rfl

end Spooky
