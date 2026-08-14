/-
  # 凍結された親層から触れる子の個数 — **run 数がちょうどの差**（2026-08-15）

  ## 何のための定理か

  `docs/35_pyramid_lower_bound_gap.md` の負の結果を厳密にする。

  ピラミッドの下界を「各層の**個数**だけを持つ抽象」で出すと、$h \le 12$ では
  実測とタイトだが $h \ge 13$ で離れ、隙間は単調に開く（$h=18$ で 50 対 58）。
  独立な 2 つの強化（凍結された親の互いに素性・区間版の制約）を試したが
  **どちらも改善 0 件**であった。

  本ファイルはその理由を定理にする。層 $k-1$ が集合 $S$ で凍結されている間に
  **触れる（＝変化しうる）層 $k$ の頂点の個数は、ちょうど $|S| - \mathrm{runs}(S)$**
  である（`touchable_card_add_runs`）。ここで $\mathrm{runs}(S)$ は $S$ を
  連続塊に分けたときの塊の個数。

  個数だけの抽象が使えるのは $\mathrm{runs}(S) \ge 1$（`one_le_runs`）だけなので、
  抽象が得る上界は $|S| - 1$ に留まる。**両者の差がそのまま隙間である。**

  ## 主定理

  | 定理 | 内容 |
  |---|---|
  | `touchable_card_add_runs` | 触れる子の個数 $+$ $\mathrm{runs}(S) = |S|$ |
  | `one_le_runs` | $S \ne \emptyset \Rightarrow \mathrm{runs}(S) \ge 1$（抽象が知る唯一の事実） |
  | `runs_eq_card_iff` | $\mathrm{runs}(S) = |S| \iff$ 触れる子が 0（$S$ が孤立点のみ） |
  | `changed_card_add_runs_le` | ペブリングへの適用: 変化した子の個数 $+ \mathrm{runs}(P \cap Q) \le |P \cap Q|$ |
  | `runs_can_exceed_one` | $\mathrm{runs}$ は $|S|$ から決まらない（同じ $|S|$ で 1 にも 3 にもなる） |

  最後の 1 本が**個数だけの抽象では原理的に埋まらない**ことの証拠である。
-/
import Revgarbage.ParPebbleDAG
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

namespace ParPebbleDAG

/-- `Changed` は Finset の所属で書かれているので決定可能（`filter` に渡すために要る）。 -/
instance decidableChanged (P Q : Finset ℕ) : DecidablePred (Changed P Q) := fun v => by
  unfold Changed; infer_instance

/-! ## 1. run 数 -/

/-- `S` の**右端**の個数。連続塊（run）は右端をちょうど 1 つ持つので、これが run の個数。 -/
def runs (S : Finset ℕ) : ℕ := (S.filter (fun j => j + 1 ∉ S)).card

/-- `S` の中で**隣接ペアの左側**になれる要素。ピラミッドではこれが
    「親が両方 `S` に居る子」と 1 対 1 に対応する。 -/
def touchable (S : Finset ℕ) : Finset ℕ := S.filter (fun j => j + 1 ∈ S)

/-- **触れる子の個数 ＋ run 数 ＝ |S|。**
    `S` の各要素は「右隣も `S` に居る」か「居ない」かのどちらかちょうど一方。 -/
theorem touchable_card_add_runs (S : Finset ℕ) :
    (touchable S).card + runs S = S.card := by
  unfold touchable runs
  exact Finset.card_filter_add_card_filter_not _

/-- 非空なら run は 1 つ以上ある（最大元は必ず右端）。
    **個数だけの抽象が使えるのはこの事実だけ**である。 -/
theorem one_le_runs {S : Finset ℕ} (hS : S.Nonempty) : 1 ≤ runs S := by
  unfold runs
  rw [Finset.one_le_card]
  refine ⟨S.max' hS, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨S.max'_mem hS, ?_⟩
  intro hmem
  have := S.le_max' _ hmem
  omega

/-- 抽象が得る上界: 触れる子は高々 `|S| - 1`。 -/
theorem touchable_card_le {S : Finset ℕ} (hS : S.Nonempty) :
    (touchable S).card ≤ S.card - 1 := by
  have h := touchable_card_add_runs S
  have := one_le_runs hS
  omega

/-- 触れる子が 0 であることと、`S` が孤立点だけからなることは同値。 -/
theorem runs_eq_card_iff {S : Finset ℕ} : runs S = S.card ↔ touchable S = ∅ := by
  constructor
  · intro h
    have hc := touchable_card_add_runs S
    exact Finset.card_eq_zero.mp (by omega)
  · intro h
    have hc := touchable_card_add_runs S
    rw [h] at hc
    simpa using hc

/-! ## 2. ペブリングへの適用 -/

/-- **凍結された親から触れる子の個数の上界（鋭い形）。**

    `P → Q` が合法で、`C` の各頂点 `v` が親として `f v` と `f v + 1` を持ち
    （ピラミッドの隣接ペア）、`f` が `C` 上で単射なら、
    `C` の中で変化した頂点の個数は `touchable (P ∩ Q)` の大きさ以下。

    `LegalStep` は「変化した頂点のすべての親が前後の両方に居る」なので、
    変化した `v` について `f v, f v + 1 ∈ P ∩ Q`、すなわち `f v ∈ touchable (P ∩ Q)`。 -/
theorem changed_card_le_touchable
    {pa : ℕ → Finset ℕ} {P Q C : Finset ℕ} {f : ℕ → ℕ}
    (hlegal : LegalStep pa P Q)
    (hpa : ∀ v ∈ C, f v ∈ pa v ∧ f v + 1 ∈ pa v)
    (hinj : ∀ v ∈ C, ∀ w ∈ C, f v = f w → v = w) :
    (C.filter (fun v => Changed P Q v)).card ≤ (touchable (P ∩ Q)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    -- `hv` は Set への強制つき（`↑(C.filter …)`）なので先にほどく
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv
    obtain ⟨hvC, hvch⟩ := hv
    obtain ⟨hf1, hf2⟩ := hpa v hvC
    have h1 := hlegal v hvch _ hf1
    have h2 := hlegal v hvch _ hf2
    simp only [Finset.mem_coe, touchable, Finset.mem_filter, Finset.mem_inter]
    exact ⟨⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩⟩
  · intro v hv w hw hfe
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
    exact hinj v hv.1 w hw.1 hfe

/-- **主定理**: 変化した子の個数 ＋ 凍結部分の run 数 ≤ 凍結部分の大きさ。

    個数だけの抽象は `runs ≥ 1` しか使えないので `変化数 ≤ |P ∩ Q| - 1` までしか出せない。
    **run 数が 2 以上になる配置では、この定理のほうが真に強い。** -/
theorem changed_card_add_runs_le
    {pa : ℕ → Finset ℕ} {P Q C : Finset ℕ} {f : ℕ → ℕ}
    (hlegal : LegalStep pa P Q)
    (hpa : ∀ v ∈ C, f v ∈ pa v ∧ f v + 1 ∈ pa v)
    (hinj : ∀ v ∈ C, ∀ w ∈ C, f v = f w → v = w) :
    (C.filter (fun v => Changed P Q v)).card + runs (P ∩ Q) ≤ (P ∩ Q).card := by
  have h := changed_card_le_touchable hlegal hpa hinj
  have he := touchable_card_add_runs (P ∩ Q)
  omega

/-! ## 3. run 数は個数から決まらない — 抽象の限界の証拠 -/

/-- 同じ大きさ 3 でも run が 1 つの集合。 -/
example : runs {0, 1, 2} = 1 := by decide

/-- 同じ大きさ 3 で run が 3 つの集合。 -/
example : runs {0, 2, 4} = 3 := by decide

/-- **`runs` は `card` の関数ではない。**
    大きさが等しい 2 つの集合で `runs` が異なるので、
    **各層の個数だけを状態に持つ抽象は `runs` を復元できない**。
    これが `docs/35` の隙間が個数の抽象で埋まらない理由である。 -/
theorem runs_not_determined_by_card :
    ∃ S T : Finset ℕ, S.card = T.card ∧ runs S ≠ runs T := by
  refine ⟨{0, 1, 2}, {0, 2, 4}, by decide, by decide⟩

/-- 触れる子の個数も `card` の関数ではない（上の対で 2 と 0）。 -/
theorem touchable_not_determined_by_card :
    ∃ S T : Finset ℕ, S.card = T.card ∧ (touchable S).card ≠ (touchable T).card := by
  refine ⟨{0, 1, 2}, {0, 2, 4}, by decide, by decide⟩

/-- 抽象が使う上界 `|S| - 1` は、run が 2 つ以上あるとき**真に緩い**。
    `S = {0, 2, 4}` では触れる子は 0 個だが、抽象は 2 個まで許してしまう。 -/
theorem abstraction_slack_example :
    (touchable {0, 2, 4}).card = 0 ∧ ({0, 2, 4} : Finset ℕ).card - 1 = 2 := by decide

end ParPebbleDAG
