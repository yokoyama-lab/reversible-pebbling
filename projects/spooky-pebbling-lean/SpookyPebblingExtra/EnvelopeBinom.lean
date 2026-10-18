/-
# 折れ目と係数の二項係数による閉じた形（`s ≥ 3`）

`Envelope.lean` の上包絡 `T_UP(n,s) = max_m (2mn - β_m(s))` の係数 `β_m(s)`（`bb`）と
折れ目 `b_m(s)`（`brk`）は 2 変数の漸化式で定義されている。ここでは `s ≥ 3`・`m ≥ 1` で

* `b_m(s) = C(m+s-2, s-1) + C(m+s-3, s-3) + C(m+s-4, s-3)`
* `β_m(s) + 1 = 2·(C(m+s-2, s) + C(m+s-3, s-2) + C(m+s-4, s-2))`

を示す。`s = u + 3`・`m = t + 1` と置いて自然数の引き算を避ける。
`s = 2` は `brk_base`・`bb_base`（`b_m(2) = m`，`β_{m+1}(2) = m² + m + 3`）がそのまま閉じた形である。

先頭の項 `C(m+s-2, s-1) ~ m^{s-1}/(s-1)!` から，`s` を固定したときの
`T_UP(n,s) ~ (2(s-1)/s)·((s-1)!)^{1/(s-1)}·n^{s/(s-1)}` が出る（漸近の部分は紙の証明。原稿 P1）。
-/
import SpookyPebblingExtra.Envelope

namespace Spooky

/-- `s = 3` の折れ目: `b_{t+1}(3) = C(t+2, 2) + 2`。 -/
theorem brk_s3 : ∀ t, brk (t + 1) 3 = (t + 2).choose 2 + 2
  | 0 => by simp
  | t + 1 => by
      have hstep : brk (t + 1 + 1) (2 + 1) = brk (t + 1) (2 + 1) + brk (t + 1 + 1) 2 :=
        brk_step (m := t + 1) (s := 2) (by omega)
      have hb : brk (t + 1 + 1) 2 = t + 2 := brk_base (by omega)
      have ih := brk_s3 t
      have hp := Nat.choose_succ_succ' (t + 2) 1
      simp only [Nat.choose_one_right, Nat.reduceAdd, Nat.add_assoc] at hp hstep ih hb ⊢
      omega

/-- 折れ目の閉じた形: `b_{t+1}(u+3) = C(t+u+2, u+2) + C(t+u+1, u) + C(t+u, u)`。 -/
theorem brk_choose : ∀ u t,
    brk (t + 1) (u + 3) =
      (t + u + 2).choose (u + 2) + (t + u + 1).choose u + (t + u).choose u := by
  intro u
  induction u with
  | zero =>
      intro t
      simp only [Nat.add_zero, Nat.zero_add, Nat.choose_zero_right]
      rw [brk_s3]
  | succ u ihu =>
      intro t
      induction t with
      | zero =>
          simp only [Nat.zero_add, Nat.choose_self, brk_one]
          rw [show u + 1 + 1 = (u + 1) + 1 from rfl, Nat.choose_succ_self_right]
          omega
      | succ t iht =>
          have hstep : brk (t + 1 + 1) (u + 3 + 1) = brk (t + 1) (u + 3 + 1) + brk (t + 1 + 1) (u + 3) :=
            brk_step (m := t + 1) (s := u + 3) (by omega)
          have hu := ihu (t + 1)
          rw [show u + 1 + 3 = u + 3 + 1 by omega, hstep]
          rw [show u + 3 + 1 = u + 1 + 3 by omega, iht]
          rw [hu]
          -- Pascal 則で 3 項それぞれを分ける
          have p1 : (t + 1 + (u + 1) + 2).choose (u + 1 + 2) =
              (t + (u + 1) + 2).choose (u + 1 + 2) + (t + 1 + u + 2).choose (u + 2) := by
            rw [show t + 1 + (u + 1) + 2 = (t + (u + 1) + 2) + 1 by omega,
              show u + 1 + 2 = (u + 2) + 1 by omega, Nat.choose_succ_succ',
              show t + (u + 1) + 2 = t + 1 + u + 2 by omega]
            omega
          have p2 : (t + 1 + (u + 1) + 1).choose (u + 1) =
              (t + (u + 1) + 1).choose (u + 1) + (t + 1 + u + 1).choose u := by
            rw [show t + 1 + (u + 1) + 1 = (t + (u + 1) + 1) + 1 by omega, Nat.choose_succ_succ',
              show t + (u + 1) + 1 = t + 1 + u + 1 by omega]
            omega
          have p3 : (t + 1 + (u + 1)).choose (u + 1) =
              (t + (u + 1)).choose (u + 1) + (t + 1 + u).choose u := by
            rw [show t + 1 + (u + 1) = (t + (u + 1)) + 1 by omega, Nat.choose_succ_succ',
              show t + (u + 1) = t + 1 + u by omega]
            omega
          rw [p1, p2, p3]
          omega

/-- 係数の閉じた形: `β_{t+1}(u+3) + 1 = 2·(C(t+u+2, u+3) + C(t+u+1, u+1) + C(t+u, u+1))`。 -/
theorem bb_choose (u : ℕ) : ∀ t,
    bb (t + 1) (u + 3) + 1 =
      2 * ((t + u + 2).choose (u + 3) + (t + u + 1).choose (u + 1) + (t + u).choose (u + 1)) := by
  intro t
  induction t with
  | zero =>
      rw [bb_one]
      simp only [Nat.zero_add]
      rw [Nat.choose_eq_zero_of_lt (by omega : u + 2 < u + 3),
        Nat.choose_eq_zero_of_lt (by omega : u < u + 1), Nat.choose_self]
  | succ t iht =>
      have hstep : bb (t + 1 + 1) (u + 3) = bb (t + 1) (u + 3) + 2 * brk (t + 1) (u + 3) :=
        bb_succ_eq_add_brk (t + 1) (by omega) (u + 3) (by omega)
      have hb := brk_choose u t
      have p1 : (t + 1 + u + 2).choose (u + 3) =
          (t + u + 2).choose (u + 2) + (t + u + 2).choose (u + 3) := by
        rw [show t + 1 + u + 2 = (t + u + 2) + 1 by omega, show u + 3 = (u + 2) + 1 by omega,
          Nat.choose_succ_succ']
      have p2 : (t + 1 + u + 1).choose (u + 1) =
          (t + u + 1).choose u + (t + u + 1).choose (u + 1) := by
        rw [show t + 1 + u + 1 = (t + u + 1) + 1 by omega, Nat.choose_succ_succ']
      have p3 : (t + 1 + u).choose (u + 1) = (t + u).choose u + (t + u).choose (u + 1) := by
        rw [show t + 1 + u = (t + u) + 1 by omega, Nat.choose_succ_succ']
      rw [hstep, p1, p2, p3]
      omega

/-- **上包絡の二項係数の形**（`s = u + 3 ≥ 3`・`n ≥ 1`）:
`T_UP(n,s) = max_{m ≥ 1} (2mn + 1 - 2(C(m+s-2,s) + C(m+s-3,s-2) + C(m+s-4,s-2)))` を
「ある `m` で等号，すべての `m` で `≥`」の形で述べる（`m = t + 1`）。 -/
theorem TUP_upper_envelope_choose {u n : ℕ} (hn : 1 ≤ n) :
    (∃ t, TUP n (u + 3) +
        2 * ((t + u + 2).choose (u + 3) + (t + u + 1).choose (u + 1) + (t + u).choose (u + 1)) =
        2 * (t + 1) * n + 1) ∧
      (∀ t, 2 * (t + 1) * n + 1 ≤ TUP n (u + 3) +
        2 * ((t + u + 2).choose (u + 3) + (t + u + 1).choose (u + 1) + (t + u).choose (u + 1))) := by
  obtain ⟨⟨m, hm, heq⟩, hall⟩ := TUP_upper_envelope (s := u + 3) (by omega) hn
  refine ⟨⟨m - 1, ?_⟩, fun t => ?_⟩
  · have h := bb_choose u (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    rw [← h, Nat.sub_add_cancel hm]
    omega
  · have h := bb_choose u t
    have := hall (t + 1) (by omega)
    omega

/-! ## 具体値との突き合わせ（原稿 P1 の表 2 の `s = 4` の行と図 1 の `β`） -/

example : brk 1 4 = 4 ∧ brk 2 4 = 9 ∧ brk 3 4 = 17 ∧ brk 4 4 = 29 ∧ brk 5 4 = 46 ∧ brk 6 4 = 69 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [brk_choose 1] <;> decide

example : bb 2 4 = 9 ∧ bb 3 4 = 27 ∧ bb 4 4 = 61 := by
  refine ⟨?_, ?_, ?_⟩
  · have := bb_choose 1 1; simp [Nat.choose] at this; omega
  · have := bb_choose 1 2; simp [Nat.choose] at this; omega
  · have := bb_choose 1 3; simp [Nat.choose] at this; omega

end Spooky
