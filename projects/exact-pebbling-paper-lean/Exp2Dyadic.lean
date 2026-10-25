/-!
# 2^r の dyadic 上界（(d) Ψ_{329} ≤ X_{329} の比較に要る部品、設計書 §21–22）

固定小数点 `k` ビットで、値 `A` は実数 `A / 2^k` を表す。「`A/2^k ≥ 2^{a/N}`」を
**Nat の不等式 `2^(a + k*N) ≤ A^N`** で述べる（両辺を N 乗して 2^{kN} を払っただけ）。
実数は使わない。

- `chkRoots`: 平方根の鎖 `R_1, R_2, …`（`R_i / 2^k ≥ 2^{2^{-i}}`）の検査器。
  1 歩の検査は `R_{i-1} * 2^k ≤ R_i * R_i` だけ。健全性は `chkRoots_sound`。
- `mulStep`: 上界 2 つの積を切り上げで k ビットに戻しても上界のまま。
- `powLift`: 指数の分母を揃える（N → N*M）。

dyadic 指数 j/2^m の上界は、j の立っているビットに対応する根を `mulStep` で掛け合わせて得る。
生成器（根の値を出すもの）は信頼しない。Python 側（m89）が出し、ここの検査器が受理したものだけを使う。
-/

namespace RevPebbling.Exp2Dyadic

/-- 平方根の 1 歩: `p` が 2^{e/N} の上界なら、`p * 2^k ≤ r * r` を満たす `r` は 2^{e/(2N)} の上界。 -/
theorem sqrtStep (k N e p r : Nat) (hp : 2 ^ (e + k * N) ≤ p ^ N)
    (h : p * 2 ^ k ≤ r * r) : 2 ^ (e + k * (2 * N)) ≤ r ^ (2 * N) := by
  have h4 : 2 ^ (e + k * (2 * N)) = 2 ^ (e + k * N) * 2 ^ (k * N) := by
    rw [← Nat.pow_add, Nat.mul_left_comm k 2 N]
    congr 1
    omega
  calc 2 ^ (e + k * (2 * N)) = 2 ^ (e + k * N) * 2 ^ (k * N) := h4
    _ ≤ p ^ N * 2 ^ (k * N) := Nat.mul_le_mul_right _ hp
    _ = (p * 2 ^ k) ^ N := by rw [Nat.mul_pow, ← Nat.pow_mul]
    _ ≤ (r * r) ^ N := Nat.pow_le_pow_left h N
    _ = r ^ (2 * N) := by rw [Nat.pow_mul, Nat.pow_two]

/-- 積の 1 歩: `A`・`B` が 2^{a/N}・2^{b/N} の上界で `A * B ≤ P * 2^k`（切り上げ）なら、
`P` は 2^{(a+b)/N} の上界。 -/
theorem mulStep (k N a b A B P : Nat) (hA : 2 ^ (a + k * N) ≤ A ^ N)
    (hB : 2 ^ (b + k * N) ≤ B ^ N) (h : A * B ≤ P * 2 ^ k) :
    2 ^ (a + b + k * N) ≤ P ^ N := by
  have key : 2 ^ (a + b + k * N) * 2 ^ (k * N) ≤ P ^ N * 2 ^ (k * N) :=
    calc 2 ^ (a + b + k * N) * 2 ^ (k * N) = 2 ^ (a + k * N) * 2 ^ (b + k * N) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
      _ ≤ A ^ N * B ^ N := Nat.mul_le_mul hA hB
      _ = (A * B) ^ N := (Nat.mul_pow _ _ _).symm
      _ ≤ (P * 2 ^ k) ^ N := Nat.pow_le_pow_left h N
      _ = P ^ N * 2 ^ (k * N) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  exact Nat.le_of_mul_le_mul_right key (Nat.two_pow_pos (k * N))

/-- 分母を揃える: 2^{a/N} の上界は 2^{aM/(NM)} の上界でもある。 -/
theorem powLift (k N M a A : Nat) (hA : 2 ^ (a + k * N) ≤ A ^ N) :
    2 ^ (a * M + k * (N * M)) ≤ A ^ (N * M) := by
  have h := Nat.pow_le_pow_left hA M
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h
  have e : (a + k * N) * M = a * M + k * (N * M) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [e] at h
  exact h

/-! ## 平方根の鎖の検査器 -/

/-- `p` は直前の根。各 `r` について `p * 2^k ≤ r * r` を確かめて進む。 -/
def chkRoots (k : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | p, r :: rs => decide (p * 2 ^ k ≤ r * r) && chkRoots k r rs

/-- 健全性: 出発点 `p` が 2^{1/N} の上界なら、受理された鎖の i 番目（0 起点）は
2^{1/(N·2^{i+1})} の上界。 -/
theorem chkRoots_sound (k : Nat) : ∀ (rs : List Nat) (N p : Nat),
    2 ^ (1 + k * N) ≤ p ^ N → chkRoots k p rs = true →
    ∀ (i : Nat) (hi : i < rs.length),
      2 ^ (1 + k * (N * 2 ^ (i + 1))) ≤ rs[i] ^ (N * 2 ^ (i + 1))
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r :: rs, N, p, hp, hc, i, hi => by
    simp only [chkRoots, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hr : 2 ^ (1 + k * (2 * N)) ≤ r ^ (2 * N) := sqrtStep k N 1 p r hp hc.1
    cases i with
    | zero =>
      have e : N * 2 ^ (0 + 1) = 2 * N := by rw [Nat.zero_add, Nat.pow_one, Nat.mul_comm]
      simp only [List.getElem_cons_zero]
      rw [e]
      exact hr
    | succ i =>
      have hi' : i < rs.length := by simp at hi; omega
      have ih := chkRoots_sound k rs (2 * N) r hr hc.2 i hi'
      have e : N * 2 ^ (i + 1 + 1) = 2 * N * 2 ^ (i + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ (i + 1)) 2, ← Nat.mul_assoc, Nat.mul_comm N 2]
      simp only [List.getElem_cons_succ]
      rw [e]
      exact ih

/-- 出発点 `2^(k+1)`（値 2 = 2^{1/1}）から始めた鎖: i 番目は 2^{2^{-(i+1)}} の上界。 -/
theorem roots_sound (k : Nat) (rs : List Nat) (hc : chkRoots k (2 ^ (k + 1)) rs = true)
    (i : Nat) (hi : i < rs.length) :
    2 ^ (1 + k * 2 ^ (i + 1)) ≤ rs[i] ^ (2 ^ (i + 1)) := by
  have h0 : 2 ^ (1 + k * 1) ≤ (2 ^ (k + 1)) ^ 1 := by
    rw [Nat.pow_one, Nat.mul_one, Nat.add_comm]
    exact Nat.le_refl _
  have := chkRoots_sound k rs 1 (2 ^ (k + 1)) h0 hc i hi
  rw [Nat.one_mul] at this
  exact this

/-! ## 小さな固定値の例（k = 8、kernel の decide） -/

/-- 256·2^{1/2} ≈ 362.04, 256·2^{1/4} ≈ 304.44, 256·2^{1/8} ≈ 279.17 の切り上げ側。 -/
example : chkRoots 8 (2 ^ 9) [363, 305, 280] = true := by decide

/-- 根 1 つ目を 1 下げる（362² = 131044 < 512·256 = 131072）と落ちる。 -/
example : chkRoots 8 (2 ^ 9) [362, 305, 280] = false := by decide

/-- 2^{3/4} の上界: 根 2^{1/2}（363）と 2^{1/4}（305）の積を切り上げる。
363·305 = 110715 ≤ 433·256 = 110848。 -/
example : 2 ^ (3 + 8 * 4) ≤ 433 ^ 4 := by
  have h1 := roots_sound 8 [363, 305, 280] (by decide) 0 (by decide)
  have h2 := roots_sound 8 [363, 305, 280] (by decide) 1 (by decide)
  have h1' := powLift 8 2 2 1 363 h1
  exact mulStep 8 4 2 1 363 305 433 h1' h2 (by decide)

end RevPebbling.Exp2Dyadic

#print axioms RevPebbling.Exp2Dyadic.chkRoots_sound
#print axioms RevPebbling.Exp2Dyadic.roots_sound
#print axioms RevPebbling.Exp2Dyadic.mulStep
