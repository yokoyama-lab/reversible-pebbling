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

/-! ## ビット積の畳み込み（2^{j/2^m} の上界、設計書 §23）

根の鎖 `rs`（長さ m）とビット列 `bs`（同じ長さ、先頭が重み 2^{-1}）から、立っているビットの根を
切り上げの積 `mulUp` で掛けていく。指数は `expBits bs`（`bs` を上位ビットから読んだ 2 進数）で、
健全性は `ubBits_sound`: 結果を 2^k で割った値は 2^{expBits bs / 2^m} 以上。 -/

/-- 切り上げの積 ⌈A·B / 2^k⌉。 -/
def mulUp (k A B : Nat) : Nat := (A * B + (2 ^ k - 1)) / 2 ^ k

theorem mulUp_spec (k A B : Nat) : A * B ≤ mulUp k A B * 2 ^ k := by
  unfold mulUp
  have hpos := Nat.two_pow_pos k
  have h1 := Nat.div_add_mod (A * B + (2 ^ k - 1)) (2 ^ k)
  have h2 := Nat.mod_lt (A * B + (2 ^ k - 1)) hpos
  rw [Nat.mul_comm ((A * B + (2 ^ k - 1)) / 2 ^ k)]
  generalize 2 ^ k * ((A * B + (2 ^ k - 1)) / 2 ^ k) = t at *
  generalize (A * B + (2 ^ k - 1)) % 2 ^ k = s at *
  generalize A * B = x at *
  generalize 2 ^ k = d at *
  omega

/-- `acc` から出発し、`b = true` の位置の根だけを切り上げで掛ける。 -/
def ubBits (k : Nat) : Nat → List Nat → List Bool → Nat
  | acc, r :: rs, b :: bs => ubBits k (if b then mulUp k acc r else acc) rs bs
  | acc, _, _ => acc

/-- ビット列を上位ビットから読んだ 2 進数。 -/
def expBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + expBits bs

/-- 一般形: 出発点 `p` が 2^{1/N} の上界で、`acc` が 2^{e/(N·2^L)} の上界なら、
畳み込みの結果は 2^{(e + expBits bs)/(N·2^L)} の上界（L = rs.length）。 -/
theorem ubBits_sound_gen (k : Nat) : ∀ (rs : List Nat) (bs : List Bool) (N p acc e : Nat),
    bs.length = rs.length →
    2 ^ (1 + k * N) ≤ p ^ N → chkRoots k p rs = true →
    2 ^ (e + k * (N * 2 ^ rs.length)) ≤ acc ^ (N * 2 ^ rs.length) →
    2 ^ (e + expBits bs + k * (N * 2 ^ rs.length)) ≤ (ubBits k acc rs bs) ^ (N * 2 ^ rs.length)
  | [], bs, _, _, acc, e, hl, _, _, ha => by
    have hb : bs = [] := List.eq_nil_of_length_eq_zero hl
    subst hb
    simp only [expBits, ubBits, Nat.add_zero]
    exact ha
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl
  | r :: rs, b :: bs, N, p, acc, e, hl, hp, hc, ha => by
    simp only [chkRoots, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hl' : bs.length = rs.length := by simpa using hl
    have hr : 2 ^ (1 + k * (2 * N)) ≤ r ^ (2 * N) := sqrtStep k N 1 p r hp hc.1
    have hD : N * 2 ^ (r :: rs).length = 2 * N * 2 ^ rs.length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm (2 ^ rs.length) 2, ← Nat.mul_assoc,
        Nat.mul_comm N 2]
    rw [hD] at ha ⊢
    have hrL := powLift k (2 * N) (2 ^ rs.length) 1 r hr
    rw [Nat.one_mul] at hrL
    have hstep : 2 ^ ((e + (if b then 2 ^ rs.length else 0)) + k * (2 * N * 2 ^ rs.length)) ≤
        (if b then mulUp k acc r else acc) ^ (2 * N * 2 ^ rs.length) := by
      cases b with
      | true =>
        simp only [if_true]
        exact mulStep k _ e (2 ^ rs.length) acc r (mulUp k acc r) ha hrL (mulUp_spec k acc r)
      | false =>
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        exact ha
    have ih := ubBits_sound_gen k rs bs (2 * N) r _ _ hl' hr hc.2 hstep
    simp only [ubBits, expBits]
    rw [← Nat.add_assoc, hl']
    exact ih

/-- 出発点 `2^(k+1)`（値 2）の鎖と、出発値 `2^k`（値 1 = 2^0）から:
`ubBits k (2^k) rs bs / 2^k ≥ 2^{expBits bs / 2^m}`（m = rs.length）。 -/
theorem ubBits_sound (k : Nat) (rs : List Nat) (bs : List Bool) (hl : bs.length = rs.length)
    (hc : chkRoots k (2 ^ (k + 1)) rs = true) :
    2 ^ (expBits bs + k * 2 ^ rs.length) ≤ (ubBits k (2 ^ k) rs bs) ^ (2 ^ rs.length) := by
  have h0 : 2 ^ (1 + k * 1) ≤ (2 ^ (k + 1)) ^ 1 := by
    rw [Nat.pow_one, Nat.mul_one, Nat.add_comm]
    exact Nat.le_refl _
  have ha : 2 ^ (0 + k * (1 * 2 ^ rs.length)) ≤ (2 ^ k) ^ (1 * 2 ^ rs.length) := by
    rw [Nat.zero_add, Nat.one_mul, ← Nat.pow_mul]
    exact Nat.le_refl _
  have h := ubBits_sound_gen k rs bs 1 (2 ^ (k + 1)) (2 ^ k) 0 hl h0 hc ha
  rw [Nat.one_mul, Nat.zero_add] at h
  exact h

/-- `j` の下位 `m` ビットを上位から並べたもの（生成器。健全性には使わない）。 -/
def bitsMSB : Nat → Nat → List Bool
  | 0, _ => []
  | m + 1, j => (j / 2 ^ m % 2 == 1) :: bitsMSB m j

/-! ## 例（k = 8 は kernel の decide、k = 64・m = 30 は本番の精度） -/

/-- 2^{6/8} = 2^{3/4}: 363·305 を切り上げて 433（上の `mulStep` の例と同じ値）。 -/
example : ubBits 8 (2 ^ 8) [363, 305, 280] [true, true, false] = 433 := by decide

example : 2 ^ (expBits [true, true, false] + 8 * 2 ^ 3) ≤
    (ubBits 8 (2 ^ 8) [363, 305, 280] [true, true, false]) ^ (2 ^ 3) :=
  ubBits_sound 8 [363, 305, 280] [true, true, false] rfl (by decide)

/-- k = 64・m = 30 の根の鎖（m89 の `gen_roots` の出力。ここでは信頼せず `chkRoots` で受理を確かめる）。 -/
def roots64 : List Nat :=
  -- GENERATED roots64 BEGIN
  [26087635650665564425, 21936999301089678047, 20116317054877281743, 19263451207323153963,
   18850675170876015536, 18647615946650685160, 18546908069882975961, 18496758270674070882,
   18471734244850835107, 18459234930309000273, 18452988445124272034, 18449865995240371899,
   18448304968436414830, 18447524504564044947, 18447134285009651016, 18446939178327825413,
   18446841625760745903, 18446792849670663278, 18446768461673986098, 18446756267687738523,
   18446750170697637487, 18446747122203342656, 18446745597956384163, 18446744835832952147,
   18446744454771247946, 18446744264240398798, 18446744168974974962, 18446744121342263228,
   18446744097525907407, 18446744085617729508]
  -- GENERATED roots64 END

theorem roots64_ok : chkRoots 64 (2 ^ 65) roots64 = true := by decide

theorem roots64_len : roots64.length = 30 := by decide

/-- 本番の精度での上界の例: 2^{j/2^30} ≤ P/2^64（P は Python の `ub_dyadic` と一致すること）。 -/
-- GENERATED ub64 BEGIN
example : ubBits 64 (2 ^ 64) roots64 (bitsMSB 30 1073741823) = 36893488123602747546 := by decide
example : ubBits 64 (2 ^ 64) roots64 (bitsMSB 30 715827882) = 29282380935392655592 := by decide
example : ubBits 64 (2 ^ 64) roots64 (bitsMSB 30 123456789) = 19977060175509150989 := by decide
-- GENERATED ub64 END

example : expBits (bitsMSB 30 123456789) = 123456789 := by decide

/-- 一般の j に対する本番規模の健全性（`roots64_ok` を差し込むだけ）。 -/
theorem ub64_sound (bs : List Bool) (hl : bs.length = 30) :
    2 ^ (expBits bs + 64 * 2 ^ 30) ≤ (ubBits 64 (2 ^ 64) roots64 bs) ^ (2 ^ 30) := by
  have h := ubBits_sound 64 roots64 bs (by rw [hl, roots64_len]) roots64_ok
  rw [roots64_len] at h
  exact h

/-! ## 有理指数への持ち上げ（設計書 §24）

E = p/q（cfg 節点の補間で出る有理数）を `T = ⌈p·2^m/q⌉` で n + j/2^m（T = n·2^m + j）へ切り上げ、
2^{j/2^m} の上界 A/2^k に 2^n を掛けて 2^{p/q} の上界を得る。 -/

/-- ⌈p·2^m / q⌉。 -/
def ceilDy (m p q : Nat) : Nat := (p * 2 ^ m + (q - 1)) / q

theorem ceilDy_spec (m p q : Nat) (hq : 0 < q) : p * 2 ^ m ≤ ceilDy m p q * q := by
  unfold ceilDy
  have h1 := Nat.div_add_mod (p * 2 ^ m + (q - 1)) q
  have h2 := Nat.mod_lt (p * 2 ^ m + (q - 1)) hq
  rw [Nat.mul_comm ((p * 2 ^ m + (q - 1)) / q)]
  generalize q * ((p * 2 ^ m + (q - 1)) / q) = t at *
  generalize (p * 2 ^ m + (q - 1)) % q = s at *
  generalize p * 2 ^ m = x at *
  omega

/-- 結合: p/q ≤ (n·2^m + j)/2^m と 2^{j/2^m} ≤ A/2^k から 2^{p/q} ≤ 2^n·A/2^k。 -/
theorem ratLift (k m p q n j A : Nat)
    (hT : p * 2 ^ m ≤ (n * 2 ^ m + j) * q)
    (hA : 2 ^ (j + k * 2 ^ m) ≤ A ^ 2 ^ m) :
    2 ^ (p + k * q) ≤ (2 ^ n * A) ^ q := by
  have hM : 0 < 2 ^ m := Nat.two_pow_pos m
  -- 両辺の 2^m 乗で比べる
  have key : (2 ^ (p + k * q)) ^ 2 ^ m ≤ ((2 ^ n * A) ^ q) ^ 2 ^ m := by
    have e1 : (2 ^ (p + k * q)) ^ 2 ^ m = 2 ^ (p * 2 ^ m + k * q * 2 ^ m) := by
      rw [← Nat.pow_mul, Nat.add_mul]
    have e2 : ((2 ^ n * A) ^ q) ^ 2 ^ m = 2 ^ (n * 2 ^ m * q) * (A ^ 2 ^ m) ^ q := by
      rw [← Nat.pow_mul, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
      rw [Nat.mul_comm q (2 ^ m), ← Nat.mul_assoc]
    rw [e1, e2]
    have s1 : 2 ^ (p * 2 ^ m + k * q * 2 ^ m) ≤ 2 ^ (n * 2 ^ m * q + (j + k * 2 ^ m) * q) := by
      apply Nat.pow_le_pow_right (by decide)
      have h0 : (n * 2 ^ m + j) * q = n * 2 ^ m * q + j * q := Nat.add_mul _ _ _
      have h1 : k * q * 2 ^ m = k * 2 ^ m * q := by
        rw [Nat.mul_assoc, Nat.mul_comm q, ← Nat.mul_assoc]
      rw [Nat.add_mul j (k * 2 ^ m) q, h1]
      rw [h0] at hT
      generalize p * 2 ^ m = a at *
      generalize n * 2 ^ m * q = b at *
      generalize j * q = c at *
      generalize k * 2 ^ m * q = d at *
      omega
    have s2 : 2 ^ (n * 2 ^ m * q + (j + k * 2 ^ m) * q) ≤ 2 ^ (n * 2 ^ m * q) * (A ^ 2 ^ m) ^ q := by
      rw [Nat.pow_add, Nat.pow_mul _ (j + k * 2 ^ m) q]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA q)
    exact Nat.le_trans s1 s2
  -- x^M ≤ y^M（M > 0）なら x ≤ y
  apply Classical.byContradiction
  intro hlt
  have hlt' : ((2 ^ n * A) ^ q) < 2 ^ (p + k * q) := Nat.lt_of_not_le hlt
  have := Nat.pow_lt_pow_left hlt' (Nat.pos_iff_ne_zero.mp hM)
  exact absurd key (Nat.not_le_of_lt this)

theorem bitsMSB_length : ∀ m j, (bitsMSB m j).length = m
  | 0, _ => rfl
  | m + 1, j => by simp only [bitsMSB, List.length_cons, bitsMSB_length m j]

theorem expBits_bitsMSB : ∀ m j, expBits (bitsMSB m j) = j % 2 ^ m
  | 0, j => by simp [bitsMSB, expBits, Nat.mod_one]
  | m + 1, j => by
    simp only [bitsMSB, expBits, bitsMSB_length, expBits_bitsMSB m j]
    rw [Nat.mod_pow_succ]
    have h := Nat.mod_lt (j / 2 ^ m) (show 0 < 2 by decide)
    generalize j / 2 ^ m % 2 = b at *
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> simp [Nat.add_comm]

/-- 本番規模（k = 64・m = 30）: 任意の有理 p/q（q > 0）について、T = ⌈p·2^30/q⌉ を
n = T / 2^30・j = T % 2^30 に分けると 2^{p/q} ≤ 2^n · ubBits(j) / 2^64。 -/
theorem ub64_rat (p q : Nat) (hq : 0 < q) :
    2 ^ (p + 64 * q) ≤
      (2 ^ (ceilDy 30 p q / 2 ^ 30) *
        ubBits 64 (2 ^ 64) roots64 (bitsMSB 30 (ceilDy 30 p q % 2 ^ 30))) ^ q := by
  have hT := ceilDy_spec 30 p q hq
  rw [← Nat.div_add_mod (ceilDy 30 p q) (2 ^ 30), Nat.mul_comm (2 ^ 30)] at hT
  have hA := ub64_sound (bitsMSB 30 (ceilDy 30 p q % 2 ^ 30)) (bitsMSB_length _ _)
  rw [expBits_bitsMSB, Nat.mod_mod] at hA
  exact ratLift 64 30 p q _ _ _ hT hA

/-- 小さい例（k = 8・m = 3）: 2^{7/4} ≤ 2^1 · 433 / 2^8（T = ⌈7·8/4⌉ = 14 = 1·8 + 6）。 -/
example : ceilDy 3 7 4 = 14 := by decide
example : 2 ^ (7 + 8 * 4) ≤ (2 ^ 1 * ubBits 8 (2 ^ 8) [363, 305, 280] (bitsMSB 3 6)) ^ 4 := by decide

end RevPebbling.Exp2Dyadic

#print axioms RevPebbling.Exp2Dyadic.chkRoots_sound
#print axioms RevPebbling.Exp2Dyadic.roots_sound
#print axioms RevPebbling.Exp2Dyadic.mulStep
#print axioms RevPebbling.Exp2Dyadic.ubBits_sound
#print axioms RevPebbling.Exp2Dyadic.ub64_sound
#print axioms RevPebbling.Exp2Dyadic.ceilDy_spec
#print axioms RevPebbling.Exp2Dyadic.ratLift
#print axioms RevPebbling.Exp2Dyadic.ub64_rat
