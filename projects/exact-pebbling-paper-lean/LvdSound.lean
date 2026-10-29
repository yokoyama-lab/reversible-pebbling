import lean.XLiftLvd

/-!
# 証明書指数 ℓ の健全性（gv ≤ 2^{ℓ/R} の受け渡し。設計書 §27、m94）

`lean/PsiCheckProd.lean` の `psi329_le` は、点の指数 ℓ（分母 R = 2048）で Ψ_{329}(2^{ℓ/R}) ≤ X を言う。
これを格子の値 gv で読むには gv ≤ 2^{ℓ/R}（= gv^R ≤ 2^ℓ）が要る。ここではそれを出す。

* `lvdCert_sound`: 検査器 `lvdCert` が真なら、疎な点ごとに g[i]^(2^k) ≤ 2^n（**一般の証明**）。
* `ellOf_sound`: 疎な点の証明書が健全なら、`ellOf` の ℓ について g^2048 ≤ 2^ℓ。
  密な点（`none`）では g < 2^{log2 g + 1} から（**一般の証明**）。
* `prod_ell_cert`: 本番格子 `buildGridLvd 4096 128 11 122` の全点で g^2048 ≤ 2^{ℓ}。
  一般の補題を `prod_lvd_cert`（m81、`native_decide`＝**有界な機械検査**）に当てたもの。

`ellOf` は `PsiCheckProd.lean` の定義の写し（そちらは 1 時間のビルドなので import しない）。
本文の一致は `scripts/probe_brw/m94_lvd_sound.py` の G1 が文字列で検査する。
-/

namespace RevPebbling.LvdSound

open RevPebbling.XLiftGrid RevPebbling.XLiftLvd

/-- 点の指数 ℓ（分母 R = 2048）。密な点は v < 2^{bit_length} なので bit_length·R。 -/
def ellOf (g : Nat) : Option Nat → Nat
  | some n => n
  | none => (Nat.log2 g + 1) * 2048

/-- `lvdCert` が受理すれば、範囲内の疎な点ごとに g[i]^(2^k) ≤ 2^n。 -/
theorem lvdCert_sound (k : Nat) (g : Array Nat) (lv : Array (Option Nat))
    (h : lvdCert k g lv = true) (i n : Nat) (hi : i < g.size) (hn : lv.getD i none = some n) :
    g.getD i 0 ^ (2 ^ k) ≤ 2 ^ n := by
  unfold lvdCert at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 i hi
  rw [hn] at this
  simpa using this

/-- 密な点の指数: g^2048 ≤ 2^{(log2 g + 1)·2048}。 -/
theorem dense_ell (g : Nat) : g ^ 2048 ≤ 2 ^ ((Nat.log2 g + 1) * 2048) := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self)) 2048

/-- 疎な点の証明書が健全なら、`ellOf` の指数は g ≤ 2^{ℓ/2048} の証明書になる。 -/
theorem ellOf_sound (g : Nat) (o : Option Nat) (hs : ∀ n, o = some n → g ^ 2048 ≤ 2 ^ n) :
    g ^ 2048 ≤ 2 ^ ellOf g o := by
  cases o with
  | none => exact dense_ell g
  | some n => exact hs n rfl

/-- 本番格子の全点で g^2048 ≤ 2^{ℓ}（`prod_lvd_cert` は native_decide＝有界な機械検査）。 -/
theorem prod_ell_cert (i : Nat) (hi : i < (buildGridLvd 4096 128 11 122).1.size) :
    (buildGridLvd 4096 128 11 122).1.getD i 0 ^ 2048 ≤
      2 ^ ellOf ((buildGridLvd 4096 128 11 122).1.getD i 0) ((buildGridLvd 4096 128 11 122).2.getD i none) :=
  ellOf_sound _ _ fun n hn => lvdCert_sound 11 _ _ prod_lvd_cert i n hi hn

/-- 小さな格子（`tiny_lvd` と同じ）でも同じ形で出る。kernel の decide で検算。 -/
example : lvdCert 2 (buildGridLvd 4 128 2 5).1 (buildGridLvd 4 128 2 5).2 = true := by decide +kernel

end RevPebbling.LvdSound

#print axioms RevPebbling.LvdSound.lvdCert_sound
#print axioms RevPebbling.LvdSound.ellOf_sound
#print axioms RevPebbling.LvdSound.prod_ell_cert
