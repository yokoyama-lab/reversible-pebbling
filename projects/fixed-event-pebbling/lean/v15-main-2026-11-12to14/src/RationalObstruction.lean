import ICert00
import ICert01
import ICert02
import ICert03
import ICert04
import ICert05
import MCert00
import MCert01
import MCert02
import MCert03
import MCert04
import MCert05
import MCert06
import MCert07
import MCert08
import MCert09
import MCert10
import MCert11
import MCert12
import MCert13
namespace MixtureCertificates
def Icounts : List Nat := [126, 120, 52, 84, 78, 77]
theorem I_overcount : Icounts.sum = 537 := by decide
theorem I_normalized_rational_obstruction (D : Nat) (hd : 0<D) (q : Fin 6→Nat)
 (mass : q ⟨0,by decide⟩ + q ⟨1,by decide⟩ + q ⟨2,by decide⟩ + q ⟨3,by decide⟩ + q ⟨4,by decide⟩ + q ⟨5,by decide⟩ = D)
 (uniform : ∀i : Fin 6,200*q i=Icounts[i.val]?.getD 0 * D) : False := by
 have h0 := uniform ⟨0,by decide⟩
 have h1 := uniform ⟨1,by decide⟩
 have h2 := uniform ⟨2,by decide⟩
 have h3 := uniform ⟨3,by decide⟩
 have h4 := uniform ⟨4,by decide⟩
 have h5 := uniform ⟨5,by decide⟩
 simp only [Icounts,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at h0 h1 h2 h3 h4 h5
 omega
#print axioms I_normalized_rational_obstruction
def Mcounts : List Nat := [299, 214, 187, 146, 186, 24, 199, 96, 287, 220, 18, 126, 141, 140]
theorem M_overcount : Mcounts.sum = 2283 := by decide
theorem M_normalized_rational_obstruction (D : Nat) (hd : 0<D) (q : Fin 14→Nat)
 (mass : q ⟨0,by decide⟩ + q ⟨1,by decide⟩ + q ⟨2,by decide⟩ + q ⟨3,by decide⟩ + q ⟨4,by decide⟩ + q ⟨5,by decide⟩ + q ⟨6,by decide⟩ + q ⟨7,by decide⟩ + q ⟨8,by decide⟩ + q ⟨9,by decide⟩ + q ⟨10,by decide⟩ + q ⟨11,by decide⟩ + q ⟨12,by decide⟩ + q ⟨13,by decide⟩ = D)
 (uniform : ∀i : Fin 14,584*q i=Mcounts[i.val]?.getD 0 * D) : False := by
 have h0 := uniform ⟨0,by decide⟩
 have h1 := uniform ⟨1,by decide⟩
 have h2 := uniform ⟨2,by decide⟩
 have h3 := uniform ⟨3,by decide⟩
 have h4 := uniform ⟨4,by decide⟩
 have h5 := uniform ⟨5,by decide⟩
 have h6 := uniform ⟨6,by decide⟩
 have h7 := uniform ⟨7,by decide⟩
 have h8 := uniform ⟨8,by decide⟩
 have h9 := uniform ⟨9,by decide⟩
 have h10 := uniform ⟨10,by decide⟩
 have h11 := uniform ⟨11,by decide⟩
 have h12 := uniform ⟨12,by decide⟩
 have h13 := uniform ⟨13,by decide⟩
 simp only [Mcounts,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
 omega
#print axioms M_normalized_rational_obstruction
theorem I_actual_extension_total : [ICert00words.length, ICert01words.length, ICert02words.length, ICert03words.length, ICert04words.length, ICert05words.length].sum = 537 := by
 rw [ICert00_count, ICert01_count, ICert02_count, ICert03_count, ICert04_count, ICert05_count]; rfl
#print axioms I_actual_extension_total
theorem M_actual_extension_total : [MCert00words.length, MCert01words.length, MCert02words.length, MCert03words.length, MCert04words.length, MCert05words.length, MCert06words.length, MCert07words.length, MCert08words.length, MCert09words.length, MCert10words.length, MCert11words.length, MCert12words.length, MCert13words.length].sum = 2283 := by
 rw [MCert00_count, MCert01_count, MCert02_count, MCert03_count, MCert04_count, MCert05_count, MCert06_count, MCert07_count, MCert08_count, MCert09_count, MCert10_count, MCert11_count, MCert12_count, MCert13_count]; rfl
#print axioms M_actual_extension_total
end MixtureCertificates
