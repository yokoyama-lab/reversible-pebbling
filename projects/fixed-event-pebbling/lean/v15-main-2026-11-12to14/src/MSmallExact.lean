import MSmallShard0
import MSmallShard1
import MSmallShard2
import MSmallShard3
namespace MSmallSwap
open SwapComponents
theorem reach0 : Reach LocalCertificate.M.Legal w0 w0 := Reach.refl legal0
theorem reach1 : Reach LocalCertificate.M.Legal w0 w1 := Reach.step reach0 edge1 legal1
theorem reach2 : Reach LocalCertificate.M.Legal w0 w2 := Reach.step reach0 edge2 legal2
theorem reach3 : Reach LocalCertificate.M.Legal w0 w3 := Reach.step reach0 edge3 legal3
theorem reach4 : Reach LocalCertificate.M.Legal w0 w4 := Reach.step reach1 edge4 legal4
theorem reach5 : Reach LocalCertificate.M.Legal w0 w5 := Reach.step reach1 edge5 legal5
theorem reach6 : Reach LocalCertificate.M.Legal w0 w6 := Reach.step reach2 edge6 legal6
theorem reach7 : Reach LocalCertificate.M.Legal w0 w7 := Reach.step reach2 edge7 legal7
theorem reach8 : Reach LocalCertificate.M.Legal w0 w8 := Reach.step reach2 edge8 legal8
theorem reach9 : Reach LocalCertificate.M.Legal w0 w9 := Reach.step reach4 edge9 legal9
theorem reach10 : Reach LocalCertificate.M.Legal w0 w10 := Reach.step reach4 edge10 legal10
theorem reach11 : Reach LocalCertificate.M.Legal w0 w11 := Reach.step reach4 edge11 legal11
theorem reach12 : Reach LocalCertificate.M.Legal w0 w12 := Reach.step reach6 edge12 legal12
theorem reach13 : Reach LocalCertificate.M.Legal w0 w13 := Reach.step reach6 edge13 legal13
theorem reach14 : Reach LocalCertificate.M.Legal w0 w14 := Reach.step reach7 edge14 legal14
theorem reach15 : Reach LocalCertificate.M.Legal w0 w15 := Reach.step reach7 edge15 legal15
theorem reach16 : Reach LocalCertificate.M.Legal w0 w16 := Reach.step reach9 edge16 legal16
theorem reach17 : Reach LocalCertificate.M.Legal w0 w17 := Reach.step reach9 edge17 legal17
theorem reach18 : Reach LocalCertificate.M.Legal w0 w18 := Reach.step reach10 edge18 legal18
theorem reach19 : Reach LocalCertificate.M.Legal w0 w19 := Reach.step reach10 edge19 legal19
theorem reach20 : Reach LocalCertificate.M.Legal w0 w20 := Reach.step reach12 edge20 legal20
theorem reach21 : Reach LocalCertificate.M.Legal w0 w21 := Reach.step reach12 edge21 legal21
theorem reach22 : Reach LocalCertificate.M.Legal w0 w22 := Reach.step reach14 edge22 legal22
theorem reach23 : Reach LocalCertificate.M.Legal w0 w23 := Reach.step reach16 edge23 legal23
theorem reach24 : Reach LocalCertificate.M.Legal w0 w24 := Reach.step reach16 edge24 legal24
theorem reach25 : Reach LocalCertificate.M.Legal w0 w25 := Reach.step reach18 edge25 legal25
theorem reach26 : Reach LocalCertificate.M.Legal w0 w26 := Reach.step reach20 edge26 legal26
theorem reach27 : Reach LocalCertificate.M.Legal w0 w27 := Reach.step reach23 edge27 legal27
theorem closed : ∀u∈component,∀v∈neighbors u,LocalCertificate.M.Legal v→v∈component := by
 simp only [component,List.forall_mem_cons]
 exact ⟨closed0,closed1,closed2,closed3,closed4,closed5,closed6,closed7,closed8,closed9,closed10,closed11,closed12,closed13,closed14,closed15,closed16,closed17,closed18,closed19,closed20,closed21,closed22,closed23,closed24,closed25,closed26,closed27,by simp⟩
theorem tree : ∀u∈component,Reach LocalCertificate.M.Legal w0 u := by
 simp only [component,List.forall_mem_cons]
 exact ⟨reach0,reach1,reach2,reach3,reach4,reach5,reach6,reach7,reach8,reach9,reach10,reach11,reach12,reach13,reach14,reach15,reach16,reach17,reach18,reach19,reach20,reach21,reach22,reach23,reach24,reach25,reach26,reach27,by simp⟩
theorem exact : ∀v,Reach LocalCertificate.M.Legal w0 v ↔ v∈component := exact_component (by decide) closed tree
#print axioms exact
end MSmallSwap
