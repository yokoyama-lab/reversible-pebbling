import LocalCounts
import Std.Tactic
namespace PebblingResidual
variable {α : Type}
def Concat (S T : List α → Prop) (w : List α) : Prop :=
  ∃ s t, S s ∧ T t ∧ w = s ++ t
def Residual (L : List α → Prop) (p z : List α) : Prop := L (p ++ z)
-- No finiteness, probability, or automaton assumption. S has a fixed length.
theorem boundary_residual (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p z : List α) (hp : p.length = n) :
    Residual (Concat S T) p z ↔ S p ∧ T z := by
  constructor
  · rintro ⟨s,t,hs,ht,eq⟩
    have len : p.length = s.length := hp.trans (fixed s hs).symm
    have eqs : p = s := List.append_inj_left eq len
    have eqt : z = t := List.append_inj_right eq len
    exact ⟨eqs ▸ hs, eqt ▸ ht⟩
  · rintro ⟨hpS,hzT⟩
    exact ⟨p,z,hpS,hzT,rfl⟩
theorem accepted_boundary (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p : List α) (hp : S p) (z : List α) :
    Residual (Concat S T) p z ↔ T z := by
  rw [boundary_residual S T n fixed p z (fixed p hp)]
  exact ⟨fun h => h.2, fun hz => ⟨hp,hz⟩⟩
theorem rejected_boundary (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p : List α) (len : p.length = n)
    (hp : ¬S p) (z : List α) : ¬Residual (Concat S T) p z := by
  intro h
  exact hp ((boundary_residual S T n fixed p z len).mp h).1
#print axioms boundary_residual
#print axioms accepted_boundary
#print axioms rejected_boundary
end PebblingResidual
namespace PebblingResidual
variable {α : Type}
theorem inside_residual (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p z : List α) (hp : p.length ≤ n) :
    Residual (Concat S T) p z ↔ Concat (Residual S p) T z := by
  constructor
  · rintro ⟨s,t,hs,ht,eq⟩
    rcases List.append_eq_append_iff.mp eq with ⟨u,hu,hz⟩ | ⟨u,hu,htz⟩
    · exact ⟨u,t,by simpa [Residual, ← hu] using hs,ht,hz⟩
    · have hl := congrArg List.length hu
      simp only [List.length_append] at hl
      have hsn := fixed s hs
      have hu0 : u.length = 0 := by omega
      have hue : u = [] := List.eq_nil_of_length_eq_zero hu0
      subst u
      simp only [List.append_nil, List.nil_append] at hu htz
      refine ⟨[],t,?_,ht,htz.symm⟩
      simpa [Residual,hu] using hs
  · rintro ⟨u,t,hs,ht,hz⟩
    refine ⟨p++u,t,hs,ht,?_⟩
    simpa [hz,List.append_assoc]
#print axioms inside_residual
end PebblingResidual
namespace PebblingResidual
variable {α : Type}
theorem residual_length (S : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p u : List α) (h : Residual S p u) :
    u.length = n - p.length := by
  have hn := fixed (p++u) h
  simp only [List.length_append] at hn
  omega
theorem residual_concat_injective (S : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p u v t w : List α)
    (hu : Residual S p u) (hv : Residual S p v) (he : u++t=v++w) :
    u=v ∧ t=w := by
  exact List.append_inj he ((residual_length S n fixed p u hu).trans
    (residual_length S n fixed p v hv).symm)
theorem residual_unique_decomposition (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p z : List α) (hp : p.length ≤ n)
    (hz : Residual (Concat S T) p z) :
    ∃ u t, Residual S p u ∧ T t ∧ z=u++t ∧
      ∀ v w, Residual S p v → T w → z=v++w → u=v ∧ t=w := by
  obtain ⟨u,t,hu,ht,eq⟩ := (inside_residual S T n fixed p z hp).mp hz
  refine ⟨u,t,hu,ht,eq,?_⟩
  intro v w hv _ eq2
  exact residual_concat_injective S n fixed p u v t w hu hv (eq.symm.trans eq2)
#print axioms residual_length
#print axioms residual_concat_injective
#print axioms residual_unique_decomposition
end PebblingResidual
namespace PebblingResidual
variable {α : Type}
def completions (us ts : List (List α)) : List (List α) :=
  us.flatMap (fun u => ts.map (fun t => u ++ t))
theorem completions_length (us ts : List (List α)) :
    (completions us ts).length = us.length * ts.length := by
  induction us with
  | nil => simp [completions]
  | cons u us ih => simpa [completions, Nat.succ_mul, Nat.add_comm] using congrArg (fun x => ts.length + x) ih

theorem completions_exact (S T : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p : List α) (hp : p.length ≤ n)
    (us ts : List (List α)) (hu : ∀ u, u ∈ us ↔ Residual S p u)
    (ht : ∀ t, t ∈ ts ↔ T t) (z : List α) :
    z ∈ completions us ts ↔ Residual (Concat S T) p z := by
  rw [inside_residual S T n fixed p z hp]
  simp only [completions, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u,hu',t,ht',eq⟩
    exact ⟨u,t,(hu u).mp hu',(ht t).mp ht',eq.symm⟩
  · rintro ⟨u,t,hu',ht',eq⟩
    exact ⟨u,(hu u).mpr hu',t,(ht t).mpr ht',eq.symm⟩

theorem completions_nodup (S : List α → Prop) (n : Nat)
    (fixed : ∀ s, S s → s.length = n) (p : List α)
    (us ts : List (List α)) (hu : ∀ u ∈ us, Residual S p u)
    (nu : us.Nodup) (nt : ts.Nodup) : (completions us ts).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro u _
    apply List.pairwise_map.mpr
    exact nt.imp (fun hab eq => hab (List.append_cancel_left eq))
  · apply nu.imp_of_mem
    intro u v hum hvm hne x hx y hy heq
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hy
    exact hne (residual_concat_injective S n fixed p u v t w
      (hu u hum) (hu v hvm) heq).1
#print axioms completions_length
#print axioms completions_exact
#print axioms completions_nodup
end PebblingResidual
namespace PhysicalResidual
-- An executable enumeration of suffixes after the exact ordered prefix p.
def suffixes (ws : List (List Nat)) (p : List Nat) : List (List Nat) :=
  ((ws.filter fun w => w.take p.length == p).map fun w => w.drop p.length)
theorem suffixes_exact (ws : List (List Nat)) (p z : List Nat) :
    z ∈ suffixes ws p ↔ p ++ z ∈ ws := by
  simp only [suffixes, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨w,⟨hw,hp⟩,hz⟩
    have eq := List.take_append_drop p.length w
    rw [hp,hz] at eq
    exact eq ▸ hw
  · intro h
    exact ⟨p++z,⟨h,by simp⟩,by simp⟩
theorem suffixes_nodup (ws : List (List Nat)) (p : List Nat)
    (hn : ws.Nodup) : (suffixes ws p).Nodup := by
  apply List.pairwise_map.mpr
  apply (hn.filter (fun w => w.take p.length == p)).imp_of_mem
  intro a b ha hb hne eq
  have ha' : a.take p.length = p := by simpa using (List.mem_filter.mp ha).2
  have hb' : b.take p.length = p := by simpa using (List.mem_filter.mp hb).2
  apply hne
  calc a = a.take p.length ++ a.drop p.length := (List.take_append_drop _ _).symm
       _ = b.take p.length ++ b.drop p.length := by rw [ha',hb',eq]
       _ = b := List.take_append_drop _ _
theorem initial_exact (p z : List Nat) :
    z ∈ suffixes UpperCertificate.I.physicalWords p ↔ LocalCertificate.I.Legal (p++z) := by
  rw [suffixes_exact,ChainWordCounts.initial_iff]
theorem middle_exact (p z : List Nat) :
    z ∈ suffixes UpperCertificate.M.physicalWords p ↔ LocalCertificate.M.Legal (p++z) := by
  rw [suffixes_exact,ChainWordCounts.middle_iff]
theorem initial_nodup (p : List Nat) : (suffixes UpperCertificate.I.physicalWords p).Nodup :=
  suffixes_nodup _ p ChainWordCounts.initial_nodup
theorem middle_nodup (p : List Nat) : (suffixes UpperCertificate.M.physicalWords p).Nodup :=
  suffixes_nodup _ p ChainWordCounts.middle_nodup
#print axioms initial_exact
#print axioms middle_exact
#print axioms initial_nodup
#print axioms middle_nodup
end PhysicalResidual
namespace PhysicalResidual
open PebblingResidual
theorem initial_product (p : List Nat) (hp : p.length ≤ 10)
    (ts : List (List Nat)) (nt : ts.Nodup) :
    let cs := completions (suffixes UpperCertificate.I.physicalWords p) ts
    (∀ z, z ∈ cs ↔ Residual (Concat LocalCertificate.I.Legal (fun t => t ∈ ts)) p z) ∧
    cs.Nodup ∧ cs.length = (suffixes UpperCertificate.I.physicalWords p).length * ts.length := by
  have fixed : ∀ w, LocalCertificate.I.Legal w → w.length = 10 := by
    intro w h
    exact h.1.1
  refine ⟨?_,?_,completions_length _ _⟩
  · intro z
    exact completions_exact _ _ 10 fixed p hp _ ts (initial_exact p) (fun _ => Iff.rfl) z
  · exact completions_nodup _ 10 fixed p _ ts
      (fun u hu => (initial_exact p u).mp hu) (initial_nodup p) nt
#print axioms initial_product
end PhysicalResidual
