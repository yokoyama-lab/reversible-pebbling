import FactorRecovery
import EventEncoding
namespace ChainFactorUnique
open LocalCertificate
 theorem map_add_injective (d : Nat) (u v : List Nat)
   (h : u.map (fun i => i+d) = v.map (fun i => i+d)) : u=v := by
   have hh := congrArg (List.map (fun i => i-d)) h
   simpa only [List.map_map,Nat.add_sub_cancel,Function.comp_def,List.map_id'] using hh
 theorem padded_map_injective (d : Nat) (pre post u v : List Nat)
   (h : pre ++ u.map (fun i => i+d) ++ post = pre ++ v.map (fun i => i+d) ++ post) : u=v := by
   have h1 := List.append_cancel_right h
   have h2 := List.append_cancel_left h1
   exact map_add_injective d u v h2
 theorem initial_lift_injective (u v : List Nat)
   (h : ChainInitialConverse.liftWord u = ChainInitialConverse.liftWord v) : u=v := by
   exact padded_map_injective 6 [0,1,2,3,4,5] [16] u v h
 theorem middle_lift_injective (u v : List Nat)
   (h : ChainMiddleConverse.liftWord u = ChainMiddleConverse.liftWord v) : u=v := by
   exact padded_map_injective 3 [0,1,2] [15] u v h
 theorem encode_injective_on (table xs ys : List Event)
   (hx : ∀ e ∈ xs, e ∈ table) (hy : ∀ e ∈ ys, e ∈ table)
   (h : ChainEventEncoding.encode table xs = ChainEventEncoding.encode table ys) : xs=ys := by
   have hd := congrArg (ChainTrace.decodeTrace table) h
   rw [ChainEventEncoding.decode_encode table xs hx,ChainEventEncoding.decode_encode table ys hy] at hd
   exact Option.some.inj hd
 theorem initial_factor_unique (w : List Nat)
   (h : legal ChainInitialSegment.events [] ChainInitialSegment.final [5] w) :
   ∃ u, (I.Legal u ∧ w=ChainInitialConverse.liftWord u) ∧
     ∀ v, (I.Legal v ∧ w=ChainInitialConverse.liftWord v) → v=u := by
   obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.initial_legal_iff_factor w).mp h
   refine ⟨u,⟨hu,he⟩,?_⟩
   intro v hv
   exact initial_lift_injective v u (hv.2.symm.trans he)
 theorem middle_factor_unique (w : List Nat)
   (h : legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11] w) :
   ∃ u, (M.Legal u ∧ w=ChainMiddleConverse.liftWord u) ∧
     ∀ v, (M.Legal v ∧ w=ChainMiddleConverse.liftWord v) → v=u := by
   obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.middle_legal_iff_factor w).mp h
   refine ⟨u,⟨hu,he⟩,?_⟩
   intro v hv
   exact middle_lift_injective v u (hv.2.symm.trans he)
#print axioms map_add_injective
#print axioms padded_map_injective
#print axioms initial_lift_injective
#print axioms middle_lift_injective
#print axioms encode_injective_on
#print axioms initial_factor_unique
#print axioms middle_factor_unique
end ChainFactorUnique
