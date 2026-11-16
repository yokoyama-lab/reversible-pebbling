import LocalCertificate
namespace SwapComponents
def neighbors : List Nat → List (List Nat)
 | a::b::xs => (b::a::xs)::(neighbors (b::xs)).map (List.cons a)
 | _ => []
inductive Reach (L : List Nat→Prop) (root : List Nat) : List Nat→Prop
 | refl : L root → Reach L root root
 | step {u v} : Reach L root u → v∈neighbors u → L v → Reach L root v

theorem reachable_stays {L : List Nat→Prop} {root : List Nat} {C : List (List Nat)}
 (member : root∈C)
 (closed : ∀u∈C,∀v∈neighbors u,L v→v∈C) :
 ∀v,Reach L root v→v∈C := by
 intro v h
 induction h with
 | refl => exact member
 | step h edge legal ih => exact closed _ ih _ edge legal

theorem exact_component {L : List Nat→Prop} {root : List Nat} {C : List (List Nat)}
 (member : root∈C)
 (closed : ∀u∈C,∀v∈neighbors u,L v→v∈C)
 (tree : ∀u∈C,Reach L root u) :
 ∀v,Reach L root v ↔ v∈C := by
 intro v;exact ⟨reachable_stays member closed v,tree v⟩
#print axioms exact_component
end SwapComponents
