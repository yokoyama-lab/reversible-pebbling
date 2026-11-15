import BridgeBase
namespace EdgeBridge
def canonFast (xs : List (SpookyDP.Result (SpookyRound.Config 7))) :=
  (((xs.map fun r => (code r,r)).eraseDups).mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd

theorem mem_canonFast (r) (xs : List (SpookyDP.Result (SpookyRound.Config 7))) : r ∈ canonFast xs ↔ r ∈ xs := by
  simp only [canonFast,List.mem_map,List.mem_mergeSort,List.mem_eraseDups]
  constructor
  · rintro ⟨x,⟨y,hy,he⟩,hr⟩
    subst x
    simpa using hr ▸ hy
  · intro h
    exact ⟨(code r,r),⟨r,h,rfl⟩,rfl⟩

def checkFast (i : Fin 2187) : Bool := canonFast (realEdges i) == canonFast (tableEdges i)
theorem checkFast_sound (i : Fin 2187) (h : checkFast i = true) (r) :
    r ∈ realEdges i ↔ r ∈ tableEdges i := by
  have heq : canonFast (realEdges i) = canonFast (tableEdges i) := by simpa [checkFast] using h
  rw [← mem_canonFast r (realEdges i),heq,mem_canonFast]
#print axioms checkFast_sound
end EdgeBridge
