import RemovalOrder
namespace RemovalOrder
open LocalCertificate ChainTrace

def isPlacement (v : Nat) (e : Event) : Bool := e.place && (e.vertex == v)

/-- The no-replacement hypothesis is derived from the placement budget,
not assumed, when the vertex is placed at most once in the whole run. -/
theorem single_placement_no_replacement
    (erasures final : List Nat) (pre post : List Event) (e : Event)
    (v : Nat) (hp : e.place = false) (he : e.vertex = v)
    (hc : (pre ++ e :: post).countP (isPlacement v) ≤ 1)
    (hr : run erasures [] (pre ++ e :: post) = some final) :
    ∀ f ∈ post, f.place = true → f.vertex ≠ v := by
  rw [run_append] at hr
  cases hs : run erasures [] pre with
  | none => simp [hs] at hr
  | some mid =>
    have hrest : run erasures mid (e :: post) = some final := by simpa [hs] using hr
    cases ht : step true erasures mid e with
    | none => simp [run,ht] at hrest
    | some after =>
      have hv : v ∈ mid := by simpa [he] using removal_requires_present erasures mid after e hp ht
      have hx := run_support erasures [] mid pre hs v hv
      obtain ⟨g,hg,hgp,hgv⟩ : ∃ g ∈ pre, g.place = true ∧ g.vertex = v := by simpa using hx
      have hpos : 0 < pre.countP (isPlacement v) := by
        apply List.countP_pos_iff.mpr
        exact ⟨g,hg, by simp [isPlacement,hgp,hgv]⟩
      have hc' : pre.countP (isPlacement v) + post.countP (isPlacement v) ≤ 1 := by
        simpa [List.countP_append, List.countP_cons, isPlacement, hp] using hc
      have hz : post.countP (isPlacement v) = 0 := by omega
      intro f hf hfp hfv
      have hn := List.countP_eq_zero.mp hz f hf
      exact hn (by simp [isPlacement,hfp,hfv])

theorem successor_before_single_placement_removal
    (erasures final : List Nat) (pre post : List Event) (e f : Event)
    (v : Nat) (hv : 0 < v) (hp : e.place = false) (he : e.vertex = v)
    (her : v+1 ∉ erasures)
    (hc : (pre ++ e :: post).countP (isPlacement v) ≤ 1)
    (hr : run erasures [] (pre ++ e :: post) = some final)
    (hf : f ∈ pre ++ e :: post) (hfv : f.vertex = v+1) : f ∈ pre := by
  exact successor_precedes_last_removal erasures final pre post e f v hv hp he her
    (single_placement_no_replacement erasures final pre post e v hp he hc hr) hr hf hfv
#print axioms single_placement_no_replacement
#print axioms successor_before_single_placement_removal
end RemovalOrder
