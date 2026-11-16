import PrefixStates
namespace ChainPrefixStates

theorem mem_states_iff (n : Nat) (words : List (List Nat)) (s : List Nat) :
    s ∈ states n words ↔ ∃ w ∈ words, ∃ t, t ≤ w.length ∧
      (List.range n).filter (fun e => (w.take t).contains e) = s := by
  simp only [states,List.mem_eraseDups,List.mem_flatMap,setsOfWord,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨w,hw,t,ht,hs⟩
    exact ⟨w,hw,t,by omega,hs⟩
  · rintro ⟨w,hw,t,ht,hs⟩
    exact ⟨w,hw,t,by omega,hs⟩

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp
    · exact eraseDups_nodup (xs.filter (fun b => !b == a))
termination_by xs.length
 decreasing_by
  have h := List.length_filter_le (fun b => !b == a) xs
  simp only [List.length_cons]
  omega

theorem states_nodup (n : Nat) (words : List (List Nat)) : (states n words).Nodup :=
  eraseDups_nodup _

#print axioms mem_states_iff
#print axioms states_nodup
end ChainPrefixStates
