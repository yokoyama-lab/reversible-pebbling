import ChainTrace
namespace ChainEventEncoding
open LocalCertificate ChainTrace
#synth BEq Event
#synth LawfulBEq Event

 theorem lookup_idxOf {α : Type} [BEq α] [LawfulBEq α]
    (table : List α) (e : α) (hm : e ∈ table) : table[table.idxOf e]? = some e := by
  induction table with
  | nil => simp at hm
  | cons a table ih =>
    by_cases he : e = a
    · subst e
      simp
    · have ht : e ∈ table := (List.mem_cons.mp hm).resolve_left he
      simp [List.idxOf_cons, cond_eq_ite, beq_iff_eq, Ne.symm he, ih ht]

def encode (table es : List Event) : List Nat := es.map table.idxOf

theorem decode_encode (table es : List Event) (subset : ∀ e ∈ es, e ∈ table) :
    decodeTrace table (encode table es) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := lookup_idxOf table e (subset e (by simp))
    have ht := ih (fun f hf => subset f (List.mem_cons_of_mem e hf))
    change decodeTrace table (es.map table.idxOf) = some es at ht
    simp [encode,decodeTrace,he,ht]

 theorem nodup_map_on {α β : Type} (f : α → β) (xs : List α) (nd : xs.Nodup)
    (inj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hn := List.nodup_cons.mp nd
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
      have hab := inj b (by simp [hb]) a (by simp) he
      exact hn.1 (hab ▸ hb)
    · exact ih hn.2 (fun b hb c hc => inj b (by simp [hb]) c (by simp [hc]))

theorem encoded_isPermutation (table es : List Event) (nd : table.Nodup)
    (perm : es.Perm table) : isPermutation table.length (encode table es) := by
  have subset : ∀ e ∈ es, e ∈ table := fun e he => (perm.mem_iff).mp he
  refine ⟨?_, ?_, ?_⟩
  · simpa [encode] using perm.length_eq
  · apply nodup_map_on table.idxOf es (perm.nodup_iff.mpr nd)
    intro a ha b hb he
    have h1 := lookup_idxOf table a (subset a ha)
    have h2 := lookup_idxOf table b (subset b hb)
    rw [he] at h1
    exact Option.some.inj (h1.symm.trans h2)
  · intro i hi
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi
    exact List.idxOf_lt_length_of_mem (subset e he)

theorem replay_encode_eq_run (table es : List Event) (erasures board : List Nat)
    (subset : ∀ e ∈ es, e ∈ table) :
    replay true table erasures board (encode table es) = run erasures board es := by
  rw [replay_eq_decode_run, decode_encode table es subset]
  rfl

theorem legal_encode_iff_run (table es : List Event) (initial final erasures : List Nat)
    (nd : table.Nodup) (perm : es.Perm table) :
    legal table initial final erasures (encode table es) ↔
      ∃ after, run erasures initial es = some after ∧ sameBoard after final = true := by
  have he := replay_encode_eq_run table es erasures initial (fun e he => perm.mem_iff.mp he)
  simp only [legal, encoded_isPermutation table es nd perm, true_and, he]
  cases hr : run erasures initial es <;> simp

#print axioms lookup_idxOf
#print axioms decode_encode
#print axioms encoded_isPermutation
#print axioms replay_encode_eq_run
#print axioms legal_encode_iff_run
end ChainEventEncoding
