import StateLower
namespace CompleteDFALower
structure DFA (n : Nat) where
 step : Fin n → Nat → Fin n
 initial : Fin n
 accept : Fin n → Prop
def run {n : Nat} (M : DFA n) : Fin n → List Nat → Fin n
 | q,[] => q
 | q,a::w => run M (M.step q a) w
def Accept {n : Nat} (M : DFA n) (w : List Nat) := M.accept (run M M.initial w)
theorem run_append {n : Nat} (M : DFA n) (q : Fin n) (u v : List Nat) :
 run M q (u++v)=run M (run M q u) v := by
 induction u generalizing q with
 | nil => rfl
 | cons a u ih => exact ih _
theorem lower_with_dead {m n : Nat} (M : DFA n) (L : List Nat → Prop)
 (rec : ∀w,Accept M w ↔ L w) (pre suf : Fin m → List Nat)
 (acc : ∀i,L (pre i++suf i)) (cross : ∀i j,i≠j → ¬L (pre i++suf j))
 (bad : List Nat) (dead : ∀i,¬L (bad++suf i)) : m+1≤n := by
 let state : Fin m → Fin n := fun i=>run M M.initial (pre i)
 let reject : Fin n := run M M.initial bad
 have inj : ∀i j,state i=state j → i=j := by
  intro i j he
  apply Classical.byContradiction;intro hn
  have hac := (rec _).mpr (acc j)
  have hcross : Accept M (pre i++suf j) := by
   unfold Accept at *;rw [run_append] at *
   change M.accept (run M (state i) (suf j))
   rw [he];exact hac
  exact cross i j hn ((rec _).mp hcross)
 have apart : ∀i,state i≠reject := by
  intro i he
  have hac := (rec _).mpr (acc i)
  have hbad : Accept M (bad++suf i) := by
   unfold Accept at *;rw [run_append] at *
   change M.accept (run M reject (suf i))
   rw [←he];exact hac
  exact dead i ((rec _).mp hbad)
 apply ErasureCardinality.fin_injection_bound (Fin.cases reject state)
 intro i j
 refine Fin.cases ?_ (fun a => ?_) i
 · refine Fin.cases ?_ (fun b => ?_) j
   · intro _;rfl
   · intro h;exact False.elim (apart b h.symm)
 · refine Fin.cases ?_ (fun b => ?_) j
   · intro h;exact False.elim (apart a h)
   · intro h;exact congrArg Fin.succ (inj a b h)
theorem physical_lower (r : Nat) (E : List Nat) (sets : List (List Nat))
 (cert : FiniteDFATransport.Certificate (ChainOccurrence.labelledLegal r E) sets)
 (n : Nat) (M : DFA n) (rec : ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E w) : sets.length+1≤n := by
 classical
 let pre := StateLower.prefixes (ChainOccurrence.labelledLegal r E) sets cert
 have viable := StateLower.prefixes_viable (ChainOccurrence.labelledLegal r E) sets cert
 let suf := fun i => Classical.choose (viable i)
 have acc (i) : ChainOccurrence.labelledLegal r E (pre i++suf i) := Classical.choose_spec (viable i)
 have perm := ChainPhysicalResidual.physical_permutation_language r E
 have distinct (i j) (hn : i≠j) : ¬(pre i).Perm (pre j) :=
  ChainResidualSeparation.different_completed_sets_not_perm (StateLower.prefixes_different _ sets cert i j hn)
 apply lower_with_dead M (ChainOccurrence.labelledLegal r E) rec pre suf acc
  (ChainResidualSeparation.cross_splice_rejected perm pre suf acc distinct)
  [0,0]
 intro i h
 have hn := (List.nodup_append.mp h.1.2.1).1
 simp at hn
theorem physical_lower_on_alphabet (r : Nat) (E : List Nat) (sets : List (List Nat))
 (cert : FiniteDFATransport.Certificate (ChainOccurrence.labelledLegal r E) sets)
 (n : Nat) (M : DFA n)
 (rec : ∀w,(∀a∈w,a<(ChainAssembledTrace.fullTable r).length) →
  (Accept M w ↔ ChainOccurrence.labelledLegal r E w)) : sets.length+1≤n := by
 classical
 let pre := StateLower.prefixes (ChainOccurrence.labelledLegal r E) sets cert
 have viable := StateLower.prefixes_viable (ChainOccurrence.labelledLegal r E) sets cert
 let suf := fun i => Classical.choose (viable i)
 have acc (i) : ChainOccurrence.labelledLegal r E (pre i++suf i) := Classical.choose_spec (viable i)
 have bounded (i) : ∀a∈pre i++suf i,a<(ChainAssembledTrace.fullTable r).length := (acc i).1.2.2
 have crossbound (i j) : ∀a∈pre i++suf j,a<(ChainAssembledTrace.fullTable r).length := by
  intro a ha;rcases List.mem_append.mp ha with h|h
  · exact bounded i a (List.mem_append_left _ h)
  · exact bounded j a (List.mem_append_right _ h)
 have reject (i j) (hn : i≠j) : ¬ChainOccurrence.labelledLegal r E (pre i++suf j) :=
  ChainResidualSeparation.cross_splice_rejected (ChainPhysicalResidual.physical_permutation_language r E)
   pre suf acc (fun i j hn => ChainResidualSeparation.different_completed_sets_not_perm
    (StateLower.prefixes_different _ sets cert i j hn)) i j hn
 apply lower_with_dead M (Accept M) (fun _=>Iff.rfl) pre suf
  (fun i => (rec _ (bounded i)).mpr (acc i))
  (fun i j hn h => reject i j hn ((rec _ (crossbound i j)).mp h)) [0,0]
 intro i ha
 have hb : ∀a∈[0,0]++suf i,a<(ChainAssembledTrace.fullTable r).length := by
  intro a ha
  rcases List.mem_append.mp ha with h|h
  · have he : a=0 := by simpa using h
    rw [he,ChainOccurrence.table_length];omega
  · exact bounded i a (List.mem_append_right _ h)
 have h := (rec _ hb).mp ha
 have hn := (List.nodup_append.mp h.1.2.1).1
 simp at hn
#print axioms physical_lower_on_alphabet
#print axioms lower_with_dead
#print axioms physical_lower
end CompleteDFALower
