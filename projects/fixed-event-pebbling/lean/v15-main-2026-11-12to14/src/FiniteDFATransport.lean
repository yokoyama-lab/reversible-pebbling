import CompletedDFA
namespace FiniteDFATransport
open CompletedSetDFA
structure Certificate (L : Language) (sets : List (List Nat)) : Prop where
 nodup : sets.Nodup
 sound : ∀c∈sets,∃u,Viable L u ∧ Same c u
 complete : ∀u,Viable L u → ∃c∈sets,Same u c
 canonical : ∀c∈sets,∀d∈sets,Same c d → c=d
noncomputable def decode (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i : Fin sets.length) : Live L :=
 ⟨(fun a => a∈sets[i.val]),cert.sound _ (List.getElem_mem i.isLt)⟩
theorem index_exists (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Live L) : ∃i : Fin sets.length,∀a,q.val a ↔ a∈sets[i.val] := by
 obtain ⟨c,hc,hs⟩ := cert.complete (representative q) (representative_viable q)
 obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hc
 refine ⟨⟨i,hi⟩,?_⟩
 intro a
 rw [he]
 exact (representative_set q a).trans (hs a)
noncomputable def encode (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Live L) : Fin sets.length := Classical.choose (index_exists L sets cert q)
theorem decode_encode (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Live L) : decode L sets cert (encode L sets cert q)=q := by
 apply Subtype.ext
 funext a
 exact propext ((Classical.choose_spec (index_exists L sets cert q) a).symm)
theorem decode_injective (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i j : Fin sets.length) (h : decode L sets cert i=decode L sets cert j) : i=j := by
 have hs : Same sets[i.val] sets[j.val] := by
  intro a
  have hv := congrArg (fun q : Live L => q.val a) h
  exact Iff.of_eq hv
 have he := cert.canonical _ (List.getElem_mem i.isLt) _ (List.getElem_mem j.isLt) hs
 exact Fin.ext ((List.getElem_inj cert.nodup).mp he)
theorem encode_decode (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (i : Fin sets.length) : encode L sets cert (decode L sets cert i)=i :=
 decode_injective L sets cert _ _ (decode_encode L sets cert (decode L sets cert i))
noncomputable def encodeState (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) :
 State L → Option (Fin sets.length)
 | none => none
 | some q => some (encode L sets cert q)
noncomputable def decodeState (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) :
 Option (Fin sets.length) → State L
 | none => none
 | some i => some (decode L sets cert i)
theorem decode_encode_state (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : State L) : decodeState L sets cert (encodeState L sets cert q)=q := by
 cases q <;> simp [decodeState,encodeState,decode_encode]
theorem encode_decode_state (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Option (Fin sets.length)) : encodeState L sets cert (decodeState L sets cert q)=q := by
 cases q <;> simp [decodeState,encodeState,encode_decode]
noncomputable def initial (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) :=
 encodeState L sets cert (CompletedSetDFA.initial L)
noncomputable def step (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Option (Fin sets.length)) (a : Nat) :=
 encodeState L sets cert (CompletedSetDFA.step L (decodeState L sets cert q) a)
def Accept (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Option (Fin sets.length)) : Prop := CompletedSetDFA.Accept L (decodeState L sets cert q)
noncomputable def run (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) :
 Option (Fin sets.length) → List Nat → Option (Fin sets.length)
 | q,[] => q
 | q,a::w => run L sets cert (step L sets cert q a) w
theorem run_transport (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : State L) (w : List Nat) :
 run L sets cert (encodeState L sets cert q) w=encodeState L sets cert (CompletedSetDFA.run L q w) := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih =>
  simp only [run,step,decode_encode_state,CompletedSetDFA.run]
  exact ih _
theorem recognizes (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (respect : Respects L) (w : List Nat) :
 Accept L sets cert (run L sets cert (initial L sets cert) w) ↔ L w := by
 unfold initial
 rw [run_transport]
 unfold Accept
 rw [decode_encode_state]
 exact CompletedSetDFA.recognizes L respect w
def number {n : Nat} : Option (Fin n) → Fin (n+1)
 | none => 0
 | some i => i.succ
def unnumber {n : Nat} (i : Fin (n+1)) : Option (Fin n) := Fin.cases none some i
theorem unnumber_number {n : Nat} (q : Option (Fin n)) : unnumber (number q)=q := by
 cases q <;> simp [number,unnumber]
theorem number_unnumber {n : Nat} (q : Fin (n+1)) : number (unnumber q)=q := by
 exact Fin.cases (by simp [number,unnumber]) (fun i => by simp [number,unnumber]) q
noncomputable def finiteInitial (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) : Fin (sets.length+1) :=
 number (initial L sets cert)
noncomputable def finiteStep (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Fin (sets.length+1)) (a : Nat) : Fin (sets.length+1) := number (step L sets cert (unnumber q) a)
noncomputable def finiteRun (L : Language) (sets : List (List Nat)) (cert : Certificate L sets) :
 Fin (sets.length+1) → List Nat → Fin (sets.length+1)
 | q,[] => q
 | q,a::w => finiteRun L sets cert (finiteStep L sets cert q a) w
theorem finite_run_transport (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (q : Option (Fin sets.length)) (w : List Nat) :
 finiteRun L sets cert (number q) w=number (run L sets cert q w) := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih => simp only [finiteRun,finiteStep,unnumber_number,run];exact ih _
theorem finite_recognizes (L : Language) (sets : List (List Nat)) (cert : Certificate L sets)
 (respect : Respects L) (w : List Nat) :
 Accept L sets cert (unnumber (finiteRun L sets cert (finiteInitial L sets cert) w)) ↔ L w := by
 unfold finiteInitial
 rw [finite_run_transport,unnumber_number]
 exact recognizes L sets cert respect w
theorem physical_finite_recognizes (r : Nat) (E : List Nat) (sets : List (List Nat))
 (cert : Certificate (ChainOccurrence.labelledLegal r E) sets) (w : List Nat) :
 Accept (ChainOccurrence.labelledLegal r E) sets cert
  (unnumber (finiteRun (ChainOccurrence.labelledLegal r E) sets cert
   (finiteInitial (ChainOccurrence.labelledLegal r E) sets cert) w)) ↔ ChainOccurrence.labelledLegal r E w :=
 finite_recognizes _ sets cert (ChainCompletedDFA.respects r E) w
#print axioms finite_recognizes
#print axioms physical_finite_recognizes
#print axioms decode_encode
#print axioms encode_decode
#print axioms recognizes
end FiniteDFATransport
