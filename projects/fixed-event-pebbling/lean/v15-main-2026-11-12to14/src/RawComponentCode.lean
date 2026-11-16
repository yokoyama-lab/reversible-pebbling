import RawSwapLift
import ComponentWordCount
namespace RawComponentCode
open LocalCertificate ChainWholeBijection ChainLabelledCount ComponentLabelledCode
theorem raw_legal {α : Type} {L : List α→Prop} {u v} (h : RawSwapGraph.Reach L u v) : L v := by
 cases h with
 | refl h => exact h
 | step _ _ h => exact h
noncomputable def root (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) : Physical bs.length E :=
 toRaw ⟨ComponentPatterns.representative (fun j=>bs.get j),ComponentPatterns.representative_legal he _⟩
abbrev Component (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :=
 {w : List Event // RawSwapGraph.Reach (FamilyCut.Trace (bs.length+1) E) (root bs E he).val w}
noncomputable def toRawComponent (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : InComponent bs E) : Component bs E he := by
 let lab : Labelled bs.length E := ⟨w.val,SwapGraphBasics.reach_legal w.property⟩
 refine ⟨(toRaw lab).val,?_⟩
 exact (RawSwapGraph.reach_iff_decode (ComponentPatterns.representative_legal he _)
  lab.property (toRaw_spec ⟨ComponentPatterns.representative (fun j=>bs.get j),ComponentPatterns.representative_legal he _⟩) (toRaw_spec lab)).mp w.property
noncomputable def toLabelledComponent (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : Component bs E he) : InComponent bs E := by
 have hw : FamilyCut.Trace (bs.length+1) E w.val := raw_legal w.property
 let raw : Physical bs.length E := ⟨w.val,hw⟩
 let lab := toLabelled E he raw
 refine ⟨lab.val,?_⟩
 exact (RawSwapGraph.reach_iff_decode (ComponentPatterns.representative_legal he _)
  lab.property (toRaw_spec ⟨ComponentPatterns.representative (fun j=>bs.get j),ComponentPatterns.representative_legal he _⟩) (toLabelled_spec E he raw)).mpr w.property

theorem labelled_raw (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : InComponent bs E) : toLabelledComponent bs E he (toRawComponent bs E he w)=w := by
 apply Subtype.ext
 exact congrArg (fun z : Labelled bs.length E=>z.val) (labelled_roundtrip E he ⟨w.val,SwapGraphBasics.reach_legal w.property⟩)

theorem raw_labelled (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : Component bs E he) : toRawComponent bs E he (toLabelledComponent bs E he w)=w := by
 apply Subtype.ext
 have hw : FamilyCut.Trace (bs.length+1) E w.val := raw_legal w.property
 exact congrArg (fun z : Physical bs.length E=>z.val) (raw_roundtrip E he ⟨w.val,hw⟩)
noncomputable def exactCode (bs : List Bool) (E : List Nat) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 ChainWordCounts.Code (Component bs E he) (400*556^(bs.count false)*28^(bs.length-bs.count false)) where
 enc w := (ComponentLabelledCode.exactCode bs E he).enc (toLabelledComponent bs E he w)
 dec i := toRawComponent bs E he ((ComponentLabelledCode.exactCode bs E he).dec i)
 dec_enc w := by simp only [ChainWordCounts.Code.dec_enc,raw_labelled]
 enc_dec i := by simp only [labelled_raw,ChainWordCounts.Code.enc_dec]
#print axioms labelled_raw
#print axioms raw_labelled
#print axioms exactCode
end RawComponentCode
