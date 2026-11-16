import FamilyGlobalCounts
namespace GlobalSplit
open LocalCertificate ChainFamilyArithmetic FamilyCut

def splitMarkers (p : Event → Bool) : List Event → List (List Event) × List Event
  | [] => ([],[])
  | e::es =>
    let (blocks,tail) := splitMarkers p es
    if p e then ([e]::blocks,tail)
    else match blocks with
      | [] => ([],e::tail)
      | b::bs => ((e::b)::bs,tail)

def Block (p : Event → Bool) (b : List Event) : Prop :=
  ∃ pre e, b=pre++[e] ∧ p e=true ∧ ∀ x∈pre, p x=false

theorem split_spec (p : Event → Bool) (word : List Event) :
    let z := splitMarkers p word
    z.1.flatten ++ z.2 = word ∧
    (∀ b∈z.1, Block p b) ∧ (∀ e∈z.2, p e=false) := by
  induction word with
  | nil => simp [splitMarkers]
  | cons e es ih =>
    cases hz : splitMarkers p es with
    | mk blocks tail =>
      simp only [hz] at ih
      obtain ⟨hflat,hblocks,htail⟩ := ih
      cases hp : p e with
      | true =>
        simp only [splitMarkers,hz,hp,ite_true]
        refine ⟨?_,?_,htail⟩
        · simpa using congrArg (List.cons e) hflat
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨[],e,rfl,hp,by simp⟩
          · exact hblocks b hb
      | false =>
        cases blocks with
        | nil =>
          simp only [splitMarkers,hz,hp,Bool.false_eq_true,ite_false]
          refine ⟨?_,by simp,?_⟩
          · simpa using congrArg (List.cons e) hflat
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hp
            · exact htail x hx
        | cons b bs =>
          simp only [splitMarkers,hz,hp,Bool.false_eq_true,ite_false]
          refine ⟨?_,?_,htail⟩
          · simpa using congrArg (List.cons e) hflat
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · obtain ⟨pre,last,he,hl,hpre⟩ := hblocks b (by simp)
              refine ⟨e::pre,last,?_,hl,?_⟩
              · simp [he]
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hp
                · exact hpre x hx
            · exact hblocks c (List.mem_cons_of_mem b hc)

theorem block_count (p : Event → Bool) (b : List Event) (hb : Block p b) :
    b.countP p = 1 := by
  obtain ⟨pre,e,rfl,hp,hn⟩ := hb
  have hz : pre.countP p=0 := List.countP_eq_zero.mpr (by
    intro x hx
    simp [hn x hx])
  simp [List.countP_append,hz,hp]

theorem split_marker_count (p : Event → Bool) (word : List Event) :
    word.countP p = (splitMarkers p word).1.length := by
  obtain ⟨hf,hb,ht⟩ := split_spec p word
  have ht0 : (splitMarkers p word).2.countP p=0 :=
    List.countP_eq_zero.mpr (by intro x hx; simp [ht x hx])
  have countBlocks (bs : List (List Event)) (hb : ∀ b∈bs, Block p b) :
      bs.flatten.countP p = bs.length := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have bc := block_count p b (hb b (by simp))
      have rest := ih (fun c hc => hb c (by simp [hc]))
      simp [List.countP_append,bc,rest,Nat.add_comm]
  calc
    word.countP p = ((splitMarkers p word).1.flatten ++ (splitMarkers p word).2).countP p := congrArg (List.countP p) hf.symm
    _ = (splitMarkers p word).1.length := by rw [List.countP_append,ht0,Nat.add_zero]; exact countBlocks _ hb

def marker (e : Event) : Bool :=
  e.place && decide (11 ≤ e.vertex ∧ (e.vertex-11)%6=0)

theorem marker_trace_iff (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (e : Event) (he : e∈word) :
    marker e=true ↔ ∃ j, j<k ∧ e.place=true ∧ e.vertex=11+6*j := by
  have hb := model.bounded e he
  simp only [marker,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hp,hlo,hmod⟩
    refine ⟨(e.vertex-11)/6,by omega,hp,?_⟩
    omega
  · rintro ⟨j,hj,hp,hv⟩
    exact ⟨hp,by omega,by omega⟩

theorem each_cut_count (k j : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (hj : j<k) :
    word.countP (FamilyCut.P (11+6*j))=1 := by
  rw [model.counts _ (by omega) (by omega)]
  have h := (block_placement_counts j).2.2.2.2.2.2
  have eqv : 11+6*j = 5+6*j+6 := by omega
  rw [eqv]
  exact h

theorem trace_simultaneous_split (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) :
    ∃ (blocks : List (List Event)) (tail : List Event),
      blocks.flatten ++ tail = word ∧
      (∀ b∈blocks, ∃ pre e j, b=pre++[e] ∧ j<k ∧ e.place=true ∧
        e.vertex=11+6*j ∧ (∀ x∈pre, marker x=false)) ∧
      (∀ e∈tail, marker e=false) ∧
      (∀ j, j<k → word.countP (FamilyCut.P (11+6*j))=1) := by
  obtain ⟨hf,hb,ht⟩ := split_spec marker word
  refine ⟨(splitMarkers marker word).1,(splitMarkers marker word).2,hf,?_,ht,
    fun j hj => each_cut_count k j erasures word model hj⟩
  intro b hmem
  obtain ⟨pre,e,he,hmark,hpre⟩ := hb b hmem
  have ew : e∈word := by
    rw [← hf]
    apply List.mem_append_left
    apply List.mem_flatten.mpr
    refine ⟨b,hmem,?_⟩
    simp [he]
  obtain ⟨j,hj,hp,hv⟩ := (marker_trace_iff k erasures word model e ew).mp hmark
  exact ⟨pre,e,j,he,hj,hp,hv,hpre⟩

#print axioms block_count
#print axioms split_marker_count
#print axioms split_spec
#print axioms marker_trace_iff
#print axioms each_cut_count
#print axioms trace_simultaneous_split
end GlobalSplit
