import GlobalSplitOrder
import InitialActual
import ActualMiddle
import TailActual
namespace GlobalSplit
open LocalCertificate FamilyCut ChainEventEncoding

theorem block_endpoint (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (left right : List (List Event)) (b : List Event)
    (layout : (splitMarkers marker word).1 = left ++ b :: right) :
    left.length < k ∧ ∃ pre e, b=pre++[e] ∧ e.place=true ∧
      e.vertex=11+6*left.length := by
  have len := trace_blocks_length k erasures word model
  rw [layout,List.length_append,List.length_cons] at len
  have lt : left.length<k := by omega
  have indices := trace_block_indices k erasures word model
  rw [layout,List.map_append,List.map_cons] at indices
  have hatidx := congrArg (fun xs : List Nat => xs[left.length]?) indices
  rw [List.getElem?_range lt] at hatidx
  rw [List.getElem?_append_right (by simp)] at hatidx
  simp only [List.length_map,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at hatidx
  have spec := (split_spec marker word).2.1
  have bm : b∈(splitMarkers marker word).1 := by rw [layout]; simp
  obtain ⟨pre,e,he,hp,hpre⟩ := spec b bm
  have ew : e∈word := by
    rw [← (split_spec marker word).1]
    apply List.mem_append_left
    exact List.mem_flatten.mpr ⟨b,bm,by simp [he]⟩
  obtain ⟨j,hj,ep,ev⟩ := (marker_trace_iff k erasures word model e ew).mp hp
  have idx : index e = left.length := by
    simpa [endpointIndex,he] using hatidx
  unfold index at idx
  refine ⟨lt,pre,e,he,ep,?_⟩
  omega

theorem split_initial_good (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (b : List Event) (rest : List (List Event))
    (layout : (splitMarkers marker word).1 = b::rest) :
    ChainInitialSegment.Good (encode ChainInitialSegment.events b) := by
  obtain ⟨hk,pre,e,hb,hp,hv⟩ := block_endpoint k erasures word model [] rest b layout
  have hf := (split_spec marker word).1
  rw [layout] at hf
  have m : Trace k erasures (pre ++ e :: (rest.flatten ++ (splitMarkers marker word).2)) := by
    rw [← hf] at model
    simpa [hb,List.append_assoc] using model
  rw [hb]
  exact initial_actual_good k erasures pre _ e hk hp hv m

theorem split_middle_good (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (left right : List (List Event)) (a b : List Event)
    (layout : (splitMarkers marker word).1 = left ++ a::b::right) :
    ChainMiddleSegment.Good
      (encode (MiddleDifference.events (5+6*left.length)) b) := by
  obtain ⟨ha,ap,t,hat,htp,htv⟩ := block_endpoint k erasures word model left (b::right) a layout
  have lb : (splitMarkers marker word).1 = (left++[a]) ++ b::right := by simpa using layout
  obtain ⟨hb,bp,u,hbu,hup,huv⟩ := block_endpoint k erasures word model (left++[a]) right b lb
  have hj : left.length+1<k := by simpa using hb
  have hf := (split_spec marker word).1
  rw [layout] at hf
  apply actual_middle_good k left.length (5+6*left.length) erasures
    (left.flatten++ap) b (right.flatten++(splitMarkers marker word).2)
    ((left.flatten++a)++bp) t u hj rfl htp (by omega) hup
  · simp only [List.length_append,List.length_singleton] at huv
    omega
  · simp [hat,hbu,List.append_assoc]
  · rw [← hf] at model
    simpa [hat,List.append_assoc] using model

theorem split_tail_two (j : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace (j+1) erasures word) (left : List (List Event)) (b : List Event)
    (layout : (splitMarkers marker word).1 = left ++ [b]) :
    let tail := (splitMarkers marker word).2
    encode (TailActual.events (5+6*j)) tail = ChainTailSegment.wordA ∨
      encode (TailActual.events (5+6*j)) tail = ChainTailSegment.wordB := by
  obtain ⟨hi,pre,t,hb,hp,hv⟩ := block_endpoint (j+1) erasures word model left [] b layout
  have len := trace_blocks_length (j+1) erasures word model
  rw [layout,List.length_append,List.length_singleton] at len
  have ij : left.length=j := by omega
  have hf := (split_spec marker word).1
  rw [layout] at hf
  apply TailActual.tail_two j erasures (left.flatten++pre) _ t hp (by omega)
  rw [← hf] at model
  simpa [hb,List.append_assoc] using model

#print axioms block_endpoint
#print axioms split_initial_good
#print axioms split_middle_good
#print axioms split_tail_two
end GlobalSplit
