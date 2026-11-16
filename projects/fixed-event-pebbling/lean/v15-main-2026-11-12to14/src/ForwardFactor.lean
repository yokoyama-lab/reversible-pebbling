import GlobalSplitGood
import FactorRecovery
import GlobalReassembly
namespace GlobalSplit
open LocalCertificate ChainTrace FamilyCut ChainEventEncoding ChainGlobalReassembly
theorem split_initial_perm (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (b : List Event) (rest : List (List Event))
    (layout : (splitMarkers marker word).1 = b::rest) :
    b.Perm ChainInitialSegment.events := by
  obtain ⟨hk,pre,e,hb,hp,hv⟩ := block_endpoint k erasures word model [] rest b layout
  have hf := (split_spec marker word).1
  rw [layout] at hf
  have m : Trace k erasures (pre ++ e :: (rest.flatten ++ (splitMarkers marker word).2)) := by
    rw [← hf] at model
    simpa [hb,List.append_assoc] using model
  rw [hb]
  exact initial_prefix_perm k erasures pre _ e hk hp hv m

theorem split_middle_perm (k : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace k erasures word) (left right : List (List Event)) (a b : List Event)
    (layout : (splitMarkers marker word).1 = left ++ a::b::right) :
    b.Perm (MiddleDifference.events (5+6*left.length)) := by
  obtain ⟨ha,ap,t,hat,htp,htv⟩ := block_endpoint k erasures word model left (b::right) a layout
  have lb : (splitMarkers marker word).1 = (left++[a]) ++ b::right := by simpa using layout
  obtain ⟨hb,bp,u,hbu,hup,huv⟩ := block_endpoint k erasures word model (left++[a]) right b lb
  have hj : left.length+1<k := by simpa using hb
  have hf := (split_spec marker word).1
  rw [layout] at hf
  apply middle_interval_perm k left.length (5+6*left.length) erasures
    (left.flatten++ap) b (right.flatten++(splitMarkers marker word).2)
    ((left.flatten++a)++bp) t u hj rfl htp (by omega) hup
  · simp only [List.length_append,List.length_singleton] at huv
    omega
  · simp [hat,hbu,List.append_assoc]
  · rw [← hf] at model
    simpa [hat,List.append_assoc] using model

theorem split_tail_perm (j : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace (j+1) erasures word) (left : List (List Event)) (b : List Event)
    (layout : (splitMarkers marker word).1 = left ++ [b]) :
    (splitMarkers marker word).2.Perm (TailActual.events (5+6*j)) := by
  obtain ⟨hi,pre,t,hb,hp,hv⟩ := block_endpoint (j+1) erasures word model left [] b layout
  have len := trace_blocks_length (j+1) erasures word model
  rw [layout,List.length_append,List.length_singleton] at len
  have ij : left.length=j := by omega
  have hf := (split_spec marker word).1
  rw [layout] at hf
  apply TailActual.tail_perm j erasures (left.flatten++pre) _ t hp (by omega)
  rw [← hf] at model
  simpa [hb,List.append_assoc] using model

theorem adjacent_layout (first : List Event) (ms : List (List Event)) (j : Nat)
    (hj : j<ms.length) :
    ∃ left a right, first::ms=left++a::ms.getD j []::right ∧ left.length=j := by
  induction j generalizing first ms with
  | zero =>
    cases ms with
    | nil => simp at hj
    | cons b rest => exact ⟨[],first,rest,rfl,rfl⟩
  | succ j ih =>
    cases ms with
    | nil => simp at hj
    | cons b rest =>
      obtain ⟨left,a,right,he,hl⟩ := ih b rest (by simpa using hj)
      refine ⟨first::left,a,right,?_,?_⟩
      · change first :: (b::rest) = first :: (left++a::rest.getD j []::right)
        exact congrArg (List.cons first) he
      · simp [hl]

theorem assemble_list (ms : List (List Event)) (n : Nat) (hn : n≤ms.length) :
    assemble (fun j => ms.getD j []) n = (ms.take n).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n<ms.length := by omega
    rw [assemble,ih (by omega),List.take_succ_eq_append_getElem hlt]
    simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt,Option.getD_some]

theorem forward_factorization (r : Nat) (erasures : List Nat) (word : List Event)
    (model : Trace (r+1) erasures word) :
    ∃ (iu tw : List Nat) (mu : Nat → List Nat)
      (initial tail : List Event) (middles : Nat → List Event),
      I.Legal iu ∧ (∀ j, j<r → M.Legal (mu j)) ∧
      (tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB) ∧
      decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iu)=some initial ∧
      (∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
        (ChainMiddleConverse.liftWord (mu j))=some (middles j)) ∧
      decodeTrace (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events) tw=some tail ∧
      word=initial ++ assemble middles r ++ tail := by
  let bs := (splitMarkers marker word).1
  let tail := (splitMarkers marker word).2
  have len : bs.length=r+1 := trace_blocks_length (r+1) erasures word model
  cases hb : bs with
  | nil => simp [hb] at len
  | cons initial ms =>
    have hms : ms.length=r := by simp [hb] at len; omega
    have layout : (splitMarkers marker word).1=initial::ms := hb
    let iw := encode ChainInitialSegment.events initial
    have ip := split_initial_perm (r+1) erasures word model initial ms layout
    have ig := split_initial_good (r+1) erasures word model initial ms layout
    have ie : iw=ChainInitialConverse.liftWord (ChainInitialSegment.middle iw) :=
      ChainFactorRecovery.initial_recovery iw
        (encoded_isPermutation _ initial initial_table_nodup ip) ig
    let mw := fun j => encode (MiddleDifference.events (5+6*j)) (ms.getD j [])
    have mp (j : Nat) (hj : j<r) :
        (ms.getD j []).Perm (MiddleDifference.events (5+6*j)) ∧
        ChainMiddleSegment.Good (mw j) := by
      obtain ⟨left,a,right,he,hl⟩ := adjacent_layout initial ms j (by omega)
      have lay : (splitMarkers marker word).1=left++a::ms.getD j []::right :=
        layout.trans he
      have p := split_middle_perm (r+1) erasures word model left right a (ms.getD j []) lay
      have g := split_middle_good (r+1) erasures word model left right a (ms.getD j []) lay
      simpa [hl,mw] using And.intro p g
    have ml (j : Nat) (hj : j<r) :
        mw j=ChainMiddleConverse.liftWord (ChainMiddleSegment.middle (mw j)) :=
      ChainFactorRecovery.middle_recovery (mw j)
        (by
          have h := encoded_isPermutation (MiddleDifference.events (5+6*j)) (ms.getD j [])
            (MiddleDifference.events_nodup _) (mp j hj).1
          simpa [MiddleDifference.events,mw] using h) (mp j hj).2
    have lastlayout : ∃ left b, bs=left++[b] := by
      have ne : bs≠[] := by intro h; simp [h] at len
      exact ⟨bs.dropLast,bs.getLast ne,(List.dropLast_concat_getLast ne).symm⟩
    obtain ⟨left,last,hlast⟩ := lastlayout
    have lastlay : (splitMarkers marker word).1=left++[last] := hlast
    let tw := encode (TailActual.events (5+6*r)) tail
    have tp := split_tail_perm r erasures word model left last lastlay
    have tg := split_tail_two r erasures word model left last lastlay
    refine ⟨ChainInitialSegment.middle iw,tw,
      (fun j => ChainMiddleSegment.middle (mw j)),initial,tail,(fun j => ms.getD j []),
      ig.2.2,(fun j hj => (mp j hj).2.2.2),tg,?_,?_,?_,?_⟩
    · rw [← ie]
      exact decode_encode _ initial (fun e he => ip.mem_iff.mp he)
    · intro j hj
      rw [← ml j hj]
      exact decode_encode _ _ (fun e he => (mp j hj).1.mem_iff.mp he)
    · rw [← TailActual.table_shift r]
      exact decode_encode _ tail (fun e he => tp.mem_iff.mp he)
    · have hf := (split_spec marker word).1
      rw [layout] at hf
      have ass := assemble_list ms r (by omega)
      have takeeq : ms.take r=ms := by rw [← hms,List.take_length]
      rw [takeeq] at ass
      simpa only [List.flatten_cons,← ass] using hf.symm

#print axioms split_initial_perm
#print axioms split_middle_perm
#print axioms split_tail_perm
#print axioms adjacent_layout
#print axioms assemble_list
#print axioms forward_factorization
end GlobalSplit
