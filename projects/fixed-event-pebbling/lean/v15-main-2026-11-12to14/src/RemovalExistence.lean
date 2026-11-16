import PositionOrder
import Lifetime
namespace RemovalExistence
open LocalCertificate ChainTrace ChainLifetime RemovalOrder PositionOrder

theorem last_vertex_event (word : List Event) (v : Nat)
    (h : ∃ e ∈ word, e.vertex = v) :
    ∃ pre e post, word = pre ++ e :: post ∧ e.vertex = v ∧
      ∀ f ∈ post, f.vertex ≠ v := by
  induction word with
  | nil => simp at h
  | cons a tail ih =>
    by_cases ht : ∃ e ∈ tail, e.vertex = v
    · obtain ⟨pre,e,post,hw,he,hn⟩ := ih ht
      exact ⟨a::pre,e,post, by simp [hw], he,hn⟩
    · obtain ⟨e,he,hev⟩ := h
      have hav : a.vertex = v := by
        rcases List.mem_cons.mp he with hh | hh
        · simpa [hh] using hev
        · exact False.elim (ht ⟨e,hh,hev⟩)
      refine ⟨[],a,tail,rfl,hav,?_⟩
      intro f hf hfv
      exact ht ⟨f,hf,hfv⟩

/-- A positive placement count and final absence force a final removal.
Every placement is before that removal, producing the exact certificate
needed by the physical checkpoint order theorem. -/
theorem exhausted_removal_exists (erasures final : List Nat) (word : List Event)
    (v budget : Nat) (hpos : 0 < budget)
    (hcount : word.countP (isPlacement v) = budget)
    (hfinal : v ∉ final) (hr : run erasures [] word = some final) :
    ∃ j, ExhaustedRemovalAt word v budget j := by
  have hc : 0 < word.countP (isPlacement v) := by omega
  obtain ⟨p,hp,hpv⟩ := List.countP_pos_iff.mp hc
  have pvertex : p.vertex = v := by
    simp [isPlacement] at hpv
    exact hpv.2
  obtain ⟨pre,e,post,hw,hev,hpost⟩ := last_vertex_event word v ⟨p,hp,pvertex⟩
  have hr' : run erasures [] (pre ++ e :: post) = some final := by simpa [hw] using hr
  rw [run_append] at hr'
  cases hb : run erasures [] pre with
  | none => simp [hb] at hr'
  | some before =>
    have hrest : run erasures before (e :: post) = some final := by simpa [hb] using hr'
    cases hs : step true erasures before e with
    | none => simp [run,hs] at hrest
    | some after =>
      have htail : run erasures after post = some final := by simpa [run,hs] using hrest
      have hremove : e.place = false := by
        cases hplace : e.place with
        | false => rfl
        | true =>
          have hpresent : v ∈ after := by simpa [hev] using placement_present erasures before after e hplace hs
          have hfmem := (run_membership_unchanged erasures after final post v hpost htail).mpr hpresent
          exact False.elim (hfinal hfmem)
      have hz : post.countP (isPlacement v) = 0 := by
        apply List.countP_eq_zero.mpr
        intro f hf
        simp [isPlacement,hpost f hf]
      have hpre : pre.countP (isPlacement v) = budget := by
        simpa [hw,List.countP_append,List.countP_cons,isPlacement,hremove,hz] using hcount
      refine ⟨pre.length,pre,post,e,hw,rfl,hremove,hev,?_,?_⟩
      · omega
      · omega
#print axioms last_vertex_event
#print axioms exhausted_removal_exists
/-- No removal-certificate existence is assumed: the six certificates
and their physical order are constructed from the placement counts. -/
theorem checkpoint_order_chain_exists
    (erasures final : List Nat) (word : List Event) (s pt : Nat)
    (hs : 0 < s) (hr : run erasures [] word = some final)
    (hno : ∀ v, s < v → v ≤ s+5 → v ∉ erasures)
    (hfinal : ∀ v, s ≤ v → v ≤ s+5 → v ∉ final)
    (hcounts : word.countP (isPlacement s) = 1 ∧
      word.countP (isPlacement (s+1)) = 2 ∧
      word.countP (isPlacement (s+2)) = 1 ∧
      word.countP (isPlacement (s+3)) = 2 ∧
      word.countP (isPlacement (s+4)) = 1 ∧
      word.countP (isPlacement (s+5)) = 1)
    (t : Event) (ht : word[pt]? = some t) (htv : t.vertex = s+6)
    (htp : t.place = true) :
    ∃ rs ra rb rc rd rh,
      ExhaustedRemovalAt word s 1 rs ∧
      ExhaustedRemovalAt word (s+1) 2 ra ∧
      ExhaustedRemovalAt word (s+2) 1 rb ∧
      ExhaustedRemovalAt word (s+3) 2 rc ∧
      ExhaustedRemovalAt word (s+4) 1 rd ∧
      ExhaustedRemovalAt word (s+5) 1 rh ∧
      pt < rh ∧ rh < rd ∧ rd < rc ∧ rc < rb ∧ rb < ra ∧ ra < rs := by
  obtain ⟨cs,ca,cb,cc,cd,ch⟩ := hcounts
  obtain ⟨rs,hrs⟩ := exhausted_removal_exists erasures final word s 1 (by decide) cs
    (hfinal _ (by omega) (by omega)) hr
  obtain ⟨ra,hra⟩ := exhausted_removal_exists erasures final word (s+1) 2 (by decide) ca
    (hfinal _ (by omega) (by omega)) hr
  obtain ⟨rb,hrb⟩ := exhausted_removal_exists erasures final word (s+2) 1 (by decide) cb
    (hfinal _ (by omega) (by omega)) hr
  obtain ⟨rc,hrc⟩ := exhausted_removal_exists erasures final word (s+3) 2 (by decide) cc
    (hfinal _ (by omega) (by omega)) hr
  obtain ⟨rd,hrd⟩ := exhausted_removal_exists erasures final word (s+4) 1 (by decide) cd
    (hfinal _ (by omega) (by omega)) hr
  obtain ⟨rh,hrh⟩ := exhausted_removal_exists erasures final word (s+5) 1 (by decide) ch
    (hfinal _ (by omega) (by omega)) hr
  exact ⟨rs,ra,rb,rc,rd,rh,hrs,hra,hrb,hrc,hrd,hrh,
    checkpoint_order_chain erasures final word s rs ra rb rc rd rh pt hs hr hno
      hrs hra hrb hrc hrd hrh t ht htv htp⟩
#print axioms checkpoint_order_chain_exists
end RemovalExistence
