import EpochCharge
namespace GhostBudget
open SpookyRound TraceBridge CutBound
variable {n : Nat} {pred : Fin n → Fin n → Bool} {q c : Config n}
 {r t : SpookyDP.Result (Config n)}

def ghosts (post : List Action) : Nat :=
 ((List.finRange n).map fun v => count .ghost (events v post)).sum

def account (pre post : List Action) (c : Config n) (root v : Fin n) : Account :=
 ⟨count .compute (events v pre),count .compute (events v post),
 count .uncompute (events v post),if c.peb v then 1 else 0,if v=root then 1 else 0⟩

theorem scalar_charge (a : Account) (g : Nat) (hv : Valid a)
 (hb : a.postCompute+a.cutPebble=g+a.postUncompute+a.isRoot) :
 3+g≤a.preCompute+a.postCompute+a.postUncompute+a.cutPebble+a.isRoot := by
 unfold Valid at hv
 omega

theorem sum_charge (xs : List α) (a : α → Account) (g : α → Nat)
 (h : ∀v ∈ xs,3+g v≤(a v).preCompute+(a v).postCompute+(a v).postUncompute+(a v).cutPebble+(a v).isRoot) :
 3*xs.length+(xs.map g).sum ≤ work (xs.map a)+pebbles (xs.map a)+roots (xs.map a) := by
 induction xs with
 | nil => simp [work,pebbles,roots]
 | cons v xs ih =>
   have hh := h v (by simp)
   have hr := ih (fun u hu => h u (by simp [hu]))
   simp only [List.length_cons,List.map_cons,List.sum_cons,work,pebbles,roots] at *
   omega

theorem occupied_kind (c : Config n) (v : Fin n) : occupied (kind c v)=(if c.peb v then 1 else 0) := by
 cases hp : c.peb v <;> cases hg : c.ghost v <;> simp [kind,occupied,hp,hg]

theorem semantic (h : ActionRuns pred q (pre++post) r)
 (ht : ActionRuns pred c post t) (root : Fin n)
 (hroot : c.peb root=true)
 (hc : ∀v : Fin n, ∃a ∈ pre, firstAt a v=.pebble)
 (hu : ∀v : Fin n,v≠root → ∃a ∈ post,firstAt a v=.unpebble)
 (hf : ∀v : Fin n, kind t.state v=if v=root then .pebble else .empty)
 (hw : r.work≤3*n+e) (hp : CutSpace.pebs c≤s) : ghosts (n:=n) post≤e+s+1 := by
 have hv := Exceptions.accounts_valid ht root hroot hc hu
 have hb : ∀v : Fin n,(account pre post c root v).postCompute+(account pre post c root v).cutPebble =
   count .ghost (events v post)+(account pre post c root v).postUncompute+(account pre post c root v).isRoot := by
   intro v
   have hh := EpochCharge.balance (actionruns_scalar ht v)
   rw [hf v] at hh
   rw [occupied_kind] at hh
   by_cases hr : v=root <;> simpa [account,occupied,hr] using hh
 have hall := sum_charge (List.finRange n) (account pre post c root) (fun v => count .ghost (events v post)) (by
   intro v hvv
   apply scalar_charge _ _ _ (hb v)
   apply hv
   exact List.mem_map.mpr ⟨v,hvv,rfl⟩)
 have he : (List.finRange n).map (account pre post c root)=Exceptions.accounts pre post c root := rfl
 rw [he,List.length_finRange] at hall
 have hw' := Exceptions.account_work_le h c root
 have hp' := CutSpace.account_pebs pre post c root
 have hr' := Exceptions.roots_bound pre post c root
 unfold ghosts
 omega
#print axioms semantic

theorem paper_ghost_budget (hn : 0<n)
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin n,0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*n+e) (hspace : r.space≤s) :
 ∃pre a post c, (pre++a::post).length=d ∧
 ActionRuns HeapPath.pred q (pre++a::post) r ∧
 c.peb ⟨0,hn⟩=true ∧ CutSpace.pebs c≤s ∧ ghosts (n:=n) post≤e+s+1 := by
 obtain ⟨pre,a,post,c0,t0,hd,ha,hroot,hlast,ht0,hfinal0,hclean⟩ :=
   WorkBridge.common_root_cut hn h (hs _) hr hf
 obtain ⟨c,t,ht,hfinal,hsp⟩ := CutSpace.occurrence pre post ha
 have hrootcut : (afterRound c a).peb ⟨0,hn⟩=true := by
   apply CutSpace.root_stays ht _ _ hlast
   rw [hfinal]; exact hr
 have hpebs : CutSpace.pebs (afterRound c a)≤s :=
   Nat.le_trans (CutSpace.after_space c a) (Nat.le_trans hsp hspace)
 refine ⟨pre,a,post,afterRound c a,hd,ha,hrootcut,hpebs,?_⟩
 apply semantic (pre:=pre++[a]) (post:=post) (c:=afterRound c a) (t:=t) (root:=⟨0,hn⟩)
 · simpa using ha
 · exact ht
 · exact hrootcut
 · exact Precut.precut_all hn ha hs hroot
 · intro u hu
   apply hclean u
   have hh : u.val≠0 := by intro hz; apply hu; apply Fin.ext; exact hz
   omega
 · intro u
   rw [hfinal]
   by_cases hu : u=⟨0,hn⟩
   · simpa [hu] using hr
   · have hh : 0<u.val := by
       have hnz : u.val≠0 := by intro hz; apply hu; apply Fin.ext; exact hz
       omega
     simpa [hu] using hf u hh
 · exact hw
 · exact hpebs
#print axioms paper_ghost_budget

theorem count_flatten (e : Event) (ss : List (List Event)) :
 count e ss.flatten=(ss.map (count e)).sum := by
 induction ss with
 | nil => rfl
 | cons xs ss ih => simp [List.flatten_cons,EpochCharge.count_append,ih]

theorem disjoint_split_charge (front back : List Event) (ss : List (List Event))
 (h : ∀xs ∈ ss,Trace .pebble xs .pebble) :
 (ss.map (count .ghost)).sum≤count .compute (front++ss.flatten++back) := by
 have hc := EpochCharge.charge_segments ss h
 rw [EpochCharge.count_append,EpochCharge.count_append,count_flatten]
 omega
#print axioms disjoint_split_charge
end GhostBudget
