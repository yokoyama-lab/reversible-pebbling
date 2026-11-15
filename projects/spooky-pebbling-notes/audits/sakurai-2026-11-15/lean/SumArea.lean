import DepthArea
namespace SumArea
open DepthArea Forest

theorem pair_labels (keep : Nat → Bool) (h i d : Nat) :
 (pairs keep h i d).map Prod.fst = (HeapForest.labels h i).filter keep := by
 induction h generalizing i d with
 | zero => rfl
 | succ h ih => cases hk : keep i <;> simp [pairs,HeapForest.labels,hk,ih]

theorem filter_sum (xs : List α) (p : α → Bool) (f : α → Nat) :
 ((xs.filter p).map f).sum = (xs.map fun x => if p x then f x else 0).sum := by
 induction xs with
 | nil => rfl
 | cons x xs ih => cases hx : p x <;> simp [hx,ih]

theorem pair_sum (keep : Nat → Bool) (h i d : Nat) (f : Nat → Nat) :
 ((pairs keep h i d).map fun vd => f vd.1).sum =
 ((HeapForest.labels h i).map fun v => if keep v then f v else 0).sum := by
 have hh := congrArg (fun xs : List Nat => (xs.map f).sum) (pair_labels keep h i d)
 simpa only [List.map_map,Function.comp_def,filter_sum] using hh

open SpookyRound TraceBridge

theorem actual_pair_sum (as : List Action) (q : Config n) (H : Nat)
 (cover : (HeapForest.labels H 0).Perm ((List.finRange n).map Fin.val)) :
 ((pairs (HeapForest.lift (HeapForest.goodAt as q)) H 0 0).map fun vd =>
 clockLift as .unpebble n vd.1-clockLift as .pebble n vd.1).sum =
 ((List.finRange n).map fun v => if HeapForest.goodAt as q v then
 Nesting.time as v .unpebble-Nesting.time as v .pebble else 0).sum := by
 rw [pair_sum _ H 0 0 (fun v => clockLift as .unpebble n v-clockLift as .pebble n v)]
 have he := HeapForest.perm_sum (cover.map (fun v => if HeapForest.lift (HeapForest.goodAt as q) v then
 clockLift as .unpebble n v-clockLift as .pebble n v else 0))
 rw [he,List.map_map]
 congr 1
 apply List.map_congr_left
 intro v hv
 simp [Function.comp_def,HeapForest.lift,clockLift,v.isLt]

def deep (ell : Nat) (ds : List Nat) := (ds.filter fun d => decide (ell≤d)).length

theorem deep_weight (ds : List Nat) (ell : Nat) :
 (2*ell+1)*deep ell ds ≤ (ds.map fun d => 2*d+1).sum := by
 induction ds with
 | nil => simp [deep]
 | cons d ds ih =>
   by_cases hd : ell≤d
   · change (2*ell+1)*deep ell ds ≤ _ at ih
     simpa [deep,hd,Nat.mul_add,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add (show 2*ell+1≤2*d+1 by omega) ih
   · simp [deep,hd] at *
     omega

theorem partition (ds : List Nat) (ell : Nat) :
 (ds.filter fun d => decide (d<ell)).length + deep ell ds = ds.length := by
 induction ds with
 | nil => rfl
 | cons d ds ih => by_cases hd : d<ell <;> simp [deep,hd,show (ell≤d) ↔ ¬d<ell from by omega] at * <;> omega

theorem forest_deep (t : Tree) (ell : Nat) :
 good t-components false t*(2^ell-1) ≤ deep ell (depths 0 t) := by
 have hp := partition (depths 0 t) ell
 have hs := shallow_bound t ell
 rw [depths_count] at hp
 unfold shallow at hs
 omega

theorem actual_weight_area {q : Config n} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns HeapPath.pred q as r) (hs : r.space≤s)
 (hf : ∀ v : Fin n,0<v.val → kind r.state v=.empty)
 (H : Nat) (cover : (HeapForest.labels H 0).Perm ((List.finRange n).map Fin.val)) :
 ((depths 0 (HeapForest.embed (HeapForest.lift (HeapForest.goodAt as q)) H 0)).map fun d => 2*d+1).sum ≤ as.length*s := by
 have hh := Exceptions.sum_le (pairs (HeapForest.lift (HeapForest.goodAt as q)) H 0 0)
   (fun vd => 2*vd.2+1) (fun vd => clockLift as .unpebble n vd.1-clockLift as .pebble n vd.1)
   (actual_depth_span h hf H)
 rw [actual_pair_sum as q H cover] at hh
 have he := congrArg (fun xs : List Nat => (xs.map fun d => 2*d+1).sum)
   (pair_depths (HeapForest.lift (HeapForest.goodAt as q)) H 0 0)
 simp only [List.map_map,Function.comp_def] at he
 rw [he] at hh
 exact Nat.le_trans hh (HeapForest.actual_good_area h hs)

theorem actual_forest_lower {q : Config n} {r : SpookyDP.Result (Config n)}
 (h : ActionRuns HeapPath.pred q as r) (hs : r.space≤s)
 (hf : ∀ v : Fin n,0<v.val → kind r.state v=.empty)
 (H ell : Nat) (cover : (HeapForest.labels H 0).Perm ((List.finRange n).map Fin.val)) :
 let t := HeapForest.embed (HeapForest.lift (HeapForest.goodAt as q)) H 0
 (2*ell+1)*(good t-components false t*(2^ell-1)) ≤ as.length*s := by
 dsimp
 exact Nat.le_trans (Nat.mul_le_mul_left _ (forest_deep _ ell))
   (Nat.le_trans (deep_weight _ ell) (actual_weight_area h hs hf H cover))
theorem size_labels (keep : Nat → Bool) (H i : Nat) :
 size (HeapForest.embed keep H i) = (HeapForest.labels H i).length := by
 induction H generalizing i with
 | zero => rfl
 | succ H ih => simp [HeapForest.embed,HeapForest.labels,size,ih]; omega

theorem good_removed (pre post : List Action) (c : Config n) (root : Fin n)
 (hr : c.peb root=true) (H : Nat)
 (cover : (HeapForest.labels H 0).Perm ((List.finRange n).map Fin.val)) :
 good (HeapForest.embed (HeapForest.lift (HeapForest.goodAt post c)) H 0) =
 n-Exceptions.removed (Exceptions.accounts pre post c root) := by
 have hp := Forest.partition (HeapForest.embed (HeapForest.lift (HeapForest.goodAt post c)) H 0)
 rw [HeapForest.bad_fin _ H cover,HeapForest.bad_removed pre post c root hr,size_labels] at hp
 have hl := cover.length_eq
 simp only [List.length_map,List.length_finRange] at hl
 rw [hl] at hp
 omega

theorem occurrence_space (pre post : List Action) {pred : Fin n → Fin n → Bool}
 (h : ActionRuns pred q (pre++a::post) r) :
 ∃ c t, ActionRuns pred (afterRound c a) post t ∧ t.state=r.state ∧
 roundSpace c a≤r.space ∧ t.space≤r.space := by
 induction pre generalizing q r with
 | nil => cases h with
   | cons hm hg hl ht => exact ⟨_,_,ht,rfl,Nat.le_max_left _ _,Nat.le_max_right _ _⟩
 | cons b pre ih => cases h with
   | cons hm hg hl ht =>
     obtain ⟨c,t,hc,hf,hs,hts⟩ := ih ht
     exact ⟨c,t,hc,hf,Nat.le_trans hs (Nat.le_max_right _ _),Nat.le_trans hts (Nat.le_max_right _ _)⟩

theorem paper_finite_lower (H ell : Nat) (hn : 0<2^H-1)
 {q : Config (2^H-1)} {r : SpookyDP.Result (Config (2^H-1))}
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin (2^H-1),0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*(2^H-1)+e) (hspace : r.space≤s) :
 (2*ell+1)*((2^H-1)-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1)) ≤ d*s := by
 obtain ⟨pre,a,post,c0,t0,hd,ha,hroot,hlast,ht0,hfinal0,hclean⟩ :=
   WorkBridge.common_root_cut hn h (hs _) hr hf
 obtain ⟨c,t,ht,hfinal,hsp,htsp⟩ := occurrence_space pre post ha
 have hrootcut : (afterRound c a).peb ⟨0,hn⟩=true := by
   apply CutSpace.root_stays ht _ _ hlast
   rw [hfinal]; exact hr
 have hpebs : CutSpace.pebs (afterRound c a)≤s :=
   Nat.le_trans (CutSpace.after_space c a) (Nat.le_trans hsp hspace)
 have hb : Exceptions.removed (Exceptions.accounts (pre++[a]) post (afterRound c a) ⟨0,hn⟩)≤e+2*s+1 := by
   apply Exceptions.semantic_exception_bound (pre:=pre++[a]) (post:=post) (c:=afterRound c a)
   · simpa using ha
   · exact ht
   · exact hrootcut
   · exact Precut.precut_all hn ha hs hroot
   · intro u hu
     apply hclean u
     have hh : u.val≠0 := by intro hz; apply hu; apply Fin.ext; exact hz
     omega
   · exact hw
   · rw [CutSpace.account_pebs]; exact hpebs
 have hc := HeapForest.component_budget (pre++[a]) post (afterRound c a) ⟨0,hn⟩ hrootcut H
   (Coverage.all_height_coverage H) hb
 have hg := good_removed (pre++[a]) post (afterRound c a) ⟨0,hn⟩ hrootcut H (Coverage.all_height_coverage H)
 have hl := actual_forest_lower ht (Nat.le_trans htsp hspace)
   (fun v hv => by rw [hfinal]; exact hf v hv) H ell (Coverage.all_height_coverage H)
 have hmul := Nat.mul_le_mul_right (2^ell-1) hc
 have hgood : (2^H-1)-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1) ≤
   good (HeapForest.embed (HeapForest.lift (HeapForest.goodAt post (afterRound c a))) H 0)-
   components false (HeapForest.embed (HeapForest.lift (HeapForest.goodAt post (afterRound c a))) H 0)*(2^ell-1) := by omega
 have hlen : post.length≤d := by simp only [List.length_append,List.length_cons] at hd; omega
 exact Nat.le_trans (Nat.mul_le_mul_left _ hgood) (Nat.le_trans hl (Nat.mul_le_mul_right s hlen))
#print axioms paper_finite_lower
#print axioms actual_forest_lower
#print axioms actual_pair_sum
end SumArea
