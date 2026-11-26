import RepresentativeLowerBounds

namespace AtlasMemo
open AtlasLower

abbrev State := List W
abbrev Layer := Array State
abbrev Table := Array Layer

def canon (s : State) : State := s.insertionSort (fun a b => a.toNat ≤ b.toNat)

theorem canon_perm (s : State) : (canon s).Perm s := List.perm_insertionSort _ _

def lookupAux (xs : Layer) (q : State) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel+1, lo, hi =>
    if lo < hi then
      let j := (lo+hi)/2
      match xs[j]? with
      | none => false
      | some s => if q == s then true else if q.lex s (fun a b => decide (a.toNat < b.toNat)) then
            lookupAux xs q fuel lo j else lookupAux xs q fuel (j+1) hi
    else false

def lookup (xs : Layer) (s : State) : Bool := lookupAux xs (canon s) (xs.size+1) 0 xs.size

theorem lookupAux_mem (xs : Layer) (q : State) (fuel lo hi : ℕ)
    (h : lookupAux xs q fuel lo hi = true) : q ∈ xs := by
  induction fuel generalizing lo hi with
  | zero => simp [lookupAux] at h
  | succ fuel ih =>
    simp only [lookupAux] at h
    split at h <;> rename_i hlt
    · split at h
      · contradiction
      · rename_i s hs
        split at h
        · rename_i eq
          have qe : q = s := by simpa using eq
          exact qe ▸ Array.mem_of_getElem? hs
        · split at h <;> exact ih _ _ h
    · contradiction

-- Reject every unusable branch by cardinality, coverage, or the already-present output word.
def nextOK (k : ℕ) (following : Layer) (parent : State) (a b : W) (r : State) : Bool :=
  (ops a b).all fun z => parent.contains z || (keepChoices a b r).all fun kept =>
    decide (k < kept.length) || cuts (z :: kept) != -1 || lookup following (z :: kept)

def stateOK (following : Layer) (d : ℕ) (s : State) : Bool :=
  !(s.contains goal) && match d with
    | 0 => true
    | k+1 => (pairs s).all fun p => nextOK k following s p.1 p.2.1 p.2.2

def layer (tab : Table) (k : ℕ) : Layer := tab[k]?.getD #[]

def checks (tab : Table) (k : ℕ) : Bool := (List.range (k+1)).all fun d =>
  (layer tab d).all fun s => stateOK (layer tab (d-1)) d s

def roots (tab : Table) (k : ℕ) (xs : State) : Bool := xs.sublists.all fun s =>
  decide (k+1 < s.length) || cuts s != -1 || lookup (layer tab k) s

def check (tab : Table) (k : ℕ) (xs : State) : Bool := roots tab k xs && checks tab k

theorem nextOK_sound {k : ℕ} {following : Layer} {ws : State} {a b z : W} {r : State}
    {needed : Finset W} (nd : ws.Nodup) (pr : ws.Perm (a :: b :: r))
    (eqn : ws.toFinset = insert a (insert b needed)) (hz : z ∈ basicOps a b)
    (fresh : z ∉ ws.toFinset) (tail : live basicOps goal k (insert z needed))
    (ok : nextOK k following ws a b r = true) :
    ∃ s ∈ following, s.Nodup ∧ live basicOps goal k s.toFinset := by
  obtain ⟨kept,hkept,hn,hs⟩ := recover_kept pr nd eqn
  have hf : z ∉ kept := by
    intro h; apply fresh; rw [eqn]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hs ▸ List.mem_toFinset.mpr h))
  have child_nd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hf,hn⟩
  have child : live basicOps goal k (z :: kept).toFinset := by simpa [hs] using tail
  have length := live_card child
  rw [List.toFinset_card_of_nodup child_nd, List.length_cons] at length
  have hc := cuts_full child
  have old : ws.contains z = false := by simpa using fresh
  have h1 := List.all_eq_true.mp ok z (List.mem_toFinset.mp hz)
  simp only [old, Bool.false_or] at h1
  have h2 := List.all_eq_true.mp h1 kept hkept
  have filtered : decide (k < kept.length) = false := by simp; omega
  simp only [filtered, hc, bne_self_eq_false, Bool.false_or] at h2
  have mem := lookupAux_mem _ _ _ _ _ h2
  have perm := canon_perm (z :: kept)
  have seteq : (canon (z :: kept)).toFinset = (z :: kept).toFinset := by
    ext w; simpa only [List.mem_toFinset] using perm.mem_iff
  exact ⟨_,mem,perm.nodup_iff.mpr child_nd,seteq ▸ child⟩

theorem noLive {tab : Table} {budget d : ℕ} (checks_ok : checks tab budget = true) (hdb : d ≤ budget) :
    ∀ s ∈ layer tab d, s.Nodup → ¬ live basicOps goal d s.toFinset := by
  induction d with
  | zero =>
    intro s hm hn h
    have all := List.all_eq_true.mp checks_ok 0 (List.mem_range.mpr (by omega))
    have ok := Array.all_eq_true_iff_forall_mem.mp all s hm
    have he := singleton_list hn h
    simp [stateOK,he] at ok
  | succ d ih =>
    intro s hm hn h
    have all := List.all_eq_true.mp checks_ok (d+1) (List.mem_range.mpr (by omega))
    have ok := Array.all_eq_true_iff_forall_mem.mp all s hm
    change (!s.contains goal && (pairs s).all (fun p => nextOK d (layer tab d) s p.1 p.2.1 p.2.2)) = true at ok
    obtain ⟨notGoal, rest⟩ := Bool.and_eq_true_iff.mp ok
    let f : W × W × State → Bool := fun p => nextOK d (layer tab d) s p.1 p.2.1 p.2.2
    have pair_ok : ∀ p ∈ pairs s, f p = true := (List.all_eq_true (l := pairs s) (p := f)).mp rest
    rcases first_live h with done | ⟨a,ha,b,hb,hneq,z,hz,hfresh,U,heq,ht⟩
    · have he := singleton_list hn done; simp [he] at notGoal
    · obtain ⟨r,pair,pr⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hneq
      have step : ∃ s ∈ layer tab d, s.Nodup ∧ live basicOps goal d s.toFinset := by
        rcases pair with direct | swapped
        · have hcheck : nextOK d (layer tab d) s a b r = true := pair_ok (a,b,r) direct
          exact nextOK_sound (k := d) (following := layer tab d) (ws := s) (a := a) (b := b)
            (z := z) (r := r) (needed := U) hn pr heq hz hfresh ht hcheck
        · have hcheck : nextOK d (layer tab d) s b a r = true := pair_ok (b,a,r) swapped
          have se : s.toFinset = insert b (insert a U) := heq.trans (Finset.insert_comm a b U)
          exact nextOK_sound (k := d) (following := layer tab d) (ws := s) (a := b) (b := a)
            (z := z) (r := r) (needed := U) hn (pr.trans (.swap _ _ _)) se (ops_swap a b ▸ hz) hfresh ht hcheck
      obtain ⟨w,hw,hnd,run⟩ := step
      exact ih (by omega) w hw hnd run

theorem noBuild {tab : Table} {k : ℕ} {xs : State} (nd : xs.Nodup) (ok : check tab k xs = true) :
    ¬ build basicOps goal k xs.toFinset := by
  intro h
  obtain ⟨roots_ok, checks_ok⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨S,hS,run⟩ := compress h
  let s := xs.filter fun w => decide (w ∈ S)
  have seteq : s.toFinset = S := by
    ext w; simp only [s, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h),h⟩⟩
  have snd : s.Nodup := nd.filter _
  have liveS : live basicOps goal k s.toFinset := seteq ▸ run
  have bound := live_card liveS
  rw [List.toFinset_card_of_nodup snd] at bound
  have root := List.all_eq_true.mp roots_ok s (List.mem_sublists.mpr List.filter_sublist)
  have len : decide (k+1 < s.length) = false := by simp; omega
  simp only [len,cuts_full liveS,bne_self_eq_false,Bool.false_or] at root
  have pr := canon_perm s
  have same : (canon s).toFinset = s.toFinset := by
    ext w; simpa only [List.mem_toFinset] using pr.mem_iff
  exact noLive checks_ok le_rfl _ (lookupAux_mem _ _ _ _ _ root) (pr.nodup_iff.mpr snd) (same ▸ liveS)

theorem singles_back {xs : State} {a : W} {r : State} (h : (a,r) ∈ singles xs) : xs.Perm (a :: r) := by
  induction xs generalizing a r with
  | nil => simp [singles] at h
  | cons w s ih =>
    rcases List.mem_cons.mp h with eq | hm
    · cases eq; exact .refl _
    · obtain ⟨⟨b,t⟩, hb, eq⟩ := List.mem_map.mp hm
      cases eq
      exact ((ih hb).cons w).trans (.swap _ _ _)

theorem pairs_back {xs : State} {a b : W} {r : State} (h : (a,b,r) ∈ pairs xs) : xs.Perm (a :: b :: r) := by
  induction xs generalizing a b r with
  | nil => simp [pairs] at h
  | cons w s ih =>
    rcases List.mem_append.mp h with first | rest
    · obtain ⟨⟨b,t⟩, hb, eq⟩ := List.mem_map.mp first
      cases eq
      exact (singles_back hb).cons w
    · obtain ⟨⟨a,b,t⟩, hb, eq⟩ := List.mem_map.mp rest
      cases eq
      exact ((ih hb).cons w).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

theorem dispatch_ex {extra : ℕ} {next : ℕ → State → Bool} {a b : W} {r : State}
    (h : dispatch extra next a b r = true) :
    ∃ z ∈ basicOps a b, ∃ t ∈ keepChoices a b r, ∃ e, next e (z :: t) = true := by
  obtain ⟨z,hz,yes⟩ := List.any_eq_true.mp h
  refine ⟨z,List.mem_toFinset.mpr hz,?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at yes
  rcases yes with ((⟨-,v⟩ | ⟨-,(⟨-,v⟩ | ⟨-,v⟩)⟩) | ⟨-,v⟩)
  · exact ⟨_,by simp [keepChoices],_,v⟩
  · exact ⟨_,by simp [keepChoices],_,v⟩
  · exact ⟨_,by simp [keepChoices],_,v⟩
  · exact ⟨_,by simp [keepChoices],_,v⟩

theorem optimized_build {n extra : ℕ} {xs : State} {S : Finset W}
    (subset : ∀ x ∈ xs, x ∈ S) (h : optimized n extra xs = true) : build basicOps goal n S := by
  induction n generalizing extra xs S with
  | zero =>
    have eq : xs = [goal] := by simpa [optimized] using h
    exact subset goal (by simp [eq])
  | succ n ih =>
    simp only [optimized, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with eq | ⟨⟨a,b,r⟩,hp,hd⟩
    · exact Or.inl (show build basicOps goal n S from by
        have hg := subset goal (by simp [eq]); clear * -hg; induction n with
        | zero => exact hg
        | succ _ ih => exact Or.inl ih)
    · obtain ⟨z,hz,t,ht,e,ok⟩ := dispatch_ex hd
      have pp := pairs_back hp
      have sub : ∀ w ∈ a :: b :: r, w ∈ S := fun x hx => subset _ (pp.mem_iff.mpr hx)
      have keep : ∀ w ∈ t, w ∈ S := by
        simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> intro w hw <;> apply sub <;> simp only [List.mem_cons] at * <;> tauto
      have aS := sub a (by simp)
      have bS := sub b (by simp)
      by_cases same : a = b
      · subst b
        have zz : z = a := by simpa [basicOps,ops] using hz
        subst z
        apply Or.inl (ih (S := S) ?_ ok)
        intro w hw; rcases List.mem_cons.mp hw with rfl | hw
        · exact aS
        · exact keep _ hw
      · refine Or.inr ⟨a,aS,b,bS,same,z,hz,ih (S := insert z S) ?_ ok⟩
        intro w hw; rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · exact Finset.mem_insert_of_mem (keep _ hw)

theorem sound {m k : ℕ} {xs : State} {samp : Fin 112 → Fin 3 × Fin 5} (tab : Table)
    (bits : ∀ j, xs.map (fun z : W => z[j.val]) = PEqualNP.Represents.oneEach (samp j).1 (samp j).2)
    (labels : ∀ j, goal[j.val] = graph m (samp j).1 (samp j).2)
    (nd : xs.Nodup) (ok : check tab k xs = true) : lower m (k+1) := by
  apply AtlasLower.sound bits labels nd
  apply List.all_eq_true.mpr
  intro s hs
  by_cases b : optimized k (k+1 - s.length) s = true
  · exact (noBuild nd ok (optimized_build (fun x hx => List.mem_toFinset.mpr ((List.mem_sublists.mp hs).subset hx)) b)).elim
  · simp_all

end AtlasMemo
