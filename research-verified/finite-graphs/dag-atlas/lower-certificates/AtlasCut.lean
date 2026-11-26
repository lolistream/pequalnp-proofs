import MemoLower

namespace AtlasCut
open AtlasLower AtlasMemo

/-- No listed state can finish within the remaining gate budget. -/
def Anchors (k : ℕ) (level : Layer) : Prop :=
  ∀ s ∈ level, s.Nodup → ¬ live basicOps goal k s.toFinset

/-- A small recursive replay may close an individual state at the cut. -/
theorem leaf {k : ℕ} {s : State} (h : optimized k (k+1-s.length) s = false)
    (hn : s.Nodup) : ¬ live basicOps goal k s.toFinset := by
  intro hrun
  have hlen := live_card hrun
  rw [List.toFinset_card_of_nodup hn] at hlen
  have yes := optimized_complete k s (k+1-s.length) hn (by omega) hrun
  rw [h] at yes
  cases yes

/-- Above the cut, only completeness of the next layer needs to be replayed. -/
theorem step {d : ℕ} {next current : Layer} (bottom : Anchors d next)
    (closed : current.all (stateOK next (d+1)) = true) : Anchors (d+1) current := by
  intro s hs hn hrun
  have ok := Array.all_eq_true_iff_forall_mem.mp closed s hs
  change (!s.contains goal && (pairs s).all (fun p => nextOK d next s p.1 p.2.1 p.2.2)) = true at ok
  obtain ⟨notGoal, rest⟩ := Bool.and_eq_true_iff.mp ok
  let f : W × W × State → Bool := fun p => nextOK d next s p.1 p.2.1 p.2.2
  have pair_ok : ∀ p ∈ pairs s, f p = true := (List.all_eq_true (l := pairs s) (p := f)).mp rest
  rcases first_live hrun with done | ⟨a,ha,b,hb,hnq,z,hz,hfresh,U,heq,ht⟩
  · have he := singleton_list hn done
    simp [he] at notGoal
  · obtain ⟨r,pair,pr⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hnq
    have child : ∃ t ∈ next, t.Nodup ∧ live basicOps goal d t.toFinset := by
      rcases pair with direct | swapped
      · exact nextOK_sound (k := d) (following := next) (ws := s) (a := a) (b := b)
          (z := z) (r := r) (needed := U) hn pr heq hz hfresh ht (pair_ok (a,b,r) direct)
      · have se : s.toFinset = insert b (insert a U) := heq.trans (Finset.insert_comm a b U)
        exact nextOK_sound (k := d) (following := next) (ws := s) (a := b) (b := a)
          (z := z) (r := r) (needed := U) hn (pr.trans (.swap _ _ _)) se
          (ops_swap a b ▸ hz) hfresh ht (pair_ok (b,a,r) swapped)
    obtain ⟨t, ht', hnd, run⟩ := child
    exact bottom t ht' hnd run

private theorem root_no_build {tab : Table} {k : ℕ} {xs : State} (nd : xs.Nodup)
    (coverage : roots tab k xs = true) (closed : Anchors k (layer tab k)) :
    ¬ build basicOps goal k xs.toFinset := by
  intro h
  obtain ⟨S,hS,run⟩ := compress h
  let s := xs.filter fun w => decide (w ∈ S)
  have seteq : s.toFinset = S := by
    ext w
    simp only [s, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h),h⟩⟩
  have snd : s.Nodup := nd.filter _
  have liveS : live basicOps goal k s.toFinset := seteq ▸ run
  have bound := live_card liveS
  rw [List.toFinset_card_of_nodup snd] at bound
  have hit := List.all_eq_true.mp coverage s (List.mem_sublists.mpr List.filter_sublist)
  have len : decide (k+1 < s.length) = false := by simp; omega
  simp only [len,cuts_full liveS,bne_self_eq_false,Bool.false_or] at hit
  have pr := canon_perm s
  have same : (canon s).toFinset = s.toFinset := by
    ext w; simpa only [List.mem_toFinset] using pr.mem_iff
  exact closed _ (lookupAux_mem _ _ _ _ _ hit) (pr.nodup_iff.mpr snd) (same ▸ liveS)

/-- A possibly shallow table plus independently checked cut obligations proves the lower bound. -/
theorem sound {m k : ℕ} {xs : State} {samp : Fin 112 → Fin 3 × Fin 5} (tab : Table)
    (bits : ∀ j, xs.map (fun z : W => z[j.val]) = PEqualNP.Represents.oneEach (samp j).1 (samp j).2)
    (labels : ∀ j, goal[j.val] = graph m (samp j).1 (samp j).2)
    (nd : xs.Nodup) (coverage : roots tab k xs = true) (closed : Anchors k (layer tab k)) :
    lower m (k+1) := by
  apply AtlasLower.sound bits labels nd
  apply List.all_eq_true.mpr
  intro s hs
  by_cases b : optimized k (k+1 - s.length) s = true
  · exact (root_no_build nd coverage closed (optimized_build (fun x hx =>
      List.mem_toFinset.mpr ((List.mem_sublists.mp hs).subset hx)) b)).elim
  · simp_all

end AtlasCut
