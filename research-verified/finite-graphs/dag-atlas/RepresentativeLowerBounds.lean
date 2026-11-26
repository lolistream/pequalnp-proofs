/- This shared finite-word lower-bound checker adapts the argument from upstream
   PEqualNP.Outside.L_meta_5473. A fixed-width word stores a pair of sampled truth
   columns; the samples and the lower-bound checks are proved correct inside Lean. -/
import Mathlib
import PEqualNP.Defs

namespace AtlasLower

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 112

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 56 := ((x >>> 56) &&& ~~~x).setWidth 56

def cuts (ws : List W) : BitVec 56 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 56) ++ (0 : BitVec 56)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 56) (w : W) : Prop :=
  w.getLsbD (56 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 56) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (56 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (56 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 56, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 56) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 112 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 56)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 112 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 112) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 112) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 112, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 112 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 112 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 112 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 112 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 112) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 112 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


def graph (m : ℕ) (u : Fin 3) (v : Fin 5) : Bool := m.testBit (5*u.val+v.val)

def cells : List (Fin 3 × Fin 5) :=
  (List.finRange 3).flatMap fun u => (List.finRange 5).map fun v => (u,v)

def sample (m : ℕ) (k : Fin 112) : Fin 3 × Fin 5 :=
  let pos := cells.filter fun p => graph m p.1 p.2
  let negs := cells.filter fun p => !graph m p.1 p.2
  if k.val < 56 then negs.getD ((k.val / pos.length) % negs.length) (0,0)
  else pos.getD ((k.val-56) % pos.length) (0,0)

def front (k : ℕ) (xs : List W) : Bool := xs.sublists.all fun l =>
  decide (k+1 < l.length) || cuts l != -1 || !(optimized k (k+1-l.length) l)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def lower (m size : ℕ) : Prop := ∀ t, PEqualNP.Represents.RepSizeAtMost (graph m) t → size ≤ t

theorem sound {m k : ℕ} {xs : List W} {samp : Fin 112 → Fin 3 × Fin 5}
    (inputs_ok : ∀ j, xs.map (bit j) = PEqualNP.Represents.oneEach (samp j).1 (samp j).2)
    (goal_ok : ∀ j, bit j goal = graph m (samp j).1 (samp j).2)
    (nd : xs.Nodup) (check : front k xs = true) : lower m (k+1) := by
  intro t H
  by_contra! ht
  obtain ⟨C,hC,hlen,hrep⟩ := H
  have prog : build basicOps goal C.gates.length xs.toFinset := by
    apply compile C.gates C.output hC xs xs.toFinset
    · intro u hu
      exact .inr (.inr (List.mem_toFinset.mpr hu))
    · intro j
      rw [inputs_ok j,goal_ok j]
      exact hrep (samp j).1 (samp j).2
  obtain ⟨S, hsub, hl⟩ := compress prog
  have hk : C.gates.length ≤ k := Nat.le_trans hlen (by omega)
  have hlk : live basicOps goal k S := extend_live hk hl
  let l := xs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := nd.filter _
  have hcard := live_card hlk
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete k l (k+1-l.length) hnd (by omega) (hlS ▸ hlk)
  have hmem : l ∈ xs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp check l hmem
  have no : decide (k+1 < l.length) = false := by simp; omega
  have full := cuts_full (ws := l) (hlS ▸ hlk)
  simp [no,full,hsearch] at hrow

theorem full_lower : lower 32767 1 := by
  rintro t ⟨C,_,hsize,hrep⟩
  by_contra! h
  have hg : C.gates = [] := List.length_eq_zero_iff.mp (show C.gates.length = 0 by
    change C.gates.length ≤ t at hsize; omega)
  let x (u : Fin 3) (v : Fin 5) := PEqualNP.Represents.oneEach u v
  have all (u : Fin 3) (v : Fin 5) : (x u v).getD C.output false = true := by
    have e := hrep u v
    have valid : ∀ i j, graph 32767 i j = true := by decide +kernel
    simpa [Circuit.eval,Circuit.wires,hg,x,valid] using e
  by_cases small : C.output < 8
  · have counter : ∀ i : Fin 8, ∃ u v, (x u v).getD i.val false = false := by decide +kernel
    obtain ⟨u,v,hbad⟩ := counter ⟨C.output,small⟩
    exact Bool.false_ne_true (hbad.symm.trans (all u v))
  · have l : (x 0 0).length = 8 := by simp [x,PEqualNP.Represents.oneEach]
    exact Bool.false_ne_true ((List.getD_eq_default (x 0 0) false (by omega : (x 0 0).length ≤ C.output)).symm.trans (all 0 0))

theorem row0 : lower 0 0 := fun _ _ => Nat.zero_le _

def cols1 : List W := [0xffffffffffffff003c00f003c00f,0x7c01f007c01f0,0xf803e00f803e00,0xffffffffffffff08402100840210,0x10844211084421,0x21088422108842,0x42110844211084,0x84221088422108]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1 : lower 1 1 :=
  sound (k := 0) (xs := cols1) (samp := sample 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3 : List W := [0xfffffffffffffff00000fc00003f,0x3ff0000ffc0,0xffc0003ff0000,0x55555555555555000c03000300c0,0xaaaaaaaaaaaaaa00300c000c0300,0x30c0300c300c03,0xc300c030c0300c,0xc0300c300c030]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3 : lower 3 2 :=
  sound (k := 1) (xs := cols3) (samp := sample 3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7 : List W := [0xffffffffffffff0003f00000003f,0xfffc00001fffc0,0xfffe00000,0x49249249249249001c0000e001c0,0x9249249249249200e00007000e00,0x2492492492492407000038007000,0x380071c0038007,0xc0038e001c0038]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7 : lower 7 3 :=
  sound (k := 2) (xs := cols7) (samp := sample 7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols15 : List W := [0xffffffffffffff00f0000000000f,0xff000000fffff0,0xfffff000000,0x111111111111110f00000f0000f0,0x22222222222222f00000f0000f00,0x4444444444444400000f0000f000,0x888888888888880000f0000f0000,0xff0000f0000f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row15 : lower 15 4 :=
  sound (k := 3) (xs := cols15) (samp := sample 15) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem row31 : lower 31 0 := fun _ _ => Nat.zero_le _

def cols33 : List W := [0x55555555555555f00003fc0000ff,0xaaaaaaaaaaaaaa0003fc0000ff00,0xffc0003ff0000,0xffffffffffffff000c0000030000,0x30300c0c0c0303,0xc0c03030300c0c,0x300c0c0c03030,0xc03030300c0c0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row33 : lower 33 2 :=
  sound (k := 1) (xs := cols33) (samp := sample 33) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols34 : List W := [0x55555555555555f00003fc0000ff,0xaaaaaaaaaaaaaa0003fc0000ff00,0xffc0003ff0000,0xaaaaaaaaaaaaaa300c000c030003,0x5555555555555500300c000c0300,0xc0c03030300c0c,0x300c0c0c03030,0xc03030300c0c0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row34 : lower 34 3 :=
  sound (k := 2) (xs := cols34) (samp := sample 34) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols38 : List W := [0xdb6db6db6db6db001ff0000001ff,0x24924924924924ffe000001ffe00,0xfffe00000,0x2492492492492400007000e00007,0x4924924924924900e00007000e00,0x9249249249249207000038007000,0x380381c0038038,0xc01c0e001c01c0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row38 : lower 38 4 :=
  sound (k := 3) (xs := cols38) (samp := sample 38) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols46 : List W := [0x777777777777770ff000000000ff,0x88888888888888f0000000ffff00,0xfffff000000,0x8888888888888800f0000f00000f,0x11111111111111f00000f0000f00,0x2222222222222200000f0000f000,0x444444444444440000f0000f0000,0xf0f0000f000f0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row46 : lower 46 5 :=
  sound (k := 4) (xs := cols46) (samp := sample 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols62 : List W := [0xbdef7bdef7bdef7c00000000001f,0x4210842108421080000001ffffe0,0x3fffffe000000,0x421084210842107c00003e00001f,0x84210842108421800007c00003e0,0x84210842108420000f800007c00,0x10842108421084001f00000f8000,0x2108421084210803e00001f00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row62 : lower 62 6 :=
  sound (k := 5) (xs := cols62) (samp := sample 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols63 : List W := [0xdf7df7df7df7df00000000000000,0x20820820820820c0000000ffffff,0x3fffffff000000,0x618618618618610000003f000000,0x82082082082082c0000fc000003f,0x41041041041040003f000000fc0,0x820820820820800fc000003f000,0x104104104104103f000000fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row63 : lower 63 2 :=
  sound (k := 1) (xs := cols63) (samp := sample 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols99 : List W := [0x33333333333333fff00000000fff,0xcccccccccccccc00000000fff000,0xfffff000000,0x555555555555550000000f000000,0xaaaaaaaaaaaaaa000000f0000000,0xf00f0000f00f,0xf00f0000f00f0,0xf00f0000f00f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row99 : lower 99 3 :=
  sound (k := 2) (xs := cols99) (samp := sample 99) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols108 : List W := [0x33333333333333fff00000000fff,0xcccccccccccccc00000000fff000,0xfffff000000,0x4444444444444400f0000f00000f,0x888888888888880f0000f00000f0,0x1111111111111100000f0000f000,0x222222222222220000f0000f0000,0xf00f0000f00f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row108 : lower 108 5 :=
  sound (k := 4) (xs := cols108) (samp := sample 108) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols124 : List W := [0x9ce739ce739ce7fc0000000003ff,0x6318c6318c631800000001fffc00,0x3fffffe000000,0x210842108421087c00003e00001f,0x42108421084210800007c00003e0,0x842108421084210000f800007c00,0x8421084210842001f00000f8000,0x1084210842108403e00001f00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row124 : lower 124 6 :=
  sound (k := 5) (xs := cols124) (samp := sample 124) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols127 : List W := [0x3e7cf9f3e7cf9f00000000000000,0xc183060c183060000000001fffff,0xffffffffe00000,0x42850a142850a10000000fe00000,0x850a142850a142000007f0000000,0x81020408102040003f80000007f,0x1020408102040801fc0000003f80,0x20408102040810fe0000001fc000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row127 : lower 127 3 :=
  sound (k := 2) (xs := cols127) (samp := sample 127) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols231 : List W := [0xc71c71c71c71c7c0000000000fff,0x38e38e38e38e3800000000fff000,0x3fffffff000000,0x492492492492490000003f000000,0x9249249249249200000fc0000000,0x249249249249240003f000000000,0xc0fc000003f03f,0x3f000000fc0fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row231 : lower 231 4 :=
  sound (k := 3) (xs := cols231) (samp := sample 231) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols235 : List W := [0xc71c71c71c71c7c0000000000fff,0x38e38e38e38e3800000000fff000,0x3fffffff000000,0x492492492492490000003f000000,0x9249249249249200000fc0000000,0x20820820820820c003f00000003f,0x410410410410400fc000003f000,0x3f000000fc0fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row235 : lower 235 6 :=
  sound (k := 5) (xs := cols235) (samp := sample 235) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols251 : List W := [0x1e3c78f1e3c78f0000000000007f,0xe1c3870e1c3870000000001fff80,0xffffffffe00000,0x224489122448910000000fe00000,0x44891224489122000007f0000000,0x810204081020400003f80000007f,0x810204081020401fc0000003f80,0x10204081020408fe0000001fc000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row251 : lower 251 7 :=
  sound (k := 6) (xs := cols251) (samp := sample 251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols255 : List W := [0x1f1f1f1f1f1f1f00000000000000,0xe0e0e0e0e0e0e00000000000ffff,0xffffffffff0000,0x2121212121212100000000ff0000,0x42424242424242000000ff000000,0x848484848484840000ff00000000,0x808080808080800ff00000000ff,0x10101010101010ff00000000ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row255 : lower 255 4 :=
  sound (k := 3) (xs := cols255) (samp := sample 255) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols495 : List W := [0xf0f0f0f0f0f0f000000000000ff,0xf0f0f0f0f0f0f00000000000ff00,0xffffffffff0000,0x1111111111111100000000ff0000,0x22222222222222000000ff000000,0x444444444444440000ff00000000,0x8888888888888800ff0000000000,0xff00000000ffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row495 : lower 495 5 :=
  sound (k := 4) (xs := cols495) (samp := sample 495) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols511 : List W := [0xc3e1f0f87c3e1f00000000000000,0x3c1e0f0783c1e0c00000000001ff,0x3ffffffffffe00,0x442211088442210000000003fe00,0x8844221108844200000007fc0000,0x1088442211088400000ff8000000,0x21108844221108001ff000000000,0x2010080402010ffe000000001ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row511 : lower 511 5 :=
  sound (k := 4) (xs := cols511) (samp := sample 511) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1023 : List W := [0x7c1f07c1f07c1f00000000000000,0x83e0f83e0f83e000000000000000,0xffffffffffffff,0x84210842108421fc0000000003ff,0x8421084210842000000000ffc00,0x108421084210840000003ff00000,0x210842108421080000ffc0000000,0x4210842108421003ff0000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1023 : lower 1023 1 :=
  sound (k := 0) (xs := cols1023) (samp := sample 1023) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem row1057 : lower 1057 0 := fun _ _ => Nat.zero_le _

def cols1058 : List W := [0x4924924924924900fff000000fff,0x92492492492492ff000000fff000,0x2492492492492400000fff000000,0xb6db6db6db6db600007000000007,0x4924924924924907000007007000,0x38038038038038,0xc01c01c01c01c0,0xe00e00e00e00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1058 : lower 1058 4 :=
  sound (k := 3) (xs := cols1058) (samp := sample 1058) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1059 : List W := [0x33333333333333fff00000000fff,0x444444444444440000000ffff000,0x88888888888888000ffff0000000,0xdddddddddddddd00000000000000,0x22222222222222000000f000f000,0xf00f000f000f,0xf00f000f000f0,0xf00f000f000f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1059 : lower 1059 2 :=
  sound (k := 1) (xs := cols1059) (samp := sample 1059) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1062 : List W := [0x33333333333333fff00000000fff,0x444444444444440000000ffff000,0x88888888888888000ffff0000000,0xcccccccccccccc00f0000000000f,0x11111111111111000000f000f000,0x2222222222222200000f000f0000,0xf00f000f000f0,0xf00f000f000f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1062 : lower 1062 5 :=
  sound (k := 4) (xs := cols1062) (samp := sample 1062) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1063 : List W := [0x9ce739ce739ce7fc0000000003ff,0x210842108421080000003ffffc00,0x4210842108421003ffffc0000000,0xe739ce739ce73900000000000000,0x8421084210842000007c0007c00,0x108421084210840000f8000f8000,0x7c1f0001f0001f,0x83e0003e0003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1063 : lower 1063 3 :=
  sound (k := 2) (xs := cols1063) (samp := sample 1063) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1070 : List W := [0x9ce739ce739ce7fc0000000003ff,0x210842108421080000003ffffc00,0x4210842108421003ffffc0000000,0x6318c6318c63187c00000000001f,0x84210842108421000007c0007c00,0x84210842108420000f8000f8000,0x10842108421084001f0001f00000,0x83e0003e0003e0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1070 : lower 1070 6 :=
  sound (k := 5) (xs := cols1070) (samp := sample 1070) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1071 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x104104104104100000003fffffc0,0x208208208208203fffffc0000000,0x71c71c71c71c7100000000000000,0x8208208208208200000fc0000fc0,0x41041041041040003f00003f000,0x820820820820800fc0000fc0000,0xff00003f00003f]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1071 : lower 1071 4 :=
  sound (k := 3) (xs := cols1071) (samp := sample 1071) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1086 : List W := [0xcf3cf3cf3cf3cfc000000000003f,0x104104104104100000003fffffc0,0x208208208208203fffffc0000000,0x30c30c30c30c30c000000000003f,0x4104104104104100000fc0000fc0,0x820820820820820003f00003f000,0x410410410410400fc0000fc0000,0x82082082082083f00003f000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1086 : lower 1086 7 :=
  sound (k := 6) (xs := cols1086) (samp := sample 1086) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1087 : List W := [0x3e7cf9f3e7cf9f00000000000000,0x408102040810200000000fffffff,0x81020408102040fffffff0000000,0xc3870e1c3870e100000000000000,0x4081020408102000007f000007f,0x81020408102040003f800003f80,0x1020408102040801fc00001fc000,0x20408102040810fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1087 : lower 1087 1 :=
  sound (k := 0) (xs := cols1087) (samp := sample 1087) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1092 : List W := [0x4924924924924900fff000000fff,0x92492492492492ff000000fff000,0x2492492492492400000fff000000,0x2492492492492407007000007007,0x9249249249249200038007000038,0x4924924924924938000038038000,0xc01c01c01c01c0,0xe00e00e00e00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1092 : lower 1092 5 :=
  sound (k := 4) (xs := cols1092) (samp := sample 1092) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1100 : List W := [0x33333333333333fff00000000fff,0x444444444444440000000ffff000,0x88888888888888000ffff0000000,0x8888888888888800f0000000f00f,0x444444444444440f0000f00000f0,0x1111111111111100000f000f0000,0x222222222222220000f000f00000,0xf00f000f000f00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1100 : lower 1100 6 :=
  sound (k := 5) (xs := cols1100) (samp := sample 1100) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1116 : List W := [0x9ce739ce739ce7fc0000000003ff,0x210842108421080000003ffffc00,0x4210842108421003ffffc0000000,0x421084210842107c000000007c1f,0x21084210842108800007c00003e0,0x842108421084210000f8000f8000,0x8421084210842001f0001f00000,0x1084210842108403e0003e000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1116 : lower 1116 7 :=
  sound (k := 6) (xs := cols1116) (samp := sample 1116) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1119 : List W := [0x3e7cf9f3e7cf9f00000000000000,0x408102040810200000000fffffff,0x81020408102040fffffff0000000,0x83060c183060c10000000000007f,0x44891224489122000007f0000000,0x81020408102040003f800003f80,0x1020408102040801fc00001fc000,0x20408102040810fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1119 : lower 1119 4 :=
  sound (k := 3) (xs := cols1119) (samp := sample 1119) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1123 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0xd6b5ad6b5ad6b500000000000000,0x294a5294a5294a000007c0000000,0x7c00f8000f801f,0x801f0001f003e0,0x3e0003e007c00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1123 : lower 1123 3 :=
  sound (k := 2) (xs := cols1123) (samp := sample 1123) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1125 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0xd6b5ad6b5ad6b500000000000000,0x210842108421087c0007c000001f,0x84210842108420000f8000f8000,0x801f0001f003e0,0x3e0003e007c00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1125 : lower 1125 4 :=
  sound (k := 3) (xs := cols1125) (samp := sample 1125) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1133 : List W := [0xc71c71c71c71c7c0000000000fff,0x186186186186180000003ffff000,0x208208208208203fffffc0000000,0x69a69a69a69a6900000000000000,0x10410410410410c0000fc000003f,0x820820820820820003f00003f000,0x410410410410400fc0000fc0000,0x3f00003f000fc0]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1133 : lower 1133 5 :=
  sound (k := 4) (xs := cols1133) (samp := sample 1133) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1149 : List W := [0x1e3c78f1e3c78f0000000000007f,0x60c183060c18300000000fffff80,0x81020408102040fffffff0000000,0xa3468d1a3468d100000000000000,0x40810204081020000007f000007f,0x40810204081020003f800003f80,0x810204081020401fc00001fc000,0x10204081020408fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1149 : lower 1149 6 :=
  sound (k := 5) (xs := cols1149) (samp := sample 1149) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1151 : List W := [0x1f1f1f1f1f1f1f00000000000000,0x6060606060606000000000ffffff,0x80808080808080ffffffff000000,0xa1a1a1a1a1a1a100000000000000,0x42424242424242000000ff000000,0x40404040404040000ff000000ff,0x808080808080800ff000000ff00,0x10101010101010ff000000ff0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1151 : lower 1151 3 :=
  sound (k := 2) (xs := cols1151) (samp := sample 1151) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1222 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x421084210842107c0000000f801f,0x94a5294a5294a5000007c0000000,0x294a5294a5294a0000f800000000,0x801f0001f003e0,0x3e0003e007c00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1222 : lower 1222 5 :=
  sound (k := 4) (xs := cols1222) (samp := sample 1222) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1240 : List W := [0x8c6318c6318c63fc000000007fff,0x318c6318c6318c0000003fff8000,0x4210842108421003ffffc0000000,0x421084210842107c0000000f801f,0x10842108421084800007c00003e0,0x210842108421080000f800007c00,0x84210842108421001f0001f00000,0x842108421084203e0003e000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1240 : lower 1240 7 :=
  sound (k := 6) (xs := cols1240) (samp := sample 1240) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1247 : List W := [0x1f1f1f1f1f1f1f00000000000000,0x6060606060606000000000ffffff,0x80808080808080ffffffff000000,0x81818181818181000000000000ff,0x22222222222222000000ff000000,0x444444444444440000ff00000000,0x808080808080800ff000000ff00,0x10101010101010ff000000ff0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1247 : lower 1247 5 :=
  sound (k := 4) (xs := cols1247) (samp := sample 1247) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1255 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x93264c993264c900000000000000,0x24489122448912000007f0000000,0x489122448912240003f800000000,0x1fc00001fc07f,0xfe00000fe03f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1255 : lower 1255 4 :=
  sound (k := 3) (xs := cols1255) (samp := sample 1255) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1273 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x93264c993264c900000000000000,0x20408102040810000007f000007f,0x408102040810200003f800003f80,0x408102040810201fc00001fc000,0x8102040810204fe00000fe00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1273 : lower 1273 6 :=
  sound (k := 5) (xs := cols1273) (samp := sample 1273) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1279 : List W := [0xc3e1f0f87c3e1f00000000000000,0x1c0e070381c0e0c000000003ffff,0x201008040201003ffffffffc0000,0x6432190c86432100000000000000,0x8844221108844200000007fc0000,0x1088442211088400000ff8000000,0x1008040201008c01ff0000001ff,0x20100804020103fe0000003fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1279 : lower 1279 4 :=
  sound (k := 3) (xs := cols1279) (samp := sample 1279) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1486 : List W := [0xe1c3870e1c38700000000003fff,0x70e1c3870e1c380000000fffc000,0x81020408102040fffffff0000000,0x81020408102040000000001fc07f,0x12244891224489000007f0000000,0x244891224489120003f800000000,0x4891224489122401fc0000000000,0xfe00000fe03f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1486 : lower 1486 6 :=
  sound (k := 5) (xs := cols1486) (samp := sample 1486) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1503 : List W := [0xc3e1f0f87c3e1f00000000000000,0x1c0e070381c0e0c000000003ffff,0x201008040201003ffffffffc0000,0x6030180c060301c00000000001ff,0x8442211088442200000007fc0000,0x884422110884400000ff8000000,0x11088442211088001ff000000000,0x20100804020103fe0000003fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1503 : lower 1503 6 :=
  sound (k := 5) (xs := cols1503) (samp := sample 1503) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1519 : List W := [0xc1e0f0783c1e0fc00000000001ff,0x1e0f0783c1e0f00000000003fe00,0x201008040201003ffffffffc0000,0x6231188c46231100000000000000,0x8442211088442200000007fc0000,0x884422110884400000ff8000000,0x11088442211088001ff000000000,0xffe0000003ffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1519 : lower 1519 5 :=
  sound (k := 4) (xs := cols1519) (samp := sample 1519) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols1535 : List W := [0x7c1f07c1f07c1f00000000000000,0x81e0781e0781e0fc0000000003ff,0x200802008020003fffffffffc00,0x8621886218862100000000000000,0x8421084210842000000000ffc00,0x108421084210840000003ff00000,0x210842108421080000ffc0000000,0x40100401004010ffff00000003ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row1535 : lower 1535 5 :=
  sound (k := 4) (xs := cols1535) (samp := sample 1535) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols2014 : List W := [0xc1e0f0783c1e0fc00000000001ff,0x1e0f0783c1e0f00000000003fe00,0x201008040201003ffffffffc0000,0x20100804020100c000000003ffff,0x4221108844221100000007fc0000,0x8442211088442200000ff8000000,0x8844221108844001ff000000000,0x110884422110883fe00000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row2014 : lower 2014 7 :=
  sound (k := 6) (xs := cols2014) (samp := sample 2014) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols2015 : List W := [0x7c1f07c1f07c1f00000000000000,0x81e0781e0781e0fc0000000003ff,0x200802008020003fffffffffc00,0x6018060180601fc0000000003ff,0x88220882208822000000000ffc00,0x104411044110440000003ff00000,0x208822088220880000ffc0000000,0x4110441104411003ff0000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row2015 : lower 2015 7 :=
  sound (k := 6) (xs := cols2015) (samp := sample 2015) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols2047 : List W := [0x81f03e07c0f81f00000000000000,0x3e07c0f81f03e000000000000000,0x40080100200400ffffffffffffff,0xc2184308610c2100000000000000,0x42084108210427ff000000007ff,0x8410821042084800000003ff800,0x10821042084108000001ffc00000,0x21042084108210000ffe00000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row2047 : lower 2047 2 :=
  sound (k := 1) (xs := cols2047) (samp := sample 2047) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3171 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x5555555555555500000000000000,0xaaaaaaaaaaaaaa00000000000000,0xc003f000fc003f,0xfc003f000fc0,0x3f000fc003f000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3171 : lower 3171 1 :=
  sound (k := 0) (xs := cols3171) (samp := sample 3171) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3173 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x5555555555555500000000000000,0x28a28a28a28a28c000000000003f,0x820820820820820003f000fc0000,0xfc003f000fc0,0x3f000fc003f000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3173 : lower 3173 5 :=
  sound (k := 4) (xs := cols3173) (samp := sample 3173) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3175 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x52a54a952a54a900000000000000,0xa54a952a54a95200000000000000,0x81020408102040003f8001fc000,0x1fc000fe0007f,0xfe0007f0003f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3175 : lower 3175 3 :=
  sound (k := 2) (xs := cols3175) (samp := sample 3175) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3180 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x14514514514514c000000000003f,0x28a28a28a28a2800000000000fc0,0x410410410410410003f000fc0000,0x8208208208208200fc003f000000,0x3f000fc003f000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3180 : lower 3180 6 :=
  sound (k := 5) (xs := cols3180) (samp := sample 3180) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3181 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x52a54a952a54a900000000000000,0xa142850a1428500000000000007f,0x40810204081020003f8001fc000,0x810204081020401fc000fe00000,0xfe0007f0003f80]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3181 : lower 3181 6 :=
  sound (k := 5) (xs := cols3181) (samp := sample 3181) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3183 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x5151515151515100000000000000,0xa2a2a2a2a2a2a200000000000000,0x40404040404040000ff0000ff00,0x808080808080800ff0000ff0000,0xff0000ff0000ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3183 : lower 3183 4 :=
  sound (k := 3) (xs := cols3183) (samp := sample 3183) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3196 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x50a142850a14280000000000007f,0xa142850a14285000000000003f80,0x20408102040810003f8001fc000,0x408102040810201fc000fe00000,0x8102040810204fe0007f0000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3196 : lower 3196 7 :=
  sound (k := 6) (xs := cols3196) (samp := sample 3196) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3197 : List W := [0xf0f0f0f0f0f0f000000000000ff,0x30303030303030000000ffffff00,0xc0c0c0c0c0c0c0ffffff00000000,0x5151515151515100000000000000,0xa0a0a0a0a0a0a0000000000000ff,0x20202020202020000ff0000ff00,0x404040404040400ff0000ff0000,0x8080808080808ff0000ff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3197 : lower 3197 7 :=
  sound (k := 6) (xs := cols3197) (samp := sample 3197) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3199 : List W := [0xc3e1f0f87c3e1f00000000000000,0xc06030180c060c0000007ffffff,0x30180c060301803ffffff8000000,0x542a150a8542a100000000000000,0xa8542a150a854200000000000000,0x804020100804c0000ff80001ff,0x1008040201008001ff00003fe00,0x20100804020103fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3199 : lower 3199 2 :=
  sound (k := 1) (xs := cols3199) (samp := sample 3199) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3241 : List W := [0xc30c30c30c30c3c000000003ffff,0xc30c30c30c30c00000ffffc0000,0x30c30c30c30c303ffff000000000,0x5555555555555500000000000000,0x20820820820820c0000000fc003f,0x82082082082080003f000000fc0,0x8208208208208200fc003f000000,0x3f000fc003f000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3241 : lower 3241 6 :=
  sound (k := 5) (xs := cols3241) (samp := sample 3241) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3257 : List W := [0xe1c3870e1c38700000000003fff,0x3060c183060c18000007ffffc000,0xc183060c183060fffff800000000,0x52a54a952a54a900000000000000,0x81020408102040000000001fc07f,0x204081020408100003f800003f80,0x408102040810201fc000fe00000,0x8102040810204fe0007f0000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3257 : lower 3257 7 :=
  sound (k := 6) (xs := cols3257) (samp := sample 3257) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3263 : List W := [0xc3e1f0f87c3e1f00000000000000,0xc06030180c060c0000007ffffff,0x30180c060301803ffffff8000000,0x542a150a8542a100000000000000,0xa05028140a0502c00000000001ff,0x884422110884400000ff8000000,0x1008040201008001ff00003fe00,0x20100804020103fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3263 : lower 3263 5 :=
  sound (k := 4) (xs := cols3263) (samp := sample 3263) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3303 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x9292929292929200000000000000,0x242424242424240000ff00000000,0xff0000ff00ff,0xff0000ff00ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3303 : lower 3303 4 :=
  sound (k := 3) (xs := cols3303) (samp := sample 3303) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3307 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x9292929292929200000000000000,0x202020202020200000ff000000ff,0x404040404040400ff0000ff0000,0xff0000ff00ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3307 : lower 3307 5 :=
  sound (k := 4) (xs := cols3307) (samp := sample 3307) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3323 : List W := [0xc1e0f0783c1e0fc00000000001ff,0xe070381c0e07000000007fffe00,0x30180c060301803ffffff8000000,0x5229148a45229100000000000000,0xa45229148a452200000000000000,0x8040201008040c0000ff80001ff,0x804020100804001ff00003fe00,0x10080402010083fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3323 : lower 3323 6 :=
  sound (k := 5) (xs := cols3323) (samp := sample 3323) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3327 : List W := [0x7c1f07c1f07c1f00000000000000,0x80e0380e0380e0fc0000000fffff,0x300c0300c030003fffffff00000,0x8521485214852100000000000000,0xa4290a4290a4200000000000000,0x108421084210840000003ff00000,0x20080200802008fc00ffc00003ff,0x4010040100401003ff00000ffc00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3327 : lower 3327 4 :=
  sound (k := 3) (xs := cols3327) (samp := sample 3327) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3487 : List W := [0xc3e1f0f87c3e1f00000000000000,0xc06030180c060c0000007ffffff,0x30180c060301803ffffff8000000,0x5028140a050281c00000000001ff,0xa05028140a05020000000003fe00,0x482412090482400000ff8000000,0x9048241209048001ff000000000,0x20100804020103fe00007fc0000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3487 : lower 3487 6 :=
  sound (k := 5) (xs := cols3487) (samp := sample 3487) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3501 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4949494949494900000000000000,0x8080808080808000000000ff00ff,0x121212121212120000ff00000000,0x2424242424242400ff0000000000,0xff0000ff00ff00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3501 : lower 3501 6 :=
  sound (k := 5) (xs := cols3501) (samp := sample 3501) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3519 : List W := [0x7c1f07c1f07c1f00000000000000,0x80e0380e0380e0fc0000000fffff,0x300c0300c030003fffffff00000,0x8521485214852100000000000000,0xa0280a0280a02fc0000000003ff,0x104411044110440000003ff00000,0x208822088220880000ffc0000000,0x4010040100401003ff00000ffc00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3519 : lower 3519 6 :=
  sound (k := 5) (xs := cols3519) (samp := sample 3519) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3567 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0f03c0f03c0f0000000000ffc00,0x300c0300c030003fffffff00000,0x4511445114451100000000000000,0x8a2288a2288a2200000000000000,0x104411044110440000003ff00000,0x208822088220880000ffc0000000,0xffff00000fffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3567 : lower 3567 5 :=
  sound (k := 4) (xs := cols3567) (samp := sample 3567) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3583 : List W := [0x81f03e07c0f81f00000000000000,0x1e03c0780f01e07ff000000007ff,0x600c0180300600800ffffffff800,0xa2144288510a2100000000000000,0x44288510a2144200000000000000,0x8410821042084800000003ff800,0x10821042084108000001ffc00000,0x10020040080107ffffe000007ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3583 : lower 3583 5 :=
  sound (k := 4) (xs := cols3583) (samp := sample 3583) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3996 : List W := [0x70707070707070000000000ffff,0x38383838383838000000ffff0000,0xc0c0c0c0c0c0c0ffffff00000000,0x4040404040404000000000ff00ff,0x80808080808080000000ff00ff00,0x90909090909090000ff00000000,0x1212121212121200ff0000000000,0x24242424242424ff000000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3996 : lower 3996 7 :=
  sound (k := 6) (xs := cols3996) (samp := sample 3996) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols3999 : List W := [0x7c1f07c1f07c1f00000000000000,0x80e0380e0380e0fc0000000fffff,0x300c0300c030003fffffff00000,0x5014050140501fc0000000003ff,0xa0280a0280a02000000000ffc00,0x902409024090240000003ff00000,0x204812048120480000ffc0000000,0x4090240902409003ff0000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row3999 : lower 3999 7 :=
  sound (k := 6) (xs := cols3999) (samp := sample 3999) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols4029 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0f03c0f03c0f0000000000ffc00,0x300c0300c030003fffffff00000,0x4511445114451100000000000000,0x2008020080200fc0000000fffff,0x882208822088220000003ff00000,0x104411044110440000ffc0000000,0x2088220882208803ff0000000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row4029 : lower 4029 7 :=
  sound (k := 6) (xs := cols4029) (samp := sample 4029) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols4031 : List W := [0x81f03e07c0f81f00000000000000,0x1e03c0780f01e07ff000000007ff,0x600c0180300600800ffffffff800,0xa2144288510a2100000000000000,0x40280500a014027ff000000007ff,0x4408811022044800000003ff800,0x8811022044088000001ffc00000,0x11022044088110000ffe00000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row4031 : lower 4031 7 :=
  sound (k := 6) (xs := cols4031) (samp := sample 4031) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols4095 : List W := [0x1f01f01f01f01f00000000000000,0xe03e03e03e03e000000000000000,0xc00c00c00c00ffffffffffffff,0x2142142142142100000000000000,0x4284284284284200000000000000,0x8408408408408400fff000000fff,0x8108108108108ff000000fff000,0x1021021021021000000fff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row4095 : lower 4095 3 :=
  sound (k := 2) (xs := cols4095) (samp := sample 4095) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7399 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x9249249249249200000000000000,0x2492492492492400000000000000,0xc01ff007fc01ff,0x3fe00ff803fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7399 : lower 7399 2 :=
  sound (k := 1) (xs := cols7399) (samp := sample 7399) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7403 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x9249249249249200000000000000,0x24120904824120c00000000001ff,0x804020100804001ff007fc0000,0x3fe00ff803fe00]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7403 : lower 7403 6 :=
  sound (k := 5) (xs := cols7403) (samp := sample 7403) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7407 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0701c0701c0700000003ffffc00,0x380e0380e038003ffffc0000000,0x4491244912449100000000000000,0x8922489224892200000000000000,0x1244912449124400000000000000,0x200802008020080000ffc00ffc00,0xffff003ff003ff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7407 : lower 7407 4 :=
  sound (k := 3) (xs := cols7407) (samp := sample 7407) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7417 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x12090482412090c00000000001ff,0x241209048241200000000003fe00,0x80402010080402001ff007fc0000,0x8040201008043fe00ff8000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7417 : lower 7417 7 :=
  sound (k := 6) (xs := cols7417) (samp := sample 7417) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7419 : List W := [0x3c0f03c0f03c0ffc0000000003ff,0xc0701c0701c0700000003ffffc00,0x380e0380e038003ffffc0000000,0x4491244912449100000000000000,0x8922489224892200000000000000,0x2409024090240fc0000000003ff,0x100401004010040000ffc00ffc00,0x2008020080200803ff003ff00000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7419 : lower 7419 7 :=
  sound (k := 6) (xs := cols7419) (samp := sample 7419) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7423 : List W := [0x81f03e07c0f81f00000000000000,0xe01c0380700e0fff000003fffff,0x700e01c0380700000fffffc00000,0x9212424849092100000000000000,0x2424849092124200000000000000,0x4849092124248400000000000000,0x8010020040087ff001ffc007ff,0x1002004008010800ffe003ff800]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7423 : lower 7423 3 :=
  sound (k := 2) (xs := cols7423) (samp := sample 7423) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7539 : List W := [0xc0e070381c0e07c000000003ffff,0x70381c0e0703800000ffffc0000,0x381c0e070381c03ffff000000000,0x4924924924924900000000000000,0x9249249249249200000000000000,0x20100804020100c0000007fc01ff,0x4020100804020001ff00003fe00,0x8040201008043fe00ff8000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7539 : lower 7539 7 :=
  sound (k := 6) (xs := cols7539) (samp := sample 7539) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7551 : List W := [0x81f03e07c0f81f00000000000000,0xe01c0380700e0fff000003fffff,0x700e01c0380700000fffffc00000,0x9212424849092100000000000000,0x2424849092124200000000000000,0x404809012024047ff000000007ff,0x8811022044088000001ffc00000,0x1002004008010800ffe003ff800]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7551 : lower 7551 6 :=
  sound (k := 5) (xs := cols7551) (samp := sample 7551) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7663 : List W := [0x80f01e03c0780f7ff000000007ff,0xf01e03c0780f0800000003ff800,0x700e01c0380700000fffffc00000,0x9112224448891100000000000000,0x2224448891122200000000000000,0x4448891122244400000000000000,0x8811022044088000001ffc00000,0xfffffe003fffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7663 : lower 7663 5 :=
  sound (k := 4) (xs := cols7663) (samp := sample 7663) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7671 : List W := [0x80f01e03c0780f7ff000000007ff,0xf01e03c0780f0800000003ff800,0x700e01c0380700000fffffc00000,0x9112224448891100000000000000,0x2224448891122200000000000000,0x4448891122244400000000000000,0x80100200400807ff001ffc007ff,0x801002004008800ffe003ff800]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7671 : lower 7671 6 :=
  sound (k := 5) (xs := cols7671) (samp := sample 7671) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7679 : List W := [0x1f01f01f01f01f00000000000000,0xe01e01e01e01e000fff000000fff,0xe00e00e00e00ff000ffffff000,0x2122122122122100000000000000,0x4244244244244200000000000000,0x8488488488488400000000000000,0x8108108108108ff000000fff000,0x1001001001001000ffffff000fff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7679 : lower 7679 5 :=
  sound (k := 4) (xs := cols7679) (samp := sample 7679) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols7999 : List W := [0x81f03e07c0f81f00000000000000,0xe01c0380700e0fff000003fffff,0x700e01c0380700000fffffc00000,0x9212424849092100000000000000,0x202404809012027ff000000007ff,0x40480901202404800000003ff800,0x4809012024048000001ffc00000,0x9012024048090000ffe00000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row7999 : lower 7999 7 :=
  sound (k := 6) (xs := cols7999) (samp := sample 7999) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols8059 : List W := [0x80f01e03c0780f7ff000000007ff,0xf01e03c0780f0800000003ff800,0x700e01c0380700000fffffc00000,0x9112224448891100000000000000,0x2224448891122200000000000000,0x40080100200400fff000003fffff,0x4408811022044000001ffc00000,0x8811022044088000ffe00000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row8059 : lower 8059 7 :=
  sound (k := 6) (xs := cols8059) (samp := sample 8059) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols8063 : List W := [0x1f01f01f01f01f00000000000000,0xe01e01e01e01e000fff000000fff,0xe00e00e00e00ff000ffffff000,0x2122122122122100000000000000,0x4244244244244200000000000000,0x480480480480400fff000000fff,0x88088088088088ff000000fff000,0x1011011011011000000fff000000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row8063 : lower 8063 7 :=
  sound (k := 6) (xs := cols8063) (samp := sample 8063) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols8191 : List W := [0xf00f807c03e01f00000000000000,0x1f00f807c03e000000000000000,0xe007003801c00ffffffffffffff,0x1210908484242100000000000000,0x2421210908484200000000000000,0x4842421210908400000000000000,0x80840420210108f0007ffc001fff,0x10808404202100fff8003ffe000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row8191 : lower 8191 4 :=
  sound (k := 3) (xs := cols8191) (samp := sample 8191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols15855 : List W := [0xf00f00f00f00f00fff000000fff,0xf00f00f00f00f0ff000000fff000,0xf00f00f00f0000000fff000000,0x1111111111111100000000000000,0x2222222222222200000000000000,0x4444444444444400000000000000,0x8888888888888800000000000000,0xffffffffffffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row15855 : lower 15855 3 :=
  sound (k := 2) (xs := cols15855) (samp := sample 15855) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols15863 : List W := [0xf00f00f00f00f00fff000000fff,0xf00f00f00f00f0ff000000fff000,0xf00f00f00f0000000fff000000,0x1111111111111100000000000000,0x2222222222222200000000000000,0x4444444444444400000000000000,0x8088088088088000fff000000fff,0x8008008008008ff000ffffff000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row15863 : lower 15863 7 :=
  sound (k := 6) (xs := cols15863) (samp := sample 15863) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols15871 : List W := [0xf00f807c03e01f00000000000000,0xf007803c01e0f0007ffc001fff,0xf007803c01e000fff8003ffe000,0x1110888444222100000000000000,0x2221110888444200000000000000,0x4442221110888400000000000000,0x8884442221110800000000000000,0x80040020010ffffffffffffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row15871 : lower 15871 4 :=
  sound (k := 3) (xs := cols15871) (samp := sample 15871) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols16127 : List W := [0xf00f807c03e01f00000000000000,0xf007803c01e0f0007ffc001fff,0xf007803c01e000fff8003ffe000,0x1110888444222100000000000000,0x2221110888444200000000000000,0x4442221110888400000000000000,0x88044022011008f0007ffc001fff,0x8804402201100fff8003ffe000]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row16127 : lower 16127 7 :=
  sound (k := 6) (xs := cols16127) (samp := sample 16127) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cols16383 : List W := [0x7c01f007c01f00000000000000,0xf803e00f803e000000000000000,0xf003c00f003c00ffffffffffffff,0x1084421108442100000000000000,0x2108842210884200000000000000,0x4211084421108400000000000000,0x8422108842210800000000000000,0x8402100840210ffffffffffffff]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem row16383 : lower 16383 5 :=
  sound (k := 4) (xs := cols16383) (samp := sample 16383) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem row32767 : lower 32767 1 := full_lower

def rows : List (ℕ × ℕ) := [(0, 0), (1, 1), (3, 2), (7, 3), (15, 4), (31, 0), (33, 2), (34, 3), (38, 4), (46, 5), (62, 6), (63, 2), (99, 3), (108, 5), (124, 6), (127, 3), (231, 4), (235, 6), (251, 7), (255, 4), (495, 5), (511, 5), (1023, 1), (1057, 0), (1058, 4), (1059, 2), (1062, 5), (1063, 3), (1070, 6), (1071, 4), (1086, 7), (1087, 1), (1092, 5), (1100, 6), (1116, 7), (1119, 4), (1123, 3), (1125, 4), (1133, 5), (1149, 6), (1151, 3), (1222, 5), (1240, 7), (1247, 5), (1255, 4), (1273, 6), (1279, 4), (1486, 6), (1503, 6), (1519, 5), (1535, 5), (2014, 7), (2015, 7), (2047, 2), (3171, 1), (3173, 5), (3175, 3), (3180, 6), (3181, 6), (3183, 4), (3196, 7), (3197, 7), (3199, 2), (3241, 6), (3257, 7), (3263, 5), (3303, 4), (3307, 5), (3323, 6), (3327, 4), (3487, 6), (3501, 6), (3519, 6), (3567, 5), (3583, 5), (3996, 7), (3999, 7), (4029, 7), (4031, 7), (4095, 3), (7399, 2), (7403, 6), (7407, 4), (7417, 7), (7419, 7), (7423, 3), (7539, 7), (7551, 6), (7663, 5), (7671, 6), (7679, 5), (7999, 7), (8059, 7), (8063, 7), (8191, 4), (15855, 3), (15863, 7), (15871, 4), (16127, 7), (16383, 5), (32767, 1)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem table_lower : ∀ p ∈ rows, lower p.1 p.2 := by
  intro p hp
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0
  · exact row1
  · exact row3
  · exact row7
  · exact row15
  · exact row31
  · exact row33
  · exact row34
  · exact row38
  · exact row46
  · exact row62
  · exact row63
  · exact row99
  · exact row108
  · exact row124
  · exact row127
  · exact row231
  · exact row235
  · exact row251
  · exact row255
  · exact row495
  · exact row511
  · exact row1023
  · exact row1057
  · exact row1058
  · exact row1059
  · exact row1062
  · exact row1063
  · exact row1070
  · exact row1071
  · exact row1086
  · exact row1087
  · exact row1092
  · exact row1100
  · exact row1116
  · exact row1119
  · exact row1123
  · exact row1125
  · exact row1133
  · exact row1149
  · exact row1151
  · exact row1222
  · exact row1240
  · exact row1247
  · exact row1255
  · exact row1273
  · exact row1279
  · exact row1486
  · exact row1503
  · exact row1519
  · exact row1535
  · exact row2014
  · exact row2015
  · exact row2047
  · exact row3171
  · exact row3173
  · exact row3175
  · exact row3180
  · exact row3181
  · exact row3183
  · exact row3196
  · exact row3197
  · exact row3199
  · exact row3241
  · exact row3257
  · exact row3263
  · exact row3303
  · exact row3307
  · exact row3323
  · exact row3327
  · exact row3487
  · exact row3501
  · exact row3519
  · exact row3567
  · exact row3583
  · exact row3996
  · exact row3999
  · exact row4029
  · exact row4031
  · exact row4095
  · exact row7399
  · exact row7403
  · exact row7407
  · exact row7417
  · exact row7419
  · exact row7423
  · exact row7539
  · exact row7551
  · exact row7663
  · exact row7671
  · exact row7679
  · exact row7999
  · exact row8059
  · exact row8063
  · exact row8191
  · exact row15855
  · exact row15863
  · exact row15871
  · exact row16127
  · exact row16383
  · exact row32767
end AtlasLower
