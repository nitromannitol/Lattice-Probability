/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ExplCover
import LatticeProb.Lattice.Planar.ExplTree
import LatticeProb.Lattice.Planar.Ring

open Finset List

namespace LatticeProb.Lattice.Planar

/-- A chain of parent steps from `z` to the first vertex of the branch `xs`. -/
structure ChainTo (s : ExplState) (xs : List Site) (z : Site) (l : List Site) : Prop where
  head : l.head? = some z
  last_mem : ∀ y ∈ l.getLast?, y ∈ xs
  dropLast_notMem : ∀ y ∈ l.dropLast, y ∉ xs
  chain : l.IsChain (fun a b => (b, a, true) ∈ s.tested)
  nodup : l.Nodup
  visited : ∀ y ∈ l, y ∈ s.visited

theorem root_mem_branch {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) : f ∈ xs :=
  List.mem_of_mem_getLast? h.root

/-- The chain from a visited face, by strong induction on the index of its visiting edge. -/
theorem exists_chainTo_aux {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) (hnd : s.tested.Nodup) :
    ∀ k (hk : k < s.tested.length), s.tested[k].2.2 = true →
      ∃ l, ChainTo s xs s.tested[k].2.1 l ∧
        ∀ y ∈ l, y = f ∨ ∃ j ≤ k, ∃ (hj : j < s.tested.length),
          s.tested[j].2.1 = y ∧ s.tested[j].2.2 = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk hopen
  set z := s.tested[k].2.1 with hz
  have hzmem : s.tested[k] ∈ s.tested := List.getElem_mem hk
  have hzvis : z ∈ s.visited := h.open_head _ hzmem hopen
  have hzf : z ≠ f := h.head_ne_root _ hzmem hopen
  by_cases hzx : z ∈ xs
  · refine ⟨[z], ⟨rfl, by simpa using hzx, by simp, List.isChain_singleton _, List.nodup_singleton _,
      by simpa using hzvis⟩, ?_⟩
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact Or.inr ⟨k, le_rfl, hk, rfl, hopen⟩
  · set p := s.tested[k].1 with hp
    have hpz : (p, z, true) ∈ s.tested := by
      have : s.tested[k] = (p, z, true) := by
        rw [hp, hz]
        ext <;> simp [hopen]
      rw [← this]; exact hzmem
    rcases h.tail_earlier k hk hopen with hpf | ⟨k', hk'k, hk', hk'z, hk'open⟩
    · -- the parent is the root
      refine ⟨[z, f], ⟨rfl, by simpa using root_mem_branch h, by simpa using hzx, ?_, ?_, ?_⟩, ?_⟩
      · rw [List.isChain_cons_cons]
        exact ⟨by rw [← hpf]; exact hpz, List.isChain_singleton _⟩
      · simp [hzf]
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hzvis
        · exact h.root_mem
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact Or.inr ⟨k, le_rfl, hk, rfl, hopen⟩
        · exact Or.inl rfl
    · obtain ⟨l', hl', hidx⟩ := ih k' hk'k hk' hk'open
      rw [hk'z] at hl'
      refine ⟨z :: l', ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro y hy
        obtain ⟨a, l'', rfl⟩ : ∃ a l'', l' = a :: l'' := by
          rcases l' with _ | ⟨a, l''⟩
          · have := hl'.head; simp at this
          · exact ⟨a, l'', rfl⟩
        rw [List.getLast?_cons_cons] at hy
        exact hl'.last_mem y hy
      · intro y hy
        have hne : l' ≠ [] := by
          intro h0
          have := hl'.head
          rw [h0] at this
          simp at this
        rw [List.dropLast_cons_of_ne_nil hne, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hzx
        · exact hl'.dropLast_notMem y hy
      · refine List.IsChain.cons hl'.chain (fun y hy => ?_)
        rw [hl'.head] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact hpz
      · refine List.nodup_cons.2 ⟨fun hzl => ?_, hl'.nodup⟩
        rcases hidx z hzl with hzf' | ⟨j, hjk', hj, hjz, hjopen⟩
        · exact hzf hzf'
        · have hjmem : s.tested[j] ∈ s.tested := List.getElem_mem hj
          have := h.open_unique _ hjmem _ hzmem hjopen hopen (by rw [hjz])
          have hjk : j = k := (List.Nodup.getElem_inj_iff hnd).1 this
          omega
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hzvis
        · exact hl'.visited y hy
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inr ⟨k, le_rfl, hk, rfl, hopen⟩
        · rcases hidx y hy with hyf | ⟨j, hjk', hj, hjy, hjopen⟩
          · exact Or.inl hyf
          · exact Or.inr ⟨j, by omega, hj, hjy, hjopen⟩

theorem exists_chainTo {f d : Site} {s : ExplState} {xs : List Site}
    {Fs : List (List (Site × Site))} (h : DFS0 f d s xs Fs) (hnd : s.tested.Nodup)
    {z : Site} (hz : z ∈ s.visited) : ∃ l, ChainTo s xs z l := by
  by_cases hzf : z = f
  · subst hzf
    exact ⟨[z], rfl, by simpa using root_mem_branch h, by simp, List.isChain_singleton _,
      List.nodup_singleton _, by simpa using hz⟩
  · obtain ⟨p, hp⟩ := h.visited_parent z hz hzf
    obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨l, hl, -⟩ := exists_chainTo_aux h hnd k hk (by rw [hpk])
    rw [hpk] at hl
    exact ⟨l, hl⟩

/-- The heads of the active edges are not enclosed by the visited set. -/
def ExplOuter (s : ExplState) : Prop := ∀ e ∈ s.active, ¬ InFiniteComponent s.visited e.2

theorem not_inFiniteComponent_singleton (f : Site) {u : Site} (hu : IsUnit u) :
    ¬ InFiniteComponent {f} (f + u) := by
  rw [inFiniteComponent_iff]
  rintro ⟨-, hfin⟩
  apply hfin.not_infinite
  -- the ray `f + (n + 1) • u` is infinite and avoids `f`
  have hray : ∀ n : ℕ, AvoidReach {f} (f + u) (f + ((n : ℤ) + 1) • u) := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, zero_add, one_smul]; exact Relation.ReflTransGen.refl
    | succ n ih =>
      refine ih.tail ⟨?_, ?_, ?_⟩
      · rw [Finset.mem_singleton]
        intro h
        have := congrArg (fun p => p - f) h
        simp only [add_sub_cancel_left, sub_self] at this
        rcases hu with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at this <;> omega
      · rw [Finset.mem_singleton]
        intro h
        have := congrArg (fun p => p - f) h
        simp only [add_sub_cancel_left, sub_self] at this
        rcases hu with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at this <;> omega
      · have : f + (((n + 1 : ℕ) : ℤ) + 1) • u - (f + ((n : ℤ) + 1) • u) = u := by
          push_cast
          rw [add_sub_add_left_eq_sub, ← sub_smul,
            show ((n : ℤ) + 1 + 1) - ((n : ℤ) + 1) = 1 by ring, one_smul]
        exact adj_of_unit (by rw [this]; exact hu)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => f + ((n : ℤ) + 1) • u) ?_ hray
  intro m n hmn
  have := congrArg (fun p => p - f) hmn
  simp only [add_sub_cancel_left] at this
  rcases hu with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at this <;> omega

theorem explOuter_init (f : Site) {d : Site} (hd : IsUnit d) : ExplOuter (explInit f d) := by
  intro e he
  simp only [explInit]
  have h1 := edgesFrom_tail f d e he
  have h2 := edgesFrom_adj f hd e he
  rw [h1] at h2
  have := isUnit_of_adj h2
  have he2 : e.2 = f + (e.2 - f) := by abel
  rw [he2]
  exact not_inFiniteComponent_singleton f this

theorem explOuter_step (ρ : Config squareGraph) {s : ExplState} : ExplOuter (explStep ρ s) := by
  intro e he
  rcases h : s.active with _ | ⟨e', rest⟩
  · rw [explStep_nil ρ h] at he
    rw [h] at he
    simp at he
  · rw [explStep_cons ρ h, explStepWith_cons h] at he ⊢
    have := List.of_mem_filter he
    simp only [decide_eq_true_eq, not_or] at this
    exact this.2

theorem explOuter_explore (ρ : Config squareGraph) (f : Site) {d : Site} (hd : IsUnit d) :
    ∀ n : ℕ, ExplOuter (explore ρ f d n)
  | 0 => explOuter_init f hd
  | n + 1 => by rw [explore_succ]; exact explOuter_step ρ

theorem wind_eq_zero_of_far_up {c : List Site} {y : Site} (hy : ∀ p ∈ c, p.2 ≤ y.2) :
    wind c y = 0 := by
  unfold wind
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have h1 := hy _ (mem_steps hs).1
  have h2 := hy _ (mem_steps hs).2
  unfold stepWind
  split_ifs with h <;> [omega; rfl]

theorem wind_eq_zero_of_far_down {c : List Site} {y : Site} (hy : ∀ p ∈ c, y.2 + 1 ≤ p.2) :
    wind c y = 0 := by
  unfold wind
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have h1 := hy _ (mem_steps hs).1
  have h2 := hy _ (mem_steps hs).2
  unfold stepWind
  split_ifs with h <;> [omega; rfl]

/-- Far to the left every vertical step counts, and a closed walk crosses each height as often
upward as downward. -/
theorem wind_eq_zero_of_far_left {c : List Site} (hc : IsClosedWalk c) {y : Site}
    (hy : ∀ p ∈ c, y.1 < p.1) : wind c y = 0 := by
  have key := sum_steps_sub_closed hc (fun p => if y.2 + 1 ≤ p.2 then (1 : ℤ) else 0)
  unfold wind
  rw [← key]
  congr 1
  refine List.map_congr_left (fun s hs => ?_)
  have hu := steps_unit hc hs
  have h1 := hy _ (mem_steps hs).1
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨y1, y2⟩ := y
  rw [isUnit_iff'] at hu
  unfold stepWind
  dsimp only at h1 ⊢
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h h' <;> split_ifs <;> omega

/-- A point lattice-connected off `c` to points arbitrarily far away has winding number zero. -/
theorem le_foldr_max (l : List ℤ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih x hx).trans (le_max_right _ _)

theorem wind_eq_zero_of_unbounded {c : List Site} (hc : IsClosedWalk c) {y : Site}
    (h : ∀ M : ℤ, ∃ z, Relation.ReflTransGen (OffAdj c) y z ∧ (M < |z.1| ∨ M < |z.2|)) :
    wind c y = 0 := by
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ p ∈ c, |p.1| ≤ M ∧ |p.2| ≤ M := by
    refine ⟨(c.map (fun p => max |p.1| |p.2|)).foldr max 0, fun p hp => ?_⟩
    have : max |p.1| |p.2| ≤ (c.map (fun p => max |p.1| |p.2|)).foldr max 0 :=
      le_foldr_max _ _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩
  obtain ⟨z, hyz, hz⟩ := h (M + 1)
  have hoff : Relation.ReflTransGen (fun p q => p ∉ c ∧ q ∉ c ∧ IsUnit (q - p)) y z := hyz
  rw [wind_eq_of_reflTransGen hc hoff]
  rcases hz with hz | hz
  · rcases le_or_gt 0 z.1 with h0 | h0
    · rw [abs_of_nonneg h0] at hz
      exact wind_eq_zero_of_far (fun p hp => by have := (hM p hp).1; rw [abs_le] at this; omega)
    · rw [abs_of_neg h0] at hz
      exact wind_eq_zero_of_far_left hc (fun p hp => by have := (hM p hp).1; rw [abs_le] at this; omega)
  · rcases le_or_gt 0 z.2 with h0 | h0
    · rw [abs_of_nonneg h0] at hz
      exact wind_eq_zero_of_far_up (fun p hp => by have := (hM p hp).2; rw [abs_le] at this; omega)
    · rw [abs_of_neg h0] at hz
      exact wind_eq_zero_of_far_down (fun p hp => by have := (hM p hp).2; rw [abs_le] at this; omega)

end LatticeProb.Lattice.Planar
