/-
The finite set of endpoints of the walks of a given length, the two one-step
recursions for the transition kernel, its reversibility against the degree
measure, and the Chapman-Kolmogorov identity.

`reach G n x` is the set of vertices joined to `x` by a walk of exactly `n`
steps.  It is a `Finset` because the graph is locally finite, and it carries
the support of `heat G n x`: outside it the `n`-step transition probability
vanishes.  Every sum over the vertex set below is therefore a finite sum, and
no summability hypothesis is needed anywhere.
-/
import LatticeProb.Graph.HeatBasic

open scoped Classical

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

noncomputable def reach (G : SimpleGraph V) [G.LocallyFinite] : ℕ → V → Finset V
  | 0, x => {x}
  | (n + 1), x => (G.neighborFinset x).biUnion fun w => reach G n w

theorem reach_zero (x : V) : reach G 0 x = {x} := rfl

theorem reach_succ (n : ℕ) (x : V) :
    reach G (n + 1) x = (G.neighborFinset x).biUnion (fun w => reach G n w) := rfl

theorem heat_eq_zero_of_notMem_reach : ∀ (n : ℕ) (x y : V),
    y ∉ reach G n x → heat G n x y = 0 := by
  intro n
  induction n with
  | zero =>
      intro x y hy
      rw [reach_zero, Finset.mem_singleton] at hy
      have : ¬ x = y := fun h => hy h.symm
      simp [heat, this]
  | succ n ih =>
      intro x y hy
      rw [reach_succ] at hy
      rw [heat_succ, walkOp,
        Finset.sum_eq_zero
          (fun w hw => ih w y (fun hmem => hy (Finset.mem_biUnion.2 ⟨w, hw, hmem⟩))),
        zero_div]

theorem heat_forward : ∀ (k : ℕ) (x y : V),
    heat G (k + 1) x y = ∑ w ∈ G.neighborFinset y, heat G k x w / (G.degree w : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro x y
      rw [heat_succ, walkOp]
      have h1 : ∀ z : V, heat G 0 z y = if z = y then (1:ℝ) else 0 := by
        intro z; by_cases h : z = y <;> simp [heat, h]
      have h2 : ∀ w : V, heat G 0 x w / (G.degree w : ℝ)
          = if x = w then 1 / (G.degree x : ℝ) else 0 := by
        intro w
        by_cases h : x = w
        · subst h; simp [heat]
        · simp [heat, h]
      simp only [h1, h2]
      rw [Finset.sum_ite_eq' (G.neighborFinset x) y (fun _ => (1:ℝ)),
        Finset.sum_ite_eq (G.neighborFinset y) x (fun _ => 1 / (G.degree x : ℝ))]
      by_cases h : G.Adj x y
      · have hxy : y ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset _ _ _).2 h
        have hyx : x ∈ G.neighborFinset y := (SimpleGraph.mem_neighborFinset _ _ _).2 h.symm
        rw [if_pos hxy, if_pos hyx, one_div]
      · have hxy : y ∉ G.neighborFinset x := fun hh =>
          h ((SimpleGraph.mem_neighborFinset _ _ _).1 hh)
        have hyx : x ∉ G.neighborFinset y := fun hh =>
          h (((SimpleGraph.mem_neighborFinset _ _ _).1 hh).symm)
        rw [if_neg hxy, if_neg hyx, zero_div]
  | succ k ih =>
      intro x y
      rw [heat_succ, walkOp]
      have : ∀ v ∈ G.neighborFinset x, heat G (k + 1) v y
          = ∑ w ∈ G.neighborFinset y, heat G k v w / (G.degree w : ℝ) := fun v _ => ih v y
      rw [Finset.sum_congr rfl this, Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [heat_succ, walkOp, ← Finset.sum_div]
      ring

theorem heat_div_degree_symm : ∀ (k : ℕ) (x y : V),
    heat G k x y / (G.degree y : ℝ) = heat G k y x / (G.degree x : ℝ) := by
  intro k
  induction k with
  | zero =>
      intro x y
      by_cases h : x = y
      · subst h; rfl
      · have h' : ¬ y = x := fun hh => h hh.symm
        simp [heat, h, h']
  | succ k ih =>
      intro x y
      rw [heat_forward, heat_succ, walkOp, div_div, Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ih x w]
      ring

theorem heat_add : ∀ (m n : ℕ) (x z : V),
    heat G (m + n) x z = ∑ y ∈ reach G m x, heat G m x y * heat G n y z := by
  intro m
  induction m with
  | zero =>
      intro n x z
      rw [reach_zero, Finset.sum_singleton]
      simp [heat]
  | succ m ih =>
      intro n x z
      have harith : m + 1 + n = (m + n) + 1 := by omega
      rw [harith, heat_succ, walkOp]
      have hsub : ∀ w ∈ G.neighborFinset x, reach G m w ⊆ reach G (m + 1) x := by
        intro w hw
        rw [reach_succ]
        exact Finset.subset_biUnion_of_mem (fun w => reach G m w) hw
      have step : ∀ w ∈ G.neighborFinset x, heat G (m + n) w z
          = ∑ y ∈ reach G (m + 1) x, heat G m w y * heat G n y z := by
        intro w hw
        rw [ih n w z]
        refine Finset.sum_subset (hsub w hw) ?_
        intro y _ hy
        rw [heat_eq_zero_of_notMem_reach m w y hy, zero_mul]
      rw [Finset.sum_congr rfl step, Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [heat_succ, walkOp, ← Finset.sum_mul]
      ring

theorem sum_heat_eq_one (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (n : ℕ) (x : V), ∑ y ∈ reach G n x, heat G n x y = 1 := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [reach_zero, Finset.sum_singleton]
      simp [heat]
  | succ n ih =>
      intro x
      have hsub : ∀ w ∈ G.neighborFinset x, reach G n w ⊆ reach G (n + 1) x := by
        intro w hw
        rw [reach_succ]
        exact Finset.subset_biUnion_of_mem (fun w => reach G n w) hw
      have step : ∀ y ∈ reach G (n + 1) x, heat G (n + 1) x y
          = (∑ w ∈ G.neighborFinset x, heat G n w y) / (G.degree x : ℝ) := by
        intro y _
        rw [heat_succ, walkOp]
      rw [Finset.sum_congr rfl step, ← Finset.sum_div, Finset.sum_comm]
      have inner : ∀ w ∈ G.neighborFinset x, ∑ y ∈ reach G (n + 1) x, heat G n w y = 1 := by
        intro w hw
        rw [← ih w]
        exact (Finset.sum_subset (hsub w hw)
          (fun y _ hy => heat_eq_zero_of_notMem_reach n w y hy)).symm
      rw [Finset.sum_congr rfl inner, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul, mul_one, div_self (Nat.cast_ne_zero.mpr (hdeg x).ne')]

theorem sum_degree_heat_mul (hdeg : ∀ v : V, 0 < G.degree v) (m n : ℕ) (x w : V)
    (T : Finset V) (hT : reach G m x ⊆ T) :
    ∑ y ∈ T, (G.degree y : ℝ) * (heat G m x y / (G.degree y : ℝ))
        * (heat G n w y / (G.degree y : ℝ))
      = heat G (m + n) x w / (G.degree w : ℝ) := by
  have hstep : ∀ y ∈ T, (G.degree y : ℝ) * (heat G m x y / (G.degree y : ℝ))
      * (heat G n w y / (G.degree y : ℝ)) = heat G m x y * (heat G n y w / (G.degree w : ℝ)) := by
    intro y _
    rw [← heat_div_degree_symm n w y]
    have : (G.degree y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg y).ne'
    field_simp
  have hshrink : ∑ y ∈ T, heat G m x y * (heat G n y w / (G.degree w : ℝ))
      = ∑ y ∈ reach G m x, heat G m x y * (heat G n y w / (G.degree w : ℝ)) :=
    (Finset.sum_subset hT
      (fun y _ hy => by rw [heat_eq_zero_of_notMem_reach m x y hy, zero_mul])).symm
  rw [Finset.sum_congr rfl hstep, hshrink, heat_add m n x w, Finset.sum_div]
  exact Finset.sum_congr rfl fun y _ => by ring



/-- A transition probability is at most one. -/
theorem heat_le_one (hdeg : ∀ v : V, 0 < G.degree v) (n : ℕ) (x y : V) : heat G n x y ≤ 1 := by
  by_cases hy : y ∈ reach G n x
  · rw [← sum_heat_eq_one hdeg n x]
    exact Finset.single_le_sum (f := fun z => heat G n x z) (fun z _ => heat_nonneg n x z) hy
  · rw [heat_eq_zero_of_notMem_reach n x y hy]
    norm_num

/-- A walk of length `n` reaches `reach G n x`, and conversely. -/
theorem exists_walk_of_mem_reach : ∀ (n : ℕ) (x y : V), y ∈ reach G n x →
    ∃ p : G.Walk x y, p.length = n := by
  intro n
  induction n with
  | zero =>
      intro x y hy
      rw [reach_zero, Finset.mem_singleton] at hy
      subst hy
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      intro x y hy
      rw [reach_succ, Finset.mem_biUnion] at hy
      obtain ⟨w, hw, hyw⟩ := hy
      obtain ⟨p, hp⟩ := ih w y hyw
      refine ⟨SimpleGraph.Walk.cons ((SimpleGraph.mem_neighborFinset _ _ _).1 hw) p, ?_⟩
      rw [SimpleGraph.Walk.length_cons, hp]

/-- The walk cannot outrun the graph distance: the `n`-step transition
probability vanishes beyond distance `n`. -/
theorem heat_eq_zero_of_lt_dist {n : ℕ} {x y : V} (h : n < G.dist x y) : heat G n x y = 0 := by
  by_contra hne
  by_cases hmem : y ∈ reach G n x
  · obtain ⟨p, hp⟩ := exists_walk_of_mem_reach n x y hmem
    exact absurd (hp ▸ SimpleGraph.dist_le p) (not_le.mpr h)
  · exact hne (heat_eq_zero_of_notMem_reach n x y hmem)

/-- On a graph of degree bounded by `d` the walk of length `n` reaches at most
`d ^ n` vertices. -/
theorem card_reach_le {d : ℕ} (hd : BoundedDegree G d) :
    ∀ (n : ℕ) (x : V), (reach G n x).card ≤ d ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [reach_zero, Finset.card_singleton, pow_zero]
  | succ n ih =>
      intro x
      rw [reach_succ]
      refine le_trans (Finset.card_biUnion_le) ?_
      refine le_trans (Finset.sum_le_sum (fun w _ => ih w)) ?_
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul,
        pow_succ, mul_comm (d ^ n) d]
      exact Nat.mul_le_mul_right _ (hd x)

end LatticeProb.Graph
