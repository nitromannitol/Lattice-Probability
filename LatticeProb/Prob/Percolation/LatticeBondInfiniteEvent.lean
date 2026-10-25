import LatticeProb.Prob.Percolation.LatticeBondProbability
import LatticeProb.Walk.Shells

/-!
# Measurability of the actual infinite open component

Finite open walks give a countable description of reachability in the actual open graph.
The component containing a vertex is infinite exactly when it escapes every finite vertex
set. This proves measurability without choosing any infinite component. The percolation
probability is the real probability that the component of the origin is infinite.
-/

namespace LatticeProb.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- Existence of a finite open walk of exactly `n` edges between the given vertices. -/
def openWalkEvent (ω : Configuration d) : ℕ → Vertex d → Vertex d → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, (openGraph ω).Adj x z ∧ openWalkEvent ω n z y

/-- The finite-walk predicate is equivalent to reachability in the actual open graph. -/
theorem reachable_iff_exists_openWalkEvent (ω : Configuration d) (x y : Vertex d) :
    (openGraph ω).Reachable x y ↔ ∃ n, openWalkEvent ω n x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨0, rfl⟩
    | @cons u v w h p ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, v, h, hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      change x = y at hn
      subst y
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      obtain ⟨z, h, hz⟩ := hn
      exact h.reachable.trans (ih z hz)

/-- Adjacency is a measurable cylinder event on one genuine lattice bond. -/
theorem measurableSet_openGraph_adj (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openGraph ω).Adj x y} := by
  by_cases h : (nearestNeighborGraph d).Adj x y
  · have heq : {ω : Configuration d | (openGraph ω).Adj x y} =
        {ω | ω (bondOfAdjacent h) = true} := by
      ext ω
      exact ⟨fun ⟨_, ho⟩ => ho, fun ho => ⟨h, ho⟩⟩
    rw [heq]
    exact (measurableSet_singleton true).preimage (measurable_pi_apply _)
  · have heq : {ω : Configuration d | (openGraph ω).Adj x y} = ∅ := by
      ext ω
      exact ⟨fun ⟨ha, _⟩ => (h ha).elim, False.elim⟩
    rw [heq]
    exact MeasurableSet.empty

/-- Finite open walks are countable unions of finite intersections of cylinder events. -/
theorem measurableSet_openWalkEvent (n : ℕ) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | openWalkEvent ω n x y} := by
  induction n generalizing x with
  | zero => exact MeasurableSet.const _
  | succ n ih =>
    simp only [openWalkEvent, Set.setOf_exists, Set.setOf_and]
    exact MeasurableSet.iUnion (fun z => (measurableSet_openGraph_adj x z).inter (ih z))

/-- Reachability between fixed vertices is measurable in the product sigma algebra. -/
theorem measurableSet_openGraph_reachable (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openGraph ω).Reachable x y} := by
  simp only [reachable_iff_exists_openWalkEvent, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_openWalkEvent n x y)

/-- The actual component of `x` has infinitely many vertices. -/
def infiniteComponentEvent (x : Vertex d) : Set (Configuration d) :=
  {ω | ((openGraph ω).connectedComponentMk x).supp.Infinite}

/-- Infinitude of the actual component is exactly escape from every finite vertex set. -/
theorem mem_infiniteComponentEvent_iff (ω : Configuration d) (x : Vertex d) :
    ω ∈ infiniteComponentEvent x ↔
      ∀ s : Finset (Vertex d), ∃ y, y ∉ s ∧ (openGraph ω).Reachable x y := by
  classical
  constructor
  · intro h s
    obtain ⟨y, hy, hys⟩ := h.exists_notMem_finset s
    refine ⟨y, hys, ?_⟩
    exact (SimpleGraph.ConnectedComponent.eq.mp
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hy)).symm
  · intro h hf
    obtain ⟨y, hy, hr⟩ := h hf.toFinset
    apply hy
    exact hf.mem_toFinset.mpr
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
        (SimpleGraph.ConnectedComponent.sound hr.symm))

/-- The actual component is infinite exactly when open walks escape every finite box. -/
theorem mem_infiniteComponentEvent_iff_box (ω : Configuration d) (x : Vertex d) :
    ω ∈ infiniteComponentEvent x ↔
      ∀ n : ℕ, ∃ y, y ∉ boxFinset (0 : Vertex d) n ∧ (openGraph ω).Reachable x y := by
  classical
  rw [mem_infiniteComponentEvent_iff]
  constructor
  · intro h n
    exact h (boxFinset 0 n)
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.sup supNorm)
    refine ⟨y, fun hys => hy ?_, hr⟩
    exact mem_boxFinset_zero_iff.mpr (Finset.le_sup hys)

/-- The event that the actual component of a fixed vertex is infinite is measurable. -/
theorem measurableSet_infiniteComponentEvent (x : Vertex d) :
    MeasurableSet (infiniteComponentEvent x) := by
  have heq : infiniteComponentEvent x =
      ⋂ s : Finset (Vertex d), ⋃ y : Vertex d,
        {ω : Configuration d | y ∉ s ∧ (openGraph ω).Reachable x y} := by
    ext ω
    simp only [mem_infiniteComponentEvent_iff, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_setOf_eq]
  rw [heq]
  refine MeasurableSet.iInter (fun s => MeasurableSet.iUnion (fun y => ?_))
  exact (MeasurableSet.const (y ∉ s)).inter (measurableSet_openGraph_reachable x y)

/-- The probability that the actual open component of the origin is infinite. -/
noncomputable def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (latticeBondLaw d p).real (infiniteComponentEvent 0)

/-- The literal defining equation of the percolation probability. -/
theorem theta_eq (d : ℕ) (p : unitInterval) :
    theta d p = (latticeBondLaw d p).real
      {ω | ((openGraph ω).connectedComponentMk 0).supp.Infinite} := rfl

/-- Percolation probability is nonnegative. -/
theorem theta_nonneg (d : ℕ) (p : unitInterval) : 0 ≤ theta d p :=
  measureReal_nonneg

/-- Percolation probability is at most one. -/
theorem theta_le_one (d : ℕ) (p : unitInterval) : theta d p ≤ 1 :=
  measureReal_le_one

/-- Every component of the fully open lattice is infinite in positive dimension. -/
theorem allOpen_mem_infiniteComponentEvent [NeZero d] (x : Vertex d) :
    allOpen d ∈ infiniteComponentEvent x := by
  have hs : ((openGraph (allOpen d)).connectedComponentMk x).supp = Set.univ := by
    ext y
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      openGraph_allOpen, Set.mem_univ, iff_true]
    exact (Graph.Zd.latticeConnected d).preconnected y x
  change ((openGraph (allOpen d)).connectedComponentMk x).supp.Infinite
  rw [hs]
  exact Set.infinite_univ

/-- The actual percolation probability is one at parameter one in positive dimension. -/
theorem theta_one (d : ℕ) [NeZero d] : theta d 1 = 1 := by
  rw [theta, latticeBondLaw_one, measureReal_def,
    Measure.dirac_apply' _ (measurableSet_infiniteComponentEvent 0)]
  rw [Set.indicator_of_mem (allOpen_mem_infiniteComponentEvent 0)]
  exact ENNReal.toReal_one

/-- Positive-theta parameters form a nonempty real set bounded between zero and one. -/
theorem positive_theta_parameters_nonempty_bounded (d : ℕ) [NeZero d] :
    {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}.Nonempty ∧
      BddBelow {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} ∧
      BddAbove {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} := by
  constructor
  · refine ⟨1, 1, rfl, ?_⟩
    rw [theta_one]
    exact zero_lt_one
  · constructor
    · refine ⟨0, ?_⟩
      rintro q ⟨p, rfl, _⟩
      exact p.property.1
    · refine ⟨1, ?_⟩
      rintro q ⟨p, rfl, _⟩
      exact p.property.2

end LatticeProb.Percolation
