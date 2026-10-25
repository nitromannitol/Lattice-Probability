import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

/-!
# Critical probability of the lattice bond model

The critical parameter is the real infimum of the actual positive percolation probability
parameters. In positive dimension this set contains one and lies in the unit interval.
Its greatest lower bound characterization uses those proved nonemptiness and bound facts.
-/

namespace LatticeProb.Percolation

variable {d : ℕ} [NeZero d]

/-- The actual positive-theta parameters contain a concrete endpoint witness. -/
theorem positive_theta_parameters_nonempty (d : ℕ) [NeZero d] :
    {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}.Nonempty :=
  (positive_theta_parameters_nonempty_bounded d).1

/-- Every actual positive-theta parameter lies between zero and one. -/
theorem positive_theta_parameters_subset_unitInterval (d : ℕ) :
    {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} ⊆ Set.Icc 0 1 := by
  rintro q ⟨p, rfl, _⟩
  exact p.property

/-- Zero is a lower bound on the actual positive-theta parameters. -/
theorem positive_theta_parameters_bddBelow (d : ℕ) [NeZero d] :
    BddBelow {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} :=
  (positive_theta_parameters_nonempty_bounded d).2.1

/-- One is an upper bound on the actual positive-theta parameters. -/
theorem positive_theta_parameters_bddAbove (d : ℕ) [NeZero d] :
    BddAbove {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} :=
  (positive_theta_parameters_nonempty_bounded d).2.2

/-- The critical probability is literally the real infimum of positive-theta parameters. -/
noncomputable def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

/-- The critical probability is the greatest lower bound of the actual parameter set. -/
theorem criticalProbability_isGLB (d : ℕ) [NeZero d] :
    IsGLB {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}
      (criticalProbability d) :=
  isGLB_csInf (positive_theta_parameters_nonempty d) (positive_theta_parameters_bddBelow d)

/-- Every parameter of positive percolation probability is at least the critical value. -/
theorem criticalProbability_le (p : unitInterval) (hp : 0 < theta d p) :
    criticalProbability d ≤ (p : ℝ) :=
  (criticalProbability_isGLB d).1 ⟨p, rfl, hp⟩

/-- A real number is below the critical value exactly when it bounds all positive parameters. -/
theorem le_criticalProbability_iff (a : ℝ) :
    a ≤ criticalProbability d ↔ ∀ p : unitInterval, 0 < theta d p → a ≤ (p : ℝ) := by
  constructor
  · intro ha p hp
    exact ha.trans (criticalProbability_le p hp)
  · intro ha
    apply (criticalProbability_isGLB d).2
    rintro q ⟨p, rfl, hp⟩
    exact ha p hp

/-- The critical value is nonnegative because all unit-interval parameters are nonnegative. -/
theorem criticalProbability_nonneg (d : ℕ) [NeZero d] : 0 ≤ criticalProbability d :=
  (le_criticalProbability_iff 0).mpr (fun p _ => p.property.1)

/-- The concrete positive parameter one bounds the critical probability above. -/
theorem criticalProbability_le_one (d : ℕ) [NeZero d] : criticalProbability d ≤ 1 := by
  apply criticalProbability_le (1 : unitInterval)
  rw [theta_one]
  exact zero_lt_one

/-- The critical parameter lies in the closed real unit interval. -/
theorem criticalProbability_mem_unitInterval (d : ℕ) [NeZero d] :
    criticalProbability d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨criticalProbability_nonneg d, criticalProbability_le_one d⟩

/-- The greatest lower bound characterization uniquely determines the critical value. -/
theorem criticalProbability_eq_iff_isGLB (a : ℝ) :
    criticalProbability d = a ↔
      IsGLB {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p} a := by
  constructor
  · intro h
    rw [← h]
    exact criticalProbability_isGLB d
  · intro ha
    exact (criticalProbability_isGLB d).unique ha

/-- Every real number strictly above criticality exceeds an actual positive-theta parameter. -/
theorem criticalProbability_lt_iff (a : ℝ) :
    criticalProbability d < a ↔
      ∃ p : unitInterval, 0 < theta d p ∧ (p : ℝ) < a := by
  rw [criticalProbability,
    csInf_lt_iff (positive_theta_parameters_bddBelow d) (positive_theta_parameters_nonempty d)]
  constructor
  · rintro ⟨q, ⟨p, rfl, hp⟩, hq⟩
    exact ⟨p, hp, hq⟩
  · rintro ⟨p, hp, hpa⟩
    exact ⟨p, ⟨p, rfl, hp⟩, hpa⟩

/-- Strictly subcritical parameters have zero probability of an infinite origin component. -/
theorem theta_eq_zero_of_lt_criticalProbability (p : unitInterval)
    (hp : (p : ℝ) < criticalProbability d) : theta d p = 0 := by
  apply le_antisymm _ (theta_nonneg d p)
  by_contra h
  exact (not_le_of_gt hp) (criticalProbability_le p (lt_of_not_ge h))

end LatticeProb.Percolation
