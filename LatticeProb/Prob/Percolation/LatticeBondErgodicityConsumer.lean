import LatticeProb.Prob.Percolation.LatticeBondErgodicity

/-!
# A vertical two-dimensional bond ergodicity consumer

The vertical unit displacement acts ergodically on the actual two-dimensional bond law.
The event that every genuine bond is open is measurable, invariant, and a proper nonempty
subset of configuration space, so the bundled ergodicity theorem gives its zero-one law.
-/

namespace LatticeProb.Percolation

open MeasureTheory

/-- The actual nonzero vertical unit displacement is ergodic for every Bernoulli parameter. -/
theorem verticalUnit_configurationTranslation_ergodic (p : unitInterval) :
    Ergodic (configurationTranslation (unit (1 : Fin 2))) (latticeBondLaw 2 p) :=
  ergodic_configurationTranslation p verticalUnit_ne_zero

/-- Requiring every genuine two-dimensional bond to be open is a measurable event. -/
theorem allBondsOpen_measurable :
    MeasurableSet {ω : Configuration 2 | ∀ e, ω e = true} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun e =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const

/-- The all-open event is invariant under the actual vertical inverse pullback. -/
theorem allBondsOpen_vertical_invariant :
    configurationTranslation (unit (1 : Fin 2)) ⁻¹'
      {ω : Configuration 2 | ∀ e, ω e = true} = {ω | ∀ e, ω e = true} := by
  ext ω
  change (∀ e, ω (bondTranslation (-unit (1 : Fin 2)) e) = true) ↔ ∀ e, ω e = true
  constructor
  · intro h e
    obtain ⟨a, rfl⟩ := (bondTranslation (-unit (1 : Fin 2))).surjective e
    exact h a
  · intro h e
    exact h _

/-- The event contains the constant-open configuration and excludes the constant-closed one. -/
theorem allBondsOpen_nontrivial :
    (fun _ : Bond 2 => true) ∈ {ω : Configuration 2 | ∀ e, ω e = true} ∧
      (fun _ : Bond 2 => false) ∉ {ω : Configuration 2 | ∀ e, ω e = true} := by
  constructor
  · intro e
    rfl
  · intro h
    exact Bool.false_ne_true (h horizontalUnitBond)

/-- The concrete proper nonempty invariant event has probability zero or one at every parameter. -/
theorem allBondsOpen_vertical_zero_or_one (p : unitInterval) :
    latticeBondLaw 2 p {ω | ∀ e, ω e = true} = 0 ∨
      latticeBondLaw 2 p {ω | ∀ e, ω e = true} = 1 :=
  latticeBondLaw_zero_or_one_of_translationInvariant p verticalUnit_ne_zero
    allBondsOpen_measurable allBondsOpen_vertical_invariant

end LatticeProb.Percolation
