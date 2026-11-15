import LatticeProb.LQG.MatingOfTreesCouplingPathwise

/-! # Measurability of proper and surjective curves -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ContinuousMap

/-- Proper continuous curves form a Borel set in the compact-open topology. -/
theorem measurableSet_isProperMap_curve
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    MeasurableSet {f : C(ℝ, E) | IsProperMap f} := by
  have heq : {f : C(ℝ, E) | IsProperMap f} =
      {f : C(ℝ, E) | ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ,
        (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖f q‖} := by
    ext f
    exact (isProperMap_iff_tendsto_cocompact.trans
      (and_iff_right f.continuous)).trans (tendsto_cocompact_iff_forall_rat f)
  rw [heq]
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.exists fun m =>
    Measurable.forall fun q => Measurable.imp measurable_const ?_)
  exact measurableSet_setOfPred.1
    (isClosed_le continuous_const (ContinuousEvalConst.continuous_eval_const (q : ℝ)).norm).measurableSet

/-- Proper surjective continuous curves form a Borel set. -/
theorem measurableSet_isProperMap_and_surjective_curve
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E] :
    MeasurableSet {f : C(ℝ, E) | IsProperMap f ∧ Function.Surjective f} := by
  have heq : {f : C(ℝ, E) | IsProperMap f ∧ Function.Surjective f} =
      {f : C(ℝ, E) | IsProperMap f ∧ DenseRange (fun q : ℚ => f q)} := by
    ext f
    constructor
    · rintro ⟨hp, hs⟩
      exact ⟨hp, (surjective_iff_denseRange_rat f
        (isProperMap_iff_tendsto_cocompact.1 hp).2).1 hs⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, (surjective_iff_denseRange_rat f
        (isProperMap_iff_tendsto_cocompact.1 hp).2).2 hd⟩
  rw [heq]
  exact measurableSet_isProperMap_curve.inter measurableSet_setOf_denseRange_rat

end ContinuousMap
