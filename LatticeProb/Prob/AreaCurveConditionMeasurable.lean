import LatticeProb.Prob.KernelCurveImage
import LatticeProb.Analysis.VagueLimitCompactMass

/-! # Measurability of the mass parametrization of a curve -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The event that a continuous curve is parametrized by a locally finite measurable
family of measures is measurable. -/
theorem measurableSet_curve_mass_parametrized
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [SigmaCompactSpace E]
    {μ : Ω → Measure E} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → E}
    (hLc : ∀ ω, Continuous (L ω)) (hLm : ∀ t, Measurable fun ω => L ω t) :
    MeasurableSet {ω | ∀ a b : ℝ, a ≤ b →
      μ ω (L ω '' Icc a b) = ENNReal.ofReal (b - a)} := by
  have heq : {ω | ∀ a b : ℝ, a ≤ b →
      μ ω (L ω '' Icc a b) = ENNReal.ofReal (b - a)} =
      ⋂ a : ℚ, ⋂ b : ℚ, ⋂ (_ : a ≤ b),
        {ω | μ ω (L ω '' Icc (a : ℝ) b) = ENNReal.ofReal ((b : ℝ) - a)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h a b hab
      exact h a b (by exact_mod_cast hab)
    · intro h a b hab
      exact VagueLimit.measure_image_Icc_eq_ofReal_of_rat h hab
  rw [heq]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun hab => ?_
  exact measurableSet_eq_fun (measurable_measure_image_Icc hμ hfin hLc hLm
    (by exact_mod_cast hab)) measurable_const

end LatticeProb
