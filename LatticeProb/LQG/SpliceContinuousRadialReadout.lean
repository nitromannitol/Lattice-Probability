import LatticeProb.LQG.SpliceCircleAverage
import LatticeProb.LQG.SpliceRadialIntegrability

/-! # Continuous radial readout of a Brownian splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- A continuous version of the circle averages reads the entire two-sided
radial splice on a single almost-sure event. The exterior path may depend on
the field and the inner Brownian path. -/
theorem ae_continuous_circleVersion_replField_twoSided
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (W V : Ω → C(ℝ≥0, ℝ))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    (c : Ω → ℝ → ℂ → ℝ)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ᵐ ω ∂P,
      c ω r 0 = circleAvg (replField X (fun ω => twoSided (W ω) (V ω)) ω) r 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, c ω (Real.exp (-t)) 0 = twoSided (W ω) (V ω) t := by
  have hloc := ae_locallyIntegrable_radialW_twoSided hB W V hW
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P,
      c ω (Real.exp (-(q : ℝ))) 0 = twoSided (W ω) (V ω) (q : ℝ) := by
    intro q
    filter_upwards [heq _ (Real.exp_pos _) ,
      ae_circleAvg_replField hX (fun ω => twoSided (W ω) (V ω)) hloc
        (Real.exp_pos (-(q : ℝ)))] with ω h₁ h₂
    simpa only [Real.log_exp, neg_neg] using h₁.trans h₂
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  have hcont : Continuous (fun t : ℝ => c ω (Real.exp (-t)) 0) := by
    apply (hc ω).comp_continuous
      (show Continuous (fun t : ℝ => (Real.exp (-t), (0 : ℂ))) by fun_prop)
    intro t
    exact ⟨Real.exp_pos _, mem_univ _⟩
  have hext := Continuous.ext_on Rat.denseRange_cast hcont (twoSided (W ω) (V ω)).continuous
    (show Set.EqOn (fun t : ℝ => c ω (Real.exp (-t)) 0)
      (twoSided (W ω) (V ω)) (Set.range ((↑) : ℚ → ℝ)) from by
        rintro _ ⟨q, rfl⟩
        exact hω q)
  exact fun t => congrFun hext t

end LatticeProb.LQG
