import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeRadialPath
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN

/-! # Local integrability of a Brownian radial splice -/

/- The growth argument uses Leonardo Bonanno's `exists_abs_le_add_of_tendsto_div`
and `locallyIntegrable_radial_of_growth` from lean-formalizations,
MatedCRTHarmonic.GMCFacts.ConeRadialPath. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- The radial profile of a splice with Brownian inner path is locally
integrable almost surely. The exterior path may depend on the inner path. -/
theorem ae_locallyIntegrable_radialW_twoSided
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (W V : Ω → C(ℝ≥0, ℝ))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) :
    ∀ᵐ ω ∂P, LocallyIntegrable (radialW (twoSided (W ω) (V ω))) volume := by
  filter_upwards [hW, hB.eval_zero_ae_eq_zero,
    QuantumZipper.BMLLN.ae_tendsto_div_atTop hB] with ω hw hz hlln
  have hcont : Continuous (fun t : ℝ≥0 => B t ω) := by
    have heq : (fun t => B t ω) = ⇑(W ω) := funext fun t => (hw t).symm
    rw [heq]
    exact (W ω).continuous
  obtain ⟨C₀, hC₀⟩ := exists_abs_le_add_of_tendsto_div hcont hlln
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hwzero : W ω 0 = 0 := (hw 0).trans hz
  have hgr : ∀ t : ℝ, 0 ≤ t → |twoSided (W ω) (V ω) t| ≤ C + 1 * t := by
    intro t ht
    rw [twoSided_apply, Real.toNNReal_of_nonpos (neg_nonpos.mpr ht), sub_self,
      add_zero, hwzero, sub_zero, hw]
    have h := hC₀ t.toNNReal
    rw [Real.coe_toNNReal t ht] at h
    dsimp [C]
    linarith [le_max_left C₀ 0]
  exact locallyIntegrable_radial_of_growth (twoSided (W ω) (V ω)).continuous
    hC zero_le_one hgr

end LatticeProb.LQG
