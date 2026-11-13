/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleAreaFinite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaSpatial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-! Eventual compact finiteness of the cone GMC approximations. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling

theorem ae_cone_areaApprox_finite_eventually
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {γ α : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      lqgAreaApprox γ
        (coneField (X ω) (coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))
        k K < ⊤ := by
  filter_upwards [ae_radialGood hX hB hB' hαQ,
    ae_hasScaleCircleAvgs_wp hX, ae_hasAreaLimitS_wp hX hγ hγ2,
    ae_tight_wp hX hγ hγ2 (le_max_left _ _) (coneExp_lt hγ hαQ)]
      with ω hr hs ha ht
  have hc := coneGood_of hαQ hr hs ha ht
  simpa only [coneField_eq_cone, lqgAreaApprox_eq_areaS] using
    (fin_cone hγ hc tendsto_dyadicScale hK)

end MatedCRTHarmonic.GMS4c

