/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.AffineVague at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineCircleSpatial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-! Existence of the dyadic GMC vague limit after an affine coordinate change. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open LQGMetric MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling

theorem isVagueLimitC_affine_of_hasAreaLimitS {γ : ℝ} (hγ : γ ≠ 0)
    {h : DistC} {μ : Measure ℂ} (h1 : HasScaleCircleAvgs h)
    (h2 : HasAreaLimitS γ h μ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) :
    IsVagueLimitC
      (lqgAreaApprox γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)))
      (ENNReal.ofReal (Real.exp (γ * c)) • μ.map (affT hr z).symm) := by
  set h' := addConst (affineComp r z h) (lqgQ γ * Real.log r + c)
  set T := affT hr z
  set e := ENNReal.ofReal (Real.exp (γ * c))
  have hmapk : ∀ k, lqgAreaApprox γ h' k = (e • areaS γ h (r * dyadicScale k)).map T.symm := by
    intro k
    rw [← map_lqgAreaApprox_affine hγ h1 hr z c k,
      Measure.map_map T.symm.measurable T.measurable, T.symm_comp_self, Measure.map_id]
  constructor
  · intro K hK
    rw [Measure.smul_apply, smul_eq_mul, MeasurableEquiv.map_apply,
      ← MeasurableEquiv.image_eq_preimage_symm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h2.1 _ (hK.image (continuous_affT hr z)))
  · intro f hf hfc
    have hg : Continuous (f ∘ T.symm) := hf.comp (continuous_affT_symm hr z)
    have hgc : HasCompactSupport (f ∘ T.symm) := by
      have := hfc.comp_homeomorph ((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans
        (Homeomorph.addRight z)).symm
      simpa only [T, affT, LQGMetric.DG.affineEquivC,
        Homeomorph.toMeasurableEquiv_symm_coe] using this
    have hlim := ((h2.2 _ hg hgc).comp (tendsto_mul_dyadicScale hr)).const_smul e.toReal
    have hval : ∀ k, ∫ w, f w ∂lqgAreaApprox γ h' k =
        e.toReal • ∫ w, (f ∘ T.symm) w ∂areaS γ h (r * dyadicScale k) := by
      intro k
      rw [hmapk k, integral_map_equiv, integral_smul_measure]
      rfl
    have hval' : ∫ w, f w ∂(e • μ.map T.symm) =
        e.toReal • ∫ w, (f ∘ T.symm) w ∂μ := by
      rw [integral_smul_measure, integral_map_equiv]
      rfl
    rw [hval']
    exact hlim.congr fun k => (hval k).symm

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTPort MatedCRTHarmonic.L43O

theorem ae_affine_zeroCone_vague
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ), 0 < r → ∀ (z : ℂ),
      ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC
        (CellScaling.lqgAreaApprox γ (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω))) μ := by
  have hQ : (0 : ℝ) < CellScaling.lqgQ γ := LQGCoord.lqgQ_pos hγ.1
  filter_upwards [ae_radialGood D.gff₀ D.bm_B₀ D.bm_B₀' hQ,
    ae_hasScaleCircleAvgs_wp D.gff₀,
    ae_hasAreaLimitS_wp D.gff₀ hγ.1 hγ.2,
    ae_tight_wp D.gff₀ hγ.1 hγ.2 (le_max_left _ _) (coneExp_lt hγ.1 hQ)]
    with ω hrad hscale harea htight
  have hc := coneGood_of hQ hrad hscale harea htight
  intro r hr z
  let h : DistC := zeroConeField γ X₀ B₀ B₀' ω
  let a := circleAvg h r z
  have hf : IGLaw.affField r 0 z h =
      addConst (affineComp r z h) (CellScaling.lqgQ γ * Real.log r +
        (-a - CellScaling.lqgQ γ * Real.log r)) := by
    rw [IGLaw.affField, L43O.rotateField_zero]
    congr 1
    ring
  have hv := isVagueLimitC_affine_of_hasAreaLimitS hγ.1.ne'
    (hasScaleCircleAvgs_cone hscale hc.li₁ hc.li₂ hc.cont₁ hc.cont₂)
    (hasAreaLimitS_cone hγ.1 hc) hr z (-a - CellScaling.lqgQ γ * Real.log r)
  change CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ
    (addConst (affineComp r z h) (CellScaling.lqgQ γ * Real.log r +
      (-a - CellScaling.lqgQ γ * Real.log r)))) _ at hv
  rw [← hf] at hv
  exact ⟨_, hv⟩

end MatedCRTHarmonic.GMS4cS

