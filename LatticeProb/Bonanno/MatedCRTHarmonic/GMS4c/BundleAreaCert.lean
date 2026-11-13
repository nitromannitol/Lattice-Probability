/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleAreaCert at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaCertBorel

/-! The Borel shifted GMC certificate holds under both bundle cone laws. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem ae_gamma_shiftedLocalAreaCert
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ ω ∂P, shiftedLocalAreaCert γ V δ J
      (restrictTo (thickOpen V δ)
        (coneField (X ω) (coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω)))) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  filter_upwards [ae_gamma_localDyadicGood D hγ V hVb hδ,
    ae_gamma_localCircle_continuous_eventually D hγ V hδ,
    ae_cone_areaApprox_finite_eventually hγ.1 hγ.2
      (MesoModel.FrozenIdentities.lt_lqgQ hγ) D.gff D.bm_B D.bm_B'
      hVb.isCompact_closure] with ω hg hc hf
  exact shiftedLocalAreaCert_of_vague_finite γ V δ J hJb _ _
    (localAreaVagueSelection_spec hg).1
    (eventually_finite_localAreaApproxDy_of_ae_continuous γ V hδ _ hc hf)

theorem ae_zero_shiftedLocalAreaCert
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) (J : ℂ ≃ₜ ℂ)
    (hJb : Bornology.IsBounded (J '' (V : Set ℂ))) :
    ∀ᵐ ω ∂P, shiftedLocalAreaCert γ V δ J
      (restrictTo (thickOpen V δ)
        (coneField (X₀ ω) (coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω)))) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  filter_upwards [ae_zero_localDyadicGood D hγ V hVb hδ,
    ae_zero_localCircle_continuous_eventually D hγ V hδ,
    ae_cone_areaApprox_finite_eventually hγ.1 hγ.2
      (MesoModel.FrozenIdentities.lqgQ_pos hγ.1) D.gff₀ D.bm_B₀ D.bm_B₀'
      hVb.isCompact_closure] with ω hg hc hf
  exact shiftedLocalAreaCert_of_vague_finite γ V δ J hJb _ _
    (localAreaVagueSelection_spec hg).1
    (eventually_finite_localAreaApproxDy_of_ae_continuous γ V hδ _ hc hf)

end MatedCRTHarmonic.GMS4c

