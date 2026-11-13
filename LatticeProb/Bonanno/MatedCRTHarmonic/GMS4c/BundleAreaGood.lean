/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleAreaGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaGood
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaSpatial
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaFinite

/-! The bundle cone restrictions satisfy the Borel GMC selector condition. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem ae_gamma_localDyadicGood
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, LocalDyadicGood γ V δ
      (restrictTo (thickOpen V δ)
        (coneField (X ω) (coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω)))) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ,
    ae_gamma_localCircle_continuous_eventually D hγ V hδ,
    ae_cone_areaApprox_finite_eventually hγ.1 hγ.2
      (MesoModel.FrozenIdentities.lt_lqgQ hγ) D.gff D.bm_B D.bm_B'
      hVb.isCompact_closure] with ω hv hc hf
  exact localDyadicGood_of_vague_continuity_finiteness γ V hVb hδ _ hv hc hf

theorem ae_zero_localDyadicGood
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, LocalDyadicGood γ V δ
      (restrictTo (thickOpen V δ)
        (coneField (X₀ ω) (coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω)))) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ,
    ae_zero_localCircle_continuous_eventually D hγ V hδ,
    ae_cone_areaApprox_finite_eventually hγ.1 hγ.2
      (MesoModel.FrozenIdentities.lqgQ_pos hγ.1) D.gff₀ D.bm_B₀ D.bm_B₀'
      hVb.isCompact_closure] with ω hv hc hf
  exact localDyadicGood_of_vague_continuity_finiteness γ V hVb hδ _ hv hc hf

theorem ae_gamma_localAreaVagueSelection_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelection γ V δ
        (restrictTo (thickOpen V δ)
          (coneField (X ω) (coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω)))) =
      (CellScaling.lqgArea γ (coneField (X ω) (coneRadial γ γ
        (fun t => B t ω) (fun t => B' t ω)))).restrict V := by
  filter_upwards [ae_gamma_localDyadicGood D hγ V hVb hδ,
    ae_gamma_localCircle_continuous_eventually D hγ V hδ,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ]
      with ω hg hc hv
  exact localAreaVagueSelection_eq_lqgArea_of_ae_continuous γ V hδ _ hg hc hv

theorem ae_zero_localAreaVagueSelection_correct
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P,
      localAreaVagueSelection γ V δ
        (restrictTo (thickOpen V δ)
          (coneField (X₀ ω) (coneRadial γ 0
            (fun t => B₀ t ω) (fun t => B₀' t ω)))) =
      (CellScaling.lqgArea γ (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω)))).restrict V := by
  filter_upwards [ae_zero_localDyadicGood D hγ V hVb hδ,
    ae_zero_localCircle_continuous_eventually D hγ V hδ,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ]
      with ω hg hc hv
  exact localAreaVagueSelection_eq_lqgArea_of_ae_continuous γ V hδ _ hg hc hv

end MatedCRTHarmonic.GMS4c

