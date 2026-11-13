/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleAreaSpatial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ConeCircleSpatial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleKolm
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-! Almost-sure spatial continuity needed by the local GMC selector. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling

theorem ae_cone_localCircle_continuous_eventually
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {γ α : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P) (hαQ : α < lqgQ γ)
    (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ)
          (coneField (X ω) (coneRadial γ α
            (fun t => B t ω) (fun t => B' t ω))))
        (dyadicScale k) w) z := by
  obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  filter_upwards [ae_radialGood hX hB hB' hαQ,
    ae_tendsto_mollAvgS_circleAvg hX] with ω hr hs
  filter_upwards [eventually_ge_atTop K] with k hk
  have hρ : 0 < dyadicScale k := by unfold dyadicScale; positivity
  have hsmall : dyadicScale k < δ := by
    rw [LQGCone.dyadicScale_eq_radius]
    exact hK k hk
  filter_upwards [ae_restrict_of_ae (ae_norm_ne (dyadicScale k)),
    ae_restrict_mem V.isOpen.measurableSet] with z hne hz
  exact continuousAt_localCircleProcess_restrictTo V hρ hsmall _ hz
    (continuousAt_circleAvg_coneField_off_resonance hr hs.2 hρ hne)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

theorem ae_gamma_localCircle_continuous_eventually
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ)
          (MatedCRT.coneField (X ω) (MatedCRT.coneRadial γ γ
            (fun t => B t ω) (fun t => B' t ω))))
        (dyadicScale k) w) z := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact ae_cone_localCircle_continuous_eventually D.gff D.bm_B D.bm_B'
    (MesoModel.FrozenIdentities.lt_lqgQ hγ) V hδ

theorem ae_zero_localCircle_continuous_eventually
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
        (restrictTo (thickOpen V δ)
          (MatedCRT.coneField (X₀ ω) (MatedCRT.coneRadial γ 0
            (fun t => B₀ t ω) (fun t => B₀' t ω))))
        (dyadicScale k) w) z := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact ae_cone_localCircle_continuous_eventually D.gff₀ D.bm_B₀ D.bm_B₀'
    (MesoModel.FrozenIdentities.lqgQ_pos hγ.1) V hδ

end MatedCRTHarmonic.GMS4c

