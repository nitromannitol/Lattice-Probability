/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaApprox
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentVer

/-! A jointly measurable dyadic spatial version of the local GMC approximations. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric

private theorem measurable_dyVer_swapped {α : Type*} [MeasurableSpace α]
    {F : ℂ → α → ℝ} (hF : ∀ z, Measurable (F z)) :
    Measurable fun p : α × ℂ => GMCIdent.dyVer F p.2 p.1 := by
  change Measurable ((fun p : ℂ × α => GMCIdent.dyVer F p.1 p.2) ∘ Prod.swap)
  exact (GMCIdent.measurable_dyVer (m := inferInstance) (F := F) hF).comp measurable_swap

/-- Spatial dyadic regularization makes the locally factored circle process jointly Borel. -/
def localCircleDyVer (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) (ρ : ℝ) (z : ℂ) : ℝ :=
  GMCIdent.dyVer (fun w S => localCircleProcess (thickOpen V δ) S ρ w) z T

theorem measurable_localCircleDyVer (V : TopologicalSpace.Opens ℂ) (δ ρ : ℝ) :
    Measurable fun p : DistOn (thickOpen V δ) × ℂ =>
      localCircleDyVer V δ p.1 ρ p.2 := by
  have hcoord : ∀ w, Measurable fun S : DistOn (thickOpen V δ) =>
      localCircleProcess (thickOpen V δ) S ρ w := fun w =>
    (measurable_pi_apply w).comp
      ((measurable_pi_apply ρ).comp (measurable_localCircleProcess (thickOpen V δ)))
  exact measurable_dyVer_swapped hcoord

/-- The dyadic version agrees with the local circle process at spatial continuity points. -/
theorem localCircleDyVer_eq_of_continuousAt
    (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) (ρ : ℝ) (z : ℂ)
    (hc : ContinuousAt (fun w => localCircleProcess (thickOpen V δ) T ρ w) z) :
    localCircleDyVer V δ T ρ z = localCircleProcess (thickOpen V δ) T ρ z := by
  unfold localCircleDyVer GMCIdent.dyVer
  exact (hc.tendsto.comp (QuantumZipper.RegClosure.tendsto_dyadicRoundC z)).limUnder_eq

/-- A Borel map into measures using the dyadic spatial version of each circle average. -/
def localAreaApproxDy (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) (k : ℕ) : Measure ℂ :=
  (volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (CellScaling.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * localCircleDyVer V δ T (CellScaling.dyadicScale k) z))).restrict V

theorem measurable_localAreaApproxDy (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (δ : ℝ) (k : ℕ) : Measurable fun T : DistOn (thickOpen V δ) =>
      localAreaApproxDy γ V δ T k := by
  unfold localAreaApproxDy
  apply (measurable_measureRestrict V).comp
  apply MeasureTheory.measurable_withDensity
  have hcircle : Measurable fun p : DistOn (thickOpen V δ) × ℂ =>
      localCircleDyVer V δ p.1 (CellScaling.dyadicScale k) p.2 :=
    measurable_localCircleDyVer V δ _
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (hcircle.const_mul γ)).const_mul _)

/-- On samples where the local circle process is spatially continuous almost everywhere on
`V`, the Borel dyadic approximation is the original GMC approximation. -/
theorem localAreaApproxDy_eq_localAreaApprox_of_ae_continuous
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) (k : ℕ)
    (hc : ∀ᵐ z ∂(volume.restrict V),
      ContinuousAt (fun w => localCircleProcess (thickOpen V δ) T
        (CellScaling.dyadicScale k) w) z) :
    localAreaApproxDy γ V δ T k = localAreaApprox γ V δ T k := by
  unfold localAreaApproxDy localAreaApprox
  rw [restrict_withDensity V.isOpen.measurableSet,
    restrict_withDensity V.isOpen.measurableSet]
  refine withDensity_congr_ae ?_
  filter_upwards [hc] with z hz
  rw [localCircleDyVer_eq_of_continuousAt V δ T (CellScaling.dyadicScale k) z hz]

end MatedCRTHarmonic.GMS4c

