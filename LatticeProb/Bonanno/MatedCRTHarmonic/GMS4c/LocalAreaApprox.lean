/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalAreaApprox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs

/-! Locality of each sufficiently fine circle-average GMC approximation. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.MatedCRT

def thickOpen (V : TopologicalSpace.Opens ℂ) (δ : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨thickening δ (V : Set ℂ), isOpen_thickening⟩

/-- The dyadic GMC density on `V`, read from field data on its `δ`-thickening. -/
def localAreaApprox (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) (k : ℕ) : Measure ℂ :=
  (volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (CellScaling.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * localCircleProcess (thickOpen V δ) T (CellScaling.dyadicScale k) z))).restrict V

/-- The local circle is admissible whenever its center lies in `V` and its radius is below `δ`. -/
theorem closedBall_subset_thickOpen {V : TopologicalSpace.Opens ℂ} {δ ρ : ℝ}
    (hρ : ρ < δ) {z : ℂ} (hz : z ∈ V) :
    closedBall z ρ ⊆ (thickOpen V δ : Set ℂ) := by
  intro w hw
  rw [mem_closedBall] at hw
  exact mem_thickening_iff.2 ⟨z, hz, hw.trans_lt hρ⟩

/-- For fine dyadic scales, the local approximation equals the actual area approximation on `V`. -/
theorem localAreaApprox_restrictTo (γ : ℝ) (V : TopologicalSpace.Opens ℂ)
    (δ : ℝ) (h : DistC) (k : ℕ) (hk : CellScaling.dyadicScale k < δ) :
    localAreaApprox γ V δ (restrictTo (thickOpen V δ) h) k =
      (CellScaling.lqgAreaApprox γ h k).restrict V := by
  unfold localAreaApprox CellScaling.lqgAreaApprox
  rw [restrict_withDensity V.isOpen.measurableSet,
    restrict_withDensity V.isOpen.measurableSet]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with z hz
  have hpos : 0 < CellScaling.dyadicScale k := by
    unfold CellScaling.dyadicScale
    positivity
  have hball := closedBall_subset_thickOpen hk hz
  have heq := congrFun (congrFun
    (localCircleProcess_restrictTo (thickOpen V δ) h) (CellScaling.dyadicScale k)) z
  have heq' : localCircleProcess (thickOpen V δ)
      (restrictTo (thickOpen V δ) h) (CellScaling.dyadicScale k) z =
        circleAvg h (CellScaling.dyadicScale k) z := by
    simpa [restrictCircles, hpos, hball] using heq
  rw [heq']

end MatedCRTHarmonic.GMS4c

