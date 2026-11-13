import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm

/-!
# Uniform convergence of circle averages against the uniform circle measure

For a measurable function `Y : ℂ → ℝ` continuous on an open set `U`, the averages
`∫ Y dσ_{z,2^{-k}}` of `Y` against the uniform probability measure `σ_{z,r} = circleUnif z r`
on the circle `∂B(z,r)` converge to `Y` uniformly on compact subsets of `U` as `k → ∞`.

This is the uniform-on-compacts convergence of the circle-average process of a continuous
function, stated for the measure-theoretic circle average `∫ · dσ_{z,r}` used for circle
averages of a Gaussian free field.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.LQG

/-- The averages of `Y` over the circles `∂B(z, 2^{-k})` (against the uniform probability
measure `circleUnif z (radius k)`) converge to `Y` uniformly on every compact `K ⊆ U`, when `Y`
is measurable and continuous on the open set `U`. -/
theorem tendstoUniformlyOn_integral_circleUnif_of_continuousOn {Y : ℂ → ℝ} (hYm : Measurable Y)
    {U : Set ℂ} (hU : IsOpen U) (hY : ContinuousOn Y U) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun k z => ∫ x, Y x ∂(QuantumZipper.circleUnif z (QuantumZipper.radius k))) Y atTop K := by
  have h : (fun k z => ∫ x, Y x ∂(QuantumZipper.circleUnif z (QuantumZipper.radius k))) =
      fun k z => Real.circleAverage Y z (QuantumZipper.radius k) := by
    funext k z
    exact QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage hYm z _
  rw [h]
  exact MatedCRTHarmonic.MoTPort.ConeArea3.tendstoUniformlyOn_circleAverage hU hY hK hKU

/-- For a continuous `Y : ℂ → ℝ`, the averages of `Y` over the circles `∂B(z, 2^{-k})` converge
to `Y` uniformly on every compact set. -/
theorem tendstoUniformlyOn_integral_circleUnif {Y : ℂ → ℝ} (hY : Continuous Y) {K : Set ℂ}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun k z => ∫ x, Y x ∂(QuantumZipper.circleUnif z (QuantumZipper.radius k))) Y atTop K :=
  tendstoUniformlyOn_integral_circleUnif_of_continuousOn hY.measurable isOpen_univ
    hY.continuousOn hK (subset_univ K)

end LatticeProb.LQG
