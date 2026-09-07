/-
The density of the standard Gaussian on a Euclidean space.

Mathlib defines the standard Gaussian on a finite-dimensional inner product
space as the pushforward of a product of one-dimensional Gaussians along an
orthonormal basis, and proves no density for it.  The density is the product of
the one-dimensional densities, because the pushforward is along a volume
preserving map.
-/
import Mathlib
import LatticeProb.Prob.PiDensity

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

/-- Pushing a density forward along a measure preserving equivalence. -/
theorem map_withDensity_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = ν.withDensity fun y => g (e.symm y) := by
  ext T hT
  rw [Measure.map_apply e.measurable hT, withDensity_apply _ (e.measurable hT),
    withDensity_apply _ hT, ← lintegral_indicator (e.measurable hT), ← lintegral_indicator hT]
  have key : ∫⁻ a, T.indicator (fun y => g (e.symm y)) (e a) ∂μ
      = ∫⁻ b, T.indicator (fun y => g (e.symm y)) b ∂ν :=
    he.lintegral_comp ((hg.comp e.symm.measurable).indicator hT)
  rw [← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : e x ∈ T
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ e ⁻¹' T from hx)]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ e ⁻¹' T from hx)]

/-- **The standard Gaussian on a Euclidean space has the product density.** -/
theorem stdGaussian_euclidean_eq_withDensity (ι : Type*) [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι)
      = (volume : Measure (EuclideanSpace ℝ ι)).withDensity
          fun y => ∏ i, gaussianPDF 0 1 (y i) := by
  classical
  have hmeas : Measurable fun x : ι → ℝ => ∏ i, gaussianPDF 0 1 (x i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hfun : (fun x : ι → ℝ => ∑ i, x i • (EuclideanSpace.basisFun ι ℝ) i)
      = ⇑(MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    funext x
    ext j
    simp [Pi.single_apply, mul_ite]
  have hmp : MeasurePreserving ⇑(MeasurableEquiv.toLp 2 (ι → ℝ))
      (volume : Measure (ι → ℝ)) (volume : Measure (EuclideanSpace ℝ ι)) :=
    PiLp.volume_preserving_toLp ι
  rw [stdGaussian_eq_map_pi_orthonormalBasis (EuclideanSpace.basisFun ι ℝ), hfun,
    pi_gaussianReal_eq_withDensity,
    map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) hmp hmeas]
  rfl

end LatticeProb

end
