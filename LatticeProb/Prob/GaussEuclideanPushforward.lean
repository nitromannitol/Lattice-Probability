import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The standard Gaussian on a Euclidean space in coordinates

The standard Gaussian measure on `EuclideanSpace ℝ (Fin n)` is the image of the product of
`n` standard one-dimensional Gaussians under the map `WithLp.toLp`. This file records the
inverse direction: pushing the standard Gaussian forward along `WithLp.ofLp` gives back that
product measure on `Fin n → ℝ`.
-/

namespace LatticeProb.GaussConc

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian on `EuclideanSpace ℝ (Fin n)`, read in coordinates, is the product
of `n` standard one-dimensional Gaussians. -/
theorem gaussEuclid_map_ofLp (n : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map WithLp.ofLp =
      Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (WithLp.measurable_ofLp (p := 2) (Fin n → ℝ))
      (WithLp.measurable_toLp (p := 2) (Fin n → ℝ))]
  exact Measure.map_id

/-- Nonvacuity: the two-dimensional case of `gaussEuclid_map_ofLp`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 2))).map WithLp.ofLp =
    Measure.pi fun _ : Fin 2 => gaussianReal 0 1 :=
  gaussEuclid_map_ofLp 2

/-- Nonvacuity: in dimension zero the standard Gaussian is the Dirac mass at the origin. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 0))).map WithLp.ofLp = Measure.dirac 0 := by
  rw [gaussEuclid_map_ofLp, Measure.pi_of_empty (fun _ : Fin 0 => gaussianReal 0 1) 0]

/-- Nonvacuity: the coordinate product `y 0 * y 1` has mean zero under the standard Gaussian
on `EuclideanSpace ℝ (Fin 2)`, computed through `gaussEuclid_map_ofLp`. -/
theorem integral_coord_mul_stdGaussian_fin_two :
    ∫ y : EuclideanSpace ℝ (Fin 2), WithLp.ofLp y 0 * WithLp.ofLp y 1
        ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) = 0 := by
  have hm : Measurable fun x : Fin 2 → ℝ => x 0 * x 1 := by fun_prop
  rw [← integral_map (WithLp.measurable_ofLp (p := 2) (Fin 2 → ℝ)).aemeasurable
    hm.aestronglyMeasurable,
    gaussEuclid_map_ofLp]
  have h : ∀ x : Fin 2 → ℝ, x 0 * x 1 = ∏ i, (id : ℝ → ℝ) (x i) := fun x => by
    simp [Fin.prod_univ_two]
  simp_rw [h]
  rw [integral_fin_nat_prod_eq_prod (fun _ : Fin 2 => (id : ℝ → ℝ))]
  simp [integral_id_gaussianReal]

end LatticeProb.GaussConc
