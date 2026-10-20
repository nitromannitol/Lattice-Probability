/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/ConcentrationDZZ.lean.
-/
import LatticeProb.Prob.GaussLipConcentration
import LatticeProb.Prob.GaussPittVector

/-!
# Borell–TIS inequality for finite maxima in Gram form

A centred Gaussian vector `(X₁, …, Xₙ)` is written as `Xᵢ = ⟪vᵢ, Z⟫` with `Z` a standard Gaussian
vector and `vᵢ` vectors of a Euclidean space; the Gram representation of a Gaussian vector is
`LatticeProb.Pitt.exists_gram_map_eq`. In this form the file proves:

* `GaussConc.lipschitzWith_gramVec`: the map `z ↦ (⟪vᵢ, z⟫)ᵢ` is `σ`-Lipschitz into `ℝⁿ` with the
  sup distance when every `‖vᵢ‖ ≤ σ`;
* `GaussConc.lipschitzWith_sup'`: the maximum of the coordinates of a vector of `ℝⁿ` is
  `1`-Lipschitz for the sup distance;
* `GaussConc.borellTIS_finiteMax`: if `‖vᵢ‖ ≤ σ` and `u ≥ 0`, then
  `P(maxᵢ Xᵢ - E maxᵢ Xᵢ ≥ u) ≤ exp (-u² / (2σ²))` for the standard Gaussian measure.

The last bound follows from the Gaussian concentration inequality for Lipschitz functions,
`GaussConc.tail_le_of_lipschitz`, applied to `z ↦ maxᵢ ⟪vᵢ, z⟫`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped RealInnerProductSpace NNReal

namespace LatticeProb.GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The vector `(⟪v i, z⟫)_i`, that is `A z` for the matrix `A` with rows `v i`. -/
def gramVec {n : ℕ} (v : Fin n → E) (z : E) : Fin n → ℝ := fun i => ⟪v i, z⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `z ↦ (⟪v i, z⟫)_i` is `σ`-Lipschitz into `ℝⁿ` with the sup distance when every row has
norm `≤ σ`. -/
lemma lipschitzWith_gramVec {n : ℕ} {v : Fin n → E} {σ : ℝ≥0} (hv : ∀ i, ‖v i‖ ≤ σ) :
    LipschitzWith σ (gramVec v) :=
  LipschitzWith.of_dist_le_mul fun z w => (dist_pi_le_iff (by positivity)).2 fun i => by
    rw [Real.dist_eq, gramVec, gramVec, ← inner_sub_right, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))

/-- The maximum of the coordinates of a vector of `ℝⁿ` is `1`-Lipschitz for the sup distance. -/
lemma lipschitzWith_sup' {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty) :
    LipschitzWith 1 fun x : Fin n → ℝ => Finset.univ.sup' hn x := by
  have key : ∀ x y : Fin n → ℝ, Finset.univ.sup' hn x ≤ Finset.univ.sup' hn y + dist x y := by
    intro x y
    refine Finset.sup'_le _ _ fun i _ => ?_
    have h1 := dist_le_pi_dist x y i
    rw [Real.dist_eq] at h1
    have h2 : y i ≤ Finset.univ.sup' hn y := Finset.le_sup' _ (Finset.mem_univ i)
    linarith [le_abs_self (x i - y i)]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_le_iff]
  constructor
  · linarith [key x y]
  · linarith [key y x, dist_comm x y]

/-- **Borell–TIS inequality for finite maxima**, in Gram form. For `Xᵢ = ⟪vᵢ, Z⟫` with
`‖vᵢ‖ ≤ σ` (so every `Var Xᵢ ≤ σ²`), a standard Gaussian vector `Z` and `u ≥ 0`,
`P(maxᵢ Xᵢ - E maxᵢ Xᵢ ≥ u) ≤ exp (-u² / (2σ²))`. -/
theorem borellTIS_finiteMax {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty)
    (v : Fin n → E) {σ : ℝ≥0} (hv : ∀ i, ‖v i‖ ≤ σ) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {z | u ≤ Finset.univ.sup' hn (gramVec v z) -
        ∫ z', Finset.univ.sup' hn (gramVec v z') ∂(stdGaussian E)} ≤
      exp (-u ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
  have h := ((lipschitzWith_sup' hn).comp (lipschitzWith_gramVec hv))
  rw [one_mul] at h
  exact tail_le_of_lipschitz h hu

namespace GaussBorellFiniteExample

/-- The one-row Gram family `v 0 = e₀` of `EuclideanSpace ℝ (Fin 1)` has `‖v 0‖ = 1`, so
`borellTIS_finiteMax` applies with `σ = 1`. -/
example {u : ℝ} (hu : 0 ≤ u) :=
  borellTIS_finiteMax (E := EuclideanSpace ℝ (Fin 1)) (n := 1) Finset.univ_nonempty
    (fun _ => EuclideanSpace.single 0 1) (σ := 1) (fun _ => by simp) hu

end GaussBorellFiniteExample

end LatticeProb.GaussConc
