import Mathlib
import LatticeProb.Prob.PittStatements
import LatticeProb.Prob.GaussianLaw

/-!
# Pitt's Gaussian association theorem: from the vector statement to Gaussian families

`pitt_associated_of_gaussianProcess` transports `PittFullStmt k` (association for the
multivariate Gaussian `N(0, S)` on `EuclideanSpace ℝ (Fin k)`) to an arbitrary centred Gaussian
family `X : T → Ω → ℝ` with nonnegative covariances, in exactly the vocabulary of the frozen
`Sandpile.External.PittGaussianFKG` with `Space 2` replaced by an arbitrary index set `T`.

The route: the moment matrix `S i j = ∫ X (q i) X (q j) dP` is positive semidefinite with
nonnegative entries; the coordinate process of `N(0, S)` is a centred Gaussian process with the
same covariance; hence both have the same law on `Fin k → ℝ`
(`LatticeProb.gaussian_law_eq_of_covariance`), and the three integrals are rewritten through
that common law.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace LatticeProb

section MomentMatrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The matrix of mixed second moments `S i j = ∫ Z i * Z j dP`. -/
noncomputable def pittMomentMatrix {k : ℕ} (P : Measure Ω) (Z : Fin k → Ω → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ ω, Z i ω * Z j ω ∂P

/-- The moment matrix of finitely many variables with integrable products is positive
semidefinite. -/
theorem pitt_momentMatrix_posSemidef {k : ℕ} (P : Measure Ω) (Z : Fin k → Ω → ℝ)
    (hint : ∀ i j, Integrable (fun ω => Z i ω * Z j ω) P) :
    (pittMomentMatrix P Z).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, pittMomentMatrix, star_trivial]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  · intro x
    have hsq : ∀ ω, (∑ i, x i * Z i ω) ^ 2 = ∑ i, ∑ j, x i * x j * (Z i ω * Z j ω) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hform : star x ⬝ᵥ (pittMomentMatrix P Z *ᵥ x)
        = ∫ ω, (∑ i, x i * Z i ω) ^ 2 ∂P := by
      simp_rw [hsq]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => (hint i j).const_mul (x i * x j)))]
      simp only [dotProduct, Matrix.mulVec, pittMomentMatrix, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul (x i * x j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
    rw [hform]
    exact integral_nonneg fun ω => sq_nonneg _

/-- The moment matrix has nonnegative entries when the pairwise second moments are nonnegative. -/
theorem pitt_momentMatrix_nonneg {k : ℕ} (P : Measure Ω) (Z : Fin k → Ω → ℝ)
    (hnn : ∀ i j, 0 ≤ ∫ ω, Z i ω * Z j ω ∂P) (i j : Fin k) :
    0 ≤ pittMomentMatrix P Z i j :=
  hnn i j

end MomentMatrix

section Coordinates

variable {k : ℕ}

/-- The coordinate family `i ↦ (x ↦ x i)` on `EuclideanSpace ℝ (Fin k)`. -/
abbrev pittCoord (k : ℕ) (i : Fin k) (x : EuclideanSpace ℝ (Fin k)) : ℝ := x i

/-- The coordinates of a Gaussian measure on `EuclideanSpace ℝ (Fin k)` form a Gaussian process. -/
theorem pitt_isGaussianProcess_coord (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsGaussian ν] :
    IsGaussianProcess (pittCoord k) ν where
  hasGaussianLaw I := by
    let L : EuclideanSpace ℝ (Fin k) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi fun i : I => EuclideanSpace.proj i.1
    exact (IsGaussian.hasGaussianLaw_id (μ := ν)).map L

/-- The coordinates are measurable. -/
theorem pitt_measurable_coord (i : Fin k) : Measurable (pittCoord k i) := by
  unfold pittCoord
  fun_prop

/-- The coordinates of the multivariate Gaussian `N(0, S)` are centred. -/
theorem pitt_integral_coord_multivariateGaussian (S : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) :
    ∫ x, pittCoord k i x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) = 0 := by
  have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S))
  simp only [id_eq, integral_id_multivariateGaussian] at h
  simpa using h

/-- The second moments of the coordinates of `N(0, S)` are the entries of `S`. -/
theorem pitt_integral_coord_mul_multivariateGaussian {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosSemidef) (i j : Fin k) :
    ∫ x, pittCoord k i x * pittCoord k j x
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) = S i j := by
  have hG := pitt_isGaussianProcess_coord
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S)
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k))) hS i j
  rw [covariance_eq_sub (hG.hasGaussianLaw_eval i).memLp_two
    (hG.hasGaussianLaw_eval j).memLp_two] at hc
  have h0 := pitt_integral_coord_multivariateGaussian S
  simp only [pittCoord] at h0 hc ⊢
  rw [h0 i, h0 j] at hc
  simpa using hc

end Coordinates

section Main

/-- **Pitt's association theorem for Gaussian families on an arbitrary index set.**  A centred
Gaussian family with nonnegative pairwise covariances is positively associated on every finite
subfamily, in the vocabulary of `Sandpile.Continuum.IsAssociatedField`, given the vector
statement `PittFullStmt k` for every `k`. -/
theorem pitt_associated_of_gaussianProcess (hP : ∀ k, PittFullStmt k) {Ω T : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : T → Ω → ℝ)
    (hG : ProbabilityTheory.IsGaussianProcess X P) (hm : ∀ t, Measurable (X t))
    (hmean : ∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0)
    (hcov : ∀ s t, Integrable (fun ω => X s ω * X t ω) P ∧ 0 ≤ ∫ ω, X s ω * X t ω ∂P)
    (k : ℕ) (q : Fin k → T) (f g : (Fin k → ℝ) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfm : Measurable f) (hgm : Measurable g) (hfb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hgb : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    (∫ ω, f (fun i => X (q i) ω) ∂P) * (∫ ω, g (fun i => X (q i) ω) ∂P)
      ≤ ∫ ω, f (fun i => X (q i) ω) * g (fun i => X (q i) ω) ∂P := by
  -- the restricted family and its moment matrix
  set Z : Fin k → Ω → ℝ := fun i => X (q i) with hZdef
  have hZ : IsGaussianProcess Z P := hG.comp_right q
  set S : Matrix (Fin k) (Fin k) ℝ := pittMomentMatrix P Z with hSdef
  have hS : S.PosSemidef :=
    pitt_momentMatrix_posSemidef P Z fun i j => (hcov (q i) (q j)).1
  have hSnn : ∀ i j, 0 ≤ S i j := fun i j => (hcov (q i) (q j)).2
  -- the Gaussian model and the equality of laws
  set ν : Measure (EuclideanSpace ℝ (Fin k)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S with hνdef
  have hY : IsGaussianProcess (pittCoord k) ν := pitt_isGaussianProcess_coord ν
  have hlaw : P.map (fun ω i => Z i ω) = ν.map (fun x i => pittCoord k i x) :=
    gaussian_law_eq_of_covariance Ω (EuclideanSpace ℝ (Fin k)) P ν Z (pittCoord k) hZ hY
      (fun i => hm (q i)) pitt_measurable_coord (fun i => (hmean (q i)).2)
      (pitt_integral_coord_multivariateGaussian S)
      (fun i j => (pitt_integral_coord_mul_multivariateGaussian hS i j).symm)
  -- transport of the integrals through the common law
  have hΦ : Measurable (fun ω i => Z i ω) := measurable_pi_lambda _ fun i => hm (q i)
  have hΨ : Measurable (fun (x : EuclideanSpace ℝ (Fin k)) i => pittCoord k i x) :=
    measurable_pi_lambda _ pitt_measurable_coord
  have hfg : Measurable (fun y => f y * g y) := hfm.mul hgm
  have key : ∀ h : (Fin k → ℝ) → ℝ, Measurable h →
      ∫ ω, h (fun i => Z i ω) ∂P = ∫ x, h (fun i => pittCoord k i x) ∂ν := by
    intro h hh
    rw [← integral_map hΦ.aemeasurable hh.aestronglyMeasurable, hlaw,
      integral_map hΨ.aemeasurable hh.aestronglyMeasurable]
  -- the vector statement
  have hmono : ∀ {h : (Fin k → ℝ) → ℝ}, Monotone h →
      PittMono (fun x : EuclideanSpace ℝ (Fin k) => h (fun i => pittCoord k i x)) :=
    fun hh x y hxy => hh fun i => hxy i
  have hbdd : ∀ {h : (Fin k → ℝ) → ℝ}, (∃ M : ℝ, ∀ x, |h x| ≤ M) →
      ∃ M : ℝ, ∀ x : EuclideanSpace ℝ (Fin k), |h (fun i => pittCoord k i x)| ≤ M :=
    fun ⟨M, hM⟩ => ⟨M, fun x => hM _⟩
  have hmeas : ∀ {h : (Fin k → ℝ) → ℝ}, Measurable h →
      Measurable (fun x : EuclideanSpace ℝ (Fin k) => h (fun i => pittCoord k i x)) :=
    fun hh => hh.comp hΨ
  have hmain := hP k S hS hSnn (fun x => f (fun i => pittCoord k i x))
    (fun x => g (fun i => pittCoord k i x)) (hmeas hfm) (hmeas hgm) (hbdd hfb) (hbdd hgb)
    (hmono hf) (hmono hg)
  have e1 := key f hfm
  have e2 := key g hgm
  have e3 := key (fun y => f y * g y) hfg
  simp only [hZdef] at e1 e2 e3
  rw [e1, e2, e3]
  exact hmain

end Main

end LatticeProb
