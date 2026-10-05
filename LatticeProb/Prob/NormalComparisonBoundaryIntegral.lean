/-
# Global integrability of the Gaussian density and its first two coordinate partials

Li--Shao normal comparison, route items 3 and 4 (`scratch/pk/normalcompare-route.md`).  The mixed
derivative integration by parts of the boundary integral needs, for the density `p = covDensity S`
of `N(0, S)` on `Fin n → ℝ` and `a x = S⁻¹ *ᵥ x`, the integrability on `Set.Iic b` of

  `∂_i p = -(a x)_i p`  and  `∂_j ∂_i p = ((a x)_i (a x)_j - S⁻¹ i j) p`.

This file proves the *global* integrability on `Fin n → ℝ` (product Lebesgue measure); then
`Integrable.integrableOn` gives every `IntegrableOn _ (Set.Iic b)`.  This is the self-contained
integrability input of the boundary-integral assembly; the marginal factorisation and the
mixed-derivative integration by parts themselves are separate route steps.

Route (probabilistic).
1. `N = multivariateGaussian 0 S` is a Gaussian measure, so the identity lies in `L²(N)`;
   coordinates and finite sums of coordinates (`y ↦ (T *ᵥ y) i`) are then in `L²(N)`, and products
   of two of them are `N`-integrable.
2. Density transfer: `N = volume.withDensity (ofReal ∘ covDensity ∘ ofLp)`, so a function
   `g ∘ ofLp` is `N`-integrable exactly when `covDensity S (ofLp y) * g (ofLp y)` is
   `volume`-integrable on `EuclideanSpace ℝ (Fin n)`.
3. Transport back to `Fin n → ℝ` along the volume-preserving `WithLp.toLp 2`.

No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace LatticeProb

section Moments

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- A coordinate of a centred Gaussian vector `N(0, S)` lies in `L²`. -/
private lemma memLp_two_coord (S : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    MemLp (fun y : EuclideanSpace ℝ (Fin n) => y k) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) := by
  have h := IsGaussian.memLp_id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) 2
    (by simp)
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp' h

/-- A linear form `y ↦ (T *ᵥ y) i` of a centred Gaussian vector `N(0, S)` lies in `L²`. -/
private lemma memLp_two_mulVec (S T : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    MemLp (fun y : EuclideanSpace ℝ (Fin n) => (T *ᵥ WithLp.ofLp y) i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) := by
  have h : (fun y : EuclideanSpace ℝ (Fin n) => (T *ᵥ WithLp.ofLp y) i)
      = fun y => ∑ k, T i k * y k := by
    funext y
    simp [Matrix.mulVec, dotProduct]
  rw [h]
  exact memLp_finsetSum _ fun k _ => (memLp_two_coord S k).const_mul (T i k)

/-- A linear form `y ↦ (T *ᵥ y) i` of a centred Gaussian vector `N(0, S)` is `N`-integrable. -/
private lemma integrable_mulVec (S T : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => (T *ᵥ WithLp.ofLp y) i)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
  (memLp_two_mulVec S T i).integrable (by norm_num)

/-- A product of two linear forms of a centred Gaussian vector `N(0, S)` is `N`-integrable. -/
private lemma integrable_mulVec_mul (S T : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (T *ᵥ WithLp.ofLp y) i * (T *ᵥ WithLp.ofLp y) j)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
  (memLp_two_mulVec S T i).integrable_mul (memLp_two_mulVec S T j)

end Moments

section Transfer

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- The density `covDensity S` is continuous. -/
private lemma continuous_covDensity (S : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (covDensity S) := by
  unfold covDensity
  have h : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (S⁻¹ *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  fun_prop

/-- **Density transfer.**  If `g ∘ ofLp` is integrable for the centred Gaussian `N(0, S)` on
`EuclideanSpace ℝ (Fin n)`, then `covDensity S * g` is Lebesgue integrable on `Fin n → ℝ`. -/
theorem integrable_covDensity_mul (hS : S.PosDef) {g : (Fin n → ℝ) → ℝ}
    (hg : Integrable (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.ofLp y))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S)) :
    Integrable (fun x : Fin n → ℝ => covDensity S x * g x) := by
  have hmeas : Measurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_covDensity S).comp (PiLp.continuous_ofLp 2 _)).measurable
  rw [multivariateGaussian_eq_withDensity_covDensity S hS,
    integrable_withDensity_iff_integrable_smul' hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hg
  simp_rw [ENNReal.toReal_ofReal (covDensity_pos hS _).le, smul_eq_mul] at hg
  have h := ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (g := fun y : EuclideanSpace ℝ (Fin n) =>
      covDensity S (WithLp.ofLp y) * g (WithLp.ofLp y))).mpr hg
  simpa [Function.comp_def] using h

end Transfer

section Targets

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- The Gaussian density `covDensity S` is Lebesgue integrable on `Fin n → ℝ`. -/
theorem integrable_covDensity (hS : S.PosDef) : Integrable (covDensity S) := by
  have h := integrable_covDensity_mul hS (g := fun _ => (1 : ℝ)) (integrable_const _)
  simpa using h

/-- The first coordinate partial `-(S⁻¹ x)_i p` of the Gaussian density is Lebesgue integrable. -/
theorem integrable_partial_covDensity (hS : S.PosDef) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => -((S⁻¹ *ᵥ x) i) * covDensity S x) := by
  have h := integrable_covDensity_mul hS (g := fun x => -((S⁻¹ *ᵥ x) i))
    (integrable_mulVec S S⁻¹ i).neg
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_comm]

/-- The second coordinate partial `((S⁻¹ x)_i (S⁻¹ x)_j - S⁻¹ i j) p` of the Gaussian density is
Lebesgue integrable. -/
theorem integrable_partial2_covDensity (hS : S.PosDef) (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ =>
      (((S⁻¹ *ᵥ x) i) * ((S⁻¹ *ᵥ x) j) - S⁻¹ i j) * covDensity S x) := by
  have h := integrable_covDensity_mul hS
    (g := fun x => ((S⁻¹ *ᵥ x) i) * ((S⁻¹ *ᵥ x) j) - S⁻¹ i j)
    ((integrable_mulVec_mul S S⁻¹ i j).sub (integrable_const _))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_comm]

/-- The Gaussian density `covDensity S` has total mass one. -/
theorem integral_covDensity (hS : S.PosDef) : ∫ x, covDensity S x = 1 := by
  have hmp := PiLp.volume_preserving_toLp (Fin n)
  have hemb := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hmeas : Measurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_covDensity S).comp (PiLp.continuous_ofLp 2 _)).measurable
  have h1 : ∫ x, covDensity S x
      = ∫ y : EuclideanSpace ℝ (Fin n), covDensity S (WithLp.ofLp y) := by
    have := hmp.integral_comp hemb
      (fun y : EuclideanSpace ℝ (Fin n) => covDensity S (WithLp.ofLp y))
    simpa using this
  have h2 : ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (covDensity S (WithLp.ofLp y)) = 1 := by
    have hN : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) Set.univ = 1 := by
      have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
        inferInstance
      exact measure_univ
    rw [multivariateGaussian_eq_withDensity_covDensity S hS, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hN
    exact hN
  rw [h1, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun y => (covDensity_pos hS _).le)
    ((continuous_covDensity S).comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable, h2]
  simp

end Targets

end LatticeProb
