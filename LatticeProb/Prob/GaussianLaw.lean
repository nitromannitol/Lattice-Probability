/-
Determination of centred Gaussian process laws by covariance.
-/
import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The mean of a finite Euclidean random vector vanishes when each coordinate mean vanishes. -/
theorem LatticeProb.integral_piLp_eq_zero {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℝ}
    (hint : Integrable (fun ω => WithLp.toLp 2 (X · ω)) P)
    (hm : ∀ i, ∫ ω, X i ω ∂P = 0) :
    ∫ ω, WithLp.toLp 2 (X · ω) ∂P = (0 : EuclideanSpace ℝ ι) := by
  ext i
  have h := (EuclideanSpace.proj i).integral_comp_comm hint
  exact h.symm.trans (hm i)


/-- Centred finite vectors with equal mixed second moments have equal covariance forms. -/
theorem LatticeProb.covarianceBilin_pi_eq_of_integral_mul_eq
    {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ i, MemLp (Y i) 2 Q)
    (hmX : ∀ i, ∫ ω, X i ω ∂P = 0) (hmY : ∀ i, ∫ ω, Y i ω ∂Q = 0)
    (hcov : ∀ i j, ∫ ω, X i ω * X j ω ∂P = ∫ ω, Y i ω * Y j ω ∂Q) :
    covarianceBilin (P.map (fun ω => WithLp.toLp 2 (X · ω))) =
      covarianceBilin (Q.map (fun ω => WithLp.toLp 2 (Y · ω))) := by
  ext x y
  rw [covarianceBilin_apply_pi hX, covarianceBilin_apply_pi hY]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_eq_sub (hX i) (hX j), covariance_eq_sub (hY i) (hY j)]
  simp only [hmX, hmY, zero_mul, sub_zero, Pi.mul_apply]
  rw [hcov]


/-- A finite restriction of a Gaussian process has a Gaussian Euclidean law. -/
theorem LatticeProb.hasGaussianLaw_toLp_restrict {T Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : T → Ω → ℝ}
    (hX : IsGaussianProcess X P) (I : Finset T) :
    HasGaussianLaw (fun ω => (WithLp.toLp 2 (I.restrict (X · ω)) : EuclideanSpace ℝ I)) P := by
  exact (hX.hasGaussianLaw I).map (EuclideanSpace.equiv I ℝ).symm.toContinuousLinearMap


/-- Measurable processes on different probability spaces have equal laws when all finite restrictions do. -/
theorem MeasureTheory.Measure.ext_of_map_restrict_eq
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : T → Ω → ℝ} {Y : T → Ω' → ℝ} (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (h : ∀ I : Finset T, P.map (fun ω => I.restrict (X · ω))
      = Q.map (fun ω => I.restrict (Y · ω))) :
    P.map (fun ω u => X u ω) = Q.map (fun ω u => Y u ω) := by
  have hX' := ProbabilityTheory.isProjectiveLimit_map (P := P) (measurable_pi_lambda _ hmX).aemeasurable
  simp_rw [h] at hX'
  exact hX'.unique (ProbabilityTheory.isProjectiveLimit_map (P := Q) (measurable_pi_lambda _ hmY).aemeasurable)


/-- Centred Gaussian processes with equal covariance have the same finite-dimensional distributions. -/
theorem ProbabilityTheory.IsGaussianProcess.map_restrict_eq
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hmean : ∀ t, ∫ ω, X t ω ∂P = 0) (hmean' : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hcov : ∀ s t, ∫ ω, X s ω * X t ω ∂P = ∫ ω, Y s ω * Y t ω ∂Q)
    (I : Finset T) :
    P.map (fun ω => I.restrict (X · ω)) = Q.map (fun ω => I.restrict (Y · ω)) := by
  haveI := hX.isProbabilityMeasure
  haveI := hY.isProbabilityMeasure
  have hgX := LatticeProb.hasGaussianLaw_toLp_restrict hX I
  have hgY := LatticeProb.hasGaussianLaw_toLp_restrict hY I
  haveI := hgX.isGaussian_map
  haveI := hgY.isGaussian_map
  apply MeasurableEquiv.map_measurableEquiv_injective (MeasurableEquiv.toLp 2 (I → ℝ))
  rw [Measure.map_map (μ := P) (g := MeasurableEquiv.toLp 2 (I → ℝ))
      (f := fun ω => I.restrict (X · ω)) (by fun_prop) (by fun_prop),
    Measure.map_map (μ := Q) (g := MeasurableEquiv.toLp 2 (I → ℝ))
      (f := fun ω => I.restrict (Y · ω)) (by fun_prop) (by fun_prop)]
  change P.map (fun ω => (WithLp.toLp 2 (I.restrict (X · ω)) : EuclideanSpace ℝ I)) =
    Q.map (fun ω => (WithLp.toLp 2 (I.restrict (Y · ω)) : EuclideanSpace ℝ I))
  apply IsGaussian.ext
  · rw [integral_map hgX.aemeasurable aestronglyMeasurable_id,
      integral_map hgY.aemeasurable aestronglyMeasurable_id]
    exact (LatticeProb.integral_piLp_eq_zero hgX.integrable (fun i : I => hmean i)).trans
      (LatticeProb.integral_piLp_eq_zero hgY.integrable (fun i : I => hmean' i)).symm
  · exact LatticeProb.covarianceBilin_pi_eq_of_integral_mul_eq
      (fun i : I => (hX.hasGaussianLaw_eval i).memLp_two)
      (fun i : I => (hY.hasGaussianLaw_eval i).memLp_two)
      (fun i : I => hmean i) (fun i : I => hmean' i) (fun i j : I => hcov i j)


/-- Centred Gaussian processes with equal covariance have equal laws on the product sigma-algebra. -/
theorem LatticeProb.gaussianProcess_map_eq_of_covariance
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hmean : ∀ t, ∫ ω, X t ω ∂P = 0) (hmean' : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hcov : ∀ s t, ∫ ω, X s ω * X t ω ∂P = ∫ ω, Y s ω * Y t ω ∂Q)
    : P.map (fun ω u => X u ω) = Q.map (fun ω u => Y u ω) := by
  haveI := hX.isProbabilityMeasure
  haveI := hY.isProbabilityMeasure
  exact MeasureTheory.Measure.ext_of_map_restrict_eq hmX hmY
    (fun I => hX.map_restrict_eq hY hmX hmY hmean hmean' hcov I)


/-- **The law of a centred Gaussian family is determined by its covariance, across two
probability spaces.**  Two centred Gaussian families indexed by the same set, one on `Ω` and
one on `Ω'`, whose covariances agree, induce the same measure on the product `ι → ℝ`.  This is
`LatticeProb.gaussianProcess_map_eq_of_covariance` with the two spaces, their measures and the
two families made explicit; the index set is arbitrary, so applying it to a product index such
as `Space × Fin k` gives the joint law of finitely many fields at once. -/
theorem LatticeProb.gaussian_law_eq_of_covariance
    {ι : Type*} (Ω Ω' : Type*) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : ProbabilityTheory.IsGaussianProcess X P)
    (hY : ProbabilityTheory.IsGaussianProcess Y P')
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hcov : ∀ i j, ∫ ω, X i ω * X j ω ∂P = ∫ ω, Y i ω * Y j ω ∂P') :
    Measure.map (fun ω => fun i => X i ω) P = Measure.map (fun ω => fun i => Y i ω) P' :=
  LatticeProb.gaussianProcess_map_eq_of_covariance hX hY hXm hYm hXmean hYmean hcov

/-- The same equality for the joint law of a finite subfamily, in the form the consumer of a
finite collection of fields uses: the law of the vector `(X i)_{i ∈ I}` on `Ω` equals the law of
`(Y i)_{i ∈ I}` on `Ω'`. -/
theorem LatticeProb.gaussian_finite_law_eq_of_covariance
    {ι : Type*} (Ω Ω' : Type*) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : ProbabilityTheory.IsGaussianProcess X P)
    (hY : ProbabilityTheory.IsGaussianProcess Y P')
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i))
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P' = 0)
    (hcov : ∀ i j, ∫ ω, X i ω * X j ω ∂P = ∫ ω, Y i ω * Y j ω ∂P')
    (I : Finset ι) :
    Measure.map (fun ω => I.restrict (X · ω)) P = Measure.map (fun ω => I.restrict (Y · ω)) P' :=
  hX.map_restrict_eq hY hXm hYm hXmean hYmean hcov I
