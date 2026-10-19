/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: QuantumZipper/Proofs/Probability/CameronMartin.lean.
-/
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cameron–Martin tilts of centred Gaussian processes

Let `X : I → Ω → ℝ` be a centred Gaussian process (`IsGaussianProcess`, all means zero) with
covariance `K i j = cov[X i, X j; P]`, indexed by an arbitrary type `I`. For a finitely supported
`σ : I →₀ ℝ` put `Xσ = ∑ σ i X i`, `K(j,σ) = ∑ σ i K j i` (`covShift`) and
`K(σ,σ) = ∑ σ j K(j,σ)` (`covNorm`).

* `integral_mul_tiltDensity` : for every measurable `Φ : (I → ℝ) → ℝ` (product σ-algebra),
  `E[Φ(X) exp(Xσ − K(σ,σ)/2)] = E[Φ(X + K(·,σ))]`.
* `map_tiltMeasure_path` : the law of the tilted process equals the law of the shifted process.
* `abs_measureReal_shift_sub_le` : the total-variation bound
  `|law(X + K(·,σ))(A) − law(X)(A)| ≤ (exp K(σ,σ) − 1)^{1/2}` for all measurable `A`
  (an `L²` bound; Pinsker is not used).

Proof: one-dimensional marginals via moment generating functions (`ext_of_complexMGF_id_eq`),
finite-dimensional marginals via `charFunDual`, then the π-system of measurable cylinders.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

namespace LatticeProb.CameronMartin

variable {Ω I : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : I → Ω → ℝ}

/-- Covariance kernel `K i j = cov[X i, X j]`. -/
noncomputable def covK (X : I → Ω → ℝ) (P : Measure Ω) (i j : I) : ℝ := cov[X i, X j; P]

/-- `Xσ = ∑ σ i X i`. -/
noncomputable def comb (X : I → Ω → ℝ) (σ : I →₀ ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ σ.support, σ i * X i ω

/-- `K(j,σ) = ∑ σ i K j i`. -/
noncomputable def covShift (X : I → Ω → ℝ) (P : Measure Ω) (σ : I →₀ ℝ) (j : I) : ℝ :=
  ∑ i ∈ σ.support, σ i * covK X P j i

/-- `K(σ,σ) = ∑ σ j K(j,σ)`. -/
noncomputable def covNorm (X : I → Ω → ℝ) (P : Measure Ω) (σ : I →₀ ℝ) : ℝ :=
  ∑ j ∈ σ.support, σ j * covShift X P σ j

/-- The Cameron–Martin density `exp(Xσ − K(σ,σ)/2)`. -/
noncomputable def tiltDensity (X : I → Ω → ℝ) (P : Measure Ω) (σ : I →₀ ℝ) (ω : Ω) : ℝ :=
  Real.exp (comb X σ ω - covNorm X P σ / 2)

/-- The tilted measure `exp(Xσ − K(σ,σ)/2) · P`. -/
noncomputable def tiltMeasure (X : I → Ω → ℝ) (P : Measure Ω) (σ : I →₀ ℝ) : Measure Ω :=
  P.withDensity fun ω ↦ ((tiltDensity X P σ ω).toNNReal : ℝ≥0∞)

section Lemmas

variable (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i))
  (hcent : ∀ i, P[X i] = 0)
include hX

/-- A finite linear combination of the coordinates of a Gaussian process is Gaussian. -/
lemma hasGaussianLaw_finsetComb (T : Finset I) (a : I → ℝ) :
    HasGaussianLaw (fun ω ↦ ∑ i ∈ T, a i * X i ω) P := by
  have h := (hX.hasGaussianLaw T).map_fun
    (∑ i : T, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T ↦ ℝ) i)
  have heq : (fun ω ↦ ∑ i ∈ T, a i * X i ω) =
      fun ω ↦ (∑ i : T, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T ↦ ℝ) i)
        (T.restrict (X · ω)) := by
    funext ω
    rw [sum_apply]
    simp only [smul_apply, ContinuousLinearMap.proj_apply, Finset.restrict,
      smul_eq_mul]
    exact (Finset.sum_coe_sort T (fun i ↦ a i * X i ω)).symm
  rw [heq]; exact h

/-- A finite linear combination of the coordinates of a Gaussian process is in `L²`. -/
lemma memLp_two_finsetComb (T : Finset I) (a : I → ℝ) :
    MemLp (fun ω ↦ ∑ i ∈ T, a i * X i ω) 2 P :=
  (hasGaussianLaw_finsetComb hX T a).memLp_two

include hcent in
/-- A finite linear combination of a centred Gaussian process is centred. -/
lemma integral_finsetComb (T : Finset I) (a : I → ℝ) :
    P[fun ω ↦ ∑ i ∈ T, a i * X i ω] = 0 := by
  rw [integral_finsetSum _ fun i _ ↦ ((hX.hasGaussianLaw_eval i).integrable).const_mul (a i)]
  simp [integral_const_mul, hcent]

/-- The covariance of two finite linear combinations of a Gaussian process, written in the
covariance kernel `covK`. -/
lemma covariance_finsetComb (A B : Finset I) (a b : I → ℝ) :
    cov[fun ω ↦ ∑ j ∈ A, a j * X j ω, fun ω ↦ ∑ i ∈ B, b i * X i ω; P] =
      ∑ j ∈ A, a j * ∑ i ∈ B, b i * covK X P j i := by
  haveI := hX.isProbabilityMeasure
  rw [covariance_fun_sum_left' (X := fun j ω ↦ a j * X j ω)
    (fun j _ ↦ (hX.hasGaussianLaw_eval j).memLp_two.const_mul (a j))
    (memLp_two_finsetComb hX B b)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [covariance_const_mul_left, covariance_fun_sum_right' (X := fun i ω ↦ b i * X i ω)
    (fun i _ ↦ (hX.hasGaussianLaw_eval i).memLp_two.const_mul (b i))
    (hX.hasGaussianLaw_eval j).memLp_two]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [covariance_const_mul_right]; rfl

/-- For a centered Gaussian `Z`, `E exp Z = exp(Var Z / 2)` and `exp Z` is integrable. -/
lemma gauss_exp {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) (hm : P[Z] = 0) :
    Integrable (fun ω ↦ Real.exp (Z ω)) P ∧ ∫ ω, Real.exp (Z ω) ∂P = Real.exp (Var[Z; P] / 2) := by
  haveI := hX.isProbabilityMeasure
  have hlaw : P.map Z = gaussianReal 0 Var[Z; P].toNNReal := by
    rw [hZ.map_eq_gaussianReal, hm]
  have hm1 := mgf_gaussianReal hlaw 1
  have hv : (Var[Z; P].toNNReal : ℝ) = Var[Z; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  constructor
  · have : 0 < mgf Z P 1 := by rw [hm1]; positivity
    simpa using (mgf_pos_iff.mp this)
  · have : mgf Z P 1 = ∫ ω, Real.exp (Z ω) ∂P := by simp [mgf]
    rw [← this, hm1, hv]; ring_nf

omit mΩ hX in
/-- The combination `comb X σ` may be summed over any finite set containing the support of `σ`. -/
lemma comb_eq_sum_subset {J : Finset I} (σ : I →₀ ℝ) (hσ : σ.support ⊆ J) (ω : Ω) :
    comb X σ ω = ∑ i ∈ J, σ i * X i ω := by
  unfold comb
  refine Finset.sum_subset hσ fun i _ hi ↦ ?_
  rw [Finsupp.notMem_support_iff.mp hi, zero_mul]

/-- The variance of `Xσ` is `K(σ,σ)`. -/
lemma variance_comb (σ : I →₀ ℝ) : Var[comb X σ; P] = covNorm X P σ := by
  have hZ := hasGaussianLaw_finsetComb hX σ.support σ
  change Var[(fun ω ↦ ∑ i ∈ σ.support, σ i * X i ω); P] = _
  rw [← covariance_self hZ.aemeasurable]
  exact covariance_finsetComb hX _ _ _ _

include hcent in
/-- The Cameron–Martin density is integrable and has mean one. -/
lemma tiltDensity_integral (σ : I →₀ ℝ) :
    Integrable (tiltDensity X P σ) P ∧ ∫ ω, tiltDensity X P σ ω ∂P = 1 := by
  obtain ⟨hi, he⟩ := gauss_exp hX (hasGaussianLaw_finsetComb hX σ.support σ)
    (integral_finsetComb hX hcent _ _)
  have hv := variance_comb hX σ
  unfold comb at hv
  refine ⟨?_, ?_⟩
  · have : tiltDensity X P σ = fun ω ↦ Real.exp (comb X σ ω) / Real.exp (covNorm X P σ / 2) := by
      funext ω; simp [tiltDensity, Real.exp_sub]
    rw [this]; exact hi.div_const _
  · simp only [tiltDensity, Real.exp_sub]
    rw [integral_div]
    unfold comb
    rw [he, hv, div_self (Real.exp_pos _).ne']

include hcent in
/-- The tilted measure is a probability measure. -/
lemma isProbabilityMeasure_tiltMeasure (σ : I →₀ ℝ) :
    IsProbabilityMeasure (tiltMeasure X P σ) := by
  obtain ⟨hi, he⟩ := tiltDensity_integral hX hcent σ
  constructor
  rw [tiltMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have : (fun ω ↦ ((tiltDensity X P σ ω).toNNReal : ℝ≥0∞)) =
      fun ω ↦ ENNReal.ofReal (tiltDensity X P σ ω) := rfl
  rw [this, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le), he, ENNReal.ofReal_one]

include hmeas in
omit hX in
/-- The Cameron–Martin density is measurable. -/
lemma measurable_tiltDensity (σ : I →₀ ℝ) : Measurable (tiltDensity X P σ) := by
  unfold tiltDensity comb
  fun_prop

include hmeas in
omit hX in
/-- Integration against the tilted measure is integration against the density. -/
lemma integral_tiltMeasure (σ : I →₀ ℝ) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(tiltMeasure X P σ) = ∫ ω, tiltDensity X P σ ω * g ω ∂P := by
  rw [tiltMeasure, integral_withDensity_eq_integral_smul
    (measurable_tiltDensity hmeas σ).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal (tiltDensity X P σ ω) (Real.exp_pos _).le]

include hmeas hcent in
/-- One-dimensional Cameron–Martin: for `Y = ∑_{j ∈ J} c j X j` with `σ.support ⊆ J`, the law of
`Y` under the tilted measure is the law of `Y + ∑ c j K(j,σ)` under `P`. -/
lemma map_tiltMeasure_finsetComb (σ : I →₀ ℝ) (J : Finset I) (hσ : σ.support ⊆ J) (c : I → ℝ) :
    (tiltMeasure X P σ).map (fun ω ↦ ∑ j ∈ J, c j * X j ω) =
      P.map (fun ω ↦ (∑ j ∈ J, c j * X j ω) + ∑ j ∈ J, c j * covShift X P σ j) := by
  haveI := hX.isProbabilityMeasure
  haveI := isProbabilityMeasure_tiltMeasure hX hcent σ
  set Y : Ω → ℝ := fun ω ↦ ∑ j ∈ J, c j * X j ω with hYdef
  set m : ℝ := ∑ j ∈ J, c j * covShift X P σ j with hmdef
  set w : ℝ≥0 := Var[Y; P].toNNReal with hwdef
  have hYm : Measurable Y := by rw [hYdef]; fun_prop
  have hYG : HasGaussianLaw Y P := hasGaussianLaw_finsetComb hX J c
  have hY0 : P[Y] = 0 := integral_finsetComb hX hcent J c
  have hwv : (w : ℝ) = Var[Y; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  -- right-hand side is `gaussianReal m w`
  have hR : P.map (fun ω ↦ Y ω + m) = gaussianReal m w := by
    have : (fun ω ↦ Y ω + m) = (· + m) ∘ Y := rfl
    rw [this, ← Measure.map_map (measurable_add_const m) hYm, hYG.map_eq_gaussianReal, hY0,
      gaussianReal_map_add_const, zero_add]
  rw [hR]
  -- the covariance computations
  have hcovYσ : cov[Y, comb X σ; P] = m := by
    unfold comb
    rw [hYdef, covariance_finsetComb hX]; rfl
  have hvσ := variance_comb hX σ
  -- mgf of `Y` under the tilted measure
  have hmgf : mgf id (gaussianReal m w) = mgf id ((tiltMeasure X P σ).map Y) := by
    funext t
    rw [mgf_id_map hYm.aemeasurable]
    have h1 : mgf id (gaussianReal m w) t = Real.exp (m * t + w * t ^ 2 / 2) :=
      congrFun (mgf_fun_id_gaussianReal (μ := m) (v := w)) t
    rw [h1, mgf, integral_tiltMeasure hmeas σ]
    -- the exponent `t Y + Xσ` is a centered Gaussian combination
    set Z : Ω → ℝ := fun ω ↦ ∑ j ∈ J, (t * c j + σ j) * X j ω with hZdef
    have hZ : ∀ ω, t * Y ω + comb X σ ω = Z ω := by
      intro ω
      rw [comb_eq_sum_subset σ hσ, hYdef, hZdef]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    obtain ⟨-, hZe⟩ := gauss_exp hX (hasGaussianLaw_finsetComb hX J
      (fun j ↦ t * c j + σ j)) (integral_finsetComb hX hcent J _)
    have hVZ : Var[Z; P] = t ^ 2 * Var[Y; P] + 2 * t * m + covNorm X P σ := by
      have hZfun : Z = (fun ω ↦ t * Y ω) + comb X σ := by
        funext ω; rw [Pi.add_apply, hZ ω]
      have hYL := memLp_two_finsetComb hX J c
      have hσL : MemLp (comb X σ) 2 P := memLp_two_finsetComb hX σ.support σ
      rw [hZfun, variance_add (hYL.const_mul t) hσL, variance_const_mul, covariance_const_mul_left,
        hcovYσ, hvσ]
      ring
    rw [show (fun ω ↦ tiltDensity X P σ ω * Real.exp (t * Y ω)) =
        fun ω ↦ Real.exp (Z ω) / Real.exp (covNorm X P σ / 2) by
      funext ω
      simp only [tiltDensity, ← hZ ω, Real.exp_sub, div_mul_eq_mul_div, ← Real.exp_add]
      congr 2; ring]
    rw [integral_div, hZe, hVZ, hwv, ← Real.exp_sub]
    congr 1; ring
  have hc := eqOn_complexMGF_of_mgf hmgf
  refine Measure.ext_of_complexMGF_id_eq (funext fun z ↦ hc ?_) |>.symm
  simp [integrableExpSet_id_gaussianReal]

open Classical in
omit mΩ hX in
/-- Expansion of a continuous linear functional on `J → ℝ` in coordinates. -/
lemma strongDual_restrict_eq_sum (J J' : Finset I) (hJ : J ⊆ J')
    (L : StrongDual ℝ (J → ℝ)) (x : I → ℝ) :
    L (J.restrict x) = ∑ j ∈ J', (if h : j ∈ J then L (fun k ↦ if (⟨j, h⟩ : J) = k then 1 else 0)
      else 0) * x j := by
  classical
  rw [show L (J.restrict x) = (L : (J → ℝ) →ₗ[ℝ] ℝ) (J.restrict x) from rfl,
    LinearMap.pi_apply_eq_sum_univ]
  rw [← Finset.sum_subset hJ (fun j _ hj ↦ by simp [hj])]
  rw [← Finset.sum_coe_sort J]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Finset.restrict, smul_eq_mul, dif_pos j.2]
  rw [mul_comm]; rfl

open Classical in
include hmeas hcent in
/-- Finite-dimensional marginals of the tilted process are those of the shifted process. -/
theorem map_tiltMeasure_restrict (σ : I →₀ ℝ) (J : Finset I) :
    (tiltMeasure X P σ).map (fun ω ↦ J.restrict (fun j ↦ X j ω)) =
      P.map (fun ω ↦ J.restrict (fun j ↦ X j ω + covShift X P σ j)) := by
  haveI := hX.isProbabilityMeasure
  haveI := isProbabilityMeasure_tiltMeasure hX hcent σ
  have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
    measurable_pi_iff.mpr fun j ↦ hmeas j
  have hV' : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω + covShift X P σ j) :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  haveI : IsProbabilityMeasure ((tiltMeasure X P σ).map fun ω ↦ J.restrict (fun j ↦ X j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (P.map fun ω ↦ J.restrict (fun j ↦ X j ω + covShift X P σ j)) :=
    (Measure.isProbabilityMeasure_map_iff hV'.aemeasurable).mpr inferInstance
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  set J' := J ∪ σ.support
  set c : I → ℝ := fun j ↦
    if h : j ∈ J then L (fun k ↦ if (⟨j, h⟩ : J) = k then 1 else 0) else 0 with hc
  have hJ : J ⊆ J' := Finset.subset_union_left
  have hσ : σ.support ⊆ J' := Finset.subset_union_right
  have key := map_tiltMeasure_finsetComb hX hmeas hcent σ J' hσ c
  have hcont : Continuous fun y : ℝ ↦ cexp (y * Complex.I) := by fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hV.aemeasurable (by fun_prop),
    integral_map hV'.aemeasurable (by fun_prop)]
  have h1 : ∀ ω, L (J.restrict (fun j ↦ X j ω)) = ∑ j ∈ J', c j * X j ω := fun ω ↦
    strongDual_restrict_eq_sum J J' hJ L _
  have h2 : ∀ ω, L (J.restrict (fun j ↦ X j ω + covShift X P σ j)) =
      (∑ j ∈ J', c j * X j ω) + ∑ j ∈ J', c j * covShift X P σ j := fun ω ↦ by
    rw [strongDual_restrict_eq_sum J J' hJ L _, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [h1, h2]
  have hYm : Measurable fun ω ↦ ∑ j ∈ J', c j * X j ω := by fun_prop
  have hYm' : Measurable fun ω ↦ (∑ j ∈ J', c j * X j ω) + ∑ j ∈ J', c j * covShift X P σ j := by
    fun_prop
  rw [← integral_map (f := fun y : ℝ ↦ cexp (y * Complex.I)) hYm.aemeasurable
      hcont.aestronglyMeasurable, key,
    integral_map hYm'.aemeasurable hcont.aestronglyMeasurable]

include hmeas hcent in
/-- **Cameron–Martin (law form).** The law of the tilted process equals the law of the process
shifted by `K(·,σ)`, as measures on `I → ℝ` with the product σ-algebra. -/
theorem map_tiltMeasure_path (σ : I →₀ ℝ) :
    (tiltMeasure X P σ).map (fun ω j ↦ X j ω) =
      P.map (fun ω j ↦ X j ω + covShift X P σ j) := by
  haveI := hX.isProbabilityMeasure
  haveI := isProbabilityMeasure_tiltMeasure hX hcent σ
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hp' : Measurable fun ω j ↦ X j ω + covShift X P σ j :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  haveI : IsProbabilityMeasure ((tiltMeasure X P σ).map fun ω j ↦ X j ω) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (P.map fun ω j ↦ X j ω + covShift X P σ j) :=
    (Measure.isProbabilityMeasure_map_iff hp'.aemeasurable).mpr inferInstance
  refine ext_of_generate_finite (measurableCylinders fun _ : I ↦ ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs ↦ ?_)
    (by simp [measure_univ])
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [Measure.map_apply hp hS.cylinder, Measure.map_apply hp' hS.cylinder]
  have := congrArg (fun μ : Measure (J → ℝ) ↦ μ S) (map_tiltMeasure_restrict hX hmeas hcent σ J)
  have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
    measurable_pi_iff.mpr fun j ↦ hmeas j
  have hV' : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω + covShift X P σ j) :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  beta_reduce at this
  rwa [Measure.map_apply hV hS, Measure.map_apply hV' hS] at this

include hmeas hcent in
/-- **Cameron–Martin.** For every measurable `Φ` of the path,
`E[Φ(X) exp(Xσ − K(σ,σ)/2)] = E[Φ(X + K(·,σ))]`. -/
theorem integral_mul_tiltDensity (σ : I →₀ ℝ) (Φ : (I → ℝ) → ℝ) (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun j ↦ X j ω) * tiltDensity X P σ ω ∂P =
      ∫ ω, Φ (fun j ↦ X j ω + covShift X P σ j) ∂P := by
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hp' : Measurable fun ω j ↦ X j ω + covShift X P σ j :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  rw [← integral_map hp'.aemeasurable hΦ.aestronglyMeasurable,
    ← map_tiltMeasure_path hX hmeas hcent σ, integral_map hp.aemeasurable hΦ.aestronglyMeasurable,
    integral_tiltMeasure hmeas σ]
  simp_rw [mul_comm]

include hcent in
/-- The second moment of the Cameron–Martin density is `exp K(σ,σ)`. -/
lemma integral_tiltDensity_sq (σ : I →₀ ℝ) :
    Integrable (fun ω ↦ tiltDensity X P σ ω ^ 2) P ∧
      ∫ ω, tiltDensity X P σ ω ^ 2 ∂P = Real.exp (covNorm X P σ) := by
  obtain ⟨hi, he⟩ := gauss_exp hX (hasGaussianLaw_finsetComb hX σ.support (fun i ↦ 2 * σ i))
    (integral_finsetComb hX hcent _ _)
  have hv : Var[fun ω ↦ ∑ i ∈ σ.support, 2 * σ i * X i ω; P] = 4 * covNorm X P σ := by
    rw [← covariance_self (hasGaussianLaw_finsetComb hX σ.support _).aemeasurable,
      covariance_finsetComb hX, covNorm]
    unfold covShift
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  have hsq : (fun ω ↦ tiltDensity X P σ ω ^ 2) =
      fun ω ↦ Real.exp (∑ i ∈ σ.support, 2 * σ i * X i ω) / Real.exp (covNorm X P σ) := by
    funext ω
    rw [tiltDensity, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    simp only [comb, Nat.cast_ofNat]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · ring
  rw [hsq]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div, he, hv, ← Real.exp_sub]
  congr 1; ring

include hmeas hcent in
/-- **Cameron–Martin, total-variation corollary (L² form).** For every measurable set `A` of
paths, `|P(X + K(·,σ) ∈ A) − P(X ∈ A)| ≤ (exp K(σ,σ) − 1)^{1/2}`. -/
theorem abs_measureReal_shift_sub_le (σ : I →₀ ℝ) (A : Set (I → ℝ)) (hA : MeasurableSet A) :
    |(P.map fun ω j ↦ X j ω + covShift X P σ j).real A - (P.map fun ω j ↦ X j ω).real A| ≤
      Real.sqrt (Real.exp (covNorm X P σ) - 1) := by
  haveI := hX.isProbabilityMeasure
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  set D := tiltDensity X P σ with hDdef
  set g : Ω → ℝ := fun ω ↦ A.indicator 1 (fun j ↦ X j ω) with hgdef
  have hΦ : Measurable (A.indicator (1 : (I → ℝ) → ℝ)) := measurable_const.indicator hA
  have hgm : Measurable g := hΦ.comp hp
  have hDm : Measurable D := measurable_tiltDensity hmeas σ
  obtain ⟨hDi, hD1⟩ := tiltDensity_integral hX hcent σ
  obtain ⟨hD2i, hD2⟩ := integral_tiltDensity_sq hX hcent σ
  have hg01 : ∀ ω, g ω = 0 ∨ g ω = 1 := fun ω ↦ by
    by_cases h : (fun j ↦ X j ω) ∈ A <;> simp [hgdef, h]
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω ↦ by rcases hg01 ω with h | h <;> simp [h]
  have hgi : Integrable g P :=
    (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have hmain := integral_mul_tiltDensity hX hmeas hcent σ _ hΦ
  have e1 : (P.map fun ω j ↦ X j ω + covShift X P σ j).real A = ∫ ω, g ω * D ω ∂P := by
    rw [← integral_indicator_one hA, integral_map
      (measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _).aemeasurable
      hΦ.aestronglyMeasurable, ← hmain]
  have e2 : (P.map fun ω j ↦ X j ω).real A = ∫ ω, g ω ∂P := by
    rw [← integral_indicator_one hA, integral_map hp.aemeasurable hΦ.aestronglyMeasurable]
  have hgD : Integrable (fun ω ↦ g ω * D ω) P :=
    hDi.bdd_mul hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  -- `D - 1 ∈ L²`
  have hDL : MemLp D 2 P := (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr hD2i
  have hD1L : MemLp (fun ω ↦ D ω - 1) 2 P := hDL.sub (memLp_const 1)
  set h : Ω → ℝ := fun ω ↦ g ω * (D ω - 1) with hhdef
  have hhL : MemLp h 2 P := by
    refine hD1L.of_le (hgm.mul (hDm.sub measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rcases hg01 ω with hg | hg <;> simp [hhdef, hg]
  have ediff : (P.map fun ω j ↦ X j ω + covShift X P σ j).real A -
      (P.map fun ω j ↦ X j ω).real A = ∫ ω, h ω ∂P := by
    rw [e1, e2, ← integral_sub hgD hgi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp [hhdef]; ring)
  rw [ediff]
  apply Real.abs_le_sqrt
  -- `(∫ h)² ≤ ∫ h² ≤ ∫ (D-1)² = Var D = e^v - 1`
  have hvar := variance_eq_sub hhL
  have hle1 : (∫ ω, h ω ∂P) ^ 2 ≤ ∫ ω, h ω ^ 2 ∂P := by
    have := variance_nonneg h P
    rw [hvar] at this
    simp only [Pi.pow_apply] at this
    linarith
  have hle2 : ∫ ω, h ω ^ 2 ∂P ≤ ∫ ω, (D ω - 1) ^ 2 ∂P := by
    refine integral_mono hhL.integrable_sq hD1L.integrable_sq fun ω ↦ ?_
    rcases hg01 ω with hg | hg <;> simp [hhdef, hg, sq_nonneg]
  have hVD : ∫ ω, (D ω - 1) ^ 2 ∂P = Real.exp (covNorm X P σ) - 1 := by
    have hv := variance_eq_integral hDm.aemeasurable (μ := P)
    rw [hD1] at hv
    rw [← hv, variance_eq_sub hDL]
    simp only [Pi.pow_apply]
    rw [hD2, hD1]; ring
  linarith

end Lemmas

/-! ### Nonvacuity

A concrete centred Gaussian process: one standard Gaussian coordinate, indexed by `Unit`, on
`Ω = ℝ` with `P = gaussianReal 0 1` and `X () = id`. The coefficient vector `σ = δ_()` is nonzero.
-/

namespace CameronMartinExample

/-- The standard Gaussian coordinate: `X () = id`, indexed by the one-point set `Unit`. -/
noncomputable abbrev stdX : Unit → ℝ → ℝ := fun _ ↦ id

/-- The standard Gaussian law on `ℝ`. -/
noncomputable abbrev stdP : Measure ℝ := gaussianReal 0 1

/-- The nonzero finitely supported coefficient vector `σ = δ_()` with value `1`. -/
noncomputable abbrev stdσ : Unit →₀ ℝ := Finsupp.single () 1

/-- The coefficient vector `stdσ` is nonzero. -/
theorem stdσ_ne_zero : stdσ ≠ 0 :=
  Finsupp.single_ne_zero.mpr one_ne_zero

/-- Every finite restriction of the standard coordinate is Gaussian. -/
lemma hasGaussianLaw_std_restrict (J : Finset Unit) :
    HasGaussianLaw (fun ω : ℝ ↦ J.restrict (fun _ : Unit ↦ ω)) (gaussianReal 0 1) := by
  have heq : (fun ω : ℝ ↦ J.restrict (fun _ : Unit ↦ ω)) =
      fun ω ↦ (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        (fun _ : J ↦ (1 : ℝ))) (id ω) := by
    funext ω
    ext k
    simp [Finset.restrict]
  rw [heq]
  exact (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (fun _ : J ↦ (1 : ℝ)))

/-- The standard Gaussian coordinate is a Gaussian process. -/
theorem isGaussianProcess_std : IsGaussianProcess stdX stdP :=
  ⟨fun J ↦ hasGaussianLaw_std_restrict J⟩

/-- The standard Gaussian coordinate is measurable. -/
theorem measurable_std : ∀ i : Unit, Measurable (stdX i) :=
  fun _ ↦ measurable_id

/-- The standard Gaussian coordinate is centred. -/
theorem centred_std : ∀ i : Unit, ∫ x, stdX i x ∂stdP = 0 :=
  fun _ ↦ integral_id_gaussianReal

/-- Nonvacuity: the Cameron–Martin tilt of the standard coordinate by `stdσ` is a probability
measure. -/
theorem isProbabilityMeasure_tiltMeasure_std : IsProbabilityMeasure (tiltMeasure stdX stdP stdσ) :=
  isProbabilityMeasure_tiltMeasure isGaussianProcess_std centred_std stdσ

/-- Nonvacuity: the law of the tilted path equals the law of the shifted path. -/
theorem map_tiltMeasure_path_std :
    (tiltMeasure stdX stdP stdσ).map (fun ω j ↦ stdX j ω) =
      stdP.map (fun ω j ↦ stdX j ω + covShift stdX stdP stdσ j) :=
  map_tiltMeasure_path isGaussianProcess_std measurable_std centred_std stdσ

/-- Nonvacuity: the total-variation bound between the shifted and unshifted path laws. -/
theorem abs_measureReal_shift_sub_le_std (A : Set (Unit → ℝ)) (hA : MeasurableSet A) :
    |(stdP.map fun ω j ↦ stdX j ω + covShift stdX stdP stdσ j).real A -
        (stdP.map fun ω j ↦ stdX j ω).real A| ≤
      Real.sqrt (Real.exp (covNorm stdX stdP stdσ) - 1) :=
  abs_measureReal_shift_sub_le isGaussianProcess_std measurable_std centred_std stdσ A hA

end CameronMartinExample

end LatticeProb.CameronMartin
