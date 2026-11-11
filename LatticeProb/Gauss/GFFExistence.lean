import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.Prob.ChentsovPiModification
import LatticeProb.Prob.KolmogorovExtension

/-!
# Existence of the whole-plane GFF: named ingredients and the elementary moment bound

Statement target: `exists_isWholePlaneGFF`, the general LP form of the whole-plane GFF existence statement.

Ingredients (labels B1-B4 are used in the statements below):

* B1 (`KolmogorovExtensionStmt`): Kolmogorov extension on an arbitrary index set with the product σ-algebra. Absent
  from pinned Mathlib; discharged below as `kolmogorovExtensionStmt_proved`.
* B2 (`WholePlaneCovPSDStmt`): positive semidefiniteness of the whole-plane covariance on admissible observables.
  Only a sketch exists; a named hypothesis, pending source check.
* B4: the moment bound. Its elementary real-analysis core is `two_log_max_add_sub_log_le` below (proved). The covariance
  identity `Var(h_r(z) - h_s(w)) = -log r - log s + 2 ∫ log max(|x - w|, s) dρ_{z,r}(x)` is not yet formalized.
* B3: continuity. `LatticeProb.exists_continuous_modification_spaceTime_all` (`LatticeProb.Prob.ChentsovPiModification`)
  is proved; the box gluing is not yet formalized.

The named Props below are hypotheses of the statements that use them.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb.Gauss

/-- Kolmogorov extension theorem for an arbitrary index type `ι`, real coordinates, product σ-algebra: a projective
family of probability measures on the finite-dimensional coordinate spaces has a projective limit.
Source: William J. Anderson, *Advanced Probability II Notes*, Theorem 6.0.6, p. 60
(<https://www.math.mcgill.ca/bill/589/589notes.pdf#page=60>).
Absent from pinned Mathlib: `Mathlib/MeasureTheory/Constructions/Projective.lean` has uniqueness only (`IsProjectiveLimit`
is defined there, no existence). -/
def KolmogorovExtensionStmt : Prop :=
  ∀ (ι : Type) (P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ)),
    IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P → (∀ J : Finset ι, IsProbabilityMeasure (P J)) →
      ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ι => ℝ) μ P

/-- B1 is discharged: the Kolmogorov extension for real coordinates on an arbitrary index set is proved in
`LatticeProb.Prob.KolmogorovExtension` (`LatticeProb.exists_isProjectiveLimit_real`, source Anderson,
Advanced Probability II Notes, Thm 6.0.6, p. 60). -/
theorem kolmogorovExtensionStmt_proved : KolmogorovExtensionStmt :=
  fun ι P hP h1 => LatticeProb.exists_isProjectiveLimit_real ι P hP h1

/-- Positive semidefiniteness of the whole-plane covariance on admissible observables: for every finite family of
admissible observables `o_i` and real `c_i`, `∑ c_i c_j wholePlaneGFFCov o_i o_j ≥ 0`.
Sketch (not a written proof): with `σ = ∑ c_i σ_i` (signed smearing measures), `m = σ(ℂ)` and `ν = σ - m ρ` (ρ the uniform
probability on the unit circle), the form equals `-∬ log|x - y| dν dν = (2π)⁻¹ ∫ |∇U|²` with `U = -log|·| * ν`. The limit from smooth regularizations is not written out.
Named hypothesis, pending source check: no consumer is unconditional until it is sourced. -/
def WholePlaneCovPSDStmt : Prop :=
  ∀ (n : ℕ) (o : Fin n → GFFObservable.Admissible) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * wholePlaneGFFCov (o i).1 (o j).1

/-- Elementary bound behind the moment estimate (B4): for `0 < a ≤ r`, `a ≤ s`, `0 ≤ d`,
`2 log (max r s + d) - log r - log s ≤ (|r - s| + 2 d) / a`. -/
theorem two_log_max_add_sub_log_le {a r s d : ℝ} (ha : 0 < a) (har : a ≤ r) (has : a ≤ s) (hd : 0 ≤ d) :
    2 * Real.log (max r s + d) - Real.log r - Real.log s ≤ (|r - s| + 2 * d) / a := by
  have hr0 : 0 < r := lt_of_lt_of_le ha har
  have hs0 : 0 < s := lt_of_lt_of_le ha has
  have hMa : a ≤ max r s := le_max_of_le_left har
  have hM0 : 0 < max r s := lt_of_lt_of_le ha hMa
  -- Step 1: `log (M + d) - log M ≤ d / M ≤ d / a` with `M = max r s`.
  have h1 : Real.log (max r s + d) - Real.log (max r s) ≤ d / a := by
    rw [← Real.log_div (by positivity) hM0.ne']
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (max r s + d) / max r s by positivity)
    have h2 : (max r s + d) / max r s - 1 = d / max r s := by
      field_simp
      ring
    have h3 : d / max r s ≤ d / a := div_le_div_of_nonneg_left hd ha hMa
    linarith
  -- Step 2: `2 log M - log r - log s ≤ |r - s| / a`.
  have h4 : 2 * Real.log (max r s) - Real.log r - Real.log s ≤ |r - s| / a := by
    rcases le_total r s with hrs | hrs
    · have hM : max r s = s := max_eq_right hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < s / r by positivity)
      rw [Real.log_div hs0.ne' hr0.ne'] at hlog
      have h5 : (s / r - 1) = (s - r) / r := by
        field_simp
      have h6 : (s - r) / r ≤ (s - r) / a := div_le_div_of_nonneg_left (by linarith) ha har
      have h7 : |r - s| = s - r := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [h7]
      linarith
    · have hM : max r s = r := max_eq_left hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < r / s by positivity)
      rw [Real.log_div hr0.ne' hs0.ne'] at hlog
      have h5 : (r / s - 1) = (r - s) / s := by
        field_simp
      have h6 : (r - s) / s ≤ (r - s) / a := div_le_div_of_nonneg_left (by linarith) ha has
      have h7 : |r - s| = r - s := abs_of_nonneg (by linarith)
      rw [h7]
      linarith
  -- Combine: `2 log (M + d) - log r - log s = 2 (log (M + d) - log M) + (2 log M - log r - log s)`.
  have h8 : (|r - s| + 2 * d) / a = |r - s| / a + 2 * d / a := by ring
  have h9 : 2 * d / a = 2 * (d / a) := by ring
  linarith

/-! ### Finite-dimensional laws of a centred Gaussian family with a positive semidefinite kernel

Adapted from Mathlib's `ProbabilityTheory.BrownianReal.projectiveFamily` (`Mathlib/Probability/BrownianMotion/
GaussianProjectiveFamily.lean`, Etienne Marion, Apache 2.0 license): the same construction with the covariance
`min s t` replaced by an arbitrary kernel `K` whose finite Gram matrices are positive semidefinite. -/

section KernelFamily

open MeasureTheory ProbabilityTheory NormedSpace Set WithLp

variable {ι : Type} [DecidableEq ι]

/-- The covariance matrix of the kernel `K` on a finite index set `I`. -/
def kernelMatrix (K : ι → ι → ℝ) (I : Finset ι) : Matrix I I ℝ := .of fun s t => K s.1 t.1

/-- The centred Gaussian measure on `I → ℝ` with covariance `K` restricted to `I`. -/
noncomputable def kernelFamily (K : ι → ι → ℝ) (I : Finset ι) : Measure (I → ℝ) :=
  multivariateGaussian 0 (kernelMatrix K I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

lemma measurePreserving_ofLp_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    MeasurePreserving ofLp (multivariateGaussian 0 (kernelMatrix K I)) (kernelFamily K I) where
  measurable := by fun_prop
  map_eq := rfl

instance isProbabilityMeasure_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    IsProbabilityMeasure (kernelFamily K I) := by
  unfold kernelFamily
  infer_instance

instance isGaussian_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) : IsGaussian (kernelFamily K I) := by
  rw [kernelFamily, show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

lemma isProjectiveMeasureFamily_kernelFamily (K : ι → ι → ℝ)
    (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : ι ↦ ℝ) (kernelFamily K) := by
  intro I J hJI
  nth_rw 2 [kernelFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ : ι ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_ofLp_kernelFamily K J).comp
        (measurePreserving_restrict₂_multivariateGaussian (hK I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _
  · fun_prop

lemma covariance_kernelFamily_fun (K : ι → ι → ℝ) (I : Finset ι) (f g : (I → ℝ) → ℝ) :
    cov[f, g; kernelFamily K I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (kernelMatrix K I)] := by
  rw [kernelFamily, covariance_map_equiv]
  rfl

lemma covariance_eval_kernelFamily (K : ι → ι → ℝ) (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef)
    (I : Finset ι) (s t : I) :
    cov[fun x : I → ℝ ↦ x s, fun x : I → ℝ ↦ x t; kernelFamily K I] = K s.1 t.1 := by
  rw [covariance_kernelFamily_fun]
  exact covariance_eval_multivariateGaussian (μ := 0) (hK I) s t

lemma integral_kernelFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ι → ι → ℝ)
    (I : Finset ι) (f : (I → ℝ) → E) :
    ∫ x, f x ∂(kernelFamily K I) = ∫ x, f (ofLp x) ∂(multivariateGaussian 0 (kernelMatrix K I)) := by
  simp [kernelFamily, integral_map_equiv]

lemma integral_id_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) :
    ∫ x, x ∂(kernelFamily K I) = 0 := by
  rw [integral_kernelFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

lemma integral_eval_kernelFamily (K : ι → ι → ℝ) (I : Finset ι) (s : I) :
    ∫ x : I → ℝ, x s ∂(kernelFamily K I) = 0 := by
  have h := integral_id_kernelFamily K I
  have hint : Integrable (fun x : I → ℝ ↦ x) (kernelFamily K I) := IsGaussian.integrable_id
  have := (ContinuousLinearMap.proj s : (I → ℝ) →L[ℝ] ℝ).integral_comp_comm hint
  simpa [h] using this

end KernelFamily

/-! ### A centred Gaussian process with a positive semidefinite kernel, from the Kolmogorov extension (B1)

Given `KolmogorovExtensionStmt` (B1) and positive semidefiniteness of every finite Gram matrix of `K` (B2, as a
hypothesis of the finite-dimensional family), the coordinate process of the projective limit is a centred Gaussian
process with covariance `K`. -/

section KernelProcess

open MeasureTheory ProbabilityTheory

variable {ι : Type} [DecidableEq ι]

/-- Kolmogorov extension (B1) applied to the kernel families: there is a probability measure `μ` on `ι → ℝ` under
which the coordinates form a centred Gaussian process with covariance `K`. -/
theorem exists_gaussian_of_kernel (hB1 : KolmogorovExtensionStmt) (K : ι → ι → ℝ)
    (hK : ∀ I : Finset ι, (kernelMatrix K I).PosSemidef) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧
      IsGaussianProcess (fun (i : ι) (ω : ι → ℝ) ↦ ω i) μ ∧
      (∀ i, ∫ ω, ω i ∂μ = 0) ∧
      ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = K i j := by
  obtain ⟨μ, hμ, hlim⟩ := hB1 ι (kernelFamily K) (isProjectiveMeasureFamily_kernelFamily K hK)
    (fun J ↦ inferInstance)
  refine ⟨μ, hμ, ⟨fun I ↦ ?_⟩, ?_, ?_⟩
  · have hm : Measurable (I.restrict : (ι → ℝ) → (I → ℝ)) := Finset.measurable_restrict _
    exact ⟨hm.aemeasurable, by rw [hlim I]; infer_instance⟩
  · intro i
    have hmeas : Measurable (({i} : Finset ι).restrict : (ι → ℝ) → ({i} : Finset ι) → ℝ) :=
      Finset.measurable_restrict _
    have hi : i ∈ ({i} : Finset ι) := Finset.mem_singleton_self i
    have h := integral_map (μ := μ) hmeas.aemeasurable
      (measurable_pi_apply (⟨i, hi⟩ : ({i} : Finset ι))).aestronglyMeasurable
      (f := fun x : ({i} : Finset ι) → ℝ ↦ x ⟨i, hi⟩)
    rw [hlim {i}, integral_eval_kernelFamily] at h
    exact h.symm
  · intro i j
    have hi : i ∈ ({i, j} : Finset ι) := by simp
    have hj : j ∈ ({i, j} : Finset ι) := by simp
    have hmeas : Measurable (({i, j} : Finset ι).restrict : (ι → ℝ) → ({i, j} : Finset ι) → ℝ) :=
      Finset.measurable_restrict _
    have hcov := covariance_map (μ := μ)
      (X := fun x : ({i, j} : Finset ι) → ℝ ↦ x ⟨i, hi⟩)
      (Y := fun x : ({i, j} : Finset ι) → ℝ ↦ x ⟨j, hj⟩) (Z := ({i, j} : Finset ι).restrict)
      (measurable_pi_apply _).aestronglyMeasurable (measurable_pi_apply _).aestronglyMeasurable
      hmeas.aemeasurable
    rw [hlim {i, j}, covariance_eval_kernelFamily K hK {i, j} ⟨i, hi⟩ ⟨j, hj⟩] at hcov
    exact hcov.symm

end KernelProcess

/-! ### Eighth moments of centred Gaussian increments and the Kolmogorov criterion (B3)

A centred Gaussian variable `D` with variance `v` has `∫ |D|⁸ = v⁴ ∫ |N|⁸` for `N ~ N(0,1)` (scaling of
`gaussianReal`). Applied to the increments `X p - X q` of a centred Gaussian field with variance bounded by a constant
times the distance, this gives the Kolmogorov moment condition with exponents `p = 8`, `q = 4` (`IsKolmogorovProcess`,
Mathlib `Probability/Process/Kolmogorov.lean`), which is the hypothesis of the multiparameter criterion
`LatticeProb.exists_continuous_modification_spaceTime_all` (`d = 2`, `q = 4 > d + 1 = 3`). -/

section GaussianMoments

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- The eighth absolute moment `∫⁻ |x|⁸ dγ` of the standard Gaussian law `γ = N(0,1)` on `ℝ`. -/
noncomputable def gaussAbsMoment8 : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|x| ^ 8) ∂(gaussianReal 0 1)

lemma gaussAbsMoment8_lt_top : gaussAbsMoment8 < ∞ := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 8).integrable_norm_pow (by norm_num)
  unfold gaussAbsMoment8
  refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) h.2
  simp [Real.enorm_eq_ofReal]

/-- Scaling: `∫⁻ |x|⁸ d N(0, v) = v⁴ · ∫⁻ |x|⁸ dγ` for `v : ℝ≥0`. -/
lemma lintegral_abs_pow8_gaussianReal (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ 8) ∂(gaussianReal 0 v) = (v : ℝ≥0∞) ^ 4 * gaussAbsMoment8 := by
  set c : ℝ := Real.sqrt (v : ℝ) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = (v : ℝ) := Real.sq_sqrt v.2
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x : ℝ ↦ c * x) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    simp [hc2]
  have h8 : ENNReal.ofReal (c ^ 8) = (v : ℝ≥0∞) ^ 4 := by
    rw [show c ^ 8 = (c ^ 2) ^ 4 by ring, hc2, ENNReal.ofReal_pow (NNReal.coe_nonneg v),
      ENNReal.ofReal_coe_nnreal]
  rw [hmap, lintegral_map' (f := fun x : ℝ ↦ ENNReal.ofReal (|x| ^ 8)) (by fun_prop) (by fun_prop),
    gaussAbsMoment8, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun x => ?_
  rw [show |c * x| ^ 8 = c ^ 8 * |x| ^ 8 by rw [abs_mul, mul_pow, abs_of_nonneg hc0],
    ENNReal.ofReal_mul (pow_nonneg hc0 8), h8]

/-- Eighth moment of a centred Gaussian variable: `∫⁻ |D|⁸ dP = (Var D)⁴ · ∫⁻ |N|⁸`. -/
lemma lintegral_abs_pow8_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℝ} (hD : HasGaussianLaw D P) (h0 : ∫ ω, D ω ∂P = 0) :
    ∫⁻ ω, ENNReal.ofReal (|D ω| ^ 8) ∂P = ((Var[D; P]).toNNReal : ℝ≥0∞) ^ 4 * gaussAbsMoment8 := by
  have hmeas : AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ 8)) (P.map D) := by fun_prop
  rw [← lintegral_map' hmeas hD.aemeasurable, hD.map_eq_gaussianReal, h0,
    lintegral_abs_pow8_gaussianReal]

/-- The Kolmogorov moment condition (exponents `p = 8`, `q = 4`) for a centred Gaussian field on `ℝ × ℝ²` whose
increments have variance bounded by a constant times the (sup) distance of the indices. -/
theorem isKolmogorovProcess_of_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℝ × (Fin 2 → ℝ) → Ω → ℝ) (hm : ∀ p, Measurable (X p))
    (hcent : ∀ p q, ∫ ω, (X p ω - X q ω) ∂P = 0)
    (hgauss : ∀ p q, HasGaussianLaw (fun ω ↦ X p ω - X q ω) P)
    {C : ℝ} (hC : 0 ≤ C)
    (hvar : ∀ p q, Var[fun ω ↦ X p ω - X q ω; P] ≤ C * dist p q) :
    ∃ M : ℝ≥0, IsKolmogorovProcess X P 8 4 M := by
  refine ⟨(gaussAbsMoment8 * ENNReal.ofReal (C ^ 4)).toNNReal, ?_⟩
  refine ⟨fun s t ↦ by rw [← BorelSpace.measurable_eq]; exact (hm s).prodMk (hm t),
    fun s t ↦ ?_, by norm_num, by norm_num⟩
  have hint : ∀ ω, edist (X s ω) (X t ω) ^ (8 : ℝ) = ENNReal.ofReal (|X s ω - X t ω| ^ 8) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  simp_rw [hint]
  rw [lintegral_abs_pow8_of_hasGaussianLaw (hgauss s t) (hcent s t)]
  have hfin : gaussAbsMoment8 * ENNReal.ofReal (C ^ 4) ≠ ∞ :=
    ENNReal.mul_ne_top gaussAbsMoment8_lt_top.ne ENNReal.ofReal_ne_top
  rw [ENNReal.coe_toNNReal hfin, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg
    (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hv : ((Var[fun ω ↦ X s ω - X t ω; P]).toNNReal : ℝ≥0∞) ≤ ENNReal.ofReal (C * dist s t) :=
    ENNReal.ofReal_le_ofReal (hvar s t)
  calc ((Var[fun ω ↦ X s ω - X t ω; P]).toNNReal : ℝ≥0∞) ^ 4 * gaussAbsMoment8
      ≤ (ENNReal.ofReal (C * dist s t)) ^ 4 * gaussAbsMoment8 := by gcongr
    _ = ENNReal.ofReal ((C * dist s t) ^ 4) * gaussAbsMoment8 := by
      rw [ENNReal.ofReal_pow (mul_nonneg hC dist_nonneg)]
    _ = gaussAbsMoment8 * ENNReal.ofReal (C ^ 4) * ENNReal.ofReal (dist s t ^ 4) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hC 4)]
      ring

end GaussianMoments

/-! ### Localization and gluing: a continuous modification on `(0, ∞) × ℝ²` (B3)

The increments of a circle-average field have variance bounded only on `{r ≥ a}` for each `a > 0`, so the global
Kolmogorov criterion applies to the processes clamped to the boxes `[1/(N+1), N+1] × [-(N+1), N+1]²`, which are
1-Lipschitz images of the parameters. The modifications `Y N` of the clamped processes are glued along the open boxes
`(1/(N+1), N+1) × (-(N+1), N+1)²` (an increasing exhaustion of `(0, ∞) × ℝ²`): on a full-measure set they agree on
every open box, by continuity and a countable dense set, which gives one continuous version on `(0, ∞) × ℝ²`. -/

section Localization

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

/-- The clamp of a real number to `[a, b]`, in the form `max a (min x b)`, is 1-Lipschitz. -/
lemma abs_clamp_sub_clamp_le (a b x y : ℝ) :
    |max a (min x b) - max a (min y b)| ≤ |x - y| := by
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h1 := abs_min_sub_min_le_max x b y b
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h1
  exact h1

/-- The clamp of a parameter to the closed box `[1/(N+1), N+1] × [-(N+1), N+1]²`. -/
noncomputable def clampBox (N : ℕ) (p : ℝ × (Fin 2 → ℝ)) : ℝ × (Fin 2 → ℝ) :=
  (max (1 / ((N : ℝ) + 1)) (min p.1 ((N : ℝ) + 1)),
    fun i ↦ max (-((N : ℝ) + 1)) (min (p.2 i) ((N : ℝ) + 1)))

/-- The open box `(1/(N+1), N+1) × (-(N+1), N+1)²`. -/
def openBox (N : ℕ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | 1 / ((N : ℝ) + 1) < p.1 ∧ p.1 < (N : ℝ) + 1 ∧ ∀ i, |p.2 i| < (N : ℝ) + 1}

lemma isOpen_openBox (N : ℕ) : IsOpen (openBox N) := by
  have h1 : IsOpen {p : ℝ × (Fin 2 → ℝ) | 1 / ((N : ℝ) + 1) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × (Fin 2 → ℝ) | p.1 < (N : ℝ) + 1} :=
    isOpen_lt continuous_fst continuous_const
  have h3 : IsOpen {p : ℝ × (Fin 2 → ℝ) | ∀ i, |p.2 i| < (N : ℝ) + 1} := by
    have : {p : ℝ × (Fin 2 → ℝ) | ∀ i, |p.2 i| < (N : ℝ) + 1} =
        ⋂ i, {p : ℝ × (Fin 2 → ℝ) | |p.2 i| < (N : ℝ) + 1} := by
      ext p
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_lt (continuous_abs.comp ((continuous_apply i).comp continuous_snd)) continuous_const
  have hset : openBox N = {p : ℝ × (Fin 2 → ℝ) | 1 / ((N : ℝ) + 1) < p.1} ∩
      {p : ℝ × (Fin 2 → ℝ) | p.1 < (N : ℝ) + 1} ∩
      {p : ℝ × (Fin 2 → ℝ) | ∀ i, |p.2 i| < (N : ℝ) + 1} := by
    ext p
    simp [openBox, and_assoc]
  rw [hset]
  exact (h1.inter h2).inter h3

lemma openBox_mono {N M : ℕ} (h : N ≤ M) : openBox N ⊆ openBox M := by
  rintro p ⟨h1, h2, h3⟩
  have hN : (N : ℝ) ≤ M := by exact_mod_cast h
  refine ⟨?_, by linarith, fun i ↦ by linarith [h3 i]⟩
  have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  exact lt_of_le_of_lt (one_div_le_one_div_of_le this (by linarith)) h1

lemma clampBox_eq_of_mem {N : ℕ} {p : ℝ × (Fin 2 → ℝ)} (hp : p ∈ openBox N) : clampBox N p = p := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine Prod.ext ?_ ?_
  · show max (1 / ((N : ℝ) + 1)) (min p.1 ((N : ℝ) + 1)) = p.1
    rw [min_eq_left h2.le, max_eq_right h1.le]
  · funext i
    show max (-((N : ℝ) + 1)) (min (p.2 i) ((N : ℝ) + 1)) = p.2 i
    rw [min_eq_left (abs_lt.mp (h3 i)).2.le, max_eq_right (abs_lt.mp (h3 i)).1.le]

lemma dist_clampBox_le (N : ℕ) (p q : ℝ × (Fin 2 → ℝ)) :
    dist (clampBox N p) (clampBox N q) ≤ dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq]
  refine max_le_max ?_ ?_
  · show dist (max (1 / ((N : ℝ) + 1)) (min p.1 ((N : ℝ) + 1)))
        (max (1 / ((N : ℝ) + 1)) (min q.1 ((N : ℝ) + 1))) ≤ dist p.1 q.1
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_clamp_sub_clamp_le _ _ _ _
  · refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
    refine le_trans ?_ (dist_le_pi_dist p.2 q.2 i)
    show dist (max (-((N : ℝ) + 1)) (min (p.2 i) ((N : ℝ) + 1)))
        (max (-((N : ℝ) + 1)) (min (q.2 i) ((N : ℝ) + 1))) ≤ dist (p.2 i) (q.2 i)
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_clamp_sub_clamp_le _ _ _ _

/-- The box index of a parameter with positive radius. -/
noncomputable def boxIdx (p : ℝ × (Fin 2 → ℝ)) : ℕ := ⌊max (1 / p.1) (max p.1 ‖p.2‖)⌋₊

lemma mem_openBox_boxIdx {p : ℝ × (Fin 2 → ℝ)} (hp : 0 < p.1) : p ∈ openBox (boxIdx p) := by
  have hxlt := Nat.lt_floor_add_one (max (1 / p.1) (max p.1 ‖p.2‖))
  have h1 : 1 / p.1 ≤ max (1 / p.1) (max p.1 ‖p.2‖) := le_max_left _ _
  have h2 : p.1 ≤ max (1 / p.1) (max p.1 ‖p.2‖) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : ‖p.2‖ ≤ max (1 / p.1) (max p.1 ‖p.2‖) := (le_max_right _ _).trans (le_max_right _ _)
  unfold boxIdx
  set x := max (1 / p.1) (max p.1 ‖p.2‖) with hx
  refine ⟨?_, by linarith, fun i ↦ ?_⟩
  · have hpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos]
    have := (div_lt_iff₀ hp).1 (lt_of_le_of_lt h1 hxlt)
    linarith [mul_comm p.1 ((⌊x⌋₊ : ℝ) + 1)]
  · rw [← Real.norm_eq_abs]
    linarith [norm_le_pi_norm p.2 i]

/-- The glued process, theorem form (B3): a continuous modification on `{r > 0}` of a centred Gaussian field whose
increment variances are bounded on each `{r ≥ a}` by a constant times the distance. -/
theorem exists_continuousOn_modification_of_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ℝ × (Fin 2 → ℝ) → Ω → ℝ) (hm : ∀ p, Measurable (X p))
    (hcent : ∀ p q, ∫ ω, (X p ω - X q ω) ∂P = 0)
    (hgauss : ∀ p q, HasGaussianLaw (fun ω ↦ X p ω - X q ω) P)
    (hvar : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℝ × (Fin 2 → ℝ), a ≤ p.1 → a ≤ q.1 →
      Var[fun ω ↦ X p ω - X q ω; P] ≤ C * dist p q) :
    ∃ Z : ℝ × (Fin 2 → ℝ) → Ω → ℝ, (∀ p, Measurable (Z p)) ∧
      (∀ p : ℝ × (Fin 2 → ℝ), 0 < p.1 → Z p =ᵐ[P] X p) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun p ↦ Z p ω) {p | 0 < p.1} := by
  -- Step 1: continuous modifications of the clamped processes (global Kolmogorov criterion, `d = 2`, `q = 4`).
  have hclamp : ∀ N : ℕ, ∃ Y : ℝ × (Fin 2 → ℝ) → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, X (clampBox N p) =ᵐ[P] Y p) ∧ ∀ ω, Continuous fun p ↦ Y p ω := by
    intro N
    have ha : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    obtain ⟨C, hC, hvarC⟩ := hvar _ ha
    obtain ⟨M, hK⟩ := isKolmogorovProcess_of_gaussian (fun p ↦ X (clampBox N p))
      (fun p ↦ hm _) (fun p q ↦ hcent _ _) (fun p q ↦ hgauss _ _) hC
      (fun p q ↦ (hvarC _ _ (le_max_left _ _) (le_max_left _ _)).trans
        (mul_le_mul_of_nonneg_left (dist_clampBox_le N p q) hC))
    exact LatticeProb.exists_continuous_modification_spaceTime_all (d := 2) hK (by norm_num)
  choose Y hYm hYae hYc using hclamp
  -- Step 2: a countable dense set and the agreement events on the open boxes.
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ × (Fin 2 → ℝ))
  let K : ℕ → ℕ → Set (ℝ × (Fin 2 → ℝ)) := fun n m => S ∩ openBox (min n m)
  have hKc : ∀ n m, (K n m).Countable := fun n m => hSc.mono inter_subset_left
  let A : ℕ → ℕ → Set Ω := fun n m => {ω | ∀ p ∈ K n m, Y n p ω = Y m p ω}
  have hAm : ∀ n m, MeasurableSet (A n m) := by
    intro n m
    have : A n m = ⋂ p ∈ K n m, {ω | Y n p ω = Y m p ω} := by
      ext ω
      simp [A]
    rw [this]
    exact MeasurableSet.biInter (hKc n m) fun p _ ↦ measurableSet_eq_fun (hYm n p) (hYm m p)
  have hYX : ∀ n p, p ∈ openBox n → Y n p =ᵐ[P] X p := by
    intro n p hp
    have h := hYae n p
    rw [clampBox_eq_of_mem hp] at h
    exact h.symm
  have hAae : ∀ n m, ∀ᵐ ω ∂P, ω ∈ A n m := by
    intro n m
    refine (ae_ball_iff (hKc n m)).2 fun p hp => ?_
    have hpb : p ∈ openBox (min n m) := hp.2
    have h1 : p ∈ openBox n := openBox_mono (min_le_left n m) hpb
    have h2 : p ∈ openBox m := openBox_mono (min_le_right n m) hpb
    exact ((hYX n p h1).trans (hYX m p h2).symm)
  let G : Set Ω := {ω | ∀ n m, ω ∈ A n m}
  have hGm : MeasurableSet G := by
    have hG : G = ⋂ n, ⋂ m, A n m := by
      ext ω
      simp [G]
    rw [hG]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => hAm n m
  have hG_ae : ∀ᵐ ω ∂P, ∀ n m, ω ∈ A n m :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun m => hAae n m
  -- Step 3: on `G`, the modifications agree on every open box.
  have hEq : ∀ ω ∈ G, ∀ n m, EqOn (fun p ↦ Y n p ω) (fun p ↦ Y m p ω) (openBox (min n m)) := by
    intro ω hω n m
    have hωA : ω ∈ A n m := (show ∀ n m, ω ∈ A n m from hω) n m
    refine Set.EqOn.of_subset_closure (s := K n m) (t := openBox (min n m)) ?_
      (hYc n ω).continuousOn (hYc m ω).continuousOn inter_subset_right
      (by
        intro x hx
        have h := hSd.open_subset_closure_inter (isOpen_openBox (min n m)) hx
        rw [Set.inter_comm] at h
        exact h)
    intro p hp
    exact hωA p hp
  -- Step 4: the glued process.
  let Z : ℝ × (Fin 2 → ℝ) → Ω → ℝ := fun p => G.indicator (fun ω ↦ Y (boxIdx p) p ω)
  have key : ∀ ω ∈ G, ∀ n p, p ∈ openBox n → Z p ω = Y n p ω := by
    intro ω hω n p hpn
    have hpos : 0 < p.1 := lt_trans (by positivity) hpn.1
    have hpi : p ∈ openBox (boxIdx p) := mem_openBox_boxIdx hpos
    have hmin : p ∈ openBox (min (boxIdx p) n) := by
      rcases min_choice (boxIdx p) n with h | h <;> rw [h]
      · exact hpi
      · exact hpn
    show G.indicator (fun ω ↦ Y (boxIdx p) p ω) ω = Y n p ω
    rw [Set.indicator_of_mem hω]
    exact hEq ω hω (boxIdx p) n hmin
  refine ⟨Z, fun p ↦ (hYm (boxIdx p) p).indicator hGm, fun p hp ↦ ?_, ?_⟩
  · have hYX' : Y (boxIdx p) p =ᵐ[P] X p := hYX (boxIdx p) p (mem_openBox_boxIdx hp)
    filter_upwards [hG_ae, hYX'] with ω hωG hωY
    show G.indicator (fun ω ↦ Y (boxIdx p) p ω) ω = X p ω
    rw [Set.indicator_of_mem (show ω ∈ G from hωG)]
    exact hωY
  · filter_upwards [hG_ae] with ω hωG
    have hωG' : ω ∈ G := show ω ∈ G from hωG
    intro p0 hp0
    have hmem : p0 ∈ openBox (boxIdx p0) := mem_openBox_boxIdx hp0
    have hev : (fun p ↦ Z p ω) =ᶠ[𝓝 p0] (fun p ↦ Y (boxIdx p0) p ω) := by
      filter_upwards [(isOpen_openBox (boxIdx p0)).mem_nhds hmem] with p hp
      exact key ω hωG' (boxIdx p0) p hp
    exact ((hYc (boxIdx p0) ω).continuousAt.congr hev.symm).continuousWithinAt

end Localization

/-!
### The whole-plane GFF on the admissible observables (general LP form)

Named input: `WholePlaneCovSymmStmt`, the symmetry of the covariance kernel
`wholePlaneGFFCov`. It is needed because `PosSemidef` in Mathlib includes `IsHermitian`.
-/

section WholePlaneGFF

open scoped Classical

open MeasureTheory ProbabilityTheory

/-- Symmetry of the whole-plane covariance on admissible observables (named input). Mathematically it follows from
`wholePlaneCov_comm` and Fubini; the pairing-pairing and circle-circle cases and the
pairing-circle case over the circle measure are not yet formalized in Lean. -/
def WholePlaneCovSymmStmt : Prop :=
  ∀ o o' : GFFObservable.Admissible, wholePlaneGFFCov o.1 o'.1 = wholePlaneGFFCov o'.1 o.1

/-- The covariance kernel on admissible observables (index type of the Gaussian process). -/
noncomputable def admKernel (o o' : GFFObservable.Admissible) : ℝ := wholePlaneGFFCov o.1 o'.1

/-- Finite Gram matrices of the covariance kernel are positive semidefinite (Mathlib sense: Hermitian and
nonnegative quadratic form), from the named inputs `WholePlaneCovPSDStmt` and `WholePlaneCovSymmStmt`. -/
theorem kernelMatrix_posSemidef_of_psd (hB2 : WholePlaneCovPSDStmt) (hsymm : WholePlaneCovSymmStmt)
    (I : Finset GFFObservable.Admissible) : (kernelMatrix admKernel I).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [kernelMatrix, Matrix.of_apply, star_trivial, admKernel, hsymm j.1 i.1]
  · set e := I.equivFin with he
    have hB := hB2 I.card (fun k => (e.symm k).1) (fun k => x (e.symm k))
    have hsum : ∑ k : Fin I.card, ∑ l : Fin I.card, x (e.symm k) * x (e.symm l)
        * wholePlaneGFFCov (e.symm k).1.1 (e.symm l).1.1
        = ∑ i : I, ∑ j : I, x i * x j * admKernel i.1 j.1 :=
      Fintype.sum_equiv e.symm _ _ fun k => Fintype.sum_equiv e.symm _ _ fun l => rfl
    have hq : dotProduct (star x) (Matrix.mulVec (kernelMatrix admKernel I) x) = ∑ i : I, ∑ j : I, x i * x j * admKernel i.1 j.1 := by
      simp only [dotProduct, Matrix.mulVec, kernelMatrix, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hq, ← hsum]
    exact hB

/-- Covariances of a.s. equal random variables agree. -/
lemma covariance_congr_ae' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') : cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- Coordinates of a centre `z ∈ ℂ` in `Fin 2 → ℝ`: the centre component of a parameter `(r, v) ∈ ℝ × (Fin 2 → ℝ)`. -/
noncomputable def coordsOf (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-- The complex centre of a parameter; inverse of `coordsOf`. -/
def cplxOf (v : Fin 2 → ℝ) : ℂ := ⟨v 0, v 1⟩

lemma cplxOf_coordsOf (z : ℂ) : cplxOf (coordsOf z) = z := by
  apply Complex.ext <;> simp [cplxOf, coordsOf]

lemma continuous_coordsOf : Continuous coordsOf := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa [coordsOf] using Complex.continuous_re
  · simpa [coordsOf] using Complex.continuous_im

/-- The circle observable of a parameter point `p = (r, v)`; off `{r > 0}` it is the fixed circle `∂B_1(0)`. -/
noncomputable def ptObs (p : ℝ × (Fin 2 → ℝ)) : GFFObservable :=
  if 0 < p.1 then .circle p.1 (cplxOf p.2) else .circle 1 0

lemma ptObs_isAdmissible (p : ℝ × (Fin 2 → ℝ)) : (ptObs p).IsAdmissible := by
  unfold ptObs
  split_ifs with h
  · exact h
  · exact one_pos

/-- The admissible observable of a parameter point. -/
noncomputable def ptAdm (p : ℝ × (Fin 2 → ℝ)) : GFFObservable.Admissible := ⟨ptObs p, ptObs_isAdmissible p⟩

lemma ptAdm_coords {r : ℝ} (hr : 0 < r) (z : ℂ) : ptAdm (r, coordsOf z) = ⟨.circle r z, hr⟩ := by
  apply Subtype.ext
  simp [ptAdm, ptObs, hr, cplxOf_coordsOf]

/-- The pairing with `φ` read off a point `ω` of the coordinate space (`0` off test functions). -/
noncomputable def pairingField (ω : GFFObservable.Admissible → ℝ) (φ : ℂ → ℝ) : ℝ :=
  if h : IsTestFunction Set.univ φ then ω ⟨.pairing φ, h⟩ else 0

lemma pairingField_apply {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) (ω : GFFObservable.Admissible → ℝ) :
    pairingField ω φ = ω ⟨.pairing φ, hφ⟩ :=
  by simp [pairingField, hφ]

/-- The whole-plane GFF in general LP form, from the Kolmogorov extension (B1, proved), the named PSD input
`WholePlaneCovPSDStmt` (B2), the named symmetry input `WholePlaneCovSymmStmt` (B3sym), and the kernel increment bound
`hvarK` on the circle parameters (discharged for the application kernel outside this file).
Construction: centred Gaussian coordinate process with covariance `admKernel`, continuous modification of the circle
process on `{r > 0}` (`exists_continuousOn_modification_of_gaussian`), and the pairings read off the coordinates. -/
theorem exists_isWholePlaneGFF (hB2 : WholePlaneCovPSDStmt) (hsymm : WholePlaneCovSymmStmt)
    (hvarK : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℝ × (Fin 2 → ℝ), a ≤ p.1 → a ≤ q.1 →
      wholePlaneGFFCov (ptObs p) (ptObs p) + wholePlaneGFFCov (ptObs q) (ptObs q)
        - 2 * wholePlaneGFFCov (ptObs p) (ptObs q) ≤ C * dist p q) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc := by
  obtain ⟨μ, hμ, hgauss, hcent, hcov⟩ :=
    exists_gaussian_of_kernel kolmogorovExtensionStmt_proved admKernel
      (kernelMatrix_posSemidef_of_psd hB2 hsymm)
  have := hμ
  have hint : ∀ o : GFFObservable.Admissible, Integrable (fun ω : GFFObservable.Admissible → ℝ => ω o) μ :=
    fun o => (hgauss.hasGaussianLaw_eval o).integrable
  have hmem : ∀ o : GFFObservable.Admissible, MemLp (fun ω : GFFObservable.Admissible → ℝ => ω o) 2 μ :=
    fun o => (hgauss.hasGaussianLaw_eval o).memLp_two
  have hmeas : ∀ o : GFFObservable.Admissible, Measurable fun ω : GFFObservable.Admissible → ℝ => ω o :=
    fun o => measurable_pi_apply o
  have hvar : ∀ o o' : GFFObservable.Admissible,
      Var[fun ω : GFFObservable.Admissible → ℝ => ω o - ω o'; μ]
        = admKernel o o - 2 * admKernel o o' + admKernel o' o' := by
    intro o o'
    have h := variance_sub (μ := μ) (hmem o) (hmem o')
    rw [← covariance_self (hmeas o).aemeasurable,
      ← covariance_self (hmeas o').aemeasurable, hcov, hcov, hcov] at h
    exact h
  obtain ⟨Z, hZm, hZae, hZcont⟩ := exists_continuousOn_modification_of_gaussian (P := μ)
    (fun (p : ℝ × (Fin 2 → ℝ)) (ω : GFFObservable.Admissible → ℝ) => ω (ptAdm p))
    (fun p => measurable_pi_apply _)
    (fun p q => by
      rw [integral_sub (hint (ptAdm p)) (hint (ptAdm q)), hcent (ptAdm p), hcent (ptAdm q), sub_zero])
    (fun p q => by
      exact hgauss.hasGaussianLaw_fun_sub (s := ptAdm p) (t := ptAdm q))
    (fun a ha => by
      obtain ⟨C, hC0, hCb⟩ := hvarK a ha
      refine ⟨C, hC0, fun p q hp hq => ?_⟩
      rw [hvar (ptAdm p) (ptAdm q)]
      show wholePlaneGFFCov (ptObs p) (ptObs p) - 2 * wholePlaneGFFCov (ptObs p) (ptObs q)
        + wholePlaneGFFCov (ptObs q) (ptObs q) ≤ C * dist p q
      linarith [hCb p q hp hq])
  have hae : ∀ o : GFFObservable.Admissible,
      (fun ω : GFFObservable.Admissible → ℝ =>
        o.1.eval (pairingField ω) (fun r z => Z (r, coordsOf z) ω)) =ᵐ[μ] fun ω => ω o := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ =>
      refine Filter.Eventually.of_forall fun ω => ?_
      exact pairingField_apply ho ω
    | circle r z =>
      have h1 := hZae (r, coordsOf z) ho
      have h2 : ptAdm (r, coordsOf z) = ⟨.circle r z, ho⟩ := ptAdm_coords (r := r) ho z
      beta_reduce at h1
      rw [h2] at h1
      exact h1
  refine ⟨GFFObservable.Admissible → ℝ, inferInstance, μ, hμ, pairingField,
    fun ω r z => Z (r, coordsOf z) ω, ?_⟩
  refine
    { measurable_pairing := fun φ hφ => ?_
      measurable_circle := fun r z _ => hZm _
      isGaussianProcess := hgauss.congr fun o => (hae o).symm
      integral_eq_zero := fun o ho => (integral_congr_ae (hae ⟨o, ho⟩)).trans (hcent _)
      covariance_eq := fun o o' ho ho' =>
        (covariance_congr_ae' (hae ⟨o, ho⟩) (hae ⟨o', ho'⟩)).trans (hcov _ _)
      ae_continuousOn_circle := ?_ }
  · have h : (fun ω : GFFObservable.Admissible → ℝ => pairingField ω φ)
        = fun ω => ω ⟨.pairing φ, hφ⟩ := funext fun ω => pairingField_apply hφ ω
    rw [h]
    exact measurable_pi_apply _
  · filter_upwards [hZcont] with ω hω
    refine hω.comp (continuous_fst.prodMk (continuous_coordsOf.comp continuous_snd)).continuousOn ?_
    intro p hp
    exact hp.1

end WholePlaneGFF

end LatticeProb.Gauss
