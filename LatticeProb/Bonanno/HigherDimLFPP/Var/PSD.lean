/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.PSD at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import LatticeProb.Bonanno.GaussianLQG.Probability.Gaussian

/-!
# Positive semidefiniteness of the covariance (1.5)

`gCov f g = π ∫₀¹ (‖f‖ + ‖g‖ - ‖f - g‖)` is positive semidefinite on every finite family of
interval-integrable profiles `ℝ → E`, for any finite-dimensional real inner product space `E`
(HA1 D2.2–D2.4).  Without this, `multivariateGaussian` silently falls back to a Dirac mass.

* `kernelR_sum_nonneg` (HA1 D2.2): the scalar kernel `(a, b) ↦ |a| + |b| - |a - b|` is PSD.  This
  re-proves publicly the private `kernel_sum_nonneg` of `LQGDimension/Section2/ZCovPSD.lean`
  (ramp indicators `1_{(0,a)}`, `1_{(a,0)}`), from which the code is copied.
* `normKernel_sum_nonneg` (HA1 D2.3, Gaussian projection): with `γ ∼ stdGaussian E` and
  `c₀ = E|N(0,1)| > 0`, `E|⟪v, γ⟫| = c₀ ‖v‖`, hence
  `c₀ (‖a‖ + ‖b‖ - ‖a - b‖) = E[|⟪a,γ⟫| + |⟪b,γ⟫| - |⟪a,γ⟫ - ⟪b,γ⟫|]`, and the scalar case applies
  pointwise in `γ`.  This is the Lean form of the paper's sphere identity `∫|θ·v| dσ = b_m |v|`.
* `gCov_psdOn` (HA1 D2.4): integrate the pointwise statement over `x ∈ [0,1]`.  The structure of
  the integration step is copied from `LQGDimension.zCovPSD` (`zCov_psdOn_aux`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace Matrix

namespace HigherDimLFPP.Var

/-! ## The scalar kernel (copied from `LQGDimension/Section2/ZCovPSD.lean`) -/

/-- `1` on `(0, a)` (empty if `a ≤ 0`). -/
def posRamp (a : ℝ) : ℝ → ℝ := (Set.Ioo (0 : ℝ) a).indicator 1

/-- `1` on `(a, 0)` (empty if `a ≥ 0`). -/
def negRamp (a : ℝ) : ℝ → ℝ := (Set.Ioo a (0 : ℝ)).indicator 1

lemma posRamp_mul_posRamp (a b : ℝ) :
    (fun y => posRamp a y * posRamp b y) = (Set.Ioo (0 : ℝ) (min a b)).indicator 1 := by
  have h : (Set.Ioo (0:ℝ) a).indicator (1:ℝ→ℝ) * (Set.Ioo (0:ℝ) b).indicator (1:ℝ→ℝ)
      = (Set.Ioo (0:ℝ) (min a b)).indicator (1:ℝ→ℝ) := by
    rw [← Set.inter_indicator_one, Set.Ioo_inter_Ioo]; norm_num
  funext y
  simpa [posRamp] using congrFun h y

lemma negRamp_mul_negRamp (a b : ℝ) :
    (fun y => negRamp a y * negRamp b y) = (Set.Ioo (max a b) (0 : ℝ)).indicator 1 := by
  have h : (Set.Ioo a (0:ℝ)).indicator (1:ℝ→ℝ) * (Set.Ioo b (0:ℝ)).indicator (1:ℝ→ℝ)
      = (Set.Ioo (max a b) (0:ℝ)).indicator (1:ℝ→ℝ) := by
    rw [← Set.inter_indicator_one, Set.Ioo_inter_Ioo]; norm_num
  funext y
  simpa [negRamp] using congrFun h y

lemma posRamp_integrable (a b : ℝ) :
    Integrable (fun y => posRamp a y * posRamp b y) volume := by
  rw [posRamp_mul_posRamp]
  refine (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const ?_)
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

lemma negRamp_integrable (a b : ℝ) :
    Integrable (fun y => negRamp a y * negRamp b y) volume := by
  rw [negRamp_mul_negRamp]
  refine (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const ?_)
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

lemma posRamp_integral (a b : ℝ) :
    ∫ y, posRamp a y * posRamp b y ∂volume = max (min a b) 0 := by
  rw [posRamp_mul_posRamp, MeasureTheory.integral_indicator_one measurableSet_Ioo]
  show (volume (Set.Ioo (0:ℝ) (min a b))).toReal = max (min a b) 0
  rcases le_total (min a b) 0 with h | h
  · rw [Set.Ioo_eq_empty (not_lt.mpr h)]
    simp [max_eq_right h]
  · rw [Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal h, max_eq_left h]

lemma negRamp_integral (a b : ℝ) :
    ∫ y, negRamp a y * negRamp b y ∂volume = max (min (-a) (-b)) 0 := by
  rw [negRamp_mul_negRamp, MeasureTheory.integral_indicator_one measurableSet_Ioo, min_neg_neg]
  show (volume (Set.Ioo (max a b) (0:ℝ))).toReal = max (-(max a b)) 0
  rcases le_total 0 (max a b) with h | h
  · rw [Set.Ioo_eq_empty (not_lt.mpr h)]
    simp [max_eq_right (by linarith : -(max a b) ≤ (0:ℝ))]
  · rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 0 - max a b), zero_sub,
      max_eq_left (by linarith : (0:ℝ) ≤ -(max a b))]

/-- For a finite family of kernels `∫ ρᵢ ρⱼ`, the quadratic form is `∫ (∑ᵢ cᵢ ρᵢ)² ≥ 0`. -/
lemma sum_ramp_sq_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρ : ι → ℝ → ℝ)
    (hInt : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun y => ρ i y * ρ j y) volume) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume) := by
  have step1 : ∀ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume)
      = ∫ y, ∑ j ∈ s, c i * c j * (ρ i y * ρ j y) ∂volume := by
    intro i hi
    simp_rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.integral_finsetSum s fun j hj =>
      (hInt i hi j hj).const_mul (c i * c j)).symm
  have hfun : (fun y => ∑ i ∈ s, ∑ j ∈ s, c i * c j * (ρ i y * ρ j y))
      = fun y => (∑ i ∈ s, c i * ρ i y) * (∑ i ∈ s, c i * ρ i y) := by
    funext y
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, ρ i y * ρ j y ∂volume)
      = ∫ y, (∑ i ∈ s, c i * ρ i y) * (∑ i ∈ s, c i * ρ i y) ∂volume := by
    rw [Finset.sum_congr rfl step1,
        ← MeasureTheory.integral_finsetSum s fun i hi =>
          MeasureTheory.integrable_finsetSum s fun j hj => (hInt i hi j hj).const_mul (c i * c j),
        hfun]
  rw [key]
  exact MeasureTheory.integral_nonneg fun y => mul_self_nonneg _

lemma kernelR_eq (x y : ℝ) :
    |x| + |y| - |x - y| = 2 * max (min x y) 0 + 2 * max (min (-x) (-y)) 0 := by
  rcases abs_cases x with ⟨hxe, hxs⟩ | ⟨hxe, hxs⟩ <;>
    rcases abs_cases y with ⟨hye, hys⟩ | ⟨hye, hys⟩ <;>
    rcases abs_cases (x - y) with ⟨hxye, hxys⟩ | ⟨hxye, hxys⟩ <;>
    rw [hxe, hye, hxye] <;>
    simp only [min_def, max_def] <;>
    split_ifs <;>
    linarith

/-- **Scalar kernel PSD** (HA1 D2.2): `(a, b) ↦ |a| + |b| - |a - b|` is positive semidefinite on
every finite family of reals. -/
theorem kernelR_sum_nonneg {ι : Type*} (s : Finset ι) (a c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (|a i| + |a j| - |a i - a j|) := by
  have hpos := sum_ramp_sq_nonneg s c (fun i => posRamp (a i))
    (fun i _ j _ => posRamp_integrable (a i) (a j))
  have hneg := sum_ramp_sq_nonneg s c (fun i => negRamp (a i))
    (fun i _ j _ => negRamp_integrable (a i) (a j))
  have heq : ∑ i ∈ s, ∑ j ∈ s, c i * c j * (|a i| + |a j| - |a i - a j|)
      = 2 * (∑ i ∈ s, ∑ j ∈ s, c i * c j * (∫ y, posRamp (a i) y * posRamp (a j) y ∂volume))
        + 2 * (∑ i ∈ s, ∑ j ∈ s, c i * c j *
          (∫ y, negRamp (a i) y * negRamp (a j) y ∂volume)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [posRamp_integral, negRamp_integral, kernelR_eq]
    ring
  rw [heq]
  linarith

/-! ## The Euclidean kernel, by Gaussian projection (HA1 D2.3) -/

/-- `c₀ = E|N(0,1)|`. -/
def gaussAbsMean : ℝ := ∫ y, |y| ∂(gaussianReal 0 1)

lemma gaussAbsMean_pos : 0 < gaussAbsMean := by
  have hint : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 ENNReal.one_ne_top).integrable le_rfl).abs
  unfold gaussAbsMean
  rw [integral_pos_iff_support_of_nonneg (fun y => abs_nonneg y) hint]
  have hsupp : Function.support (fun y : ℝ => |y|) = {0}ᶜ := by
    ext y; simp
  rw [hsupp]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_singleton,
    measure_univ]
  simp

section Euclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `E|⟪v, γ⟫| = c₀ ‖v‖` for `γ ∼ stdGaussian E`. -/
lemma integral_abs_inner_stdGaussian [MeasurableSpace E] [BorelSpace E] (v : E) :
    ∫ x, |⟪v, x⟫| ∂(stdGaussian E) = gaussAbsMean * ‖v‖ := by
  have h := GaussianLQG.integral_abs_rpow_of_hasLaw_gaussianReal
    (LQGDimension.GaussianMax.hasLaw_inner v) 1
  simp only [Real.rpow_one] at h
  rw [h, mul_comm, gaussAbsMean]
  congr 1
  rw [Real.coe_toNNReal _ (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

lemma integrable_abs_inner_stdGaussian [MeasurableSpace E] [BorelSpace E] (v : E) :
    Integrable (fun x => |⟪v, x⟫|) (stdGaussian E) :=
  (IsGaussian.integrable_id.const_inner v).abs

/-- **Euclidean kernel PSD** (HA1 D2.3): `(a, b) ↦ ‖a‖ + ‖b‖ - ‖a - b‖` is positive semidefinite on
every finite family of vectors of a finite-dimensional real inner product space. -/
theorem normKernel_sum_nonneg {ι : Type*} (s : Finset ι) (a : ι → E) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * (‖a i‖ + ‖a j‖ - ‖a i - a j‖) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hI := integrable_abs_inner_stdGaussian (E := E)
  have hIpair : ∀ i j, Integrable (fun x => c i * c j *
      (|⟪a i, x⟫| + |⟪a j, x⟫| - |⟪a i, x⟫ - ⟪a j, x⟫|)) (stdGaussian E) := by
    intro i j
    have e : (fun x => |⟪a i, x⟫ - ⟪a j, x⟫|) = fun x => |⟪a i - a j, x⟫| := by
      funext x; rw [inner_sub_left]
    refine Integrable.const_mul ?_ _
    refine ((hI (a i)).add (hI (a j))).sub ?_
    rw [e]; exact hI (a i - a j)
  have hpair : ∀ i j, ∫ x, c i * c j * (|⟪a i, x⟫| + |⟪a j, x⟫| - |⟪a i, x⟫ - ⟪a j, x⟫|)
      ∂(stdGaussian E) = gaussAbsMean * (c i * c j * (‖a i‖ + ‖a j‖ - ‖a i - a j‖)) := by
    intro i j
    have e : ∀ x : E, |⟪a i, x⟫ - ⟪a j, x⟫| = |⟪a i - a j, x⟫| := fun x => by
      rw [inner_sub_left]
    simp_rw [e]
    have hIij : Integrable (fun x => |⟪a i, x⟫| + |⟪a j, x⟫|) (stdGaussian E) :=
      (hI (a i)).add (hI (a j))
    rw [integral_const_mul, integral_sub hIij (hI (a i - a j)),
      integral_add (hI (a i)) (hI (a j)), integral_abs_inner_stdGaussian,
      integral_abs_inner_stdGaussian, integral_abs_inner_stdGaussian]
    ring
  have hsum : ∫ x, ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (|⟪a i, x⟫| + |⟪a j, x⟫| - |⟪a i, x⟫ - ⟪a j, x⟫|) ∂(stdGaussian E)
      = gaussAbsMean * ∑ i ∈ s, ∑ j ∈ s, c i * c j * (‖a i‖ + ‖a j‖ - ‖a i - a j‖) := by
    rw [MeasureTheory.integral_finsetSum s
      (fun i _ => MeasureTheory.integrable_finsetSum s (fun j _ => hIpair i j)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finsetSum s (fun j _ => hIpair i j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hpair i j
  have hnn : 0 ≤ ∫ x, ∑ i ∈ s, ∑ j ∈ s, c i * c j *
      (|⟪a i, x⟫| + |⟪a j, x⟫| - |⟪a i, x⟫ - ⟪a j, x⟫|) ∂(stdGaussian E) :=
    integral_nonneg fun x => kernelR_sum_nonneg s (fun i => ⟪a i, x⟫) c
  rw [hsum] at hnn
  exact (mul_nonneg_iff_of_pos_left gaussAbsMean_pos).1 hnn

/-! ## PSD of `gCov` (HA1 D2.4) -/

/-- Linearity of the interval integral over a finite double sum, with a pointwise
nonnegativity hypothesis.  (Copied from `LQGDimension/Section2/ZCovPSD.lean`.) -/
lemma sum_intervalIntegral_nonneg {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ → ℝ)
    (hInt : ∀ i ∈ s, ∀ j ∈ s, IntervalIntegrable (g i j) volume 0 1)
    (hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, g i j x) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x := by
  have step1 : ∀ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x
      = ∫ x in (0:ℝ)..1, ∑ j ∈ s, g i j x :=
    fun i hi => (intervalIntegral.integral_finsetSum fun j hj => hInt i hi j hj).symm
  have hFi : ∀ i ∈ s, IntervalIntegrable (fun x => ∑ j ∈ s, g i j x) volume 0 1 := by
    intro i hi
    have heq : (fun x => ∑ j ∈ s, g i j x) = ∑ j ∈ s, g i j := by
      funext x; rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum s fun j hj => hInt i hi j hj
  have step2 : ∑ i ∈ s, ∑ j ∈ s, ∫ x in (0:ℝ)..1, g i j x
      = ∫ x in (0:ℝ)..1, ∑ i ∈ s, ∑ j ∈ s, g i j x := by
    rw [Finset.sum_congr rfl step1, ← intervalIntegral.integral_finsetSum hFi]
  rw [step2]
  exact intervalIntegral.integral_nonneg zero_le_one hpt

/-- **PSD of (1.5)** (HA1 D2.4): `gCov ∘ φ` is positive semidefinite on every finite family of
interval-integrable profiles `φ i : ℝ → E`. -/
theorem gCov_psdOn {ι : Type*} (F : Finset ι) (φ : ι → ℝ → E)
    (hφ : ∀ i ∈ F, IntervalIntegrable (φ i) volume 0 1) :
    LQGDimension.PSDOn F (fun i j => gCov (φ i) (φ j)) := by
  rw [LQGDimension.PSDOn, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun c => ?_⟩
  · simp only [Matrix.of_apply, star_trivial]
    exact gCov_comm (φ (j : ι)) (φ (i : ι))
  · have hsum : star c ⬝ᵥ ((Matrix.of fun i j : F => gCov (φ i) (φ j)) *ᵥ c)
        = ∑ i : F, ∑ j : F, c i * c j * gCov (φ (i : ι)) (φ (j : ι)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    set g : F → F → ℝ → ℝ := fun i j x => c i * c j *
      (‖φ (i : ι) x‖ + ‖φ (j : ι) x‖ - ‖φ (i : ι) x - φ (j : ι) x‖) with hg_def
    have hInt : ∀ i ∈ (Finset.univ : Finset F), ∀ j ∈ (Finset.univ : Finset F),
        IntervalIntegrable (g i j) volume 0 1 := by
      intro i _ j _
      exact (((hφ (i : ι) i.2).norm.add (hφ (j : ι) j.2).norm).sub
        (((hφ (i : ι) i.2).sub (hφ (j : ι) j.2)).norm)).const_mul (c i * c j)
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∑ i : F, ∑ j : F, g i j x :=
      fun x _ => normKernel_sum_nonneg Finset.univ (fun i : F => φ (i : ι) x) c
    have hnn := sum_intervalIntegral_nonneg (Finset.univ : Finset F) g hInt hpt
    have hrw : ∑ i : F, ∑ j : F, c i * c j * gCov (φ (i : ι)) (φ (j : ι))
        = Real.pi * ∑ i : F, ∑ j : F, ∫ x in (0 : ℝ)..1, g i j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show c i * c j * gCov (φ (i : ι)) (φ (j : ι)) = Real.pi * ∫ x in (0 : ℝ)..1, g i j x
      unfold gCov
      simp only [hg_def]
      rw [intervalIntegral.integral_const_mul]
      ring
    rw [hrw]
    exact mul_nonneg Real.pi_pos.le hnn

/-- **(T5) PSD of `gCov` on finite families of continuous profiles** (the template `ZCovEPSD` of
HA6 D.4). -/
theorem gCov_psdOn_of_continuous (F : Finset (ℝ → E)) (hF : ∀ f ∈ F, Continuous f) :
    LQGDimension.PSDOn F (fun f g => gCov f g) :=
  gCov_psdOn F id fun f hf => (hF f hf).intervalIntegrable 0 1

/-- PSD of `gCov` on finite subfamilies of `Vg E n`. -/
theorem gCov_psdOn_Vg (n : ℕ) (F : Finset (Vg E n)) :
    LQGDimension.PSDOn F (fun f g => gCov (f : ℝ → E) g) :=
  gCov_psdOn F (fun f => (f : ℝ → E)) fun f _ => Vg_intervalIntegrable f.2 0 1

end Euclid

end HigherDimLFPP.Var
