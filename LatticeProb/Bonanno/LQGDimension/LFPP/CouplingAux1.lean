/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.CouplingAux1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Node `C36`, auxiliary file 1: circle measures and the Gaussian kernel

* `angMeas`: normalised Lebesgue measure on `(0, 2π]`; `circMeas c r`: the uniform probability
  measure on the circle `∂B(c, r)` (image of `angMeas` under `circleMap c r`).
* `gK t x y = e^{-|x-y|²/(4t²)}` and the pairing `gPair t μ ν = ∫∫ gK t x y dν(y) dμ(x)`.
* **Fourier features** (`gPair_eq_integral_fPair`): with `γ` the standard Gaussian on `ℂ ≅ ℝ²`,
  `gPair t μ ν = ∫ (C_μ C_ν + S_μ S_ν) dγ`, where `C_μ(ξ) = ∫ cos(λ⟪ξ, z⟫) dμ(z)`, etc.
  This gives positive semidefiniteness of Gaussian-kernel Gram matrices of finite
  signed combinations of finite measures.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Coupling

/-! ## 1. Circle measures -/

/-- Normalised Lebesgue measure on `(0, 2π]`. -/
def angMeas : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance : IsProbabilityMeasure angMeas := by
  constructor
  have h2 : (0 : ℝ) < 2 * π := by positivity
  rw [angMeas, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using h2) ENNReal.ofReal_ne_top

lemma integral_angMeas (f : ℝ → ℝ) :
    ∫ θ, f θ ∂angMeas = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ := by
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [angMeas, integral_smul_measure, intervalIntegral.integral_of_le h2, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal h2]

lemma angMeas_le (s : Set ℝ) : angMeas s ≤ (ENNReal.ofReal (2 * π))⁻¹ * volume s := by
  rw [angMeas, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)

/-- The uniform probability measure on the circle `∂B(c, r)`. -/
def circMeas (c : ℂ) (r : ℝ) : Measure ℂ := angMeas.map (circleMap c r)

instance (c : ℂ) (r : ℝ) : IsProbabilityMeasure (circMeas c r) := by
  unfold circMeas; infer_instance

lemma integral_circMeas {c : ℂ} {r : ℝ} {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (circMeas c r)) :
    ∫ z, f z ∂circMeas c r = ∫ θ, f (circleMap c r θ) ∂angMeas :=
  integral_map (continuous_circleMap c r).aemeasurable hf

lemma integral_circMeas' {c : ℂ} {r : ℝ} {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (circMeas c r)) :
    ∫ z, f z ∂circMeas c r = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f (circleMap c r θ) := by
  rw [integral_circMeas hf, integral_angMeas]

lemma integral_circMeas_eq_circleAverage {c : ℂ} {r : ℝ} {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (circMeas c r)) :
    ∫ z, f z ∂circMeas c r = Real.circleAverage f c r := by
  rw [integral_circMeas' hf, Real.circleAverage_def, smul_eq_mul]

lemma ae_circMeas (c : ℂ) (r : ℝ) : ∀ᵐ z ∂circMeas c r, ‖z - c‖ = |r| := by
  have hs : MeasurableSet {z : ℂ | ‖z - c‖ = |r|} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [circMeas, ae_map_iff (continuous_circleMap c r).aemeasurable hs]
  exact ae_of_all _ fun θ => by
    show ‖circleMap c r θ - c‖ = |r|
    rw [circleMap_sub_center, norm_circleMap_zero]

lemma circMeas_singleton {c : ℂ} {r : ℝ} (hr : r ≠ 0) (x : ℂ) : circMeas c r {x} = 0 := by
  rw [circMeas, Measure.map_apply (continuous_circleMap c r).measurable
    (measurableSet_singleton x)]
  refine le_antisymm ((angMeas_le _).trans ?_) zero_le
  rw [((Set.countable_singleton x).preimage_circleMap c hr).measure_zero, mul_zero]

/-- The diagonal is null for a product of two circle measures. -/
lemma ae_ne_circMeas_prod (c c' : ℂ) (r : ℝ) {r' : ℝ} (hr' : r' ≠ 0) :
    ∀ᵐ p ∂(circMeas c r).prod (circMeas c' r'), 0 < ‖p.1 - p.2‖ := by
  have hd : MeasurableSet (Set.diagonal ℂ) := isClosed_diagonal.measurableSet
  have h0 : ((circMeas c r).prod (circMeas c' r')) (Set.diagonal ℂ) = 0 := by
    rw [Measure.prod_apply hd]
    have : ∀ x : ℂ, Prod.mk x ⁻¹' Set.diagonal ℂ = {x} := by
      intro x; ext y; simp [Set.mem_diagonal_iff, eq_comm]
    simp only [this, circMeas_singleton hr', lintegral_zero]
  rw [ae_iff]
  refine measure_mono_null (fun p (hp : ¬ 0 < ‖p.1 - p.2‖) => ?_) h0
  rw [not_lt, norm_le_zero_iff, sub_eq_zero] at hp
  exact hp

/-! ## 2. The Gaussian kernel and its pairing -/

/-- `gK t x y = e^{-|x - y|²/(4t²)}`. -/
def gK (t : ℝ) (x y : ℂ) : ℝ := Real.exp (-‖x - y‖ ^ 2 / (4 * t ^ 2))

lemma gK_pos (t : ℝ) (x y : ℂ) : 0 < gK t x y := Real.exp_pos _

lemma gK_le_one (t : ℝ) (x y : ℂ) : gK t x y ≤ 1 := by
  rw [gK, Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

lemma gK_comm (t : ℝ) (x y : ℂ) : gK t x y = gK t y x := by
  rw [gK, gK, norm_sub_rev]

lemma measurable_gK : Measurable fun q : ℝ × ℂ × ℂ => gK q.1 q.2.1 q.2.2 := by
  unfold gK; fun_prop

lemma continuous_gK (t : ℝ) : Continuous fun p : ℂ × ℂ => gK t p.1 p.2 := by
  unfold gK; fun_prop

lemma integrable_gK {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (t : ℝ) {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun a => gK t (f a) (g a)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun a => ?_)
  · exact ((continuous_gK t).measurable.comp (hf.prodMk hg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (gK_pos _ _ _)]; exact gK_le_one _ _ _

/-- The Gaussian-kernel pairing `∫∫ e^{-|x-y|²/(4t²)} dν(y) dμ(x)`. -/
def gPair (t : ℝ) (μ ν : Measure ℂ) : ℝ := ∫ x, ∫ y, gK t x y ∂ν ∂μ

lemma gPair_eq_prod (t : ℝ) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gPair t μ ν = ∫ p, gK t p.1 p.2 ∂(μ.prod ν) :=
  (integral_prod _ (integrable_gK _ t measurable_fst measurable_snd)).symm

lemma gPair_comm (t : ℝ) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gPair t μ ν = gPair t ν μ := by
  rw [gPair, gPair, integral_integral_swap]
  · simp_rw [gK_comm t]
  · exact integrable_gK _ t measurable_fst measurable_snd

lemma gPair_le (t : ℝ) (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    gPair t μ ν ≤ 1 := by
  rw [gPair_eq_prod]
  calc ∫ p, gK t p.1 p.2 ∂(μ.prod ν) ≤ ∫ _p, (1 : ℝ) ∂(μ.prod ν) :=
        integral_mono (integrable_gK _ t measurable_fst measurable_snd) (integrable_const _)
          fun p => gK_le_one _ _ _
    _ = 1 := by simp

lemma gPair_nonneg (t : ℝ) (μ ν : Measure ℂ) : 0 ≤ gPair t μ ν :=
  integral_nonneg fun x => integral_nonneg fun y => (gK_pos t x y).le

lemma measurable_gPair (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    Measurable fun t => gPair t μ ν := by
  have h1 : StronglyMeasurable fun q : ℝ × ℂ => ∫ y, gK q.1 q.2 y ∂ν := by
    refine StronglyMeasurable.integral_prod_right' (f := fun q : (ℝ × ℂ) × ℂ => gK q.1.1 q.1.2 q.2)
      ?_
    exact (measurable_gK.comp (by fun_prop : Measurable fun q : (ℝ × ℂ) × ℂ =>
      (q.1.1, q.1.2, q.2))).stronglyMeasurable
  exact (h1.integral_prod_right' (ν := μ)).measurable

lemma gPair_dirac_left (t : ℝ) (s : ℂ) (ν : Measure ℂ) :
    gPair t (Measure.dirac s) ν = ∫ y, gK t s y ∂ν := by
  rw [gPair, integral_dirac]

lemma gPair_dirac_right (t : ℝ) (μ : Measure ℂ) (s : ℂ) :
    gPair t μ (Measure.dirac s) = ∫ x, gK t x s ∂μ := by
  rw [gPair]; simp_rw [integral_dirac]

/-! ## 3. Fourier features -/

/-- The frequency scale `(√2 t)⁻¹`. -/
def hkF (t : ℝ) : ℝ := (Real.sqrt 2 * t)⁻¹

/-- Cosine feature `z ↦ cos(λ⟪ξ, z⟫)`. -/
def cF (t : ℝ) (ξ z : ℂ) : ℝ := Real.cos (hkF t * ⟪ξ, z⟫)

/-- Sine feature `z ↦ sin(λ⟪ξ, z⟫)`. -/
def sF (t : ℝ) (ξ z : ℂ) : ℝ := Real.sin (hkF t * ⟪ξ, z⟫)

lemma continuous_cF (t : ℝ) : Continuous fun p : ℂ × ℂ => cF t p.1 p.2 := by
  unfold cF; fun_prop

lemma continuous_sF (t : ℝ) : Continuous fun p : ℂ × ℂ => sF t p.1 p.2 := by
  unfold sF; fun_prop

lemma integral_cos_inner' (u : ℂ) :
    ∫ x, Real.cos ⟪x, u⟫ ∂(stdGaussian ℂ) = Real.exp (-‖u‖ ^ 2 / 2) := by
  have h := charFun_stdGaussian (E := ℂ) u
  rw [charFun_apply] at h
  have hint : Integrable (fun x : ℂ => Complex.exp (⟪x, u⟫ * Complex.I)) (stdGaussian ℂ) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 := integral_re hint
  rw [h] at h2
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at h2
  rw [h2, show (-(‖u‖ : ℂ) ^ 2 / 2) = ((-‖u‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.exp_ofReal_re _

/-- `e^{-|z-w|²/(4t²)} = ∫ (cos cos + sin sin) dγ`. -/
lemma gK_eq_integral (t : ℝ) (z w : ℂ) :
    gK t z w = ∫ x, (cF t x z * cF t x w + sF t x z * sF t x w) ∂(stdGaussian ℂ) := by
  have hfun : (fun x : ℂ => cF t x z * cF t x w + sF t x z * sF t x w) =
      fun x => Real.cos ⟪x, (hkF t : ℝ) • (z - w)⟫ := by
    funext x
    simp only [cF, sF, inner_smul_right, inner_sub_right, mul_sub]
    rw [Real.cos_sub]
  rw [hfun, integral_cos_inner', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hkF, gK]
  congr 1
  rw [inv_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- `C_μ(ξ) = ∫ cos(λ⟪ξ, z⟫) dμ(z)`. -/
def cA (t : ℝ) (μ : Measure ℂ) (ξ : ℂ) : ℝ := ∫ z, cF t ξ z ∂μ

/-- `S_μ(ξ) = ∫ sin(λ⟪ξ, z⟫) dμ(z)`. -/
def sA (t : ℝ) (μ : Measure ℂ) (ξ : ℂ) : ℝ := ∫ z, sF t ξ z ∂μ

lemma measurable_cA (t : ℝ) (μ : Measure ℂ) [SFinite μ] : Measurable (cA t μ) :=
  ((continuous_cF t).measurable.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma measurable_sA (t : ℝ) (μ : Measure ℂ) [SFinite μ] : Measurable (sA t μ) :=
  ((continuous_sF t).measurable.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma abs_cA_le (t : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ] (ξ : ℂ) : |cA t μ ξ| ≤ 1 := by
  rw [cA, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun z => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _

lemma abs_sA_le (t : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ] (ξ : ℂ) : |sA t μ ξ| ≤ 1 := by
  rw [sA, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun z => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _

/-- The Fourier integrand `C_μ C_ν + S_μ S_ν`. -/
def fPair (t : ℝ) (μ ν : Measure ℂ) (ξ : ℂ) : ℝ := cA t μ ξ * cA t ν ξ + sA t μ ξ * sA t ν ξ

lemma integrable_fPair (t : ℝ) (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : Integrable (fPair t μ ν) (stdGaussian ℂ) := by
  refine Integrable.of_bound ?_ 2 (ae_of_all _ fun ξ => ?_)
  · unfold fPair
    exact (((measurable_cA t μ).mul (measurable_cA t ν)).add
      ((measurable_sA t μ).mul (measurable_sA t ν))).aestronglyMeasurable
  · have h1 := abs_cA_le t μ ξ
    have h2 := abs_cA_le t ν ξ
    have h3 := abs_sA_le t μ ξ
    have h4 := abs_sA_le t ν ξ
    rw [Real.norm_eq_abs, fPair]
    calc _ ≤ |cA t μ ξ * cA t ν ξ| + |sA t μ ξ * sA t ν ξ| := abs_add_le _ _
      _ = |cA t μ ξ| * |cA t ν ξ| + |sA t μ ξ| * |sA t ν ξ| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num

/-- **Fourier representation of `gPair`.** -/
theorem gPair_eq_integral_fPair (t : ℝ) (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : gPair t μ ν = ∫ ξ, fPair t μ ν ξ ∂(stdGaussian ℂ) := by
  let k : ℂ × ℂ → ℂ → ℝ := fun p ξ => cF t ξ p.1 * cF t ξ p.2 + sF t ξ p.1 * sF t ξ p.2
  have hk : k = fun p ξ => cF t ξ p.1 * cF t ξ p.2 + sF t ξ p.1 * sF t ξ p.2 := rfl
  have hkc : Continuous (Function.uncurry k) := by
    simp only [hk, cF, sF]
    fun_prop
  have hki : Integrable (Function.uncurry k) ((μ.prod ν).prod (stdGaussian ℂ)) := by
    refine Integrable.of_bound hkc.aestronglyMeasurable 2 (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, hk, cF, sF, Real.norm_eq_abs]
    have h1 := Real.abs_cos_le_one (hkF t * ⟪q.2, q.1.1⟫)
    have h2 := Real.abs_cos_le_one (hkF t * ⟪q.2, q.1.2⟫)
    have h3 := Real.abs_sin_le_one (hkF t * ⟪q.2, q.1.1⟫)
    have h4 := Real.abs_sin_le_one (hkF t * ⟪q.2, q.1.2⟫)
    calc _ ≤ |Real.cos (hkF t * ⟪q.2, q.1.1⟫) * Real.cos (hkF t * ⟪q.2, q.1.2⟫)| +
          |Real.sin (hkF t * ⟪q.2, q.1.1⟫) * Real.sin (hkF t * ⟪q.2, q.1.2⟫)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  have hinner : ∀ ξ, ∫ p, k p ξ ∂(μ.prod ν) = fPair t μ ν ξ := by
    intro ξ
    have hc1 : Continuous fun z => cF t ξ z := by unfold cF; fun_prop
    have hs1 : Continuous fun z => sF t ξ z := by unfold sF; fun_prop
    have i1 : Integrable (fun p : ℂ × ℂ => cF t ξ p.1 * cF t ξ p.2) (μ.prod ν) := by
      refine Integrable.of_bound ((hc1.comp continuous_fst).mul
        (hc1.comp continuous_snd)).aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    have i2 : Integrable (fun p : ℂ × ℂ => sF t ξ p.1 * sF t ξ p.2) (μ.prod ν) := by
      refine Integrable.of_bound ((hs1.comp continuous_fst).mul
        (hs1.comp continuous_snd)).aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    simp only [hk]
    rw [integral_add i1 i2, integral_prod_mul (fun z => cF t ξ z) (fun z => cF t ξ z),
      integral_prod_mul (fun z => sF t ξ z) (fun z => sF t ξ z)]
    simp only [fPair, cA, sA]
  rw [gPair_eq_prod]
  have h1 : ∫ p, gK t p.1 p.2 ∂(μ.prod ν) = ∫ p, ∫ ξ, k p ξ ∂(stdGaussian ℂ) ∂(μ.prod ν) := by
    congr 1
    funext p
    exact gK_eq_integral t p.1 p.2
  rw [h1, integral_integral_swap hki]
  exact integral_congr_ae (ae_of_all _ hinner)

/-! ## 4. Two-term signed combinations -/

/-- Cosine feature of the signed combination `a₁ μ₁ + a₂ μ₂`. -/
def cL (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) (ξ : ℂ) : ℝ := a₁ * cA t μ₁ ξ + a₂ * cA t μ₂ ξ

/-- Sine feature of the signed combination `a₁ μ₁ + a₂ μ₂`. -/
def sL (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) (ξ : ℂ) : ℝ := a₁ * sA t μ₁ ξ + a₂ * sA t μ₂ ξ

lemma lin_expand (t a₁ a₂ b₁ b₂ : ℝ) (μ₁ μ₂ ν₁ ν₂ : Measure ℂ) (ξ : ℂ) :
    cL t a₁ a₂ μ₁ μ₂ ξ * cL t b₁ b₂ ν₁ ν₂ ξ + sL t a₁ a₂ μ₁ μ₂ ξ * sL t b₁ b₂ ν₁ ν₂ ξ =
      a₁ * b₁ * fPair t μ₁ ν₁ ξ + a₁ * b₂ * fPair t μ₁ ν₂ ξ + a₂ * b₁ * fPair t μ₂ ν₁ ξ +
        a₂ * b₂ * fPair t μ₂ ν₂ ξ := by
  simp only [cL, sL, fPair]; ring

lemma integrable_lin (t a₁ a₂ b₁ b₂ : ℝ) (μ₁ μ₂ ν₁ ν₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    Integrable (fun ξ => cL t a₁ a₂ μ₁ μ₂ ξ * cL t b₁ b₂ ν₁ ν₂ ξ +
      sL t a₁ a₂ μ₁ μ₂ ξ * sL t b₁ b₂ ν₁ ν₂ ξ) (stdGaussian ℂ) := by
  simp_rw [lin_expand]
  exact ((((integrable_fPair t μ₁ ν₁).const_mul _).add ((integrable_fPair t μ₁ ν₂).const_mul _)).add
    ((integrable_fPair t μ₂ ν₁).const_mul _)).add ((integrable_fPair t μ₂ ν₂).const_mul _)

/-- **Bilinear expansion** of the Fourier pairing of two two-term combinations. -/
theorem integral_lin (t a₁ a₂ b₁ b₂ : ℝ) (μ₁ μ₂ ν₁ ν₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    ∫ ξ, (cL t a₁ a₂ μ₁ μ₂ ξ * cL t b₁ b₂ ν₁ ν₂ ξ + sL t a₁ a₂ μ₁ μ₂ ξ * sL t b₁ b₂ ν₁ ν₂ ξ)
        ∂(stdGaussian ℂ) =
      a₁ * b₁ * gPair t μ₁ ν₁ + a₁ * b₂ * gPair t μ₁ ν₂ + a₂ * b₁ * gPair t μ₂ ν₁ +
        a₂ * b₂ * gPair t μ₂ ν₂ := by
  simp_rw [lin_expand]
  have i11 := (integrable_fPair t μ₁ ν₁).const_mul (a₁ * b₁)
  have i12 := (integrable_fPair t μ₁ ν₂).const_mul (a₁ * b₂)
  have i21 := (integrable_fPair t μ₂ ν₁).const_mul (a₂ * b₁)
  have i22 := (integrable_fPair t μ₂ ν₂).const_mul (a₂ * b₂)
  have j1 : Integrable (fun ξ => a₁ * b₁ * fPair t μ₁ ν₁ ξ + a₁ * b₂ * fPair t μ₁ ν₂ ξ)
      (stdGaussian ℂ) := i11.add i12
  have j2 : Integrable (fun ξ => a₁ * b₁ * fPair t μ₁ ν₁ ξ + a₁ * b₂ * fPair t μ₁ ν₂ ξ +
      a₂ * b₁ * fPair t μ₂ ν₁ ξ) (stdGaussian ℂ) := j1.add i21
  rw [integral_add j2 i22, integral_add j1 i21, integral_add i11 i12, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, ← gPair_eq_integral_fPair, ← gPair_eq_integral_fPair,
    ← gPair_eq_integral_fPair, ← gPair_eq_integral_fPair]

lemma measurable_cL (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) [SFinite μ₁] [SFinite μ₂] :
    Measurable (cL t a₁ a₂ μ₁ μ₂) := by
  unfold cL
  exact ((measurable_cA t μ₁).const_mul _).add ((measurable_cA t μ₂).const_mul _)

lemma measurable_sL (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) [SFinite μ₁] [SFinite μ₂] :
    Measurable (sL t a₁ a₂ μ₁ μ₂) := by
  unfold sL
  exact ((measurable_sA t μ₁).const_mul _).add ((measurable_sA t μ₂).const_mul _)

lemma abs_cL_le (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (ξ : ℂ) : |cL t a₁ a₂ μ₁ μ₂ ξ| ≤ |a₁| + |a₂| := by
  unfold cL
  calc _ ≤ |a₁ * cA t μ₁ ξ| + |a₂ * cA t μ₂ ξ| := abs_add_le _ _
    _ = |a₁| * |cA t μ₁ ξ| + |a₂| * |cA t μ₂ ξ| := by rw [abs_mul, abs_mul]
    _ ≤ |a₁| * 1 + |a₂| * 1 := by
        gcongr
        · exact abs_cA_le t μ₁ ξ
        · exact abs_cA_le t μ₂ ξ
    _ = |a₁| + |a₂| := by ring

lemma abs_sL_le (t a₁ a₂ : ℝ) (μ₁ μ₂ : Measure ℂ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (ξ : ℂ) : |sL t a₁ a₂ μ₁ μ₂ ξ| ≤ |a₁| + |a₂| := by
  unfold sL
  calc _ ≤ |a₁ * sA t μ₁ ξ| + |a₂ * sA t μ₂ ξ| := abs_add_le _ _
    _ = |a₁| * |sA t μ₁ ξ| + |a₂| * |sA t μ₂ ξ| := by rw [abs_mul, abs_mul]
    _ ≤ |a₁| * 1 + |a₂| * 1 := by
        gcongr
        · exact abs_sA_le t μ₁ ξ
        · exact abs_sA_le t μ₂ ξ
    _ = |a₁| + |a₂| := by ring

end LQGDimension.Coupling
