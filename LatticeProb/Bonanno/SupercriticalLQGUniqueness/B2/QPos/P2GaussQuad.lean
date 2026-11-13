/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2GaussQuad at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2GaussLinAlg

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Complex Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 
def quadCoeff (μ : ℝ) : ℂ := -(1 - μ * I) / 2

theorem quadCoeff_re (μ : ℝ) : (quadCoeff μ).re < 0 := by
  simp [quadCoeff]
  norm_num

 
def quadConst (μ : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) * ((Real.pi : ℂ) / -quadCoeff μ) ^ (1 / 2 : ℂ)

 
theorem integral_cexp_quad_gaussianReal (μ β : ℝ) :
    ∫ x, cexp (((μ * x ^ 2 / 2 + β * x : ℝ) : ℂ) * I) ∂(gaussianReal 0 1) =
      quadConst μ * cexp (-((β : ℂ) * I) ^ 2 / (4 * quadCoeff μ)) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • cexp (((μ * x ^ 2 / 2 + β * x : ℝ) : ℂ) * I) =
      (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        cexp (quadCoeff μ * (x : ℂ) ^ 2 + ((β : ℂ) * I) * x + 0) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, Complex.real_smul]
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [quadCoeff]
    push_cast
    ring_nf
  simp_rw [h]
  rw [integral_const_mul, integral_cexp_quadratic (quadCoeff_re μ), quadConst]
  simp only [zero_sub, mul_assoc]
  congr 2
  ring

theorem quadCoeff_ne_zero (μ : ℝ) : quadCoeff μ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [quadCoeff] at this

theorem one_sub_mul_I_ne_zero (μ : ℝ) : (1 : ℂ) - μ * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

variable {V : Type*} [Fintype V] [DecidableEq V]

 

theorem integral_multivariateGaussian_eigen (K : Matrix V V ℝ) (θ : V → ℝ)
    (F : EuclideanSpace ℝ V → ℂ) (hF : Continuous F) :
    ∫ φ, F φ ∂(multivariateGaussian 0 K⁻¹) =
      ∫ c, F (WithLp.toLp 2 (GaussDiag.sq K *ᵥ ∑ i, c i • GaussDiag.e K θ i))
        ∂(Measure.pi fun _ : V => gaussianReal 0 1) := by
  set b := (GaussDiag.S_isHermitian K θ).eigenvectorBasis
  have hm : AEMeasurable (fun x : V → ℝ => ∑ i, x i • b i)
      (Measure.pi fun _ : V => gaussianReal 0 1) :=
    (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).measurable.aemeasurable
  rw [multivariateGaussian, integral_map (by fun_prop) hF.aestronglyMeasurable,
    stdGaussian_eq_map_pi_orthonormalBasis b, integral_map hm
      (by exact (hF.comp (by fun_prop)).aestronglyMeasurable)]
  congr 1
  funext c
  congr 1
  ext v
  simp only [zero_add, ofLp_toEuclideanCLM, WithLp.ofLp_sum, WithLp.ofLp_smul]
  rfl

 
theorem integral_cexp_shift_sq (K : Matrix V V ℝ) (hK : K.PosDef) (θ : V → ℝ) (u : ℝ)
    (p : V → ℂ)
    (hp : (K.map (fun x => (x : ℂ)) - Matrix.diagonal fun v => (θ v : ℂ) * I) *ᵥ p =
      fun v => (θ v : ℂ)) :
    ∫ φ, cexp (((∑ v, θ v * (φ v + u) ^ 2 / 2 : ℝ) : ℂ) * I) ∂(multivariateGaussian 0 K⁻¹) =
      (∫ φ, cexp (((∑ v, θ v * (φ v) ^ 2 / 2 : ℝ) : ℂ) * I) ∂(multivariateGaussian 0 K⁻¹)) *
        cexp (-((u ^ 2 / 2 : ℝ) : ℂ) * (∑ v, (θ v : ℂ) * p v - I * ∑ v, (θ v : ℂ))) := by
  have hcont : ∀ w : ℝ, Continuous fun φ : EuclideanSpace ℝ V =>
      cexp (((∑ v, θ v * (φ v + w) ^ 2 / 2 : ℝ) : ℂ) * I) := by
    intro w
    refine Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    refine continuous_finsetSum _ fun v _ => ?_
    exact (continuous_const.mul (((PiLp.continuous_apply 2 _ v).add continuous_const).pow 2)).div_const _
  
  have hgen : ∀ w : ℝ,
      ∫ φ, cexp (((∑ v, θ v * (φ v + w) ^ 2 / 2 : ℝ) : ℂ) * I) ∂(multivariateGaussian 0 K⁻¹) =
        cexp (((w ^ 2 / 2 * ∑ v, θ v : ℝ) : ℂ) * I) *
          ∏ i, (quadConst (GaussDiag.μ K θ i) *
            cexp (-((w * GaussDiag.β K θ i : ℝ) * I) ^ 2 / (4 * quadCoeff (GaussDiag.μ K θ i)))) := by
    intro w
    rw [integral_multivariateGaussian_eigen K θ _ (hcont w)]
    have hpt : ∀ c : V → ℝ,
        cexp (((∑ v, θ v * ((WithLp.toLp 2 (GaussDiag.sq K *ᵥ ∑ i, c i • GaussDiag.e K θ i) :
            EuclideanSpace ℝ V) v + w) ^ 2 / 2 : ℝ) : ℂ) * I) =
          cexp (((w ^ 2 / 2 * ∑ v, θ v : ℝ) : ℂ) * I) *
            ∏ i, cexp (((GaussDiag.μ K θ i * c i ^ 2 / 2 + (w * GaussDiag.β K θ i) * c i : ℝ) : ℂ)
              * I) := by
      intro c
      have hq := GaussDiag.sum_theta_sq K θ c
      have hl := GaussDiag.sum_theta_lin K θ c
      set φ : V → ℝ := GaussDiag.sq K *ᵥ ∑ i, c i • GaussDiag.e K θ i
      have hexpand : (∑ v, θ v * (φ v + w) ^ 2 / 2) =
          (w ^ 2 / 2 * ∑ v, θ v) +
            ∑ i, (GaussDiag.μ K θ i * c i ^ 2 / 2 + (w * GaussDiag.β K θ i) * c i) := by
        have : (∑ v, θ v * (φ v + w) ^ 2 / 2) =
            (∑ v, θ v * φ v ^ 2) / 2 + w * (∑ v, θ v * φ v) + w ^ 2 / 2 * ∑ v, θ v := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring
        rw [this, hq, hl, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
        rw [show ∑ i, w * (c i * GaussDiag.β K θ i) = ∑ i, w * GaussDiag.β K θ i * c i by
          apply Finset.sum_congr rfl; intro i _; ring]
        ring
      have hφ : (fun v => (WithLp.toLp 2 φ : EuclideanSpace ℝ V) v) = φ := rfl
      simp only [hφ]
      rw [show (∑ v, θ v * ((WithLp.toLp 2 φ : EuclideanSpace ℝ V) v + w) ^ 2 / 2) =
        ∑ v, θ v * (φ v + w) ^ 2 / 2 from rfl, hexpand]
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_sum, Finset.sum_mul,
        Complex.exp_sum]
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) =>
      cexp (((GaussDiag.μ K θ i * x ^ 2 / 2 + (w * GaussDiag.β K θ i) * x : ℝ) : ℂ) * I))]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_cexp_quad_gaussianReal _ _
  rw [hgen u]
  have h0 := hgen 0
  simp only [add_zero] at h0
  rw [h0]
  simp only [zero_mul, Complex.ofReal_zero, zero_pow two_ne_zero, mul_zero, neg_zero,
    zero_div, Complex.exp_zero, mul_one, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div]
  have hsum := GaussDiag.sum_beta_sq_div K θ hK p hp
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hterm : ∀ i, -((u * GaussDiag.β K θ i : ℝ) * I) ^ 2 / (4 * quadCoeff (GaussDiag.μ K θ i)) =
      -((u ^ 2 / 2 : ℝ) : ℂ) * ((GaussDiag.β K θ i : ℂ) ^ 2 / (1 - GaussDiag.μ K θ i * I)) := by
    intro i
    have h1 := quadCoeff_ne_zero (GaussDiag.μ K θ i)
    have h2 := one_sub_mul_I_ne_zero (GaussDiag.μ K θ i)
    simp only [quadCoeff] at h1 ⊢
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hsum]
  rw [mul_comm (cexp _) _, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end SupercriticalLQGUniqueness.B2.QPos
