/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Existence.HeatFeature at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Heat-kernel features for the Green's functions on `ℍ`

For a sign `s = ±1` put `K_s(x, y) = -log|x - y| - s log|x - ȳ|`, so `K_{-1} = greenH` and
`K_1 = neumannH`. We write `K_s` as an `L²` Gram kernel:

* Fourier features (`LQGDimension.Coupling.cF`, `sF`): with `g_x(ξ) = cos(λ⟪ξ,x⟫) + sin(λ⟪ξ,x⟫)`
  and `γ` the standard Gaussian on `ℂ`, `∫ g_x g_y dγ = e^{-|x-y|²/(4t²)}` (the odd part
  integrates to zero, `hkG_mul_integral`).
* Method of images: `h_x = g_x + s g_{x̄}` gives `∫ h_x h_y dγ = 2 (gK t x y + s gK t x ȳ)`.
* Frullani (`LQGDimension.HeatKernel.frIntegrand_integral`):
  `∫_0^∞ (gK t x y + s gK t x ȳ) dt/t = K_s(x, y)` up to reference terms that cancel for
  balanced pairs, or for `s = -1`.

The feature of a pair `p = (μ₁, μ₂)` is `(2t)^{-1/2} (∫ h_x dμ₁ - ∫ h_x dμ₂)` on
`(0, ∞) × ℂ` with `dt ⊗ γ`; its `L²` inner products are `kernelCov2 K_s` (`hk_integral_mul`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped RealInnerProductSpace ComplexConjugate ENNReal

namespace QuantumZipper.GFFExist

open LQGDimension.Coupling LQGDimension.HeatKernel

/-! ### Definitions -/

/-- The point feature `g_x(ξ) = cos(λ⟪ξ,x⟫) + sin(λ⟪ξ,x⟫)` at scale `t`. -/
def hkG (t : ℝ) (ξ x : ℂ) : ℝ := cF t ξ x + sF t ξ x

/-- The reflected point feature `h_x = g_x + s g_{x̄}`. -/
def hkH (s t : ℝ) (ξ x : ℂ) : ℝ := hkG t ξ x + s * hkG t ξ (conj x)

/-- The feature of a measure: `∫ h_x(ξ) dμ(x)`. -/
def hkA (s t : ℝ) (μ : Measure ℂ) (ξ : ℂ) : ℝ := ∫ x, hkH s t ξ x ∂μ

/-- The feature of a pair of measures on `(0,∞) × ℂ`. -/
def hkFeat (s : ℝ) (p : Measure ℂ × Measure ℂ) (q : ℝ × ℂ) : ℝ :=
  (Real.sqrt (2 * q.1))⁻¹ * (hkA s q.1 p.1 q.2 - hkA s q.1 p.2 q.2)

/-- The base measure `dt ⊗ γ` on `(0,∞) × ℂ`. -/
def hkM : Measure (ℝ × ℂ) := (volume.restrict (Ioi (0 : ℝ))).prod (stdGaussian ℂ)

/-- The kernel `K_s(x,y) = -log|x-y| - s log|x-ȳ|`. -/
def hkK (s : ℝ) (x y : ℂ) : ℝ := -Real.log ‖x - y‖ - s * Real.log ‖x - conj y‖

theorem hkK_neg_one : hkK (-1) = greenH := by
  funext x y; simp only [hkK, greenH]; ring

theorem hkK_one : hkK 1 = neumannH := by
  funext x y; simp only [hkK, neumannH]; ring

/-- The integrability package for a pair of measures. -/
def HkGood (μ ν : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
    (∀ᵐ z ∂(μ.prod ν), 0 < ‖z.1 - z.2‖ ∧ 0 < ‖z.1 - conj z.2‖) ∧
    Integrable (fun z : ℂ × ℂ => Real.log ‖z.1 - z.2‖) (μ.prod ν) ∧
    Integrable (fun z : ℂ × ℂ => Real.log ‖z.1 - conj z.2‖) (μ.prod ν)

/-! ### Measurability and bounds -/

lemma measurable_hkH (s : ℝ) : Measurable fun q : (ℝ × ℂ) × ℂ => hkH s q.1.1 q.1.2 q.2 := by
  have hc : Continuous fun q : ℂ × ℂ => ⟪q.1, q.2⟫ := continuous_inner
  have h1 : Measurable fun q : (ℝ × ℂ) × ℂ => ⟪q.1.2, q.2⟫ :=
    hc.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun q : (ℝ × ℂ) × ℂ => ⟪q.1.2, conj q.2⟫ :=
    hc.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
      (Complex.continuous_conj.measurable.comp measurable_snd))
  have hk : Measurable fun q : (ℝ × ℂ) × ℂ => hkF q.1.1 := by
    unfold hkF; fun_prop
  have hα : Measurable fun q : (ℝ × ℂ) × ℂ => hkF q.1.1 * ⟪q.1.2, q.2⟫ := hk.mul h1
  have hβ : Measurable fun q : (ℝ × ℂ) × ℂ => hkF q.1.1 * ⟪q.1.2, conj q.2⟫ := hk.mul h2
  unfold hkH hkG cF sF
  exact ((Real.measurable_cos.comp hα).add (Real.measurable_sin.comp hα)).add
    (measurable_const.mul ((Real.measurable_cos.comp hβ).add (Real.measurable_sin.comp hβ)))

lemma continuous_hkH (s t : ℝ) : Continuous fun q : ℂ × ℂ => hkH s t q.1 q.2 := by
  unfold hkH hkG cF sF
  fun_prop

lemma abs_hkG_le (t : ℝ) (ξ x : ℂ) : |hkG t ξ x| ≤ 2 := by
  unfold hkG cF sF
  have := Real.abs_cos_le_one (hkF t * ⟪ξ, x⟫)
  have := Real.abs_sin_le_one (hkF t * ⟪ξ, x⟫)
  exact (abs_add_le _ _).trans (by linarith)

lemma abs_hkH_le (s t : ℝ) (ξ x : ℂ) : |hkH s t ξ x| ≤ 2 + |s| * 2 := by
  unfold hkH
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have := abs_hkG_le t ξ x
  have := abs_hkG_le t ξ (conj x)
  have := abs_nonneg s
  nlinarith

lemma measurable_hkA (s : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun q : ℝ × ℂ => hkA s q.1 μ q.2 :=
  ((measurable_hkH s).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma measurable_hkA_t (s t : ℝ) (μ : Measure ℂ) [SFinite μ] : Measurable (hkA s t μ) :=
  ((continuous_hkH s t).measurable.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma abs_hkA_le (s t : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] (ξ : ℂ) :
    |hkA s t μ ξ| ≤ (2 + |s| * 2) * μ.real univ := by
  rw [hkA, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 2 + |s| * 2)
    (ae_of_all _ fun x => ?_)).trans (le_of_eq (by ring))
  rw [Real.norm_eq_abs]; exact abs_hkH_le s t ξ x

lemma measurable_hkFeat (s : ℝ) (p : Measure ℂ × Measure ℂ) [SFinite p.1] [SFinite p.2] :
    Measurable (hkFeat s p) := by
  unfold hkFeat
  exact (by fun_prop : Measurable fun q : ℝ × ℂ => (Real.sqrt (2 * q.1))⁻¹).mul
    ((measurable_hkA s p.1).sub (measurable_hkA s p.2))

lemma hk_integrable_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ) (h : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf C (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h x)

/-! ### Linearity of the features in the measure -/

lemma hk_integrable_hkH (s t : ℝ) (ξ : ℂ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (fun x => hkH s t ξ x) μ :=
  hk_integrable_bdd (Continuous.aestronglyMeasurable (by unfold hkH hkG cF sF; fun_prop))
    (2 + |s| * 2) (fun x => abs_hkH_le s t ξ x)

lemma hkA_smul (s t : ℝ) (μ : Measure ℂ) (c : ℝ≥0∞) (ξ : ℂ) :
    hkA s t (c • μ) ξ = c.toReal * hkA s t μ ξ := by
  simp only [hkA, integral_smul_measure, smul_eq_mul]

lemma hkA_comb (s t : ℝ) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : NNReal) (ξ : ℂ) :
    hkA s t (a • μ + b • ν) ξ = (a : ℝ) * hkA s t μ ξ + (b : ℝ) * hkA s t ν ξ := by
  simp only [hkA]
  rw [integral_add_measure (hk_integrable_hkH s t ξ _) (hk_integrable_hkH s t ξ _),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def,
    NNReal.smul_def, smul_eq_mul, smul_eq_mul]

/-! ### Fourier identities -/

lemma hk_integral_sin_inner (u : ℂ) : ∫ x, Real.sin ⟪x, u⟫ ∂(stdGaussian ℂ) = 0 := by
  have h := charFun_stdGaussian (E := ℂ) u
  rw [charFun_apply] at h
  have hint : Integrable (fun x : ℂ => Complex.exp (⟪x, u⟫ * Complex.I)) (stdGaussian ℂ) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 := integral_im hint
  rw [h] at h2
  simp only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I_im] at h2
  rw [h2, show (-(‖u‖ : ℂ) ^ 2 / 2) = ((-‖u‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.exp_ofReal_im _

lemma hk_integrable_hkG_mul (t : ℝ) (a b : ℂ) :
    Integrable (fun ξ => hkG t ξ a * hkG t ξ b) (stdGaussian ℂ) := by
  refine hk_integrable_bdd (Continuous.aestronglyMeasurable (by unfold hkG cF sF; fun_prop)) 4
    (fun ξ => ?_)
  rw [abs_mul]
  have := abs_hkG_le t ξ a
  have := abs_hkG_le t ξ b
  nlinarith [abs_nonneg (hkG t ξ a), abs_nonneg (hkG t ξ b)]

/-- `∫ g_a g_b dγ = gK t a b`. -/
lemma hkG_mul_integral (t : ℝ) (a b : ℂ) :
    ∫ ξ, hkG t ξ a * hkG t ξ b ∂(stdGaussian ℂ) = gK t a b := by
  have hfun : (fun ξ => hkG t ξ a * hkG t ξ b) = fun ξ =>
      (cF t ξ a * cF t ξ b + sF t ξ a * sF t ξ b) + Real.sin ⟪ξ, (hkF t : ℝ) • (a + b)⟫ := by
    funext ξ
    simp only [hkG, cF, sF, inner_smul_right, inner_add_right, mul_add, Real.sin_add]
    ring
  have i1 : Integrable (fun ξ => cF t ξ a * cF t ξ b + sF t ξ a * sF t ξ b)
      (stdGaussian ℂ) := by
    refine hk_integrable_bdd (Continuous.aestronglyMeasurable (by unfold cF sF; fun_prop)) 2
      (fun ξ => ?_)
    unfold cF sF
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := Real.abs_cos_le_one (hkF t * ⟪ξ, a⟫)
    have := Real.abs_cos_le_one (hkF t * ⟪ξ, b⟫)
    have := Real.abs_sin_le_one (hkF t * ⟪ξ, a⟫)
    have := Real.abs_sin_le_one (hkF t * ⟪ξ, b⟫)
    nlinarith [abs_nonneg (Real.cos (hkF t * ⟪ξ, a⟫)), abs_nonneg (Real.sin (hkF t * ⟪ξ, a⟫))]
  have i2 : Integrable (fun ξ : ℂ => Real.sin ⟪ξ, (hkF t : ℝ) • (a + b)⟫) (stdGaussian ℂ) :=
    hk_integrable_bdd (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (fun ξ => Real.abs_sin_le_one _)
  rw [hfun, integral_add i1 i2, hk_integral_sin_inner, add_zero, gK_eq_integral]

lemma gK_conj_left (t : ℝ) (x y : ℂ) : gK t (conj x) y = gK t x (conj y) := by
  unfold gK
  congr 3
  rw [← Complex.norm_conj (conj x - y), map_sub, Complex.conj_conj]

lemma gK_conj_conj (t : ℝ) (x y : ℂ) : gK t (conj x) (conj y) = gK t x y := by
  unfold gK
  congr 3
  rw [← map_sub, Complex.norm_conj]

/-- `∫ h_x h_y dγ = 2 (gK t x y + s gK t x ȳ)`. -/
lemma hkH_mul_integral (s t : ℝ) (hs : s * s = 1) (x y : ℂ) :
    ∫ ξ, hkH s t ξ x * hkH s t ξ y ∂(stdGaussian ℂ) =
      2 * (gK t x y + s * gK t x (conj y)) := by
  have hfun : (fun ξ => hkH s t ξ x * hkH s t ξ y) = fun ξ =>
      ((hkG t ξ x * hkG t ξ y + s * (hkG t ξ x * hkG t ξ (conj y))) +
        s * (hkG t ξ (conj x) * hkG t ξ y)) +
        (s * s) * (hkG t ξ (conj x) * hkG t ξ (conj y)) := by
    funext ξ; simp only [hkH]; ring
  have i1 := hk_integrable_hkG_mul t x y
  have i2 := (hk_integrable_hkG_mul t x (conj y)).const_mul s
  have i3 := (hk_integrable_hkG_mul t (conj x) y).const_mul s
  have i4 := (hk_integrable_hkG_mul t (conj x) (conj y)).const_mul (s * s)
  have i12 : Integrable (fun ξ => hkG t ξ x * hkG t ξ y +
      s * (hkG t ξ x * hkG t ξ (conj y))) (stdGaussian ℂ) := i1.add i2
  have i123 : Integrable (fun ξ => hkG t ξ x * hkG t ξ y +
      s * (hkG t ξ x * hkG t ξ (conj y)) + s * (hkG t ξ (conj x) * hkG t ξ y))
      (stdGaussian ℂ) := i12.add i3
  rw [hfun, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul,
    hkG_mul_integral, hkG_mul_integral, hkG_mul_integral, hkG_mul_integral, gK_conj_left,
    gK_conj_conj, hs]
  ring

lemma hk_integrable_hkA_mul (s t : ℝ) (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : Integrable (fun ξ => hkA s t μ ξ * hkA s t ν ξ) (stdGaussian ℂ) := by
  have hm : Measurable fun ξ => hkA s t μ ξ * hkA s t ν ξ :=
    (measurable_hkA_t s t μ).mul (measurable_hkA_t s t ν)
  refine hk_integrable_bdd hm.aestronglyMeasurable
    (((2 + |s| * 2) * μ.real univ) * ((2 + |s| * 2) * ν.real univ)) (fun ξ => ?_)
  rw [abs_mul]
  exact mul_le_mul (abs_hkA_le s t μ ξ) (abs_hkA_le s t ν ξ) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_hkA_le s t μ ξ))

/-- `∫ A_μ A_ν dγ = ∫∫ 2 (gK t x y + s gK t x ȳ) d(μ ⊗ ν)`. -/
lemma hkA_mul_integral (s t : ℝ) (hs : s * s = 1) (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    ∫ ξ, hkA s t μ ξ * hkA s t ν ξ ∂(stdGaussian ℂ) =
      ∫ z, 2 * (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(μ.prod ν) := by
  have hprod : ∀ ξ, hkA s t μ ξ * hkA s t ν ξ =
      ∫ z, hkH s t ξ z.1 * hkH s t ξ z.2 ∂(μ.prod ν) := fun ξ =>
    (integral_prod_mul (L := ℝ) (μ := μ) (ν := ν) (fun x => hkH s t ξ x)
      (fun y => hkH s t ξ y)).symm
  rw [integral_congr_ae (ae_of_all _ hprod)]
  have hc : Continuous fun q : ℂ × (ℂ × ℂ) => hkH s t q.1 q.2.1 * hkH s t q.1 q.2.2 := by
    unfold hkH hkG cF sF; fun_prop
  have hint : Integrable (fun q : ℂ × (ℂ × ℂ) => hkH s t q.1 q.2.1 * hkH s t q.1 q.2.2)
      ((stdGaussian ℂ).prod (μ.prod ν)) := by
    refine hk_integrable_bdd hc.aestronglyMeasurable ((2 + |s| * 2) * (2 + |s| * 2))
      (fun q => ?_)
    rw [abs_mul]
    exact mul_le_mul (abs_hkH_le s t q.1 q.2.1) (abs_hkH_le s t q.1 q.2.2) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_hkH_le s t q.1 q.2.1))
  have hsw := integral_integral_swap (μ := stdGaussian ℂ) (ν := μ.prod ν)
    (f := fun ξ z => hkH s t ξ z.1 * hkH s t ξ z.2) hint
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact hkH_mul_integral s t hs z.1 z.2

/-! ### Frullani -/

/-- The Frullani integrand of the kernel `K_s`. -/
def hkFr (s : ℝ) (z : ℂ × ℂ) (t : ℝ) : ℝ :=
  frIntegrand ‖z.1 - z.2‖ t + s * frIntegrand ‖z.1 - conj z.2‖ t

lemma gK_div_eq (t : ℝ) (x y : ℂ) :
    gK t x y / t = frIntegrand ‖x - y‖ t + Real.exp (-1 / (4 * t ^ 2)) / t := by
  unfold gK frIntegrand; ring

lemma measurable_hkFr (s : ℝ) : Measurable fun q : ℝ × (ℂ × ℂ) => hkFr s q.2 q.1 := by
  unfold hkFr frIntegrand; fun_prop

lemma abs_frIntegrand_le (r t : ℝ) : |frIntegrand r t| ≤ 2 * |t⁻¹| := by
  unfold frIntegrand
  rw [div_eq_mul_inv, abs_mul]
  have h1 : |Real.exp (-r ^ 2 / (4 * t ^ 2)) - Real.exp (-1 / (4 * t ^ 2))| ≤ 2 := by
    have a1 : Real.exp (-r ^ 2 / (4 * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity))
    have a2 : Real.exp (-1 / (4 * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
    have := Real.exp_pos (-r ^ 2 / (4 * t ^ 2))
    have := Real.exp_pos (-1 / (4 * t ^ 2))
    rw [abs_le]; constructor <;> linarith
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- For fixed `t`, the scale-`t` pairing, split into its Frullani part and a reference term. -/
lemma hk_pair_div_eq (s t : ℝ) (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(μ.prod ν)) / t =
      ∫ z, hkFr s z t ∂(μ.prod ν) +
        (1 + s) * (Real.exp (-1 / (4 * t ^ 2)) / t) * (μ.real univ * ν.real univ) := by
  have hfun : ∀ z : ℂ × ℂ, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) / t =
      hkFr s z t + (1 + s) * (Real.exp (-1 / (4 * t ^ 2)) / t) := by
    intro z
    have e1 := gK_div_eq t z.1 z.2
    have e2 := gK_div_eq t z.1 (conj z.2)
    simp only [hkFr]
    rw [add_div, mul_div_assoc, e1, e2]
    ring
  have hFrm : Measurable fun z : ℂ × ℂ => hkFr s z t := by
    unfold hkFr frIntegrand; fun_prop
  have hFri : Integrable (fun z : ℂ × ℂ => hkFr s z t) (μ.prod ν) := by
    refine hk_integrable_bdd hFrm.aestronglyMeasurable (2 * |t⁻¹| + |s| * (2 * |t⁻¹|))
      (fun z => ?_)
    simp only [hkFr]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := abs_frIntegrand_le ‖z.1 - z.2‖ t
    have := abs_frIntegrand_le ‖z.1 - conj z.2‖ t
    have := abs_nonneg s
    nlinarith [abs_nonneg (frIntegrand ‖z.1 - conj z.2‖ t)]
  rw [← integral_div]
  simp_rw [hfun]
  rw [integral_add hFri (integrable_const _), integral_const, smul_eq_mul]
  have hu : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    rw [measureReal_def, measureReal_def, measureReal_def, ← Set.univ_prod_univ,
      Measure.prod_prod, ENNReal.toReal_mul]
  rw [hu]
  ring

lemma hk_fr_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] (D : X → ℝ)
    (hD : Measurable D) (hpos : ∀ᵐ x ∂μ, 0 < D x)
    (hlog : Integrable (fun x => Real.log (D x)) μ) :
    Integrable (fun q : ℝ × X => frIntegrand (D q.2) q.1) ((volume.restrict (Ioi 0)).prod μ) := by
  have hFm : Measurable (fun q : ℝ × X => frIntegrand (D q.2) q.1) := by
    unfold frIntegrand; fun_prop
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  constructor
  · filter_upwards [hpos] with x hx
    exact frIntegrand_integrableOn hx
  · refine hlog.abs.congr ?_
    filter_upwards [hpos] with x hx
    simp only [Real.norm_eq_abs]
    rw [frIntegrand_abs_integral hx]

/-- **Heat-kernel representation of `K_s`** for one pair of measures. -/
theorem hk_fr_rep (s : ℝ) (μ ν : Measure ℂ) (h : HkGood μ ν) :
    IntegrableOn (fun t => ∫ z, hkFr s z t ∂(μ.prod ν)) (Ioi 0) ∧
      ∫ t in Ioi 0, ∫ z, hkFr s z t ∂(μ.prod ν) = kernelCov (hkK s) μ ν := by
  obtain ⟨hμ, hν, hne, hl1, hl2⟩ := h
  have hd1 : Measurable fun z : ℂ × ℂ => ‖z.1 - z.2‖ := by fun_prop
  have hd2 : Measurable fun z : ℂ × ℂ => ‖z.1 - conj z.2‖ :=
    (measurable_fst.sub (Complex.continuous_conj.measurable.comp measurable_snd)).norm
  have i1 := hk_fr_integrable (μ.prod ν) _ hd1 (hne.mono fun z hz => hz.1) hl1
  have i2 := hk_fr_integrable (μ.prod ν) _ hd2 (hne.mono fun z hz => hz.2) hl2
  have hFi : Integrable (fun q : ℝ × (ℂ × ℂ) => hkFr s q.2 q.1)
      ((volume.restrict (Ioi 0)).prod (μ.prod ν)) := i1.add (i2.const_mul s)
  refine ⟨hFi.integral_prod_left, ?_⟩
  have hK : Integrable (fun z : ℂ × ℂ => hkK s z.1 z.2) (μ.prod ν) := by
    simp only [hkK]; exact hl1.neg.sub (hl2.const_mul s)
  rw [integral_integral_swap (f := fun t z => hkFr s z t) hFi, kernelCov,
    ← integral_prod _ hK]
  refine integral_congr_ae ?_
  filter_upwards [hne] with z hz
  simp only [hkFr, hkK]
  rw [integral_add (frIntegrand_integrableOn hz.1) ((frIntegrand_integrableOn hz.2).const_mul s),
    integral_const_mul, frIntegrand_integral hz.1, frIntegrand_integral hz.2]
  ring

/-! ### Features of pairs -/

/-- The scale-`t` kernel of two pairs. -/
def hkKerT (s : ℝ) (p q : Measure ℂ × Measure ℂ) (t : ℝ) : ℝ :=
  ∫ z, hkFr s z t ∂(p.1.prod q.1) - ∫ z, hkFr s z t ∂(p.1.prod q.2) -
    ∫ z, hkFr s z t ∂(p.2.prod q.1) + ∫ z, hkFr s z t ∂(p.2.prod q.2)

lemma hk_feat_mul_integral (s : ℝ) (hs : s * s = 1) (p q : Measure ℂ × Measure ℂ)
    [IsFiniteMeasure p.1] [IsFiniteMeasure p.2] [IsFiniteMeasure q.1] [IsFiniteMeasure q.2]
    (hbal : (1 + s) * (p.1.real univ - p.2.real univ) = 0) {t : ℝ} (ht : 0 < t) :
    ∫ ξ, hkFeat s p (t, ξ) * hkFeat s q (t, ξ) ∂(stdGaussian ℂ) = hkKerT s p q t := by
  have hfun : ∀ ξ, hkFeat s p (t, ξ) * hkFeat s q (t, ξ) = (2 * t)⁻¹ *
      (((hkA s t p.1 ξ * hkA s t q.1 ξ - hkA s t p.1 ξ * hkA s t q.2 ξ) -
        hkA s t p.2 ξ * hkA s t q.1 ξ) + hkA s t p.2 ξ * hkA s t q.2 ξ) := by
    intro ξ
    simp only [hkFeat]
    have h2 : (Real.sqrt (2 * t))⁻¹ * (Real.sqrt (2 * t))⁻¹ = (2 * t)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    rw [← h2]
    ring
  simp_rw [hfun]
  have j11 := hk_integrable_hkA_mul s t p.1 q.1
  have j12 := hk_integrable_hkA_mul s t p.1 q.2
  have j21 := hk_integrable_hkA_mul s t p.2 q.1
  have j22 := hk_integrable_hkA_mul s t p.2 q.2
  have k1 : Integrable (fun ξ => hkA s t p.1 ξ * hkA s t q.1 ξ -
      hkA s t p.1 ξ * hkA s t q.2 ξ) (stdGaussian ℂ) := j11.sub j12
  have k2 : Integrable (fun ξ => hkA s t p.1 ξ * hkA s t q.1 ξ -
      hkA s t p.1 ξ * hkA s t q.2 ξ - hkA s t p.2 ξ * hkA s t q.1 ξ) (stdGaussian ℂ) :=
    k1.sub j21
  rw [integral_const_mul, integral_add k2 j22, integral_sub k1 j21, integral_sub j11 j12,
    hkA_mul_integral s t hs, hkA_mul_integral s t hs, hkA_mul_integral s t hs,
    hkA_mul_integral s t hs, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have e11 := hk_pair_div_eq s t p.1 q.1
  have e12 := hk_pair_div_eq s t p.1 q.2
  have e21 := hk_pair_div_eq s t p.2 q.1
  have e22 := hk_pair_div_eq s t p.2 q.2
  rw [div_eq_inv_mul] at e11 e12 e21 e22
  simp only [hkKerT]
  have ht0 : t ≠ 0 := ht.ne'
  have hres : (1 + s) * (Real.exp (-1 / (4 * t ^ 2)) / t) *
      (p.1.real univ * q.1.real univ - p.1.real univ * q.2.real univ -
        p.2.real univ * q.1.real univ + p.2.real univ * q.2.real univ) = 0 := by
    have : (1 + s) * (Real.exp (-1 / (4 * t ^ 2)) / t) *
      (p.1.real univ * q.1.real univ - p.1.real univ * q.2.real univ -
        p.2.real univ * q.1.real univ + p.2.real univ * q.2.real univ) =
        ((1 + s) * (p.1.real univ - p.2.real univ)) * (Real.exp (-1 / (4 * t ^ 2)) / t) *
          (q.1.real univ - q.2.real univ) := by ring
    rw [this, hbal, zero_mul, zero_mul]
  have key : (2 * t)⁻¹ * (((2 * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.1.prod q.1) -
      2 * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.1.prod q.2)) -
      2 * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.2.prod q.1)) +
      2 * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.2.prod q.2)) =
      t⁻¹ * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.1.prod q.1) -
      t⁻¹ * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.1.prod q.2) -
      t⁻¹ * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.2.prod q.1) +
      t⁻¹ * ∫ z, (gK t z.1 z.2 + s * gK t z.1 (conj z.2)) ∂(p.2.prod q.2) := by
    field_simp
  rw [key, e11, e12, e21, e22]
  linear_combination hres

lemma hk_kerT_rep (s : ℝ) (p q : Measure ℂ × Measure ℂ) (h11 : HkGood p.1 q.1)
    (h12 : HkGood p.1 q.2) (h21 : HkGood p.2 q.1) (h22 : HkGood p.2 q.2) :
    IntegrableOn (hkKerT s p q) (Ioi 0) ∧
      ∫ t in Ioi 0, hkKerT s p q t = kernelCov2 (hkK s) p q := by
  obtain ⟨i11, e11⟩ := hk_fr_rep s _ _ h11
  obtain ⟨i12, e12⟩ := hk_fr_rep s _ _ h12
  obtain ⟨i21, e21⟩ := hk_fr_rep s _ _ h21
  obtain ⟨i22, e22⟩ := hk_fr_rep s _ _ h22
  have k1 : IntegrableOn (fun t => ∫ z, hkFr s z t ∂(p.1.prod q.1) -
      ∫ z, hkFr s z t ∂(p.1.prod q.2)) (Ioi 0) := i11.sub i12
  have k2 : IntegrableOn (fun t => ∫ z, hkFr s z t ∂(p.1.prod q.1) -
      ∫ z, hkFr s z t ∂(p.1.prod q.2) - ∫ z, hkFr s z t ∂(p.2.prod q.1)) (Ioi 0) := k1.sub i21
  refine ⟨k2.add i22, ?_⟩
  unfold hkKerT
  rw [integral_add k2 i22, integral_sub k1 i21, integral_sub i11 i12, e11, e12, e21, e22, kernelCov2]

theorem hk_memLp (s : ℝ) (hs : s * s = 1) (p : Measure ℂ × Measure ℂ) (h11 : HkGood p.1 p.1)
    (h12 : HkGood p.1 p.2) (h21 : HkGood p.2 p.1) (h22 : HkGood p.2 p.2)
    (hbal : (1 + s) * (p.1.real univ - p.2.real univ) = 0) :
    MemLp (hkFeat s p) 2 hkM := by
  have := h11.1
  have := h22.1
  have hm := measurable_hkFeat s p
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable, hkM,
    integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable]
  have hbd : ∀ t, Integrable (fun ξ => hkFeat s p (t, ξ) ^ 2) (stdGaussian ℂ) := by
    intro t
    have e : (fun ξ => hkFeat s p (t, ξ) ^ 2) = fun ξ => (Real.sqrt (2 * t))⁻¹ ^ 2 *
        ((hkA s t p.1 ξ * hkA s t p.1 ξ - hkA s t p.1 ξ * hkA s t p.2 ξ) -
          (hkA s t p.2 ξ * hkA s t p.1 ξ - hkA s t p.2 ξ * hkA s t p.2 ξ)) := by
      funext ξ; simp only [hkFeat]; ring
    rw [e]
    exact (((hk_integrable_hkA_mul s t _ _).sub (hk_integrable_hkA_mul s t _ _)).sub
      ((hk_integrable_hkA_mul s t _ _).sub (hk_integrable_hkA_mul s t _ _))).const_mul _
  refine ⟨ae_of_all _ hbd, ?_⟩
  refine (hk_kerT_rep s p p h11 h12 h21 h22).1.congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hnn : ∀ ξ, ‖hkFeat s p (t, ξ) ^ 2‖ = hkFeat s p (t, ξ) * hkFeat s p (t, ξ) := by
    intro ξ; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  simp_rw [hnn]
  exact (hk_feat_mul_integral s hs p p hbal ht).symm

theorem hk_integral_mul (s : ℝ) (hs : s * s = 1) (p q : Measure ℂ × Measure ℂ)
    (h11 : HkGood p.1 q.1) (h12 : HkGood p.1 q.2) (h21 : HkGood p.2 q.1) (h22 : HkGood p.2 q.2)
    (hbal : (1 + s) * (p.1.real univ - p.2.real univ) = 0)
    (hp : MemLp (hkFeat s p) 2 hkM) (hq : MemLp (hkFeat s q) 2 hkM) :
    ∫ x, hkFeat s p x * hkFeat s q x ∂hkM = kernelCov2 (hkK s) p q := by
  have := h11.1
  have := h11.2.1
  have := h22.1
  have := h22.2.1
  have hint : Integrable (fun x => hkFeat s p x * hkFeat s q x) hkM := hp.integrable_mul hq
  rw [hkM] at hint ⊢
  rw [integral_prod _ hint, ← (hk_kerT_rep s p q h11 h12 h21 h22).2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact hk_feat_mul_integral s hs p q hbal ht

end QuantumZipper.GFFExist
