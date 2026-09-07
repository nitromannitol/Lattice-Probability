/-
An independent family of standard Gaussians indexed by an arbitrary set, and the
law of a finite linear combination of its coordinates.

The construction of every Gaussian process here starts from one object: the
product of standard Gaussians over an index set.  What is needed of it is the
law of `∑_{i ∈ s} c_i ω_i` for a finite `s`, and that is Fubini: reading the
family along the finitely many indices of `s` gives a finite product measure,
and the characteristic function of the linear combination is the product of the
characteristic functions, each a Gaussian one.
-/
import Mathlib
import LatticeProb.Prob.FiniteMarginal
import LatticeProb.Gauss.Limit

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Complex

open scoped ENNReal NNReal Topology

variable {ι : Type*}

/-- The law of an independent family of standard Gaussians indexed by `ι`. -/
def gaussLaw (ι : Type*) : Measure (ι → ℝ) := Measure.infinitePi fun _ : ι => gaussianReal 0 1

instance isProbabilityMeasure_gaussLaw : IsProbabilityMeasure (gaussLaw ι) := by
  unfold gaussLaw
  infer_instance

/-- A bounded complex exponential is integrable on a finite measure. -/
theorem integrable_cexp_mul_I {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {g : Ω → ℝ} (hg : Measurable g) (t : ℝ) :
    Integrable (fun ω => Complex.exp ((t : ℂ) * (g ω : ℂ) * Complex.I)) P := by
  have hm : Measurable (fun ω => Complex.exp ((t : ℂ) * (g ω : ℂ) * Complex.I)) :=
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hg).const_mul _).mul_const _)
  refine Integrable.mono' (integrable_const 1) hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [show (t : ℂ) * (g ω : ℂ) * Complex.I = ((t * g ω : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

/-- The finite linear combination `∑_{i ∈ s} c_i ω_i`. -/
def gaussSum (c : ι → ℝ) (s : Finset ι) (ω : ι → ℝ) : ℝ := ∑ i ∈ s, c i * ω i

theorem measurable_gaussSum (c : ι → ℝ) (s : Finset ι) : Measurable (gaussSum c s) := by
  unfold gaussSum
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

/-- **The law of a finite linear combination of independent standard
Gaussians.** -/
theorem map_gaussSum (c : ι → ℝ) (s : Finset ι) :
    (gaussLaw ι).map (gaussSum c s) = gaussianReal 0 (∑ i ∈ s, c i ^ 2).toNNReal := by
  classical
  haveI : IsProbabilityMeasure ((gaussLaw ι).map (gaussSum c s)) :=
    Measure.isProbabilityMeasure_map (measurable_gaussSum c s).aemeasurable
  set T : (ι → ℝ) → (↥s → ℝ) := fun ω i => ω (i : ι) with hT
  have hTmeas : Measurable T := measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)
  have hTmap : (gaussLaw ι).map T = Measure.pi fun _ : ↥s => (gaussianReal 0 1 : Measure ℝ) := by
    rw [gaussLaw]
    exact infinitePi_map_comp _ (fun i : ↥s => (i : ι)) Subtype.val_injective
  set G : (↥s → ℝ) → ℝ := fun x => ∑ i : ↥s, c (i : ι) * x i with hG
  have hGmeas : Measurable G :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  have hGT : G ∘ T = gaussSum c s := by
    funext ω
    rw [hG, gaussSum]
    exact Finset.sum_coe_sort s fun i => c i * ω i
  have hmap : (gaussLaw ι).map (gaussSum c s)
      = (Measure.pi fun _ : ↥s => (gaussianReal 0 1 : Measure ℝ)).map G := by
    rw [← hTmap, Measure.map_map hGmeas hTmeas, hGT]
  have hnn : (0 : ℝ) ≤ ∑ i ∈ s, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine Measure.ext_of_charFun ?_
  funext t
  have hfm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      ((gaussLaw ι).map (gaussSum c s)) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hfm2 : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      ((Measure.pi fun _ : ↥s => (gaussianReal 0 1 : Measure ℝ)).map G) := by
    rw [← hmap]; exact hfm
  rw [charFun_apply_real, hmap, integral_map hGmeas.aemeasurable hfm2]
  have hprod : ∀ x : ↥s → ℝ, Complex.exp ((t : ℂ) * (G x : ℂ) * Complex.I)
      = ∏ i : ↥s, Complex.exp (((t * c (i : ι) : ℝ) : ℂ) * (x i : ℂ) * Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    rw [hG]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod),
    integral_fintype_prod_eq_prod
      (fun (i : ↥s) (y : ℝ) => Complex.exp (((t * c (i : ι) : ℝ) : ℂ) * (y : ℂ) * Complex.I))]
  have hone : ∀ i : ↥s, ∫ y : ℝ, Complex.exp (((t * c (i : ι) : ℝ) : ℂ) * (y : ℂ) * Complex.I)
        ∂(gaussianReal 0 1)
      = Complex.exp (-((c (i : ι) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro i
    rw [← charFun_apply_real, charFun_gaussianReal]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl fun i _ => hone i, ← Complex.exp_sum, charFun_gaussianReal,
    Real.coe_toNNReal _ hnn]
  congr 1
  have hA : (((∑ i ∈ s, c i ^ 2 : ℝ)) : ℂ) = ∑ i : ↥s, ((c (i : ι) : ℝ) : ℂ) ^ 2 := by
    rw [← Finset.sum_coe_sort s fun i => c i ^ 2]
    push_cast
    rfl
  simp only [hA, Finset.sum_mul, Finset.sum_div, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

end LatticeProb

end
