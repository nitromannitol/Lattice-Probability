/-
A fixed symmetric exponential (Laplace) reference law, with its moment hypotheses.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.ExpTail
import Mathlib.Probability.Moments.Variance

noncomputable section
namespace LatticeProb.ConvexOrder
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The symmetric unit-rate Laplace law. -/
def laplaceLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • ProbabilityTheory.expMeasure 1 +
    (2 : ℝ≥0∞)⁻¹ • (ProbabilityTheory.expMeasure 1).map (fun x : ℝ => -x)

/-- The Laplace law is a probability measure. -/
instance laplaceLaw_isProbability : IsProbabilityMeasure laplaceLaw := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  refine ⟨?_⟩
  simp [laplaceLaw, Measure.add_apply, Measure.map_apply measurable_neg]
  exact ENNReal.inv_two_add_inv_two

/-- A function is integrable for the Laplace law once both it and its reflection are
integrable for the unit exponential law. -/
theorem integrable_laplaceLaw {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Integrable f (ProbabilityTheory.expMeasure 1))
    (hn : Integrable (fun x : ℝ => f (-x)) (ProbabilityTheory.expMeasure 1)) :
    Integrable f laplaceLaw := by
  unfold laplaceLaw
  refine (hp.smul_measure (by norm_num)).add_measure ?_
  refine (Integrable.smul_measure ?_ (by norm_num))
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable).mpr hn

/-- The Laplace-law integral splits into the average of the unit-exponential integrals of `f`
and of its reflection. -/
theorem integral_laplaceLaw {f : ℝ → ℝ} (hf : Measurable f)
    (hp : Integrable f (ProbabilityTheory.expMeasure 1))
    (hn : Integrable (fun x : ℝ => f (-x)) (ProbabilityTheory.expMeasure 1)) :
    ∫ x, f x ∂laplaceLaw =
      (∫ x, f x ∂(ProbabilityTheory.expMeasure 1)) / 2 +
        (∫ x, f (-x) ∂(ProbabilityTheory.expMeasure 1)) / 2 := by
  have hm : Integrable f ((ProbabilityTheory.expMeasure 1).map (fun x : ℝ => -x)) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable).mpr hn
  rw [laplaceLaw, integral_add_measure (hp.smul_measure (by norm_num))
    (hm.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The Laplace law has an exponential moment at every rate below `1`. -/
theorem laplaceLaw_expMoment {θ : ℝ} (hθ : θ < 1) :
    Integrable (fun x : ℝ => Real.exp (θ * |x|)) laplaceLaw := by
  apply integrable_laplaceLaw (by fun_prop) (integrable_exp_abs_expMeasure_one hθ)
  simpa only [abs_neg] using integrable_exp_abs_expMeasure_one hθ

/-- The Laplace law has an integrable identity function. -/
theorem laplaceLaw_integrable_id : Integrable (id : ℝ → ℝ) laplaceLaw :=
  integrable_laplaceLaw measurable_id integrable_id_expMeasure_one integrable_id_expMeasure_one.neg

/-- The Laplace law has mean zero. -/
theorem laplaceLaw_mean : ∫ x, x ∂laplaceLaw = 0 := by
  rw [integral_laplaceLaw (f := fun x : ℝ => x) measurable_id
    integrable_id_expMeasure_one integrable_id_expMeasure_one.neg]
  rw [integral_neg (fun x : ℝ => x), integral_id_expMeasure_one]
  ring

/-- The unit exponential law has an integrable square. -/
theorem integrable_sq_expMeasure_one :
    Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.expMeasure 1) := by
  rw [integrable_expMeasure_one_iff]
  have h := Real.GammaIntegral_convergent (s := 3) (by norm_num)
  norm_num at h
  exact h

/-- The second moment of the unit exponential law is `2`. -/
theorem integral_sq_expMeasure_one :
    ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.expMeasure 1) = 2 := by
  rw [integral_expMeasure_one]
  have h := Real.Gamma_eq_integral (s := 3) (by norm_num)
  norm_num at h
  exact h.symm

/-- The Laplace law has an integrable square. -/
theorem laplaceLaw_integrable_sq : Integrable (fun x : ℝ => x ^ 2) laplaceLaw := by
  apply integrable_laplaceLaw (by fun_prop) integrable_sq_expMeasure_one
  simpa only [neg_sq] using integrable_sq_expMeasure_one

/-- The second moment of the Laplace law is `2`. -/
theorem laplaceLaw_second_moment : ∫ x : ℝ, x ^ 2 ∂laplaceLaw = 2 := by
  rw [integral_laplaceLaw (by fun_prop) integrable_sq_expMeasure_one
    (by simpa only [neg_sq] using integrable_sq_expMeasure_one)]
  simp only [neg_sq, integral_sq_expMeasure_one]
  norm_num

/-- The Laplace law has finite variance. -/
theorem laplaceLaw_evariance_lt_top : evariance (id : ℝ → ℝ) laplaceLaw < ⊤ := by
  exact evariance_lt_top ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    laplaceLaw_integrable_sq)

/-- The Laplace law has strictly positive variance. -/
theorem laplaceLaw_evariance_pos : 0 < evariance (id : ℝ → ℝ) laplaceLaw := by
  refine pos_iff_ne_zero.mpr fun hz => ?_
  have hae := (evariance_eq_zero_iff (X := (id : ℝ → ℝ)) (μ := laplaceLaw)
    measurable_id.aemeasurable).mp hz
  have hm : ∫ x, (id x : ℝ) ∂laplaceLaw = 0 := laplaceLaw_mean
  rw [hm] at hae
  have heq : (fun x : ℝ => x ^ 2) =ᵐ[laplaceLaw] fun _ => 0 := by
    filter_upwards [hae] with x hx
    change x = 0 at hx
    simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h := integral_congr_ae heq
  rw [laplaceLaw_second_moment, integral_zero] at h
  norm_num at h
end LatticeProb.ConvexOrder
