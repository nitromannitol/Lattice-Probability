/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyCont at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Heat-kernel mollification of a continuous function (task P2-FHEAT, part 1)

GM (1.2), `literature/src/1905.00383/uniqueness-final.tex` l. 170–177: for a continuous `f`,
`f*_ε(z) := (f * p_{ε²/2})(z) = ∫ f(w) p_{ε²/2}(z,w) dw`; footnote l. 212: boundedness of `f`
makes the convolution finite. Here we check that the statement-layer definition `heatMollify`
(limit of truncated pairings, FOUNDATIONS §3) returns this classical convolution, and that it is
continuous in `z` for bounded continuous `f`.

Proofs: dominated convergence (mathlib `tendsto_integral_of_dominated_convergence`,
`continuous_of_dominated`) and the Gaussian integral `integral_rexp_neg_mul_sq_norm`. These are
standard facts (own elementary proofs of routine measure theory).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace LQGMetric

lemma heatKernel_nonneg (s : ℝ) (hs : 0 ≤ s) (z w : ℂ) : 0 ≤ heatKernel s z w := by
  unfold heatKernel; positivity

lemma heatKernel_eq_zero_center (s : ℝ) (z u : ℂ) :
    heatKernel s z (z + u) = heatKernel s 0 u := by
  simp [heatKernel, norm_neg]

lemma heatKernel_symm (s : ℝ) (z w : ℂ) : heatKernel s z w = heatKernel s w z := by
  simp [heatKernel, norm_sub_rev]

/-- `w ↦ exp(-b‖w‖²)` is integrable on `ℂ` (from mathlib's complex Gaussian). -/
lemma integrable_rexp_neg_mul_sq_norm_complex {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℂ => Real.exp (-b * ‖w‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

lemma integrable_heatKernel (s : ℝ) (hs : 0 < s) (z : ℂ) :
    Integrable (heatKernel s z) := by
  have h : Integrable (fun w : ℂ => Real.exp (-(2 * s)⁻¹ * ‖w‖ ^ 2)) :=
    integrable_rexp_neg_mul_sq_norm_complex (by positivity)
  have h2 := (h.comp_sub_left z).const_mul (2 * Real.pi * s)⁻¹
  refine h2.congr (Eventually.of_forall fun w => ?_)
  simp only [heatKernel]
  congr 2
  ring

/-- `∫ p_s(z, w) dw = 1`. -/
lemma integral_heatKernel (s : ℝ) (hs : 0 < s) (z : ℂ) : ∫ w, heatKernel s z w = 1 := by
  have h1 : ∫ w, heatKernel s z w = ∫ u, heatKernel s z (z + u) :=
    (integral_add_left_eq_self (fun w => heatKernel s z w) z).symm
  rw [h1]
  simp only [heatKernel_eq_zero_center]
  simp only [heatKernel, zero_sub, norm_neg]
  rw [integral_const_mul]
  have h2 : ∫ u : ℂ, Real.exp (-‖u‖ ^ 2 / (2 * s)) =
      ∫ u : ℂ, Real.exp (-(2 * s)⁻¹ * ‖u‖ ^ 2) := by
    congr 1; ext u; congr 1; ring
  rw [h2, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  simp only [Complex.finrank_real_complex]
  norm_num
  field_simp

lemma cutoff_eventually_one (w : ℂ) : ∀ᶠ n : ℕ in atTop, (cutoff n : ℂ → ℝ) w = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖w‖
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  apply (cutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  show ‖w‖ ≤ (n : ℝ) + 1
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma heatTrunc_apply (s : ℝ) (z : ℂ) (n : ℕ) (w : ℂ) :
    heatTrunc s z n w = heatKernel s z w * cutoff n w := rfl

lemma ofCont_apply_heat (f : C(ℂ, ℝ)) (φ : TestC) : ofCont f φ = ∫ w, φ w * f w := by
  unfold ofCont
  rw [Distribution.ofFun_apply (f.continuous.locallyIntegrable.locallyIntegrableOn _)]
  rfl

/-- The truncated pairings converge to the convolution whenever `p_s(z,·) f` is integrable. -/
lemma tendsto_ofCont_heatTrunc (f : C(ℂ, ℝ)) (s : ℝ) (hs : 0 < s) (z : ℂ)
    (hf : Integrable (fun w => heatKernel s z w * f w)) :
    Tendsto (fun n : ℕ => ofCont f (heatTrunc s z n)) atTop
      (𝓝 (∫ w, heatKernel s z w * f w)) := by
  simp only [ofCont_apply_heat, heatTrunc_apply]
  refine tendsto_integral_of_dominated_convergence (fun w => ‖heatKernel s z w * f w‖)
    (fun n => ?_) hf.norm (fun n => Eventually.of_forall fun w => ?_)
    (Eventually.of_forall fun w => ?_)
  · have : Continuous fun w => heatKernel s z w * (cutoff n : ℂ → ℝ) w * f w := by
      have hc := (heatTrunc s z n).continuous
      exact hc.mul f.continuous
    exact this.aestronglyMeasurable
  · have h0 := (cutoff n).nonneg (x := w)
    have h1 := (cutoff n).le_one (x := w)
    rw [show heatKernel s z w * (cutoff n : ℂ → ℝ) w * f w =
      (cutoff n : ℂ → ℝ) w * (heatKernel s z w * f w) by ring, norm_mul,
      Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [cutoff_eventually_one w] with n hn
    rw [hn, mul_one]

/-- `p_s(z,·) f` is integrable for bounded continuous `f` (GM footnote l. 212). -/
lemma integrable_heatKernel_mul_of_bdd (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M)
    (s : ℝ) (hs : 0 < s) (z : ℂ) : Integrable (fun w => heatKernel s z w * f w) := by
  refine Integrable.mono' ((integrable_heatKernel s hs z).mul_const M)
    ((by unfold heatKernel; fun_prop : Continuous fun w => heatKernel s z w * f w)
      |>.aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  · rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg s hs.le z w), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM w) (heatKernel_nonneg s hs.le z w)

/-- **GM (1.2) for continuous `f`**: `heatMollify ε f z = ∫ f(w) p_{ε²/2}(z,w) dw` whenever the
integrand is integrable. -/
theorem heatMollify_ofCont_of_integrable (f : C(ℂ, ℝ)) (ε : ℝ) (hε : ε ≠ 0) (z : ℂ)
    (hf : Integrable (fun w => heatKernel (ε ^ 2 / 2) z w * f w)) :
    heatMollify ε (ofCont f) z = ∫ w, f w * heatKernel (ε ^ 2 / 2) z w := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  simp_rw [mul_comm (f _)]
  exact (tendsto_ofCont_heatTrunc f _ hs z hf).limUnder_eq

/-- **GM (1.2) for bounded continuous `f`** (footnote l. 212). -/
theorem heatMollify_ofCont (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) (ε : ℝ) (hε : ε ≠ 0)
    (z : ℂ) : heatMollify ε (ofCont f) z = ∫ w, f w * heatKernel (ε ^ 2 / 2) z w :=
  heatMollify_ofCont_of_integrable f ε hε z
    (integrable_heatKernel_mul_of_bdd f M hM _ (by positivity) z)

/-- The convolution as an integral against the centred kernel: `∫ f(z+u) p_s(0,u) du`. -/
lemma integral_heatKernel_mul_eq_shift (f : C(ℂ, ℝ)) (s : ℝ) (z : ℂ) :
    ∫ w, f w * heatKernel s z w = ∫ u, f (z + u) * heatKernel s 0 u := by
  rw [← integral_add_left_eq_self (fun w => f w * heatKernel s z w) z]
  simp only [heatKernel_eq_zero_center]

/-- **Continuity of `f*_ε`** for bounded continuous `f`. -/
theorem continuous_heatMollify_ofCont (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) (ε : ℝ)
    (hε : ε ≠ 0) : Continuous (heatMollify ε (ofCont f)) := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have : heatMollify ε (ofCont f) =
      fun z => ∫ u, f (z + u) * heatKernel (ε ^ 2 / 2) 0 u := by
    funext z
    rw [heatMollify_ofCont f M hM ε hε z, integral_heatKernel_mul_eq_shift]
  rw [this]
  refine continuous_of_dominated (bound := fun u => M * heatKernel (ε ^ 2 / 2) 0 u)
    (fun z => ?_) (fun z => Eventually.of_forall fun u => ?_)
    ((integrable_heatKernel _ hs 0).const_mul M) (Eventually.of_forall fun u => ?_)
  · have : Continuous fun u => f (z + u) * heatKernel (ε ^ 2 / 2) 0 u := by
      unfold heatKernel; fun_prop
    exact this.aestronglyMeasurable
  · rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg _ hs.le 0 u), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (heatKernel_nonneg _ hs.le 0 u)
  · fun_prop

end LQGMetric
