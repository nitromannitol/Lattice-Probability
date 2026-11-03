/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseKernel at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The heat kernels of DDDF's white-noise field (task P2-WN)

DDDF (arXiv:1904.08021, `tightness.tex` l. 289): for `0 < a < b`,
`φ_{a,b}(x) := √π ∫_{a²}^{b²} ∫_{ℝ²} p_{t/2}(x − y) W(dy, dt)`, `p_t(z) = (2πt)⁻¹ e^{−|z|²/(2t)}`.
Here: the kernel `phiKernel a b x (t, y) = 1_{[a²,b²]}(t) p_{t/2}(x − y)` and its `L²` class.

* `heatKernel_mul_heatKernel_eq`, `integral_heatKernel_mul_heatKernel`: the semigroup identity
  `∫ p_s(x,y) p_s(x',y) dy = p_{2s}(x,x')` (DDDF l. 287, "`p_{t/2} * p_{t/2} = p_t`"). Proof:
  completing the square (parallelogram law) and mathlib's Gaussian integral
  `GaussianFourier.integral_rexp_neg_mul_sq_norm` (own elementary proof of a standard fact).
* `integral_phiKernel_mul`: `∫∫ k_x k_{x'} = ∫_{[a²,b²]} p_t(x, x') dt` (Fubini).
* `inner_phiKernelL2`: the same as an inner product in `WNSpace`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- Completing the square: `p_s(x,y) p_s(x',y) = (2πs)⁻² e^{−|x−x'|²/(4s)} e^{−|y−m|²/s}`,
`m = (x + x')/2`. -/
lemma heatKernel_mul_heatKernel_eq (s : ℝ) (hs : 0 < s) (x x' y : ℂ) :
    heatKernel s x y * heatKernel s x' y =
      ((2 * Real.pi * s)⁻¹ ^ 2 * Real.exp (-‖x - x'‖ ^ 2 / (4 * s))) *
        Real.exp (-s⁻¹ * ‖y - (x + x') / 2‖ ^ 2) := by
  have hpar : ‖x - y‖ ^ 2 + ‖x' - y‖ ^ 2 = 2 * ‖y - (x + x') / 2‖ ^ 2 + ‖x - x'‖ ^ 2 / 2 := by
    have h1 : x - y = ((x + x') / 2 - y) + (x - x') / 2 := by ring
    have h2 : x' - y = ((x + x') / 2 - y) - (x - x') / 2 := by ring
    have h3 : ‖(x - x') / 2‖ = ‖x - x'‖ / 2 := by rw [norm_div]; simp
    have h4 : ‖(x + x') / 2 - y‖ = ‖y - (x + x') / 2‖ := norm_sub_rev _ _
    have hpl := parallelogram_law_with_norm ℝ ((x + x') / 2 - y) ((x - x') / 2)
    rw [← h1, ← h2, h3, h4] at hpl
    linear_combination hpl
  have hs' : s ≠ 0 := hs.ne'
  have key : -‖x - y‖ ^ 2 / (2 * s) + -‖x' - y‖ ^ 2 / (2 * s) =
      -‖x - x'‖ ^ 2 / (4 * s) + -s⁻¹ * ‖y - (x + x') / 2‖ ^ 2 := by
    rw [← add_div, ← neg_add, hpar]
    field_simp
    ring
  unfold heatKernel
  rw [mul_mul_mul_comm, ← Real.exp_add, key, Real.exp_add]
  ring

lemma integrable_heatKernel_mul_heatKernel (s : ℝ) (hs : 0 < s) (x x' : ℂ) :
    Integrable (fun y => heatKernel s x y * heatKernel s x' y) := by
  simp_rw [heatKernel_mul_heatKernel_eq s hs]
  exact ((integrable_rexp_neg_mul_sq_norm_complex (inv_pos.mpr hs)).comp_sub_right
    ((x + x') / 2)).const_mul _

/-- The semigroup identity `∫ p_s(x, y) p_s(x', y) dy = p_{2s}(x, x')`. -/
lemma integral_heatKernel_mul_heatKernel (s : ℝ) (hs : 0 < s) (x x' : ℂ) :
    ∫ y, heatKernel s x y * heatKernel s x' y = heatKernel (2 * s) x x' := by
  simp_rw [heatKernel_mul_heatKernel_eq s hs]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : ℂ => Real.exp (-s⁻¹ * ‖y‖ ^ 2)) ((x + x') / 2),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.mpr hs)]
  simp only [Complex.finrank_real_complex]
  norm_num
  unfold heatKernel
  have hs' : s ≠ 0 := hs.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [show -‖x - x'‖ ^ 2 / (2 * (2 * s)) = -‖x - x'‖ ^ 2 / (4 * s) by ring]
  field_simp

/-- DDDF's kernel `k_{a,b,x}(t, y) = 1_{[a²,b²]}(t) p_{t/2}(x − y)`. -/
def phiKernel (a b : ℝ) (x : ℂ) : ℝ × ℂ → ℝ :=
  (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator fun p => heatKernel (p.1 / 2) x p.2

lemma measurable_heatKernel_half (x : ℂ) :
    Measurable fun p : ℝ × ℂ => heatKernel (p.1 / 2) x p.2 := by
  unfold heatKernel; fun_prop

lemma measurable_phiKernel (a b : ℝ) (x : ℂ) : Measurable (phiKernel a b x) :=
  (measurable_heatKernel_half x).indicator (measurableSet_Icc.prod MeasurableSet.univ)

lemma phiKernel_mul (a b : ℝ) (x x' : ℂ) :
    (fun p => phiKernel a b x p * phiKernel a b x' p) =
      (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator
        (fun p : ℝ × ℂ => heatKernel (p.1 / 2) x p.2 * heatKernel (p.1 / 2) x' p.2) := by
  funext p
  unfold phiKernel
  by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) <;> simp [hp]

lemma continuousOn_heatKernel_time (a : ℝ) (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    ContinuousOn (fun t => heatKernel t x x') (Icc (a ^ 2) (b ^ 2)) := by
  unfold heatKernel
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht => lt_of_lt_of_le (by positivity) ht.1
  refine ContinuousOn.mul ?_ ?_
  · exact (continuousOn_const.mul continuousOn_id).inv₀ fun t ht =>
      (mul_pos (by positivity : (0:ℝ) < 2 * Real.pi) (hpos t ht)).ne'
  · exact Real.continuous_exp.comp_continuousOn
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun t ht =>
        (mul_pos two_pos (hpos t ht)).ne')

/-- Fubini for the kernels: `∫∫ k_x k_{x'} = ∫_{[a²,b²]} p_t(x, x') dt`, and integrability. -/
lemma integrable_integral_phiKernel_mul (a b : ℝ) (ha : 0 < a) (x x' : ℂ) :
    Integrable (fun p => phiKernel a b x p * phiKernel a b x' p) ∧
      ∫ p, phiKernel a b x p * phiKernel a b x' p =
        ∫ t in Icc (a ^ 2) (b ^ 2), heatKernel t x x' := by
  rw [phiKernel_mul]
  set F : ℝ × ℂ → ℝ := (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator
    (fun p : ℝ × ℂ => heatKernel (p.1 / 2) x p.2 * heatKernel (p.1 / 2) x' p.2) with hF
  have hpos : ∀ t ∈ Icc (a ^ 2) (b ^ 2), 0 < t := fun t ht => lt_of_lt_of_le (by positivity) ht.1
  have hsec : ∀ t, (fun y => F (t, y)) =
      (Icc (a ^ 2) (b ^ 2)).indicator (fun t => 1) t *
        (fun y => heatKernel (t / 2) x y * heatKernel (t / 2) x' y) := by
    intro t; funext y
    by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2) <;> simp [hF, ht]
  have hinner : ∀ t, ∫ y, F (t, y) = (Icc (a ^ 2) (b ^ 2)).indicator
      (fun t => heatKernel t x x') t := by
    intro t
    rw [hsec t]
    by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2)
    · simp only [ht, indicator_of_mem, one_mul]
      rw [integral_heatKernel_mul_heatKernel _ (by linarith [hpos t ht])]
      congr 1; ring
    · simp [ht]
  have hFm : Measurable F :=
    ((measurable_heatKernel_half x).mul (measurable_heatKernel_half x')).indicator
      (measurableSet_Icc.prod MeasurableSet.univ)
  have hnn : ∀ p, 0 ≤ F p := fun p => by
    simp only [hF]
    refine indicator_nonneg (fun q hq => ?_) p
    have := hpos q.1 (mem_prod.mp hq).1
    exact mul_nonneg (heatKernel_nonneg _ (by linarith) _ _) (heatKernel_nonneg _ (by linarith) _ _)
  have hI : IntegrableOn (fun t => heatKernel t x x') (Icc (a ^ 2) (b ^ 2)) :=
    (continuousOn_heatKernel_time a ha b x x').integrableOn_compact isCompact_Icc
  have hint : Integrable F := by
    rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
      integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · rw [hsec t]
      by_cases ht : t ∈ Icc (a ^ 2) (b ^ 2)
      · simp only [ht, indicator_of_mem, one_mul]
        exact integrable_heatKernel_mul_heatKernel _ (by linarith [hpos t ht]) x x'
      · simp [ht]
    · have : (fun t => ∫ y, ‖F (t, y)‖) = (Icc (a ^ 2) (b ^ 2)).indicator
          (fun t => heatKernel t x x') := by
        funext t
        rw [← hinner t]
        congr 1; funext y
        exact Real.norm_of_nonneg (hnn _)
      rw [this, integrable_indicator_iff measurableSet_Icc]
      exact hI
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod F hint]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Icc]

lemma memLp_phiKernel (a b : ℝ) (ha : 0 < a) (x : ℂ) :
    MemLp (phiKernel a b x) 2 (volume : Measure (ℝ × ℂ)) := by
  rw [memLp_two_iff_integrable_sq (measurable_phiKernel a b x).aestronglyMeasurable]
  simpa [sq] using (integrable_integral_phiKernel_mul a b ha x x).1

/-- The `L²` class of DDDF's kernel (junk `0` when `a ≤ 0`, where it is not square
integrable; deviation WN-3). -/
def phiKernelL2 (a b : ℝ) (x : ℂ) : WNSpace :=
  if h : 0 < a then (memLp_phiKernel a b h x).toLp _ else 0

lemma coeFn_phiKernelL2 (a b : ℝ) (ha : 0 < a) (x : ℂ) :
    (phiKernelL2 a b x : ℝ × ℂ → ℝ) =ᵐ[volume] phiKernel a b x := by
  rw [phiKernelL2, dite_eq_left_of_eq_true (eq_true ha)]
  exact MemLp.coeFn_toLp _

/-- `⟪k_{a,b,x}, k_{a,b,x'}⟫ = ∫_{[a²,b²]} p_t(x, x') dt`. -/
lemma inner_phiKernelL2 (a b : ℝ) (ha : 0 < a) (x x' : ℂ) :
    ⟪phiKernelL2 a b x, phiKernelL2 a b x'⟫ = ∫ t in Icc (a ^ 2) (b ^ 2), heatKernel t x x' := by
  rw [L2.inner_def, ← (integrable_integral_phiKernel_mul a b ha x x').2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_phiKernelL2 a b ha x, coeFn_phiKernelL2 a b ha x'] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

end WhiteNoise
end LQGMetric
