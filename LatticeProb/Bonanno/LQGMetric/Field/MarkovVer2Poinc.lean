/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer2Poinc at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.BubbleHardy
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# A Poincaré inequality for functions vanishing on the unit circle (task P2-MKV, leaf (V))

`lintegral_ball_sq_le`: if `f : ℂ → ℝ` is `C¹` and vanishes on `∂𝔻`, then for `A ≥ 1`
`∫_{B(0,A)} f² ≤ A³ ∫_ℂ ‖Df‖²`.

This is the input for the variance bound of the zero-boundary GFF of an open set `V` with
`V ∩ ∂𝔻 = ∅` on bounded densities supported in `B(0,A)`: every `f ∈ C_c^∞(V)` vanishes on `∂𝔻`.

Proof (own elementary proof, the classical Friedrichs/Poincaré argument along rays): in polar
coordinates (mathlib `Complex.lintegral_comp_polarCoord_symm`), on each ray `g(r) = f(r e^{iθ})`
has `g(1) = 0`, so `g(r) = ∫_1^r g'` and Cauchy–Schwarz on the interval (QZ
`QuantumZipper.K3.interval_cauchy_schwarz_sq`) gives `r g(r)² ≤ A² ∫ s g'(s)² ds` for `0 < r < A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace LQGMetric
namespace MarkovVer2

/-- derivative of `f` along the ray through `u` -/
lemma hasDerivAt_ray {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (u : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => f ((t : ℂ) * u)) (fderiv ℝ f ((s : ℂ) * u) u) s := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u s := by
    simpa using ((hasDerivAt_id s).ofReal_comp).mul_const u
  have h2 : HasFDerivAt f (fderiv ℝ f ((s : ℂ) * u)) ((s : ℂ) * u) :=
    (hf.differentiable one_ne_zero _).hasFDerivAt
  exact h2.comp_hasDerivAt s h1

lemma continuous_ray_deriv {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (u : ℂ) :
    Continuous fun s : ℝ => fderiv ℝ f ((s : ℂ) * u) u :=
  ((hf.continuous_fderiv one_ne_zero).comp (Complex.continuous_ofReal.mul continuous_const)).clm_apply
    continuous_const

/-- one ray: `r g(r)² ≤ A² ∫_{s > 0} s ‖Df(s u)‖²` for `0 < r ≤ A`, `A ≥ 1`, `‖u‖ = 1`, `g(1) = 0` -/
lemma ray_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {u : ℂ} (hu : ‖u‖ = 1) (hf1 : f u = 0)
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hrA : r ≤ A) :
    ENNReal.ofReal (r * f ((r : ℂ) * u) ^ 2) ≤
      ENNReal.ofReal (A ^ 2) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s * ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2) := by
  set φ : ℝ → ℝ := fun s => fderiv ℝ f ((s : ℂ) * u) u
  have hφc : Continuous φ := continuous_ray_deriv hf u
  set a := min r 1
  set b := max r 1
  have hab : a ≤ b := min_le_max
  have ha0 : 0 < a := lt_min hr one_pos
  have hint : ∀ x y : ℝ, IntervalIntegrable φ volume x y := fun x y => hφc.intervalIntegrable x y
  have hFTC : ∀ x y : ℝ, ∫ s in x..y, φ s = f ((y : ℂ) * u) - f ((x : ℂ) * u) := fun x y =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_ray hf u s) (hint x y)
  have hg : f ((r : ℂ) * u) ^ 2 = (∫ s in a..b, φ s) ^ 2 := by
    rw [hFTC]
    have h1 : f (((1 : ℝ) : ℂ) * u) = 0 := by simpa using hf1
    rcases le_total r 1 with h | h
    · rw [show a = r from min_eq_left h, show b = 1 from max_eq_right h, h1]; ring
    · rw [show a = 1 from min_eq_right h, show b = r from max_eq_left h, h1]; ring
  have hCS := QuantumZipper.K3.interval_cauchy_schwarz_sq hφc hab
  -- pointwise weight comparison `r (b - a) ≤ A² s` on `[a, b]`
  have hw : ∀ s ∈ Icc a b, r * (b - a) * φ s ^ 2 ≤ A ^ 2 * (s * ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2) := by
    intro s hs
    have hφs : φ s ^ 2 ≤ ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2 := by
      have : |φ s| ≤ ‖fderiv ℝ f ((s : ℂ) * u)‖ := by
        have := (fderiv ℝ f ((s : ℂ) * u)).le_opNorm u
        rw [hu, mul_one, Real.norm_eq_abs] at this; exact this
      nlinarith [abs_nonneg (φ s), sq_abs (φ s)]
    have hs0 : 0 < s := ha0.trans_le hs.1
    have hk : r * (b - a) ≤ A ^ 2 * s := by
      rcases le_total r 1 with h | h
      · rw [show a = r from min_eq_left h, show b = 1 from max_eq_right h] at hs ⊢
        have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
        calc r * (1 - r) ≤ r := by nlinarith
          _ ≤ s := hs.1
          _ ≤ A ^ 2 * s := le_mul_of_one_le_left hs0.le hA2
      · rw [show a = 1 from min_eq_right h, show b = r from max_eq_left h] at hs ⊢
        calc r * (r - 1) ≤ A * A := by nlinarith
          _ = A ^ 2 * 1 := by ring
          _ ≤ A ^ 2 * s := mul_le_mul_of_nonneg_left hs.1 (sq_nonneg _)
    have h0 : 0 ≤ r * (b - a) := mul_nonneg hr.le (sub_nonneg.2 hab)
    calc r * (b - a) * φ s ^ 2 ≤ r * (b - a) * ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hφs h0
      _ ≤ A ^ 2 * s * ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hk (sq_nonneg _)
      _ = _ := by ring
  set G : ℝ → ℝ := fun s => s * ‖fderiv ℝ f ((s : ℂ) * u)‖ ^ 2
  have hGc : Continuous G := continuous_id.mul
    (((hf.continuous_fderiv one_ne_zero).comp (Complex.continuous_ofReal.mul continuous_const)).norm.pow 2)
  have hreal : r * f ((r : ℂ) * u) ^ 2 ≤ A ^ 2 * ∫ s in a..b, G s := by
    rw [hg]
    calc r * (∫ s in a..b, φ s) ^ 2 ≤ r * ((b - a) * ∫ s in a..b, φ s ^ 2) :=
          mul_le_mul_of_nonneg_left hCS hr.le
      _ = ∫ s in a..b, r * (b - a) * φ s ^ 2 := by
          rw [intervalIntegral.integral_const_mul]; ring
      _ ≤ ∫ s in a..b, A ^ 2 * G s :=
          intervalIntegral.integral_mono_on hab ((hφc.pow 2).const_mul _ |>.intervalIntegrable _ _)
            ((hGc.const_mul _).intervalIntegrable _ _) hw
      _ = A ^ 2 * ∫ s in a..b, G s := intervalIntegral.integral_const_mul _ _
  have hG0 : ∀ s, 0 ≤ s → 0 ≤ G s := fun s hs => mul_nonneg hs (sq_nonneg _)
  have hlin : ENNReal.ofReal (∫ s in a..b, G s) ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (G s) := by
    rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
      ((hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs =>
        hG0 s (ha0.le.trans hs.1.le)))]
    exact lintegral_mono_set (fun s hs => ha0.trans hs.1)
  calc ENNReal.ofReal (r * f ((r : ℂ) * u) ^ 2) ≤ ENNReal.ofReal (A ^ 2 * ∫ s in a..b, G s) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (∫ s in a..b, G s) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ _ := by gcongr

/-- unit vector `e^{iθ}` -/
def uvec (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

lemma norm_uvec (θ : ℝ) : ‖uvec θ‖ = 1 := by
  have : uvec θ = Complex.exp (θ * Complex.I) := by
    rw [uvec, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma continuous_uvec : Continuous uvec := by unfold uvec; fun_prop

/-- polar coordinates, `θ` outside -/
lemma lintegral_polar {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z = ∫⁻ θ in Ioo (-π) π, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r * F ((r : ℂ) * uvec θ) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod_symm]
  · simp only [Complex.polarCoord_symm_apply, smul_eq_mul, uvec]
  · refine (Measurable.mul ?_ ?_).aemeasurable
    · exact ENNReal.measurable_ofReal.comp measurable_fst
    · refine hF.comp ?_
      have : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
          fun p => (p.1 : ℂ) * uvec p.2 := by
        funext p; simp [uvec]
      rw [this]
      exact (Complex.continuous_ofReal.comp continuous_fst).mul
        (continuous_uvec.comp continuous_snd) |>.measurable

/-- **Poincaré inequality** for `C¹` functions vanishing on `∂𝔻`:
`∫_{B(0,A)} f² ≤ A³ ∫ ‖Df‖²` (`A ≥ 1`). -/
theorem lintegral_ball_sq_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (h0 : ∀ z ∈ sphere (0 : ℂ) 1, f z = 0) {A : ℝ} (hA : 1 ≤ A) :
    ∫⁻ z in ball (0 : ℂ) A, ENNReal.ofReal (f z ^ 2) ≤
      ENNReal.ofReal (A ^ 2) * ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
  have hfm : Measurable fun z => ENNReal.ofReal (f z ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hf.continuous.pow 2).measurable)
  have hdm : Measurable fun z => ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hf.continuous_fderiv one_ne_zero).norm.pow 2).measurable
  rw [← lintegral_indicator measurableSet_ball, lintegral_polar (hfm.indicator measurableSet_ball),
    lintegral_polar hdm, ← lintegral_const_mul _ ?meas]
  case meas =>
    exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
      ENNReal.ofReal p.2 * ENNReal.ofReal (‖fderiv ℝ f ((p.2 : ℂ) * uvec p.1)‖ ^ 2))
      ((ENNReal.measurable_ofReal.comp measurable_snd).mul (hdm.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          (continuous_uvec.comp continuous_fst)).measurable))
  refine setLIntegral_mono' measurableSet_Ioo fun θ _ => ?_
  set J := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
    ENNReal.ofReal (‖fderiv ℝ f ((r : ℂ) * uvec θ)‖ ^ 2)
  have hJ : J = ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s * ‖fderiv ℝ f ((s : ℂ) * uvec θ)‖ ^ 2) :=
    setLIntegral_congr_fun measurableSet_Ioi fun s hs => by
      rw [ENNReal.ofReal_mul (le_of_lt hs)]
  have hu1 : f (uvec θ) = 0 := h0 _ (mem_sphere_zero_iff_norm.2 (norm_uvec θ))
  calc ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        (ball (0 : ℂ) A).indicator (fun z => ENNReal.ofReal (f z ^ 2)) ((r : ℂ) * uvec θ)
      ≤ ∫⁻ r in Ioi (0 : ℝ), (Iio A).indicator (fun _ => ENNReal.ofReal (A ^ 2) * J) r := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        have hn : ‖(r : ℂ) * uvec θ‖ = r := by
          rw [norm_mul, norm_uvec, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hr]
        by_cases hrA : r < A
        · rw [indicator_of_mem (by rwa [mem_ball, dist_zero_right, hn]),
            indicator_of_mem (show r ∈ Iio A from hrA), ← ENNReal.ofReal_mul (le_of_lt hr), hJ]
          exact ray_bound hf (norm_uvec θ) hu1 hA hr hrA.le
        · rw [indicator_of_notMem (by rwa [mem_ball, dist_zero_right, hn]), mul_zero]
          exact bot_le
    _ = ENNReal.ofReal (A ^ 2) * J * ENNReal.ofReal A := by
        rw [lintegral_indicator measurableSet_Iio, setLIntegral_const, Measure.restrict_apply
          measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
    _ = _ := by ring

end MarkovVer2
end LQGMetric
