import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import LatticeProb.Bonanno.LQGMetric.Field.WholePlaneLateral

/-!
# Integrals of the radial point against circle averages

For a whole-plane field with circle averages `h_s(0)` (Duplantier-Sheffield, arXiv:0808.1560, Section 3.1), the
radial point `radialPoint x = (|x|, 0)` of the circle-average parametrisation has the covariance kernel

  `radialCovKernel x s = log max(|x|, 1) + log max(s, 1) - log max(s, |x|)`,

which is the average over the circle `∂B_s(0)` of the whole-plane covariance `w ↦ wholePlaneCov x w`
(see `circleAverage_wholePlaneCov` for the same expression).

The file collects the real-analysis facts on this kernel and general versions of the integrals of the
radial point against circle averages: the pointwise covariance, the Fubini extensions to radial integrals and
to circle averages, and the integrability needed for those Fubini steps. The Gaussian input enters only through
explicit hypotheses (a covariance identity, a pairing identity, integrability and second-moment identities),
so the statements do not depend on how the field is constructed.
-/

namespace LatticeProb.RadialPointIntegrals

open MeasureTheory ProbabilityTheory Filter Set Real

/-- The covariance kernel of the radial point: `log max(|x|, 1) + log max(s, 1) - log max(s, |x|)`, the average
over the circle `∂B_s(0)` of the whole-plane covariance `w ↦ wholePlaneCov x w`. -/
noncomputable def radialCovKernel (x : ℂ) (s : ℝ) : ℝ :=
  Real.log (max ‖x‖ 1) + Real.log (max s 1) - Real.log (max s ‖x‖)

/-- For `u > 0`, the doubled logarithm of `max(u, 1)` minus `log u` equals `|log u|`. This identifies the second
moment `E[h_{|x|}(0)²] = |log |x||` of the radial point (Duplantier-Sheffield). -/
lemma two_log_max_sub_log {u : ℝ} (hu : 0 < u) :
    2 * Real.log (max u 1) - Real.log u = |Real.log u| := by
  rcases le_total u 1 with h | h
  · rw [max_eq_right h, Real.log_one, abs_of_nonpos (Real.log_nonpos hu.le h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (Real.log_nonneg h)]
    ring

/-- The product of two reals is bounded by half the sum of their squares. -/
lemma abs_mul_le_sq_add_sq_div_two (a b : ℝ) : ‖a * b‖ ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [Real.norm_eq_abs, abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith

/-- The zero set of `θ ↦ z + r e^{iθ}` is countable, hence null for Lebesgue measure on `(0, 2π]`. -/
lemma circleMap_ne_zero_ae {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))), circleMap z r θ ≠ 0 := by
  have hcount : Set.Countable {θ : ℝ | circleMap z r θ = 0} := by
    by_cases hne : ∃ θ₁ : ℝ, circleMap z r θ₁ = 0
    · obtain ⟨θ₁, h₁⟩ := hne
      refine (Set.countable_range (fun n : ℤ => θ₁ + (n : ℝ) * (2 * π))).mono ?_
      intro θ hθ
      have hθ' : circleMap z r θ = 0 := hθ
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have he : Complex.exp (θ * Complex.I) = Complex.exp (θ₁ * Complex.I) := by
        unfold circleMap at hθ' h₁
        apply mul_left_cancel₀ hr'
        linear_combination hθ' - h₁
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
      refine ⟨n, ?_⟩
      have hc : (θ : ℂ) = (θ₁ : ℂ) + (n : ℂ) * (2 * π) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        linear_combination hn
      exact_mod_cast hc.symm
    · exact Set.Countable.mono (fun θ hθ => absurd ⟨θ, hθ⟩ hne) Set.countable_empty
  exact ae_restrict_of_ae (ae_iff.2 (by simpa only [not_not] using hcount.measure_zero volume))

/-- The absolute logarithm of the modulus of a circle is integrable on `(0, 2π]` (circle integrability of
`log |w - 0|` on the circle of centre `z` and radius `r`). -/
lemma integrable_abs_log_circleMap (z : ℂ) (r : ℝ) :
    Integrable (fun θ : ℝ => |Real.log ‖circleMap z r θ‖|)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) := by
  have h1 : CircleIntegrable (fun w : ℂ => Real.log ‖w - 0‖) z r :=
    circleIntegrable_log_norm_sub_const (a := 0) (c := z) r
  have h2 : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap z r θ‖) volume 0 (2 * π) := by
    simpa [CircleIntegrable] using h1
  have h3 : Integrable (fun θ : ℝ => Real.log ‖circleMap z r θ‖)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 h2
  exact h3.abs

/-- The average of the radial covariance kernel over a circle centred at `0` depends only on the modulus of
its argument: it equals the kernel at any point of that circle. -/
lemma circleAverage_radialCovKernel_sphere {t : ℝ} (ht : 0 < t) (x : ℂ) (s : ℝ) (hx : ‖x‖ = t) :
    Real.circleAverage (fun y : ℂ => radialCovKernel y s) 0 t = radialCovKernel x s := by
  have hf : Set.EqOn (fun y : ℂ => radialCovKernel y s) (fun _ => radialCovKernel x s)
      (Metric.sphere (0 : ℂ) |t|) := by
    intro y hy
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos ht] at hy
    show radialCovKernel y s = radialCovKernel x s
    unfold radialCovKernel
    rw [hy, hx]
  rw [Real.circleAverage_congr_sphere hf, Real.circleAverage_const]

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Pointwise covariance of a circle average with the radial point. If the covariance of `hcirc ω s 0` with the
circle averages `hcirc ω t 0` is the average of `radialCovKernel · s` over `∂B_t(0)`, and `F` is a version of the
circle averages, then `E[h_s(0) F(radialPoint x)] = radialCovKernel x s` for `x ≠ 0`. -/
lemma integral_mul_radialPoint {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2) {s : ℝ}
    (hcov : ∀ t : ℝ, 0 < t → ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P =
      Real.circleAverage (fun x : ℂ => radialCovKernel x s) 0 t)
    {x : ℂ} (hx : x ≠ 0) :
    ∫ ω, hcirc ω s 0 * F ω (radialPoint x) ∂P = radialCovKernel x s := by
  have hae : (fun ω => hcirc ω s 0 * F ω (radialPoint x)) =ᵐ[P]
      (fun ω => hcirc ω s 0 * hcirc ω ‖x‖ 0) := by
    filter_upwards [hFae] with ω hω
    rw [hω (radialPoint x), radialPoint_fst_of_ne hx, radialPoint_snd]
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [integral_congr_ae hae, hcov ‖x‖ hpos, circleAverage_radialCovKernel_sphere hpos x s rfl]

/-- The radial integral of a test function against the circle averages agrees almost surely with its
expression through the radial point. -/
lemma radialIntegral_ae_eq {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2) (φ : ℂ → ℝ) :
    ∀ᵐ ω ∂P, ∫ x, φ x * hcirc ω ‖x‖ 0 = ∫ x, φ x * F ω (radialPoint x) := by
  filter_upwards [hFae] with ω hω
  apply integral_congr_ae
  have hae0 : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hae0] with x hx
  have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx
  rw [hω (radialPoint x), radialPoint_fst_of_ne hx0, radialPoint_snd]

/-- Fubini for the radial integral: if `E[Z · F(radialPoint x)] = radialCovKernel x s` for `x ≠ 0` and the
integrand `(ω, x) ↦ φ(x) F_ω(radialPoint x) Z(ω)` is integrable, then
`E[Z(ω) ∫ φ(x) h_{|x|}(0) dx] = ∫ φ(x) radialCovKernel x s dx`. -/
lemma integral_circle_mul_radialIntegral [IsProbabilityMeasure P] {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Ω → C(CircleParameter, ℝ)} {Z : Ω → ℝ} {φ : ℂ → ℝ} {s : ℝ}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    (hint : Integrable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2) * Z q.1) (P.prod volume))
    (hpair : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z ω * F ω (radialPoint x) ∂P = radialCovKernel x s) :
    ∫ ω, Z ω * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P = ∫ x, φ x * radialCovKernel x s := by
  have step1 : (fun ω => Z ω * ∫ x, φ x * hcirc ω ‖x‖ 0) =ᵐ[P]
      (fun ω => Z ω * ∫ x, φ x * F ω (radialPoint x)) := by
    filter_upwards [radialIntegral_ae_eq hFae φ] with ω hω
    rw [hω]
  rw [integral_congr_ae step1]
  have hI : Integrable (Function.uncurry fun (ω : Ω) (x : ℂ) =>
      Z ω * (φ x * F ω (radialPoint x))) (P.prod volume) := by
    refine hint.congr (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry]
    ring
  have hconst : ∀ ω, Z ω * ∫ x, φ x * F ω (radialPoint x) =
      ∫ x, Z ω * (φ x * F ω (radialPoint x)) := fun ω => (integral_const_mul _ _).symm
  simp_rw [hconst]
  rw [integral_integral_swap hI]
  have hae0 : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  refine integral_congr_ae ?_
  filter_upwards [hae0] with x hx
  have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx
  have hmul : ∀ ω, Z ω * (φ x * F ω (radialPoint x)) = φ x * (Z ω * F ω (radialPoint x)) :=
    fun ω => by ring
  simp_rw [hmul]
  rw [integral_const_mul, hpair x hx0]

/-- Integrability of `(ω, θ) ↦ Z(ω) · F_ω(radialPoint (circleMap z r θ))` against `P ⊗ dθ` on `(0, 2π]`, for an
`L²` variable `Z` and a family whose radial point has finite second moment equal to `|log |x||`. The radial factor
has `E[F²] = |log |z + r e^{iθ}||`, which is circle integrable. -/
lemma integrable_mul_radialPoint_circle [IsProbabilityMeasure P] {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F) {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P)
    (hFL2 : ∀ x : ℂ, x ≠ 0 → MemLp (fun ω => F ω (radialPoint x)) 2 P)
    (hsq : ∀ x : ℂ, x ≠ 0 → ∫ ω, F ω (radialPoint x) ^ 2 ∂P = |Real.log ‖x‖|)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : Ω × ℝ => Z q.1 * F q.1 (radialPoint (circleMap z r q.2)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmeasF : Measurable (fun q : Ω × ℝ =>
      F q.1 (radialPoint (circleMap z r q.2))) :=
    (measurable_circleVersion_joint hF).comp (measurable_fst.prodMk
      (measurable_radialPoint.comp ((continuous_circleMap z r).measurable.comp measurable_snd)))
  have hF2 : Integrable (fun q : Ω × ℝ =>
      F q.1 (radialPoint (circleMap z r q.2)) ^ 2)
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    rw [integrable_prod_iff' (hmeasF.pow_const 2).aestronglyMeasurable]
    constructor
    · filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      exact (hFL2 _ hθ).integrable_sq
    · refine (integrable_abs_log_circleMap z r).congr ?_
      filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      have := hsq _ hθ
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact this.symm
  have hZ2 : Integrable (fun q : Ω × ℝ => Z q.1 ^ 2)
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) := integrable_const 1
    have hprod := hZ.integrable_sq.mul_prod h1
    simpa using hprod
  refine Integrable.mono' ((hZ2.add hF2).div_const 2) ?_ (ae_of_all _ fun q => ?_)
  · exact (hZm.comp measurable_fst |>.mul hmeasF).aestronglyMeasurable
  · exact abs_mul_le_sq_add_sq_div_two _ _

/-- Fubini for the radial circle average: `E[Z · avg_{∂B_r(z)} h_{|·|}(0)] = avg_{∂B_r(z)} radialCovKernel · s`,
under the pairing identity `E[Z · F(radialPoint x)] = radialCovKernel x s` for `x ≠ 0` and the integrability of
`(ω, θ) ↦ Z(ω) F_ω(radialPoint (circleMap z r θ))`. -/
lemma integral_circle_mul_circleAverage [IsProbabilityMeasure P] {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Ω → C(CircleParameter, ℝ)} {Z : Ω → ℝ} {s : ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    (hint : Integrable (fun q : Ω × ℝ => Z q.1 * F q.1 (radialPoint (circleMap z r q.2)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))))
    (hpair : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z ω * F ω (radialPoint x) ∂P = radialCovKernel x s) :
    ∫ ω, Z ω * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P =
      Real.circleAverage (fun x : ℂ => radialCovKernel x s) z r := by
  have hI : Integrable (Function.uncurry fun (ω : Ω) (θ : ℝ) =>
      Z ω * F ω (radialPoint (circleMap z r θ)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    refine hint.congr (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry]
  have step1 : ∀ᵐ ω ∂P, (∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0) =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π), F ω (radialPoint (circleMap z r θ)) := by
    filter_upwards [hFae] with ω hω
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
  have step3 : (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
      (∫ ω, Z ω * F ω (radialPoint (circleMap z r θ)) ∂P)) =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π), radialCovKernel (circleMap z r θ) s := by
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    exact hpair _ hθ
  simp only [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  calc ∫ ω, Z ω * ((2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0) ∂P
      = ∫ ω, (2 * π)⁻¹ * (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          Z ω * F ω (radialPoint (circleMap z r θ))) ∂P := by
        apply integral_congr_ae
        filter_upwards [step1] with ω hω
        rw [hω, integral_const_mul]
        ring
    _ = (2 * π)⁻¹ * ∫ ω, (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          Z ω * F ω (radialPoint (circleMap z r θ))) ∂P := by
        rw [integral_const_mul]
    _ = (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          (∫ ω, Z ω * F ω (radialPoint (circleMap z r θ)) ∂P) := by
        rw [integral_integral_swap hI]
    _ = (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π), radialCovKernel (circleMap z r θ) s := by
        rw [step3]

end Integrals

end LatticeProb.RadialPointIntegrals
