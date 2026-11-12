import Mathlib

/-!
# Bounded Lipschitz integrals and the Lévy-Prokhorov distance

If two probability measures are at Lévy-Prokhorov distance less than `ε`, the integrals of a bounded
Lipschitz function against them differ by at most `(L + 2 ‖f‖) ε`, where `L` is a Lipschitz constant of
`f`. This is the quantitative form of the fact that the Prokhorov topology is finer than the weak
topology, and it is what allows one to pass from uniform closeness of laws in the Prokhorov metric to
uniform closeness of expectations of bounded Lipschitz functionals.

## Main results

* `integral_le_add_of_levyProkhorovEDist_lt_of_lipschitz`: for `f ≥ 0` bounded and `L`-Lipschitz,
  `∫ f dμ ≤ ∫ f dν + (L + ‖f‖) ε`.
* `abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_lipschitz`: for bounded `L`-Lipschitz `f`,
  `|∫ f dμ - ∫ f dν| ≤ (L + 2 ‖f‖) ε`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric BoundedContinuousFunction
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

omit [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] in
/-- The measure of a decreasing family of sets is interval integrable. -/
lemma integrableOn_measureReal_of_antitone (ν : Measure Ω) [IsFiniteMeasure ν] (S : ℝ → Set Ω)
    (hS : Antitone S) (a b : ℝ) : IntegrableOn (fun t => ν.real (S t)) (Ioc a b) := by
  apply Measure.integrableOn_of_bounded (M := ν.real univ) measure_Ioc_lt_top.ne
  · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
    exact fun _ _ hst => measure_mono (hS hst)
  · apply Filter.Eventually.of_forall <| fun t => ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact ENNReal.toReal_mono (by finiteness) <| measure_mono (subset_univ _)

/-- **One-sided bound for nonnegative bounded Lipschitz functions.** If
`levyProkhorovEDist μ ν < ε`, `f ≥ 0` is bounded continuous and `L`-Lipschitz, then
`∫ f dμ ≤ ∫ f dν + (L + ‖f‖) ε`. -/
theorem integral_le_add_of_levyProkhorovEDist_lt_of_lipschitz (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (hf0 : ∀ x, 0 ≤ f x)
    {L : ℝ≥0} (hL : LipschitzWith L f) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν + (L + ‖f‖) * ε := by
  have h1 := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν f
    (Filter.Eventually.of_forall hf0)
  set c : ℝ := L * ε with hc
  have hc0 : 0 ≤ c := by positivity
  -- thickening of `{t ≤ f}` lies in `{t ≤ f + c}`
  have hsub : ∀ t : ℝ, thickening ε {a | t ≤ f a} ⊆ {a | t ≤ f a + c} := by
    intro t a ha
    obtain ⟨b, hb, hab⟩ := mem_thickening_iff.1 ha
    have h2 : dist (f a) (f b) ≤ L * dist a b := hL.dist_le_mul a b
    have h3 : L * dist a b ≤ L * ε := mul_le_mul_of_nonneg_left hab.le (NNReal.coe_nonneg L)
    have h4 : f b - f a ≤ dist (f a) (f b) := by
      rw [Real.dist_eq]; linarith [neg_abs_le (f a - f b), le_abs_self (f b - f a), abs_sub_comm (f a) (f b)]
    have hb' : t ≤ f b := hb
    show t ≤ f a + c
    linarith
  have hanti1 : Antitone (fun t : ℝ => thickening ε {a | t ≤ f a}) :=
    fun s t hst => thickening_subset_of_subset ε (fun _ h => hst.trans h)
  have hanti2 : Antitone (fun t : ℝ => {a | t ≤ f a + c}) :=
    fun s t hst a ha => le_trans hst ha
  have h5 : ∫ t in Ioc 0 ‖f‖, ν.real (thickening ε {a | t ≤ f a})
      ≤ ∫ t in Ioc 0 ‖f‖, ν.real {a | t ≤ f a + c} :=
    setIntegral_mono (integrableOn_measureReal_of_antitone ν _ hanti1 0 ‖f‖)
      (integrableOn_measureReal_of_antitone ν _ hanti2 0 ‖f‖)
      (fun t => measureReal_mono (hsub t))
  -- layer cake for `f + c`
  have hint : Integrable (fun x => f x + c) ν := (f.integrable ν).add (integrable_const c)
  have hnn : 0 ≤ᵐ[ν] fun x => f x + c := Filter.Eventually.of_forall (fun x => by
    have := hf0 x; simp only [Pi.zero_apply]; linarith)
  have hbdd : (fun x => f x + c) ≤ᵐ[ν] fun _ => ‖f‖ + c := Filter.Eventually.of_forall (fun x => by
    have := f.norm_coe_le_norm x
    have := le_abs_self (f x)
    simp only [Real.norm_eq_abs] at *
    linarith)
  have hlay := Integrable.integral_eq_integral_Ioc_meas_le hint hnn hbdd
  have h6 : ∫ t in Ioc 0 ‖f‖, ν.real {a | t ≤ f a + c}
      ≤ ∫ t in Ioc 0 (‖f‖ + c), ν.real {a | t ≤ f a + c} := by
    apply setIntegral_mono_set (integrableOn_measureReal_of_antitone ν _ hanti2 0 (‖f‖ + c))
    · exact Filter.Eventually.of_forall (fun t => measureReal_nonneg)
    · exact Filter.Eventually.of_forall (Ioc_subset_Ioc_right (by linarith))
  have h7 : ∫ x, (f x + c) ∂ν = ∫ x, f x ∂ν + c := by
    rw [integral_add (f.integrable ν) (integrable_const c)]; simp
  have h8 : (L : ℝ) * ε + ‖f‖ * ε = (L + ‖f‖) * ε := by ring
  nlinarith [h1, h5, hlay, h6, h7, h8]

/-- **Bounded Lipschitz integrals and the Lévy-Prokhorov distance.** If
`levyProkhorovEDist μ ν < ε`, `f` is bounded continuous and `L`-Lipschitz, then
`|∫ f dμ - ∫ f dν| ≤ (L + 2 ‖f‖) ε`. -/
theorem abs_integral_sub_integral_le_of_levyProkhorovEDist_lt_of_lipschitz (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L f) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (L + 2 * ‖f‖) * ε := by
  -- shift to a nonnegative function
  let g : Ω →ᵇ ℝ := f + BoundedContinuousFunction.const Ω ‖f‖
  have hgx : ∀ x, g x = f x + ‖f‖ := fun x => by simp [g]
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    have h1 := f.norm_coe_le_norm x
    have h2 := neg_abs_le (f x)
    rw [hgx]
    simp only [Real.norm_eq_abs] at h1
    linarith
  have hgL : LipschitzWith L g := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [hgx, hgx, dist_add_right]
    exact hL.dist_le_mul x y
  have hgn : ‖g‖ ≤ 2 * ‖f‖ := by
    refine (norm_le (by positivity)).2 (fun x => ?_)
    have h1 := f.norm_coe_le_norm x
    rw [hgx]
    simp only [Real.norm_eq_abs] at h1 ⊢
    rw [abs_le] at h1
    rw [abs_le]
    constructor <;> linarith [norm_nonneg f]
  have hgint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → ∫ x, g x ∂ρ = ∫ x, f x ∂ρ + ‖f‖ := by
    intro ρ hρ
    have : (g : Ω → ℝ) = fun x => f x + ‖f‖ := funext hgx
    rw [this, integral_add (f.integrable ρ) (integrable_const _)]; simp
  have hμν' : levyProkhorovEDist ν μ < ENNReal.ofReal ε := by rwa [levyProkhorovEDist_comm]
  have a1 := integral_le_add_of_levyProkhorovEDist_lt_of_lipschitz μ ν hε hμν g hg0 hgL
  have a2 := integral_le_add_of_levyProkhorovEDist_lt_of_lipschitz ν μ hε hμν' g hg0 hgL
  rw [hgint μ inferInstance, hgint ν inferInstance] at a1 a2
  have hb : (L + ‖g‖) * ε ≤ (L + 2 * ‖f‖) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  rw [abs_le]
  constructor <;> linarith

end LatticeProb
