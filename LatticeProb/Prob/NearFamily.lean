/-
A family of integer-valued laws indexed by a real parameter, uniformly close to a fixed law
in mean, exponential moment and coupling distance, and the recentring shift of one such law
to the real line.

`NearFamily δ₀ ν θ M K` collects: each `ν δ` (`δ ∈ [0, δ₀]`) is a probability law on `ℤ`; the
mean of `ν δ` is `-δ`; `ν 0` is not a point mass; each `ν δ` has an exponential moment at rate
`θ` bounded uniformly by `M`; and `ν δ` is coupled to `ν 0` (for `δ ∈ (0, δ₀]`) with expected
absolute difference at most `K δ`. The integrability clause is not redundant: without it the
Bochner integral of a nonintegrable function is zero, and every family, however heavy tailed,
would otherwise satisfy the mean hypothesis vacuously.

`shiftLaw δ ν` is the image of `ν` under `k ↦ k + δ`, the one-site law of a family recentred to
have mean zero when `ν` has mean `-δ`. Its moments and exponential tail are controlled
uniformly in `δ` by those of `ν`, since `|k + δ| ≤ |k| + |δ|` costs only the factor
`e^{θ|δ|} ≤ e^{θδ₀}` on `[0, δ₀]`.

`integrable_intCast_of_exp` records that a finite exponential moment already forces an
integrable first moment, for a law on `ℤ`.

Moved from Parking-Sharpness (`Parking.NearFamily` in `Parking/Support/Near.lean`,
`Parking.shiftLaw` together with its lemmas in `Parking/Support/XiLaw.lean`, and
`Parking.integrable_intCast_of_exp` of `Parking/Support/MeanHorizonStep1.lean`).
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace LatticeProb.ConvexOrder

/-- The hypotheses of a near-family of one-site integer laws: uniform mean, non-degeneracy at
the base point, a uniformly bounded exponential moment, and a coupling to the base law with
expected distance controlled linearly in the parameter. -/
def NearFamily (δ₀ : ℝ) (ν : ℝ → Measure ℤ) (θ M K : ℝ) : Prop :=
  0 < δ₀ ∧ 0 < θ ∧
  (∀ δ ∈ Set.Icc 0 δ₀, IsProbabilityMeasure (ν δ)) ∧
  (∀ δ ∈ Set.Icc 0 δ₀, ∫ k, (k : ℝ) ∂(ν δ) = -δ) ∧
  (∀ k : ℤ, ν 0 {k} ≠ 1) ∧
  (∀ δ ∈ Set.Icc 0 δ₀, Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) ∧
    ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M) ∧
  (∀ δ ∈ Set.Ioc 0 δ₀, ∃ π : Measure (ℤ × ℤ), IsProbabilityMeasure π ∧
    π.map Prod.fst = ν δ ∧ π.map Prod.snd = ν 0 ∧
    ∫ p, |((p.1 : ℝ) - p.2)| ∂π ≤ K * δ)

/-- The one-site law of the recentred scenery: the image of `ν` under `k ↦ k + δ`. -/
def shiftLaw (δ : ℝ) (ν : Measure ℤ) : Measure ℝ := ν.map (fun k : ℤ => (k : ℝ) + δ)

/-- The shift map `k ↦ k + δ` is measurable. -/
theorem measurable_intShift (δ : ℝ) : Measurable (fun k : ℤ => (k : ℝ) + δ) :=
  (measurable_of_countable (fun k : ℤ => (k : ℝ))).add_const δ

/-- The shifted law is a probability measure. -/
instance isProbabilityMeasure_shiftLaw (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (shiftLaw δ ν) :=
  Measure.isProbabilityMeasure_map (measurable_intShift δ).aemeasurable

/-- The shift moves the mean by `δ`. -/
theorem integral_shiftLaw_id (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) :
    ∫ z, z ∂(shiftLaw δ ν) = (∫ k, ((k : ℝ)) ∂ν) + δ := by
  rw [shiftLaw, integral_map (f := fun z : ℝ => z) (measurable_intShift δ).aemeasurable
    (measurable_id : Measurable (fun z : ℝ => z)).aestronglyMeasurable]
  rw [integral_add hint (integrable_const δ), integral_const]
  simp

/-- The shifted law has an integrable identity function whenever the base law does. -/
theorem integrable_id_shiftLaw (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) :
    Integrable (id : ℝ → ℝ) (shiftLaw δ ν) := by
  rw [shiftLaw]
  rw [integrable_map_measure (measurable_id : Measurable (id : ℝ → ℝ)).aestronglyMeasurable
    (measurable_intShift δ).aemeasurable]
  exact (hint.add (integrable_const δ)).congr (Filter.Eventually.of_forall fun _ => rfl)

/-- Shifting by `δ` costs only the factor `e^{θ|δ|}` in the exponential-moment bound. -/
theorem exp_abs_shift_le (θ δ : ℝ) (hθ : 0 ≤ θ) (k : ℤ) :
    Real.exp (θ * |(k : ℝ) + δ|) ≤ Real.exp (θ * |δ|) * Real.exp (θ * |(k : ℝ)|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : |(k : ℝ) + δ| ≤ |(k : ℝ)| + |δ| := abs_add_le _ _
  nlinarith [h, hθ, abs_nonneg ((k : ℝ)), abs_nonneg δ]

/-- The exponential-moment integrand is almost everywhere strongly measurable, for any
measure. -/
theorem aesm_exp_abs (μ : Measure ℝ) (θ : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => Real.exp (θ * |z|)) μ :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable

/-- The shifted law has an integrable exponential-moment integrand whenever the base law
does. -/
theorem integrable_exp_abs_shiftLaw (θ δ : ℝ) (hθ : 0 ≤ θ) (ν : Measure ℤ)
    [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun z : ℝ => Real.exp (θ * |z|)) (shiftLaw δ ν) := by
  rw [shiftLaw, integrable_map_measure (aesm_exp_abs _ θ) (measurable_intShift δ).aemeasurable]
  refine Integrable.mono' (hint.const_mul (Real.exp (θ * |δ|)))
    (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact exp_abs_shift_le θ δ hθ k

/-- The exponential moment of the shifted law, uniformly in `δ` through `e^{θ|δ|}`. -/
theorem integral_exp_abs_shiftLaw_le (θ δ M : ℝ) (hθ : 0 ≤ θ) (ν : Measure ℤ)
    [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hM : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ M) :
    ∫ z, Real.exp (θ * |z|) ∂(shiftLaw δ ν) ≤ Real.exp (θ * |δ|) * M := by
  have hmap : ∫ z, Real.exp (θ * |z|) ∂(shiftLaw δ ν)
      = ∫ k, Real.exp (θ * |(k : ℝ) + δ|) ∂ν := by
    rw [shiftLaw, integral_map (measurable_intShift δ).aemeasurable (aesm_exp_abs _ θ)]
  rw [hmap]
  calc ∫ k, Real.exp (θ * |(k : ℝ) + δ|) ∂ν
      ≤ ∫ k, Real.exp (θ * |δ|) * Real.exp (θ * |(k : ℝ)|) ∂ν := by
        refine integral_mono ?_ (hint.const_mul _) (fun k => exp_abs_shift_le θ δ hθ k)
        refine Integrable.mono' (hint.const_mul (Real.exp (θ * |δ|)))
          (measurable_of_countable _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun k => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact exp_abs_shift_le θ δ hθ k
    _ = Real.exp (θ * |δ|) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := integral_const_mul _ _
    _ ≤ Real.exp (θ * |δ|) * M := mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)

/-- A finite exponential moment at a positive rate implies an integrable identity function,
for an integer-valued law. -/
theorem integrable_intCast_of_exp {θ : ℝ} (hθ : 0 < θ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun k : ℤ => ((k : ℝ))) ν := by
  refine Integrable.mono' (hint.const_mul θ⁻¹)
    (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs]
  have h1 : θ * |(k : ℝ)| ≤ Real.exp (θ * |(k : ℝ)|) := by
    have := Real.add_one_le_exp (θ * |(k : ℝ)|)
    linarith
  rw [inv_mul_eq_div, le_div_iff₀ hθ]
  linarith [h1]

end LatticeProb.ConvexOrder
