import LatticeProb.Prob.BernsteinFactorialPredictable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Integrability of predictable products

A conditional expectation bound gives integrability of a product with a
nonnegative predictable factor.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- An integrable upper bound for the predictable factor times the conditional
expectation controls the corresponding product. -/
theorem integrable_mul_of_condExp_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {f g u : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hu : Integrable u μ)
    (hbound : ∀ᵐ ω ∂μ, f ω * (μ[g | m]) ω ≤ u ω) :
    Integrable (fun ω => f ω * g ω) μ := by
  let trunc : ℕ → Ω → ℝ := fun n ω => min (f ω) (n : ℝ)
  have htm : ∀ n, StronglyMeasurable[m] (trunc n) := by
    intro n
    exact (hf.measurable.min measurable_const).stronglyMeasurable
  have ht0 : ∀ n ω, 0 ≤ trunc n ω := by
    intro n ω
    exact le_min (hf0 ω) (Nat.cast_nonneg n)
  have htb : ∀ n ω, ‖trunc n ω‖ ≤ (n : ℝ) := by
    intro n ω
    rw [Real.norm_eq_abs, abs_of_nonneg (ht0 n ω)]
    exact min_le_right _ _
  have hti : ∀ n, Integrable (fun ω => trunc n ω * g ω) μ := by
    intro n
    exact hg.bdd_mul ((htm n).mono hm).aestronglyMeasurable
      (Eventually.of_forall (htb n))
  have hci : ∀ n, Integrable (fun ω => trunc n ω * (μ[g | m]) ω) μ := by
    intro n
    exact integrable_condExp.bdd_mul ((htm n).mono hm).aestronglyMeasurable
      (Eventually.of_forall (htb n))
  have hc0 : ∀ᵐ ω ∂μ, 0 ≤ (μ[g | m]) ω :=
    condExp_nonneg (Eventually.of_forall hg0)
  have hi : ∀ n, (∫ ω, trunc n ω * g ω ∂μ) ≤ ∫ ω, u ω ∂μ := by
    intro n
    have heq : (∫ ω, trunc n ω * g ω ∂μ) =
        ∫ ω, trunc n ω * (μ[g | m]) ω ∂μ := by
      rw [← integral_condExp hm (f := fun ω => trunc n ω * g ω)]
      exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left (htm n) (hti n) hg)
    rw [heq]
    apply integral_mono_ae (hci n) hu
    filter_upwards [hc0, hbound] with ω hcω hbω
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hcω).trans hbω
  have hmeas : AEStronglyMeasurable[m₀] (fun ω => f ω * g ω) μ :=
    ((hf.mono hm).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Eventually.of_forall fun ω => mul_nonneg (hf0 ω) (hg0 ω))).mp
  have hpoint : ∀ ω, ENNReal.ofReal (f ω * g ω) =
      ⨆ n : ℕ, ENNReal.ofReal (trunc n ω * g ω) := by
    intro ω
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_ge (f ω)
      refine (le_iSup (fun n : ℕ => ENNReal.ofReal (trunc n ω * g ω)) n).trans' ?_
      simp only [trunc, min_eq_left hn, le_refl]
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg0 ω))
  simp_rw [hpoint]
  rw [lintegral_iSup']
  · apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hti n)
      (Eventually.of_forall fun ω => mul_nonneg (ht0 n ω) (hg0 ω))]
    exact ENNReal.ofReal_le_ofReal (hi n)
  · intro n
    exact ((((htm n).mono hm).aestronglyMeasurable.mul
      hg.aestronglyMeasurable).aemeasurable.ennreal_ofReal)
  · exact Eventually.of_forall fun ω n k hnk => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_min_left _ (Nat.cast_le.mpr hnk)) (hg0 ω))

/-- The predictable product satisfies the same conditional bound. -/
theorem condExp_mul_le_of_condExp_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) {f g u : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (hu : Integrable u μ)
    (hbound : ∀ᵐ ω ∂μ, f ω * (μ[g | m]) ω ≤ u ω) :
    Integrable (fun ω => f ω * g ω) μ ∧ μ[fun ω => f ω * g ω | m] ≤ᵐ[μ] u := by
  have hfg := integrable_mul_of_condExp_le hm hf hf0 hg hg0 hu hbound
  refine ⟨hfg, ?_⟩
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hf hfg hg, hbound] with ω hω hbω
  exact hω.le.trans hbω

end LatticeProb
