import LatticeProb.Prob.JumpChain.MarkovProperty
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Bounded increments from displacement tails

A displacement tail controls the truncated metric increment under the transition kernel,
conditionally on the natural past, and after averaging over the history law.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section

variable {S E : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MetricSpace E]

/-- Splitting at a positive distance bounds a truncated kernel increment by its tail. -/
theorem kernel_increment_le (rates : BoundedRates S) (ι : S → E)
    (β : ℝ≥0 → ℝ → ℝ)
    (hβ : ∀ u x η, 0 < η → rates.transitionKernel u x
      {y | η < dist (ι y) (ι x)} ≤ ENNReal.ofReal (β u η))
    (u : ℝ≥0) (x : S) {a : ℝ} (ha : 0 < a) :
    (∑' y, rates.transitionKernel u x {y} *
      ENNReal.ofReal (min (dist (ι y) (ι x)) 1)) ≤
      ENNReal.ofReal a + ENNReal.ofReal (β u a) := by
  classical
  let A : Set S := {y | a < dist (ι y) (ι x)}
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hpoint (y : S) : ENNReal.ofReal (min (dist (ι y) (ι x)) 1) ≤
      ENNReal.ofReal a + A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
        (by simpa only [ENNReal.ofReal_one] using
          (le_add_self : (1 : ℝ≥0∞) ≤ ENNReal.ofReal a + 1))
    · rw [Set.indicator_of_notMem hy, add_zero]
      exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (le_of_not_gt hy))
  calc
    _ = ∫⁻ y, ENNReal.ofReal (min (dist (ι y) (ι x)) 1)
        ∂rates.transitionKernel u x := by
      rw [lintegral_countable']
      simp only [mul_comm]
    _ ≤ ∫⁻ y, ENNReal.ofReal a + A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y
        ∂rates.transitionKernel u x := lintegral_mono hpoint
    _ = ENNReal.ofReal a + rates.transitionKernel u x A := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_indicator_const hA]
      simp only [measure_univ, mul_one, one_mul]
    _ ≤ _ := add_le_add le_rfl (hβ u x a ha)

/-- The conditional truncated increment is bounded uniformly over the natural past. -/
theorem condLExp_increment_le (rates : BoundedRates S) (ι : S → E)
    (β : ℝ≥0 → ℝ → ℝ)
    (hβ : ∀ u x η, 0 < η → rates.transitionKernel u x
      {y | η < dist (ι y) (ι x)} ≤ ENNReal.ofReal (β u η))
    (μ : Measure S) [IsProbabilityMeasure μ] (t u : ℝ≥0)
    {a : ℝ} (ha : 0 < a) :
    (rates.regularLaw μ)⁻[fun h ↦ ENNReal.ofReal
      (min (dist (ι (h.position (t + u))) (ι (h.position t))) 1) | naturalSigma t]
      ≤ᵐ[rates.regularLaw μ] fun _ ↦ ENNReal.ofReal a + ENNReal.ofReal (β u a) := by
  have hm := rates.condLExp_markov μ t u
    (fun x y ↦ ENNReal.ofReal (min (dist (ι y) (ι x)) 1))
    (measurable_of_countable _)
  filter_upwards [hm] with h hh
  rw [hh]
  exact rates.kernel_increment_le ι β hβ u (h.position t) ha

/-- Averaging the Markov identity bounds increments at every deterministic starting time. -/
theorem lintegral_increment_le (rates : BoundedRates S) (ι : S → E)
    (β : ℝ≥0 → ℝ → ℝ)
    (hβ : ∀ u x η, 0 < η → rates.transitionKernel u x
      {y | η < dist (ι y) (ι x)} ≤ ENNReal.ofReal (β u η))
    (μ : Measure S) [IsProbabilityMeasure μ] (t u : ℝ≥0)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ h, ENNReal.ofReal
      (min (dist (ι (h.position (t + u))) (ι (h.position t))) 1)
      ∂rates.regularLaw μ) ≤ ENNReal.ofReal a + ENNReal.ofReal (β u a) := by
  have hm := rates.setLIntegral_markov μ t u univ MeasurableSet.univ
    (fun x y ↦ ENNReal.ofReal (min (dist (ι y) (ι x)) 1))
    (measurable_of_countable _)
  simp only [Measure.restrict_univ] at hm
  rw [hm]
  calc
    _ ≤ ∫⁻ _ : RegularHistory S, ENNReal.ofReal a + ENNReal.ofReal (β u a)
        ∂rates.regularLaw μ :=
      lintegral_mono fun h ↦ rates.kernel_increment_le ι β hβ u (h.position t) ha
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The cubic-root cutoff converts the displacement estimate into a vanishing bound.
The nonnegative constant is necessary for monotonicity in the time increment. -/
theorem increment_cutoff_le (β : ℝ≥0 → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hβ : ∀ u η, 0 < η → β u η ≤
      K * (u : ℝ) * (1 + Real.log (2 + η)) / η ^ 2)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (u : ℝ≥0) (hu : (u : ℝ) ≤ δ) :
    ENNReal.ofReal (δ ^ (1 / 3 : ℝ)) +
      ENNReal.ofReal (β u (δ ^ (1 / 3 : ℝ))) ≤
    ENNReal.ofReal (δ ^ (1 / 3 : ℝ) +
      K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) := by
  let a := δ ^ (1 / 3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hδ _
  have ha1 : a ≤ 1 := Real.rpow_le_one hδ.le hδ1.le (by norm_num)
  have hcube : a ^ 3 = δ := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have hlog : 1 + Real.log (2 + a) ≤ 1 + Real.log 3 := by
    exact add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))
  have hlog0 : 0 ≤ 1 + Real.log (2 + a) := by
    have := Real.log_nonneg (show 1 ≤ 2 + a by linarith)
    linarith
  have hb : β u a ≤ K * a * (1 + Real.log 3) := by
    calc
      β u a ≤ K * (u : ℝ) * (1 + Real.log (2 + a)) / a ^ 2 := hβ u a ha
      _ ≤ K * δ * (1 + Real.log (2 + a)) / a ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg a)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hK) hlog0
      _ ≤ K * δ * (1 + Real.log 3) / a ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (mul_nonneg hK hδ.le)) (sq_nonneg a)
      _ = K * a * (1 + Real.log 3) := by
        rw [← hcube]
        field_simp [ne_of_gt ha]
  have hc : 0 ≤ K * a * (1 + Real.log 3) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    positivity
  calc
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal (K * a * (1 + Real.log 3)) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal hb)
    _ = _ := (ENNReal.ofReal_add ha.le hc).symm

/-- Combining the tail and cutoff estimates gives the uniform conditional modulus. -/
theorem condLExp_increment_cutoff_le (rates : BoundedRates S) (ι : S → E)
    (β : ℝ≥0 → ℝ → ℝ)
    (htail : ∀ u x η, 0 < η → rates.transitionKernel u x
      {y | η < dist (ι y) (ι x)} ≤ ENNReal.ofReal (β u η))
    {K : ℝ} (hK : 0 ≤ K)
    (hβ : ∀ u η, 0 < η → β u η ≤
      K * (u : ℝ) * (1 + Real.log (2 + η)) / η ^ 2)
    (μ : Measure S) [IsProbabilityMeasure μ] (t u : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hu : (u : ℝ) ≤ δ) :
    (rates.regularLaw μ)⁻[fun h ↦ ENNReal.ofReal
      (min (dist (ι (h.position (t + u))) (ι (h.position t))) 1) | naturalSigma t]
      ≤ᵐ[rates.regularLaw μ] fun _ ↦ ENNReal.ofReal
        (δ ^ (1 / 3 : ℝ) + K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) := by
  filter_upwards [rates.condLExp_increment_le ι β htail μ t u
    (Real.rpow_pos_of_pos hδ (1 / 3 : ℝ))] with h hh
  exact hh.trans (increment_cutoff_le β hK hβ hδ hδ1 u hu)

/-- The deterministic cubic-root increment bound tends to zero from the right. -/
theorem tendsto_increment_cutoff (K : ℝ) :
    Filter.Tendsto (fun δ : ℝ ↦ δ ^ (1 / 3 : ℝ) +
      K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hp : Filter.Tendsto (fun δ : ℝ ↦ δ ^ (1 / 3 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc := Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using hp.add ((hp.const_mul K).mul_const (1 + Real.log 3))

end

end LatticeProb.JumpChain.BoundedRates
