import LatticeProb.Analysis.Schauder.Continuum

/-!
# An approximate identity for bounded continuous functions

A family of nonnegative integrable kernels `K t` on `ℝ^d` of total mass one whose mass outside
every ball `{‖y‖ < δ}` tends to `0` as `t → 0⁺` convolves a bounded continuous function `g` to a
family converging pointwise to `g`.

Mathlib's `tendsto_integral_comp_smul_smul_of_integrable'` requires `g` to be integrable, which
fails for the periodic functions to which the heat kernel is applied; here `g` is only bounded and
continuous, and the assumption on the kernel is the tail condition itself.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- **Approximate identity for bounded continuous functions.** If `K t ≥ 0` is integrable with
`∫ K t = 1` for each `t > 0` and its mass `∫_{‖y‖ ≥ δ} K t` outside every ball tends to `0` as
`t → 0⁺`, then `∫ K t y * g (x - y) dy → g x` for every bounded continuous `g` and every `x`. -/
theorem tendsto_integral_mul_comp_sub_of_tails {K : ℝ → Euc d → ℝ}
    (hK0 : ∀ t, 0 < t → ∀ y, 0 ≤ K t y) (hKi : ∀ t, 0 < t → Integrable (K t))
    (hK1 : ∀ t, 0 < t → ∫ y, K t y = 1)
    (htail : ∀ δ, 0 < δ →
      Tendsto (fun t => ∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {g : Euc d → ℝ} (hgc : Continuous g) {A : ℝ} (hgA : ∀ y, |g y| ≤ A) (x : Euc d) :
    Tendsto (fun t => ∫ y, K t y * g (x - y)) (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hgA x)
  have hgx : Continuous fun y : Euc d => g (x - y) := hgc.comp (continuous_const.sub continuous_id)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hgx.continuousAt (ε / 2) (by positivity)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y < ε / (4 * (A + 1)) :=
    (htail δ hδ).eventually (gt_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 hts
  have ht : 0 < t := ht0
  have hset : MeasurableSet {y : Euc d | δ ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  -- the kernel against `g (x - ·)` and against the constant `g x` is integrable
  have h1 : Integrable (fun y => K t y * g (x - y)) :=
    (hKi t ht).mul_bdd hgx.aestronglyMeasurable (Eventually.of_forall fun y => hgA (x - y))
  have h2 : Integrable (fun y => K t y * g x) := (hKi t ht).mul_const _
  -- the error is the integral of `K t * (g (x - ·) - g x)`
  have herr : ∫ y, K t y * (g (x - y) - g x) = (∫ y, K t y * g (x - y)) - g x := by
    simp_rw [mul_sub]
    rw [integral_sub h1 h2, integral_mul_const, hK1 t ht, one_mul]
  -- pointwise bound by a small multiple of the kernel plus the kernel's tail
  have hG : Integrable
      (fun y => ε / 2 * K t y + 2 * A * {y : Euc d | δ ≤ ‖y‖}.indicator (K t) y) :=
    ((hKi t ht).const_mul _).add (((hKi t ht).indicator hset).const_mul _)
  have hpt : ∀ y, |K t y * (g (x - y) - g x)| ≤
      ε / 2 * K t y + 2 * A * {y : Euc d | δ ≤ ‖y‖}.indicator (K t) y := by
    intro y
    have hKy := hK0 t ht y
    rw [abs_mul, abs_of_nonneg hKy]
    by_cases hy : δ ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : Euc d | δ ≤ ‖y‖} from hy)]
      have : |g (x - y) - g x| ≤ 2 * A := by
        calc |g (x - y) - g x| ≤ |g (x - y)| + |g x| := abs_sub _ _
          _ ≤ 2 * A := by linarith [hgA (x - y), hgA x]
      nlinarith [mul_le_mul_of_nonneg_left this hKy]
    · rw [Set.indicator_of_notMem (show y ∉ {y : Euc d | δ ≤ ‖y‖} from hy)]
      have hyδ : dist y 0 < δ := by simpa using not_le.1 hy
      have h := hδ' hyδ
      rw [Real.dist_eq, sub_zero] at h
      rw [mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left h.le hKy |>.trans_eq (by ring)
  -- integrate the pointwise bound
  have hT0 : 0 ≤ ∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y :=
    setIntegral_nonneg hset fun y _ => hK0 t ht y
  have hGint : ∫ y, (ε / 2 * K t y + 2 * A * {y : Euc d | δ ≤ ‖y‖}.indicator (K t) y) =
      ε / 2 + 2 * A * ∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y := by
    rw [integral_add ((hKi t ht).const_mul _) (((hKi t ht).indicator hset).const_mul _),
      integral_const_mul, integral_const_mul, hK1 t ht, integral_indicator hset, mul_one]
  have hmain : |(∫ y, K t y * g (x - y)) - g x| ≤
      ε / 2 + 2 * A * ∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y := by
    rw [← herr, ← hGint]
    exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (Eventually.of_forall fun y => abs_nonneg _) hG (Eventually.of_forall hpt))
  have hT : (∫ y in {y : Euc d | δ ≤ ‖y‖}, K t y) * (4 * (A + 1)) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hts
  rw [Real.dist_eq]
  nlinarith [hT, hT0, hA, hmain]

end

end LatticeProb.Analysis.Schauder
