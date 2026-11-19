import Mathlib

/-!
# A continuous functional of a weakly convergent sequence is tight

Let `X n` be random elements of a topological space `E` whose laws converge weakly to a finite measure `ν`
(tested against bounded continuous functions), and let `Φ : E → ℝ` be continuous.  Then the real random variables
`Φ (X n)` are eventually tight from above: for every `r > 0` there is `R` with
`P[Φ (X n) > R] ≤ r` for all large `n`.

The proof compares the indicator of `{Φ > R + 1}` with the bounded continuous function
`max 0 (min 1 (Φ - R))`, whose `ν`-integral tends to `0` as `R → ∞` by dominated convergence.

* `LatticeProb.exists_forall_eventually_measure_lt_le_of_tendsto_integral`: the statement above.
-/

namespace LatticeProb

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

section Cutoff

variable {E : Type*} [TopologicalSpace E]

/-- The cutoff `max 0 (min 1 (x - R))` as a bounded continuous function of `Φ`. -/
noncomputable def cutoffComp (Φ : E → ℝ) (hΦ : Continuous Φ) (R : ℝ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max 0 (min 1 (Φ x - R)))
    (continuous_const.max (continuous_const.min (hΦ.sub continuous_const))) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [le_max_left 0 (min 1 (Φ x - R))],
        max_le zero_le_one (min_le_left _ _)⟩)

theorem cutoffComp_apply (Φ : E → ℝ) (hΦ : Continuous Φ) (R : ℝ) (x : E) :
    cutoffComp Φ hΦ R x = max 0 (min 1 (Φ x - R)) := rfl

end Cutoff

variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- **A continuous functional of a weakly convergent sequence of random elements is tight from above.**
If `∫ f (X n) dμ n → ∫ f dν` for every bounded continuous `f` on `E`, `ν` is a finite measure and `Φ : E → ℝ`
is continuous, then for every `r > 0` there is `R` with `μ n {Φ (X n) > R} ≤ r` eventually. -/
theorem exists_forall_eventually_measure_lt_le_of_tendsto_integral
    {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)] {X : ℕ → Ω → E}
    (hX : ∀ n, AEMeasurable (X n) (μ n)) {ν : Measure E} [IsFiniteMeasure ν]
    (hlaw : ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (X n ω) ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)))
    {Φ : E → ℝ} (hΦ : Continuous Φ) {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, ∀ᶠ n in atTop, μ n {ω | R < Φ (X n ω)} ≤ ENNReal.ofReal r := by
  -- the `ν`-integral of the cutoff tends to `0`
  have hν : Tendsto (fun N : ℕ => ∫ x, cutoffComp Φ hΦ (N : ℝ) x ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun (N : ℕ) x => cutoffComp Φ hΦ (N : ℝ) x) (f := fun _ => (0 : ℝ)) (bound := fun _ => 1)
      (fun N => (cutoffComp Φ hΦ (N : ℝ)).continuous.aestronglyMeasurable)
      (integrable_const _) (fun N => Eventually.of_forall fun x => by
        rw [cutoffComp_apply, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [le_max_left 0 (min 1 (Φ x - (N : ℝ)))],
          max_le zero_le_one (min_le_left _ _)⟩)
      (Eventually.of_forall fun x => by
        obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Φ x)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N₀] with N hN
        have hle : Φ x - (N : ℝ) ≤ 0 := by
          have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
          linarith
        show (0 : ℝ) = _
        rw [cutoffComp_apply, min_eq_right (by linarith), max_eq_left hle])
    simpa using h
  obtain ⟨N, hN⟩ := (hν.eventually (gt_mem_nhds hr)).exists
  refine ⟨(N : ℝ) + 1, ?_⟩
  filter_upwards [(hlaw (cutoffComp Φ hΦ (N : ℝ))).eventually (gt_mem_nhds hN)] with n hn
  set f := cutoffComp Φ hΦ (N : ℝ) with hf
  have hint : Integrable (fun ω => f (X n ω)) (μ n) :=
    Integrable.of_bound (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun ω => f.norm_coe_le_norm (X n ω))
  have hnn : 0 ≤ᵐ[μ n] fun ω => f (X n ω) := Eventually.of_forall fun ω => le_max_left _ _
  have hm := mul_meas_ge_le_integral_of_nonneg hnn hint 1
  have hsub : {ω | (N : ℝ) + 1 < Φ (X n ω)} ⊆ {ω | 1 ≤ f (X n ω)} := fun ω (hω : (N : ℝ) + 1 < Φ (X n ω)) => by
    show 1 ≤ f (X n ω)
    rw [hf, cutoffComp_apply]
    exact le_max_of_le_right (le_min le_rfl (by linarith))
  calc μ n {ω | (N : ℝ) + 1 < Φ (X n ω)} ≤ μ n {ω | 1 ≤ f (X n ω)} := measure_mono hsub
    _ = ENNReal.ofReal ((μ n).real {ω | 1 ≤ f (X n ω)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith [hm, hn])

end LatticeProb
