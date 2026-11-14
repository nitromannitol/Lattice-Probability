import LatticeProb.Prob.ExcursionCountKappa
import LatticeProb.Prob.ExcursionCountAsLimit
import LatticeProb.Analysis.ExcursionCountSandwich
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianPathFacts

/-!
# Lévy's excursion-count formula for Brownian motion

Let `B` be a standard real Brownian motion with continuous paths, extended to `ℝ` by `X = nnExtend B` (constant on
`(-∞, 0]`). Almost surely, for every `t ≥ 0`,

  `√(π ε / 2) · #{excursions of X above its running infimum in [0, t], of length larger than ε}
      → X 0 - inf_{[0, t]} X`   as `ε → 0⁺`,

where the excursions are the complementary intervals of the forward ladder set
`{s ≥ 0 | X s ≤ X u for all u ∈ [0, s]}`. This is Lévy's description of the running infimum (the local time at the
infimum) as the limit of the normalised number of long excursions; the normalisation `√(π ε / 2)` is the inverse of
the tail `n(ζ > ε) = √(2 / (π ε))` of the excursion length.

The proof combines
* the almost sure limit `√ε J_ε(b) → b κ` at a fixed level `b > 0` (`ae_tendsto_sqrt_mul_pathExcursionCount`);
* the value of the constant `κ = E J_1(1) = √(2/π)` (`toReal_lintegral_pathExcursionCount_one_one`);
* almost sure unboundedness below of the Brownian path;
* the deterministic sandwich `tendsto_excursionCount_forwardLadderSet`, applied on the countable set of rational
  levels.

## Main results

* `ae_tendsto_sqrt_pi_mul_pathExcursionCount`: for fixed `b > 0`, a.s. `√(π ε / 2) J_ε(b) → b`.
* `ae_tendsto_sqrt_pi_mul_excursionCount_forwardLadderSet`: Lévy's formula, simultaneously for all `t ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Lévy's formula at a fixed level.** For `b > 0`, almost surely `√(π ε / 2) J_ε(b) → b` as `ε → 0⁺`. -/
theorem ae_tendsto_sqrt_pi_mul_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (pathExcursionCount (fun t => B t ω) b ε : ℝ)) (𝓝[>] 0) (𝓝 b) := by
  filter_upwards [ae_tendsto_sqrt_mul_pathExcursionCount hB hm hcont hb] with ω hω
  rw [toReal_lintegral_pathExcursionCount_one_one hB hm hcont] at hω
  have hπ : Real.pi / 2 * (2 / Real.pi) = 1 := by
    rw [div_mul_div_comm, mul_comm Real.pi 2, div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  have hc : √(Real.pi / 2) * (b * √(2 / Real.pi)) = b := by
    rw [mul_left_comm, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2), hπ, Real.sqrt_one, mul_one]
  have h := hω.const_mul (√(Real.pi / 2))
  rw [hc] at h
  refine h.congr fun ε => ?_
  rw [← mul_assoc, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  congr 2
  ring

/-- **Almost sure unboundedness below.** Almost surely the extended path goes below `X 0 - b` for every `b`. -/
theorem ae_exists_nnExtend_lt_sub [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, ∃ s, (0 : ℝ) ≤ s ∧
      nnExtend (fun t => B t ω) s < nnExtend (fun t => B t ω) 0 - b := by
  filter_upwards [MatedCRTHarmonic.MatedCRT.BrownianPathFacts.ae_unboundedBelowInt hB.toIsPreBrownianReal hm,
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
  intro b
  obtain ⟨n, -, hn⟩ := hω ⌈b⌉₊ 0
  refine ⟨((n : ℝ≥0) : ℝ), NNReal.coe_nonneg _, ?_⟩
  simp only [nnExtend, Real.toNNReal_coe, Real.toNNReal_zero, h0, zero_sub]
  linarith [Nat.le_ceil b]

/-- **Lévy's excursion-count formula.** Almost surely, for every `t ≥ 0`, the number of excursions of the Brownian path
above its running infimum in `[0, t]` of length larger than `ε`, multiplied by `√(π ε / 2)`, converges as `ε → 0⁺` to
the drop `X 0 - inf_{[0, t]} X` of the running infimum. -/
theorem ae_tendsto_sqrt_pi_mul_excursionCount_forwardLadderSet [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet (nnExtend fun s => B s ω) 0) 0 t ε : ℝ)) (𝓝[>] 0)
      (𝓝 (nnExtend (fun s => B s ω) 0 - sInf (nnExtend (fun s => B s ω) '' Icc 0 t))) := by
  have hlev : ∀ᵐ ω ∂P, ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (pathExcursionCount (fun t => B t ω) b ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ)) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 0 < b
    · filter_upwards [ae_tendsto_sqrt_pi_mul_pathExcursionCount hB hm hcont (Rat.cast_pos.2 hb)] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall fun _ h => absurd h hb
  filter_upwards [hlev, ae_exists_nnExtend_lt_sub hB hm] with ω hlevω hunbω
  intro t ht
  exact tendsto_excursionCount_forwardLadderSet (continuous_nnExtend (hcont ω)) hunbω hlevω ht

end LatticeProb.LadderSet
