import Mathlib
import LatticeProb.Topology.ContinuousMapBorel
import LatticeProb.Prob.BrownianDriftSmallBallBound
import LatticeProb.Prob.UpcrossLaplaceIdentity

/-!
# A drifted Brownian path leaves every half-line `(-δ, ∞)` immediately

For a Brownian motion with drift `μ` (any real number) and a positive time `s`, the probability
that the path stays above `-δ` up to time `s` tends to `0` as `δ → 0⁺`.

The small-ball recursion for the non-strict stay event at the dyadic scales `2⁻ʲ` gives, for
every `k`, the bound `P(stay above -δ up to time 2⁻ʲ) ≤ 4δ(√2^(j+k) + c) + 2⁻ᵏ` once
`16 δ² ≤ 2^-(j+k)`; the drift is reduced to a positive one by monotonicity.

* `LatticeProb.le_two_mul_add_pow_of_rec`: telescoping of the recursion `A j ≤ b + A (j+1)/2`.
* `LatticeProb.measureReal_closedStay_dyadic_le`: the bound above.
* `LatticeProb.tendsto_measureReal_closedStay_zero`: `P(stay above -δ up to time s) → 0`.
* `LatticeProb.isOpen_stayUpTo`: the set of paths above `-δ` up to time `s` is open.
* `LatticeProb.tendsto_driftLaw_stay_small`: the same for the law `driftLaw P B hcont μ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Telescoping of a recursion `A j ≤ b + A (j + 1) / 2` for `j < k`, with `A k ≤ 1`. -/
theorem le_two_mul_add_pow_of_rec (A : ℕ → ℝ) {b : ℝ} (hb : 0 ≤ b) (k : ℕ)
    (hrec : ∀ j < k, A j ≤ b + A (j + 1) / 2) (h1 : A k ≤ 1) (_h0 : 0 ≤ A k) :
    A 0 ≤ 2 * b + (1 / 2 : ℝ) ^ k := by
  have h := telescope_half A (fun _ => b) k hrec k le_rfl
  have hsum : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j * b ≤ 2 * b := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (geom_sum_half_le k) hb
  have hk : (1 / 2 : ℝ) ^ k * A k ≤ (1 / 2 : ℝ) ^ k := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    nlinarith
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Small-ball bound at the dyadic scale `2⁻ʲ`.**  For `c > 0` and `16 δ² ≤ 2^-(j+k)`,
`P(B t + c t ≥ -δ for all t ≤ 2⁻ʲ) ≤ 2 (2 δ √2^(j+k) + 2 c δ) + 2⁻ᵏ`. -/
theorem measureReal_closedStay_dyadic_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    {δ : ℝ} (hδ : 0 < δ) (j k : ℕ) (hs : 16 * δ ^ 2 ≤ (1 / 2 : ℝ) ^ (j + k)) :
    P.real (closedStay B c δ ((1 / 2 : ℝ≥0) ^ j)) ≤
      2 * (2 * δ * (√2) ^ (j + k) + 2 * c * δ) + (1 / 2 : ℝ) ^ k := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set A : ℕ → ℝ := fun i => P.real (closedStay B c δ ((1 / 2 : ℝ≥0) ^ (j + i))) with hA
  have hu : (1 : ℝ) ≤ √2 := by
    rw [Real.one_le_sqrt]; norm_num
  have hb : 0 ≤ 2 * δ * (√2) ^ (j + k) + 2 * c * δ := by positivity
  have hrec : ∀ i < k, A i ≤ (2 * δ * (√2) ^ (j + k) + 2 * c * δ) + A (i + 1) / 2 := by
    intro i hi
    have hsi : 16 * δ ^ 2 ≤ (((1 / 2 : ℝ≥0) ^ (j + i) : ℝ≥0) : ℝ) := by
      push_cast
      refine hs.trans ?_
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h := measureReal_closedStay_le_half hB hm hcont hc hδ ((1 / 2 : ℝ≥0) ^ (j + i)) hsi
    have e1 : ((1 / 2 : ℝ≥0) ^ (j + i)) / 2 = (1 / 2 : ℝ≥0) ^ (j + (i + 1)) := by
      rw [← add_assoc, pow_succ, div_eq_mul_one_div]
    have e2 : 2 * δ / √((((1 / 2 : ℝ≥0) ^ (j + i) : ℝ≥0)) : ℝ) = 2 * δ * (√2) ^ (j + i) := by
      rw [sqrt_half_pow, div_inv_eq_mul]
    rw [e1, e2] at h
    have e3 : 2 * δ * (√2) ^ (j + i) ≤ 2 * δ * (√2) ^ (j + k) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (by omega)) (by positivity)
    simp only [hA]
    linarith
  have h := le_two_mul_add_pow_of_rec A hb k hrec measureReal_le_one measureReal_nonneg
  simpa [hA] using h

/-- **A drifted Brownian motion leaves every half-line immediately.**  For a Brownian motion
`B` (pre-Brownian, continuous paths), `c > 0` and `s > 0`,
`P(B t + c t ≥ -δ for all t ≤ s) → 0` as `δ → 0⁺`. -/
theorem tendsto_measureReal_closedStay_zero (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    {s : ℝ≥0} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => P.real (closedStay B c δ s)) (𝓝[>] 0) (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < s by exact_mod_cast hs)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hjs : (1 / 2 : ℝ≥0) ^ j ≤ s := by
    have : (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ) ≤ (s : ℝ) := by push_cast; exact hj.le
    exact_mod_cast this
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · exact Eventually.of_forall fun δ => lt_of_lt_of_le ha measureReal_nonneg
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hε) (show (1 / 2 : ℝ) < 1 by norm_num)
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + k) := by positivity
    have e1 : ∀ᶠ δ : ℝ in 𝓝 0, 16 * δ ^ 2 < (1 / 2 : ℝ) ^ (j + k) := by
      have : Tendsto (fun δ : ℝ => 16 * δ ^ 2) (𝓝 0) (𝓝 0) := by
        have h := (by fun_prop : Continuous fun δ : ℝ => 16 * δ ^ 2).tendsto (0 : ℝ)
        rwa [show 16 * (0 : ℝ) ^ 2 = 0 by norm_num] at h
      exact this.eventually (gt_mem_nhds hpos)
    have e2 : ∀ᶠ δ : ℝ in 𝓝 0, 4 * δ * ((√2) ^ (j + k) + c) < ε / 2 := by
      have : Tendsto (fun δ : ℝ => 4 * δ * ((√2) ^ (j + k) + c)) (𝓝 0) (𝓝 0) := by
        have h := (by fun_prop : Continuous fun δ : ℝ => 4 * δ * ((√2) ^ (j + k) + c)).tendsto
          (0 : ℝ)
        rwa [show 4 * (0 : ℝ) * ((√2) ^ (j + k) + c) = 0 by ring] at h
      exact this.eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (e1.and e2), self_mem_nhdsWithin]
      with δ ⟨h1, h2⟩ hδ
    have hδ' : 0 < δ := hδ
    have hmono : P.real (closedStay B c δ s) ≤ P.real (closedStay B c δ ((1 / 2 : ℝ≥0) ^ j)) :=
      measureReal_mono (closedStay_anti hjs)
    have hb := measureReal_closedStay_dyadic_le hB hm hcont hc hδ' j k h1.le
    nlinarith

/-- The set of paths strictly above `-δ` up to time `s` is open in the compact-open topology. -/
theorem isOpen_stayUpTo (δ : ℝ) (s : ℝ≥0) :
    IsOpen {w : C(ℝ≥0, ℝ) | ∀ t : ℝ≥0, t ≤ s → -δ < w t} := by
  have h := ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc (a := (0 : ℝ≥0)) (b := s))
    (isOpen_Ioi (a := -δ))
  convert h using 1
  ext w
  simp [Set.MapsTo]

/-- **The drifted path goes below `0` immediately.**  For a Brownian motion with drift `μ` (any
real number) and a time `s > 0`, the probability that the path stays strictly above `-δ` up to
time `s` tends to `0` as `δ → 0⁺`. -/
theorem tendsto_driftLaw_stay_small (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (μ : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => driftLaw P B hcont μ {w : C(ℝ≥0, ℝ) | ∀ t : ℝ≥0, t ≤ s → -δ < w t})
      (𝓝[>] 0) (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set c : ℝ := max μ 1 with hcdef
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hμc : μ ≤ c := le_max_left _ _
  have hlim := tendsto_measureReal_closedStay_zero hB hm hcont hc hs
  have hlim' : Tendsto (fun δ : ℝ => P (closedStay B c δ s)) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hlim
    rw [ENNReal.ofReal_zero] at h
    refine h.congr fun δ => ?_
    simp only [Measure.real]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun δ => zero_le) (fun δ => ?_)
  have hS : MeasurableSet {w : C(ℝ≥0, ℝ) | ∀ t : ℝ≥0, t ≤ s → -δ < w t} :=
    (isOpen_stayUpTo δ s).measurableSet
  have hpm : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
  rw [driftLaw, Measure.map_apply (measurable_driftMap μ) hS,
    Measure.map_apply hpm ((measurable_driftMap μ) hS)]
  refine measure_mono fun ω hω t ht => ?_
  have h1 : -δ < B t ω + μ * t := by simpa [pathMap_apply] using hω t ht
  have h2 : μ * (t : ℝ) ≤ c * t := mul_le_mul_of_nonneg_right hμc t.2
  linarith

end LatticeProb
