import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power-law bounds for medians from exponent convergence in probability

Let `L ε` be a family of nonnegative random variables indexed by a scale `ε > 0`, and let `m ε` be a
median of `L ε`, that is `P (L ε ≤ m ε) ≥ 1/2` and `P (m ε ≤ L ε) ≥ 1/2`. If `L ε` is of order
`ε ^ (λ + o(1))` in probability, then so is every choice of medians: for each `δ > 0`, eventually as
`ε ↓ 0`,
`ε ^ (λ + δ) ≤ m ε ≤ ε ^ (λ - δ)`.

This is the passage from a distance exponent stated in probability (`log D_ε / log ε → λ` in
probability, as for Liouville first passage percolation distances) to the same exponent stated for
medians (`𝔞_ε = ε ^ (λ + o(1))`).

* `median_rpow_bounds_of_tail`: the median bounds from the vanishing of the two tail probabilities
  `P (L ε < ε ^ (λ + δ))` and `P (L ε > ε ^ (λ - δ))`;
* `tendsto_measure_rpow_of_tendstoInMeasure_log_div`: for a positive real family `D ε`, convergence in
  probability of `log (D ε) / log ε` to `λ` gives the vanishing of both tail probabilities;
* `median_rpow_bounds_of_tendstoInMeasure_log_div`: the composite, for medians of `ENNReal.ofReal (D ε)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Median bounds from tail bounds.** If `P (L ε < ε ^ (λ + δ)) → 0` and `P (L ε > ε ^ (λ - δ)) → 0`
as `ε ↓ 0` for every `δ > 0`, then every family of medians `m ε` of `L ε` satisfies
`ε ^ (λ + δ) ≤ m ε ≤ ε ^ (λ - δ)` eventually, for every `δ > 0`. -/
theorem median_rpow_bounds_of_tail {L : ℝ → Ω → ℝ≥0∞} {m : ℝ → ℝ≥0∞} {lam : ℝ}
    (hmed : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      2⁻¹ ≤ P {ω | L ε ω ≤ m ε} ∧ 2⁻¹ ≤ P {ω | m ε ≤ L ε ω})
    (hlow : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε : ℝ => P {ω | L ε ω < ENNReal.ofReal (ε ^ (lam + δ))}) (𝓝[>] 0) (𝓝 0))
    (hup : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε : ℝ => P {ω | ENNReal.ofReal (ε ^ (lam - δ)) < L ε ω}) (𝓝[>] 0) (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (lam + δ)) ≤ m ε ∧ m ε ≤ ENNReal.ofReal (ε ^ (lam - δ)) := by
  have h2 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  filter_upwards [hmed, (hlow δ hδ).eventually (Iio_mem_nhds h2),
    (hup δ hδ).eventually (Iio_mem_nhds h2)] with ε hm hl hu
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    have hsub : P {ω | L ε ω ≤ m ε} ≤ P {ω | L ε ω < ENNReal.ofReal (ε ^ (lam + δ))} :=
      measure_mono fun ω (hω : L ε ω ≤ m ε) => lt_of_le_of_lt hω hlt
    exact absurd (hm.1.trans hsub) (not_le.2 hl)
  · by_contra hlt
    rw [not_le] at hlt
    have hsub : P {ω | m ε ≤ L ε ω} ≤ P {ω | ENNReal.ofReal (ε ^ (lam - δ)) < L ε ω} :=
      measure_mono fun ω (hω : m ε ≤ L ε ω) => lt_of_lt_of_le hlt hω
    exact absurd (hm.2.trans hsub) (not_le.2 hu)

/-- **Tail bounds from exponent convergence in probability.** If `D ε > 0` almost surely for small
`ε` and `log (D ε) / log ε → λ` in probability as `ε ↓ 0`, then for every `δ > 0` both
`P (D ε < ε ^ (λ + δ))` and `P (D ε > ε ^ (λ - δ))` tend to `0`. -/
theorem tendsto_measure_rpow_of_tendstoInMeasure_log_div {D : ℝ → Ω → ℝ} {lam : ℝ}
    (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, 0 < D ε ω)
    (hconv : TendstoInMeasure P (fun ε ω => Real.log (D ε ω) / Real.log ε) (𝓝[>] 0)
      (fun _ => lam))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => P {ω | D ε ω < ε ^ (lam + δ)}) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => P {ω | ε ^ (lam - δ) < D ε ω}) (𝓝[>] 0) (𝓝 0) := by
  have hε1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have key := tendstoInMeasure_iff_dist.1 hconv δ hδ
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds key
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hpos, hε1] with ε hp hε
    refine measure_mono_ae (hp.mono fun ω hpω (hω : D ε ω < ε ^ (lam + δ)) => ?_)
    have hlog : Real.log ε < 0 := Real.log_neg hε.1 hε.2
    have h1 : Real.log (D ε ω) < (lam + δ) * Real.log ε := by
      have := Real.log_lt_log hpω hω
      rwa [Real.log_rpow hε.1] at this
    have h2 : lam + δ < Real.log (D ε ω) / Real.log ε := (lt_div_iff_of_neg hlog).2 h1
    show δ ≤ dist (Real.log (D ε ω) / Real.log ε) lam
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds key
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hε1] with ε hε
    refine measure_mono fun ω (hω : ε ^ (lam - δ) < D ε ω) => ?_
    have hlog : Real.log ε < 0 := Real.log_neg hε.1 hε.2
    have h1 : (lam - δ) * Real.log ε < Real.log (D ε ω) := by
      have := Real.log_lt_log (Real.rpow_pos_of_pos hε.1 _) hω
      rwa [Real.log_rpow hε.1] at this
    have h2 : Real.log (D ε ω) / Real.log ε < lam - δ := (div_lt_iff_of_neg hlog).2 h1
    show δ ≤ dist (Real.log (D ε ω) / Real.log ε) lam
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith

/-- **Median bounds from exponent convergence in probability.** If `D ε > 0` almost surely for small
`ε`, `log (D ε) / log ε → λ` in probability as `ε ↓ 0`, and `m ε` is a median of `ENNReal.ofReal (D ε)`
for small `ε`, then for every `δ > 0`, eventually `ε ^ (λ + δ) ≤ m ε ≤ ε ^ (λ - δ)`. -/
theorem median_rpow_bounds_of_tendstoInMeasure_log_div {D : ℝ → Ω → ℝ} {m : ℝ → ℝ≥0∞}
    {lam : ℝ}
    (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, 0 < D ε ω)
    (hconv : TendstoInMeasure P (fun ε ω => Real.log (D ε ω) / Real.log ε) (𝓝[>] 0)
      (fun _ => lam))
    (hmed : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      2⁻¹ ≤ P {ω | ENNReal.ofReal (D ε ω) ≤ m ε} ∧ 2⁻¹ ≤ P {ω | m ε ≤ ENNReal.ofReal (D ε ω)})
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (lam + δ)) ≤ m ε ∧ m ε ≤ ENNReal.ofReal (ε ^ (lam - δ)) := by
  refine median_rpow_bounds_of_tail (L := fun ε ω => ENNReal.ofReal (D ε ω)) hmed
    (fun δ' hδ' => ?_) (fun δ' hδ' => ?_) δ hδ
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_rpow_of_tendstoInMeasure_log_div hpos hconv δ' hδ').1
      (fun _ => zero_le) (fun ε => measure_mono fun ω hω => ?_)
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hω).1
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_rpow_of_tendstoInMeasure_log_div hpos hconv δ' hδ').2
      (fun _ => zero_le) (fun ε => measure_mono fun ω hω => ?_)
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hω).1

end LatticeProb.Probability
