import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Distance exponents from tightness of normalized distances

Let `D ε` be a family of positive random variables indexed by a scale `ε > 0` and let `m ε > 0` be
deterministic normalizing constants. Suppose that

* the normalizing constants have a power-law exponent: `m ε = ε ^ (λ + o(1))`, that is
  `log (m ε) / log ε → λ` as `ε ↓ 0`;
* the normalized family `D ε / m ε` is tight above and below: for every `η > 0` there is `M > 0`
  with `P (D ε > M m ε) + P (D ε < M⁻¹ m ε) ≤ η` for all small `ε`.

Then `log (D ε) / log ε → λ` in probability. This is how the tightness of normalized Liouville
first passage percolation distances (for instance point-to-point distances normalized by the median
of a crossing distance) yields the convergence in probability of their exponent.

* `tendsto_log_div_log_of_rpow_bounds`: if `ε ^ (λ + δ) ≤ m ε ≤ ε ^ (λ - δ)` eventually for every
  `δ > 0`, then `log (m ε) / log ε → λ`;
* `tendstoInMeasure_log_div_of_tight`: the statement above.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Exponent of power-law bounds.** If `ε ^ (λ + δ) ≤ m ε ≤ ε ^ (λ - δ)` eventually as `ε ↓ 0`,
for every `δ > 0`, then `log (m ε) / log ε → λ`. -/
theorem tendsto_log_div_log_of_rpow_bounds {m : ℝ → ℝ} {lam : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (lam + δ) ≤ m ε ∧ m ε ≤ ε ^ (lam - δ)) :
    Tendsto (fun ε => Real.log (m ε) / Real.log ε) (𝓝[>] 0) (𝓝 lam) := by
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  filter_upwards [h (δ / 2) (half_pos hδ), Ioo_mem_nhdsGT one_pos] with ε hb hε
  have hlog : Real.log ε < 0 := Real.log_neg hε.1 hε.2
  have hm : 0 < m ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hε.1 _) hb.1
  have h1 : (lam + δ / 2) * Real.log ε ≤ Real.log (m ε) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hε.1 _) hb.1
    rwa [Real.log_rpow hε.1] at this
  have h2 : Real.log (m ε) ≤ (lam - δ / 2) * Real.log ε := by
    have := Real.log_le_log hm hb.2
    rwa [Real.log_rpow hε.1] at this
  have h3 : Real.log (m ε) / Real.log ε ≤ lam + δ / 2 := (div_le_iff_of_neg hlog).2 h1
  have h4 : lam - δ / 2 ≤ Real.log (m ε) / Real.log ε := (le_div_iff_of_neg hlog).2 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Exponent in probability from two-sided tightness.** If `D ε > 0` almost surely and `m ε > 0`
for small `ε`, `log (m ε) / log ε → λ`, and `D ε / m ε` is tight above and below, then
`log (D ε) / log ε → λ` in probability as `ε ↓ 0`. -/
theorem tendstoInMeasure_log_div_of_tight {D : ℝ → Ω → ℝ} {m : ℝ → ℝ} {lam : ℝ}
    (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, 0 < D ε ω)
    (hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < m ε)
    (hmexp : Tendsto (fun ε => Real.log (m ε) / Real.log ε) (𝓝[>] 0) (𝓝 lam))
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P {ω | M * m ε < D ε ω} + P {ω | D ε ω < M⁻¹ * m ε} ≤ η) :
    TendstoInMeasure P (fun ε ω => Real.log (D ε ω) / Real.log ε) (𝓝[>] 0) (fun _ => lam) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  have hlarge : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * |Real.log M| < δ * -Real.log ε :=
    ((tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).const_mul_atTop hδ).eventually_gt_atTop _
  have hclose := Metric.tendsto_nhds.1 hmexp (δ / 2) (half_pos hδ)
  filter_upwards [hev, hpos, hm, hlarge, hclose, Ioo_mem_nhdsGT one_pos] with ε hε hp hmε hL hc hε01
  have hlog : Real.log ε < 0 := Real.log_neg hε01.1 hε01.2
  calc P {ω | δ ≤ dist (Real.log (D ε ω) / Real.log ε) lam}
      ≤ P ({ω | M * m ε < D ε ω} ∪ {ω | D ε ω < M⁻¹ * m ε}) := by
        refine measure_mono_ae (hp.mono fun ω hpω
          (hω : δ ≤ dist (Real.log (D ε ω) / Real.log ε) lam) => ?_)
        by_cases hA : M * m ε < D ε ω
        · exact Or.inl hA
        by_cases hB : D ε ω < M⁻¹ * m ε
        · exact Or.inr hB
        exfalso
        rw [not_lt] at hA hB
        have hup : Real.log (D ε ω) ≤ Real.log M + Real.log (m ε) := by
          rw [← Real.log_mul hM.ne' hmε.ne']
          exact Real.log_le_log hpω hA
        have hlo : -Real.log M + Real.log (m ε) ≤ Real.log (D ε ω) := by
          rw [← Real.log_inv, ← Real.log_mul (inv_ne_zero hM.ne') hmε.ne']
          exact Real.log_le_log (mul_pos (inv_pos.2 hM) hmε) hB
        have habs : |Real.log (D ε ω) - Real.log (m ε)| ≤ |Real.log M| := by
          rw [abs_le]
          constructor <;> linarith [le_abs_self (Real.log M), neg_abs_le (Real.log M)]
        have hfrac : |(Real.log (D ε ω) - Real.log (m ε)) / Real.log ε| < δ / 2 := by
          rw [abs_div, abs_of_neg hlog, div_lt_iff₀ (neg_pos.2 hlog)]
          linarith
        have hsplit : Real.log (D ε ω) / Real.log ε - lam =
            (Real.log (D ε ω) - Real.log (m ε)) / Real.log ε +
              (Real.log (m ε) / Real.log ε - lam) := by
          rw [sub_div]; ring
        rw [Real.dist_eq, hsplit] at hω
        rw [Real.dist_eq] at hc
        have := abs_add_le ((Real.log (D ε ω) - Real.log (m ε)) / Real.log ε)
          (Real.log (m ε) / Real.log ε - lam)
        linarith
    _ ≤ P {ω | M * m ε < D ε ω} + P {ω | D ε ω < M⁻¹ * m ε} := measure_union_le _ _
    _ ≤ η := hε

end LatticeProb.Probability
