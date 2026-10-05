/-
# The layer-cake identity behind the `L^p` Doob maximal inequality

For a non-negative, a.e.-measurable real random variable `M` with `M^p` integrable (`p > 0`), the
Bochner form of Cavalieri's principle is

  `∫ M^p dμ = ∫_0^∞ p t^{p-1} μ{M ≥ t} dt`.

Equivalently, writing `M` for the running maximum of the partial sums of a martingale and
`f = |S n|`, the ε-form of Doob's maximal inequality
`t · μ{M ≥ t} ≤ ∫_{M ≥ t} f` (Mathlib's
`MeasureTheory.maximal_ineq`) feeds this identity and yields the `L^p` Doob maximal inequality
`‖M‖_p ≤ p/(p-1) · ‖f‖_p`.

This is a self-contained analytic lemma: it uses the Mathlib layer-cake formula
`Integrable.integral_eq_integral_meas_le` and the change of variables `y = x ^ p`
(`integral_comp_rpow_Ioi_of_pos`).  There is no new external input.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **Layer cake / Cavalieri, Bochner form.**  For a non-negative `M` with `M^p` integrable and
`p > 0`,

  `∫ M^p dμ = ∫_0^∞ p t^{p-1} μ{M ≥ t} dt`,

where `μ{M ≥ t}` is read through `ENNReal.toReal`.  The strict and non-strict forms agree
a.e., so the same identity holds with `t < M`. -/
theorem integral_rpow_eq_integral_meas_le {M : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hMnn : 0 ≤ᵐ[μ] M) (hMint : Integrable (fun ω => M ω ^ p) μ) :
    ∫ ω, M ω ^ p ∂μ
      = ∫ t in Set.Ioi 0, p * t ^ (p - 1) * (μ {ω | t ≤ M ω}).toReal := by
  have hMpnn : 0 ≤ᵐ[μ] fun ω => M ω ^ p :=
    hMnn.mono fun ω hω => Real.rpow_nonneg hω p
  -- on the a.e. set `0 ≤ M`, `x^p ≤ M^p ↔ x ≤ M` for `x > 0`
  have hset : ∀ x : ℝ, 0 < x →
      {ω | x ^ p ≤ M ω ^ p} =ᵐ[μ] {ω | x ≤ M ω} := by
    intro x hx
    filter_upwards [hMnn] with ω hω
    exact propext (Real.rpow_le_rpow_iff (le_of_lt hx) hω hp)
  have hGH : (fun x : ℝ => (μ {ω | x ^ p ≤ M ω ^ p}).toReal)
      =ᵐ[volume.restrict (Set.Ioi 0)] (fun x : ℝ => (μ {ω | x ≤ M ω}).toReal) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact congrArg ENNReal.toReal (measure_congr (hset x (Set.mem_Ioi.mp hx)))
  calc ∫ ω, M ω ^ p ∂μ
      = ∫ t in Set.Ioi 0, (μ {ω | t ≤ M ω ^ p}).toReal :=
        hMint.integral_eq_integral_meas_le hMpnn
    _ = ∫ x in Set.Ioi 0, (p * x ^ (p - 1)) * (μ {ω | x ^ p ≤ M ω ^ p}).toReal := by
        rw [← integral_comp_rpow_Ioi_of_pos
          (g := fun t : ℝ => (μ {ω | t ≤ M ω ^ p}).toReal) hp]
        simp only [smul_eq_mul]
    _ = ∫ t in Set.Ioi 0, p * t ^ (p - 1) * (μ {ω | t ≤ M ω}).toReal := by
        refine integral_congr_ae ?_
        filter_upwards [hGH] with x hx
        rw [hx]

/-- **Layer cake / Cavalieri, Lebesgue form.**  The same identity in `ℝ≥0∞`, without the
integrability hypothesis: for `p > 0`, `∫⁻ M^p = p ∫⁻_0^∞ t^{p-1} μ{M ≥ t}`. -/
theorem lintegral_rpow_eq_lintegral_meas_le {M : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hMnn : 0 ≤ᵐ[μ] M) (hMmble : AEMeasurable M μ) :
    ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ
      = ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0,
          μ {ω | t ≤ M ω} * ENNReal.ofReal (t ^ (p - 1)) :=
  lintegral_rpow_eq_lintegral_meas_le_mul (μ := μ) hMnn hMmble hp

end LatticeProb
