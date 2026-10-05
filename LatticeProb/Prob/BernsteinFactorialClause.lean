/-
# The factorial-Bernstein clause: tail to `r`-th moment

The second display of `Parking.External.Bernstein` reads: if the factorial conditional moments
satisfy `∑_i E[|ξ_i|^q | F_{i-1}] ≤ (q!/2) a^{q-2} v` a.s. for all integers `q ≥ 2`, then
`(E|∑ ξ_i|^r)^{1/r} ≤ C (√(r v) + r a)` with `C` universal.  The factorial hypothesis
gives the conditional Bernstein mgf `E[e^{λ S} | F] ≤ e^{λ²v/(2(1-aλ))}`
(`LatticeProb.condExp_exp_le_of_factorial`) and hence the two-sided tail

  `P(|S| ≥ s) ≤ 2 e^{-s²/(2(v+as))}`.

This file closes the remaining analytic step: from that tail it derives the `r`-th moment bound,
using the Bochner layer-cake identity `∫ Y^r dμ = ∫_0^∞ r t^{r-1} μ{Y ≥ t} dt`
(`LatticeProb.integral_rpow_eq_integral_meas_le`) and the deterministic Bernstein integral
`∫_0^∞ r t^{r-1} e^{-t²/(2(v+at))} dt ≤ 16^r (r^{r/2} v^{r/2} + (r a)^r)`
(`LatticeProb.integral_rpow_exp_bernstein`):

  `(∫ Y^r dμ)^{1/r} ≤ 32 (√(r v) + r a)`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinLayerCake
import LatticeProb.Prob.BernsteinIntegrate

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The factorial-Bernstein clause: tail to moment.**  A non-negative `Y` in `L^r` (`r ≥ 2`)
whose two-sided tail is dominated by the Bernstein tail `2 e^{-s²/(2(v+as))}` satisfies

  `(∫ Y^r)^{1/r} ≤ 32 (√(r v) + r a)`.

The constants are explicit and universal. -/
theorem integral_rpow_le_of_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ} {r a v : ℝ}
    (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v)
    (hYnn : 0 ≤ᵐ[μ] Y) (hYint : Integrable (fun ω => Y ω ^ r) μ)
    (htail : ∀ s : ℝ, 0 < s →
      (μ {ω | s ≤ Y ω}).toReal ≤ 2 * Real.exp (-(s ^ 2 / (2 * (v + a * s)))))
    (hint : Integrable (fun t : ℝ => r * t ^ (r - 1) * (μ {ω | t ≤ Y ω}).toReal)
      (volume.restrict (Set.Ioi 0)))
    (htailint : Integrable (fun t : ℝ => r * t ^ (r - 1)
      * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t)))))) (volume.restrict (Set.Ioi 0))) :
    (∫ ω, Y ω ^ r ∂μ) ^ (1 / r) ≤ 32 * (Real.sqrt (r * v) + r * a) := by
  have hr1 : (0 : ℝ) < r := by linarith
  have hlayer := integral_rpow_eq_integral_meas_le (μ := μ) hr1 hYnn hYint
  -- the tail bound on the layer-cake integrand
  have hstep : ∫ t in Set.Ioi 0, r * t ^ (r - 1) * (μ {ω | t ≤ Y ω}).toReal
      ≤ ∫ t in Set.Ioi 0, r * t ^ (r - 1)
          * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t))))) := by
    refine integral_mono_ae hint htailint ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    exact mul_le_mul_of_nonneg_left (htail t ht0)
      (mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le _))
  -- pull the factor `2` out and apply the deterministic Bernstein integral
  have hdet : ∫ t in Set.Ioi 0, r * t ^ (r - 1)
        * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t)))))
      = 2 * ∫ t in Set.Ioi 0, r * t ^ (r - 1)
          * Real.exp (-(t ^ 2 / (2 * (v + a * t)))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  have hbern := integral_rpow_exp_bernstein r a v hr ha hv
  have hmain : ∫ ω, Y ω ^ r ∂μ
      ≤ 2 * 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) := by
    rw [hlayer]
    calc ∫ t in Set.Ioi 0, r * t ^ (r - 1) * (μ {ω | t ≤ Y ω}).toReal
        ≤ ∫ t in Set.Ioi 0, r * t ^ (r - 1)
            * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t))))) := hstep
      _ = 2 * ∫ t in Set.Ioi 0, r * t ^ (r - 1)
            * Real.exp (-(t ^ 2 / (2 * (v + a * t)))) := hdet
      _ ≤ 2 * (16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r)) :=
          mul_le_mul_of_nonneg_left hbern (by norm_num)
      _ = 2 * 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) := by ring
  -- take the `r`-th root
  have hArg : 0 ≤ ∫ ω, Y ω ^ r ∂μ :=
    integral_nonneg_of_ae (hYnn.mono fun ω hω => Real.rpow_nonneg hω r)
  have hA : 0 ≤ r ^ (r / 2) * v ^ (r / 2) := by positivity
  have hB : 0 ≤ (r * a) ^ r := by positivity
  have hsub : (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) ^ (1 / r)
      ≤ (r ^ (r / 2) * v ^ (r / 2)) ^ (1 / r) + ((r * a) ^ r) ^ (1 / r) :=
    Real.rpow_add_le_add_rpow hA hB (by positivity)
      (by rw [div_le_iff₀ hr1]; linarith)
  have hAroot : (r ^ (r / 2) * v ^ (r / 2)) ^ (1 / r) = Real.sqrt (r * v) := by
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr1
    have hv0 : (0 : ℝ) ≤ v := le_of_lt hv
    have h1 : (r ^ (r / 2)) ^ (1 / r) = Real.sqrt r := by
      rw [← Real.rpow_mul hr0 (r / 2) (1 / r),
        show r / 2 * (1 / r) = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow]
    have h2 : (v ^ (r / 2)) ^ (1 / r) = Real.sqrt v := by
      rw [← Real.rpow_mul hv0 (r / 2) (1 / r),
        show r / 2 * (1 / r) = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow]
    rw [Real.mul_rpow (by positivity) (by positivity), h1, h2, ← Real.sqrt_mul hr0]
  have hBroot : ((r * a) ^ r) ^ (1 / r) = r * a := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r * a) r (1 / r),
      show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have hfac : (2 * 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r)) ^ (1 / r)
      = 2 ^ (1 / r) * 16
        * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) ^ (1 / r) := by
    have hAB : 0 ≤ r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r := by positivity
    rw [Real.mul_rpow (by positivity) hAB,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg (by norm_num) r),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16) r (1 / r),
      show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have h2 : (2 : ℝ) ^ (1 / r) ≤ (2 : ℝ) := by
    have h2r : (1 : ℝ) / r ≤ 1 := by rw [div_le_iff₀ hr1]; linarith
    calc (2 : ℝ) ^ (1 / r) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2r
      _ = 2 := Real.rpow_one 2
  have hfin : (2 * 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r)) ^ (1 / r)
      ≤ 32 * (Real.sqrt (r * v) + r * a) := by
    rw [hfac]
    have h3 : (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) ^ (1 / r)
        ≤ Real.sqrt (r * v) + r * a := by
      calc (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) ^ (1 / r)
          ≤ (r ^ (r / 2) * v ^ (r / 2)) ^ (1 / r)
            + ((r * a) ^ r) ^ (1 / r) := hsub
        _ = Real.sqrt (r * v) + r * a := by rw [hAroot, hBroot]
    nlinarith [h3, h2, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / r),
      Real.sqrt_nonneg (r * v), mul_pos ha hr1]
  exact (Real.rpow_le_rpow hArg hmain (by positivity)).trans hfin

end LatticeProb
