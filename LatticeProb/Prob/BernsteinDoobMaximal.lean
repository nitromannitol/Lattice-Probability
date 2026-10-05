/-
# The `L^p` Doob maximal inequality for the partial sums

`LatticeProb.integral_rpow_le_integral_weak_type` (`Prob/BernsteinMaximalLayerCake.lean`) turns the
layer-cake identity and the weak-type (Doob) bound into

  `∫ M^p dμ ≤ ∫_0^∞ p t^{p-2} (∫_{M ≥ t} f) dt`.

This file closes the maximal inequality: exchanging the two integrals (the Fubini identity,
carried explicitly) gives `∫ M^p ≤ p/(p-1) ∫ f M^{p-1}`, Hölder turns this into
`∫ M^p ≤ (p/(p-1)) ‖f‖_p (∫ M^p)^{(p-1)/p}`, and solving yields the `L^p` maximal bound
with the source constant `p/(p-1)`:

  `(∫ M^p)^{1/p} ≤ (p/(p-1)) (∫ f^p)^{1/p}`.

Specialising to `M = max_{k≤n}|S k|` and `f = |S n|` for the real martingale partial sums
`S k = ∑_{i≤k} ξ_i` gives Doob's maximal inequality for the process.  The Fubini identity (the
Tonelli exchange together with the elementary inner integral `∫_0^{Mω} p t^{p-2} dt =
p/(p-1) Mω^{p-1}`) is the one step carried as a hypothesis here; all Bochner integrals are finite
by the stated integrability, so no integral collapses to the junk `0`.  No new external input.
-/
import LatticeProb.Prob.BernsteinMaximalLayerCake
import LatticeProb.Prob.BernsteinCrossTerm

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The `L^p` maximal bound from the weak-type bound.**  For `p > 1`, a non-negative `M` with
`M^p` integrable, `f` satisfying `μ{M ≥ t} ≤ t⁻¹ ∫_{M ≥ t} f`, the Fubini identity
`∫_0^∞ p t^{p-2}(∫_{M ≥ t} f) = p/(p-1) ∫ f M^{p-1}`, and the finiteness data,

  `(∫ M^p)^{1/p} ≤ (p/(p-1)) (∫ f^p)^{1/p}`. -/
theorem integral_rpow_le_of_weak_type [IsProbabilityMeasure μ] {M f : Ω → ℝ} {p : ℝ}
    (hp : 1 < p) (hMnn : 0 ≤ᵐ[μ] M) (hMint : Integrable (fun ω => M ω ^ p) μ)
    (hfnn : 0 ≤ᵐ[μ] f)
    (hweak : ∀ t : ℝ, 0 < t →
      (μ {ω | t ≤ M ω}).toReal ≤ t⁻¹ * ∫ ω in {ω | t ≤ M ω}, f ω ∂μ)
    (hint : Integrable (fun t : ℝ => p * t ^ (p - 1) * (μ {ω | t ≤ M ω}).toReal)
      (volume.restrict (Set.Ioi 0)))
    (hbound : Integrable (fun t : ℝ => p * t ^ (p - 2) *
      (∫ ω in {ω | t ≤ M ω}, f ω ∂μ)) (volume.restrict (Set.Ioi 0)))
    (hFubini : ∫ t in Set.Ioi 0, p * t ^ (p - 2) * (∫ ω in {ω | t ≤ M ω}, f ω ∂μ)
      = (p / (p - 1)) * ∫ ω, f ω * M ω ^ (p - 1) ∂μ)
    (hfmem : MemLp f (ENNReal.ofReal p) μ)
    (hMmem : MemLp (fun ω => M ω ^ (p - 1)) (ENNReal.ofReal (p / (p - 1))) μ) :
    (∫ ω, M ω ^ p ∂μ) ^ (1 / p) ≤ (p / (p - 1)) * (∫ ω, f ω ^ p ∂μ) ^ (1 / p) := by
  -- the truncation step
  have hred := integral_rpow_le_integral_weak_type hp hMnn hMint hweak hint hbound
  rw [hFubini] at hred
  -- Hölder with the conjugate exponents `p` and `p/(p-1)`
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hconj : Real.HolderConjugate p (p / (p - 1)) := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · linarith
    · field_simp
      ring
  have hMpnn : 0 ≤ᵐ[μ] fun ω => M ω ^ (p - 1) :=
    hMnn.mono fun ω hω => Real.rpow_nonneg hω _
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj hfnn hMpnn hfmem hMmem
  -- rewrite the two Hölder powers
  have hMpow : ∫ ω, (M ω ^ (p - 1)) ^ (p / (p - 1)) ∂μ = ∫ ω, M ω ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hMnn] with ω hω
    rw [← Real.rpow_mul hω (p - 1) (p / (p - 1))]
    congr 1
    field_simp
  rw [hMpow] at hholder
  have h2 : (1 : ℝ) / (p / (p - 1)) = (p - 1) / p := by rw [one_div_div]
  rw [h2] at hholder
  -- combine
  have hAnn : (0 : ℝ) ≤ ∫ ω, M ω ^ p ∂μ :=
    integral_nonneg_of_ae (hMnn.mono fun ω hω => Real.rpow_nonneg hω p)
  have hBnn : (0 : ℝ) ≤ (∫ ω, f ω ^ p ∂μ) ^ (1 / p) :=
    Real.rpow_nonneg
      (integral_nonneg_of_ae (hfnn.mono fun ω hω => Real.rpow_nonneg hω p)) _
  have hCnn : (0 : ℝ) ≤ p / (p - 1) := le_of_lt (div_pos (by linarith) hp1)
  have hkey : ∫ ω, M ω ^ p ∂μ
      ≤ (p / (p - 1)) * (∫ ω, f ω ^ p ∂μ) ^ (1 / p)
        * (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p) := by
    calc ∫ ω, M ω ^ p ∂μ
        ≤ (p / (p - 1)) * ∫ ω, f ω * M ω ^ (p - 1) ∂μ := hred
      _ ≤ (p / (p - 1)) * ((∫ ω, f ω ^ p ∂μ) ^ (1 / p)
            * (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p)) :=
          mul_le_mul_of_nonneg_left hholder hCnn
      _ = (p / (p - 1)) * (∫ ω, f ω ^ p ∂μ) ^ (1 / p)
            * (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p) := by ring
  -- solve `A ≤ C · B · A^((p-1)/p)` for `A^(1/p) ≤ C · B`
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0]
    simp only [Real.zero_rpow (by positivity : (1 : ℝ) / p ≠ 0)]
    exact mul_nonneg hCnn hBnn
  · have hdiv : (∫ ω, M ω ^ p ∂μ) / (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p)
        ≤ (p / (p - 1)) * (∫ ω, f ω ^ p ∂μ) ^ (1 / p) := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hApos _)]
      exact hkey
    have hAeq : (∫ ω, M ω ^ p ∂μ) / (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p)
        = (∫ ω, M ω ^ p ∂μ) ^ (1 / p) := by
      rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hApos _))]
      have h1 : (∫ ω, M ω ^ p ∂μ) ^ (1 / p)
            * (∫ ω, M ω ^ p ∂μ) ^ ((p - 1) / p) = ∫ ω, M ω ^ p ∂μ := by
        have hexp : (1 : ℝ) / p + (p - 1) / p = 1 := by
          rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring]
          exact div_self (ne_of_gt (by linarith : (0 : ℝ) < p))
        rw [← Real.rpow_add hApos, hexp, Real.rpow_one]
      exact h1.symm
    rwa [hAeq] at hdiv

/-- **Doob's maximal inequality for the martingale partial sums.**  For the real partial sums
`S k = ∑_{i ≤ k} ξ i`, the running maximum `M = max_{k ≤ n}|S k|`, and `f = |S n|`, the
weak-type bound and the Fubini identity give the `L^p` maximal inequality with the source constant
`p/(p-1)`:

  `(∫ M^p)^{1/p} ≤ (p/(p-1)) (∫ |S n|^p)^{1/p}`. -/
theorem doob_maximal_crossTermMax [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → ℝ} {p : ℝ} (hp : 1 < p) (n : ℕ)
    (hMint : Integrable (fun ω => crossTermMax ξ n ω ^ p) μ)
    (hweak : ∀ t : ℝ, 0 < t →
      (μ {ω | t ≤ crossTermMax ξ n ω}).toReal
        ≤ t⁻¹ * ∫ ω in {ω | t ≤ crossTermMax ξ n ω},
            |crossTermPartialSum ξ n ω| ∂μ)
    (hint : Integrable (fun t : ℝ => p * t ^ (p - 1)
      * (μ {ω | t ≤ crossTermMax ξ n ω}).toReal) (volume.restrict (Set.Ioi 0)))
    (hbound : Integrable (fun t : ℝ => p * t ^ (p - 2)
      * (∫ ω in {ω | t ≤ crossTermMax ξ n ω}, |crossTermPartialSum ξ n ω| ∂μ))
        (volume.restrict (Set.Ioi 0)))
    (hFubini : ∫ t in Set.Ioi 0, p * t ^ (p - 2)
        * (∫ ω in {ω | t ≤ crossTermMax ξ n ω}, |crossTermPartialSum ξ n ω| ∂μ)
      = (p / (p - 1)) * ∫ ω,
          |crossTermPartialSum ξ n ω| * crossTermMax ξ n ω ^ (p - 1) ∂μ)
    (hfmem : MemLp (fun ω => |crossTermPartialSum ξ n ω|) (ENNReal.ofReal p) μ)
    (hMmem : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 1))
      (ENNReal.ofReal (p / (p - 1))) μ) :
    (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ (1 / p)
      ≤ (p / (p - 1))
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ (1 / p) :=
  integral_rpow_le_of_weak_type hp
    (Filter.Eventually.of_forall fun ω => crossTermMax_nonneg ξ n ω)
    hMint (Filter.Eventually.of_forall fun ω => abs_nonneg (crossTermPartialSum ξ n ω))
    hweak hint hbound
    hFubini hfmem hMmem

end LatticeProb
