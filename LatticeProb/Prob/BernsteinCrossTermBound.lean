/-
# The full maximal-form cross-term bound for the Bernstein/Rosenthal route

This file combines the verified pieces of `LatticeProb/Prob/BernsteinCrossTerm.lean`

* `crossTerm_le_max_mul` — the pointwise finite-maximum domination,
* `crossTerm_integral_le` — the Hölder pairing of the cross term with
  `(∫ (max |S|)^p)^{(p-2)/p} (∫ V^{p/2})^{2/p}`,
* `doob_maximal_crossTerm` — Doob's maximal inequality for the partial sums (the `ε` form),

into the maximal-form cross-term bound of Pinelis's Rosenthal/Bernstein argument.  With the real
partial sums `S k = ∑_{i ∈ Icc 1 k} ξ i`, the predictable quadratic variation
`V n = ∑_{i ∈ range n} v (i+1) = ∑_{j=1}^{n} v j`, and the running maximum
`M = max_{k≤n} |S k|`, the cumulative cross term is

  `∫ ∑_{i<n} |S i|^{p-2} v (i+1) ≤ (∫ M^p)^{(p-2)/p} (∫ V^{p/2})^{2/p}`,

and, once the `L^p` form of Doob's maximal inequality
`∫ M^p ≤ (p/(p-1))^p ∫ |S n|^p` is supplied,

  `∫ ∑_{i<n} |S i|^{p-2} v (i+1)
     ≤ (p/(p-1))^{p-2} (∫ V^{p/2})^{2/p} (∫ |S n|^p)^{(p-2)/p}`.

The `L^p` Doob input is the one remaining genuine step (it is not the false
`PinelisDoobStep`); it is carried as an explicit hypothesis of `crossTerm_le_variance_of_doob`
and is derivable from the `ε` form `doob_maximal_crossTerm` by the layer-cake formula.  All the
Bochner integrals below are integrable by hypothesis, so no integral collapses to the junk `0`.

There is no new external input and the file is not imported by the root.
-/
import LatticeProb.Prob.BernsteinCrossTerm

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- The predictable quadratic variation `V n = ∑_{j=1}^{n} v j`, written as
`∑_{i ∈ range n} v (i+1)` so that `v` is indexed by the martingale difference `ξ (i+1)`. -/
noncomputable def crossTermVariance (v : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, v (i + 1) ω

/-- **Per-term maximal bound.**  For `p > 2`, an index `i ≤ n`, and a non-negative weight `v`, the
single cross-term integrand is bounded by `(∫ M^p)^{(p-2)/p} (∫ v^{p/2})^{2/p}` with
`M = max_{k≤n} |S k|`.  This is the termwise form of the maximal cross-term bound. -/
theorem crossTerm_term_le [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    {ξ : ℕ → Ω → ℝ} {v : Ω → ℝ} {n i : ℕ} (hin : i ≤ n) (hv : 0 ≤ᵐ[μ] v)
    (hMmem : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 2))
      (ENNReal.ofReal (p / (p - 2))) μ)
    (hvmem : MemLp v (ENNReal.ofReal (p / 2)) μ)
    (hint : Integrable (fun ω => crossTermMax ξ n ω ^ (p - 2) * v ω) μ)
    (hintL : Integrable (fun ω => |crossTermPartialSum ξ i ω| ^ (p - 2) * v ω) μ) :
    ∫ ω, |crossTermPartialSum ξ i ω| ^ (p - 2) * v ω ∂μ
      ≤ (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ ((p - 2) / p)
        * (∫ ω, v ω ^ (p / 2) ∂μ) ^ (2 / p) := by
  have hp2 : 0 < p - 2 := by linarith
  have hpoint : ∀ᵐ ω ∂μ, |crossTermPartialSum ξ i ω| ^ (p - 2) * v ω
      ≤ crossTermMax ξ n ω ^ (p - 2) * v ω := by
    filter_upwards [hv] with ω hvω
    refine mul_le_mul_of_nonneg_right ?_ hvω
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ (le_of_lt hp2)
    exact Finset.le_sup' (s := Finset.range (n + 1))
      (f := fun k => |crossTermPartialSum ξ k ω|)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
  have hmono := integral_mono_ae hintL hint hpoint
  have hconj : Real.HolderConjugate (p / (p - 2)) (p / 2) := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp2]; linarith
    · field_simp
      ring
  have hMnn : 0 ≤ᵐ[μ] fun ω => crossTermMax ξ n ω ^ (p - 2) :=
    Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (crossTermMax_nonneg ξ n ω) (p - 2)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj hMnn hv hMmem hvmem
  have hMpow : ∫ ω, (crossTermMax ξ n ω ^ (p - 2)) ^ (p / (p - 2)) ∂μ
      = ∫ ω, crossTermMax ξ n ω ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    rw [← Real.rpow_mul (crossTermMax_nonneg ξ n ω) (p - 2) (p / (p - 2))]
    congr 1
    field_simp
  rw [hMpow] at hholder
  have h1 : (1 : ℝ) / (p / (p - 2)) = (p - 2) / p := by rw [one_div_div]
  have h2 : (1 : ℝ) / (p / 2) = 2 / p := by rw [one_div_div]
  rw [h1, h2] at hholder
  exact hmono.trans hholder

/-- **The full maximal-form cross-term bound.**  Combining the pointwise finite-maximum
domination, the Hölder pairing, and the `L^p` Doob maximal inequality
`∫ (max |S|)^p ≤ (p/(p-1))^p ∫ |S n|^p`, the cumulative cross term is bounded by the source
quantities with the explicit Doob constant:

  `∫ ∑_{i<n} |S i|^{p-2} v (i+1)
     ≤ (p/(p-1))^{p-2} (∫ V n^{p/2})^{2/p} (∫ |S n|^p)^{(p-2)/p}`.

The `L^p` Doob input is the only hypothesis; the Bochner integrals are finite by the stated
integrability. -/
theorem crossTerm_le_variance_of_doob [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    {ξ v : ℕ → Ω → ℝ} (n : ℕ) (hv : ∀ i, 0 ≤ᵐ[μ] v i)
    (hMmem : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 2))
      (ENNReal.ofReal (p / (p - 2))) μ)
    (hVmem : MemLp (crossTermVariance v n) (ENNReal.ofReal (p / 2)) μ)
    (hint : Integrable (fun ω => crossTermMax ξ n ω ^ (p - 2) * crossTermVariance v n ω) μ)
    (hintL : Integrable (fun ω => ∑ i ∈ Finset.range n,
      |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) μ)
    (hdoob : ∫ ω, crossTermMax ξ n ω ^ p ∂μ
      ≤ (p / (p - 1)) ^ p * ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) ∂μ
      ≤ (p / (p - 1)) ^ (p - 2)
        * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p) := by
  have hbase := crossTerm_integral_le hp n hv hMmem hVmem hint hintL
  have hMnn : (0 : ℝ) ≤ ∫ ω, crossTermMax ξ n ω ^ p ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (crossTermMax_nonneg ξ n ω) p)
  have hAnn : (0 : ℝ) ≤ ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (abs_nonneg _) p)
  have hVnn_ae : 0 ≤ᵐ[μ] crossTermVariance v n := by
    filter_upwards [ae_all_iff.mpr hv] with ω hω
    exact Finset.sum_nonneg fun i _ => hω (i + 1)
  have hVpnn : (0 : ℝ) ≤ (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p) :=
    Real.rpow_nonneg
      (integral_nonneg_of_ae (hVnn_ae.mono fun ω hω => Real.rpow_nonneg hω (p / 2))) _
  have hpow : (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ ((p - 2) / p)
      ≤ ((p / (p - 1)) ^ p * ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ)
          ^ ((p - 2) / p) :=
    Real.rpow_le_rpow hMnn hdoob (by positivity)
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hq : (0 : ℝ) ≤ p / (p - 1) := le_of_lt (div_pos hp0 hp1)
  have hconst : ((p / (p - 1)) ^ p * ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ)
        ^ ((p - 2) / p)
      = (p / (p - 1)) ^ (p - 2)
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hq p) hAnn,
      ← Real.rpow_mul hq p ((p - 2) / p)]
    congr 1
    field_simp
  have hstep : (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ ((p - 2) / p)
        * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
      ≤ (p / (p - 1)) ^ (p - 2)
        * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p) := by
    have hle := mul_le_mul_of_nonneg_right (hpow.trans_eq hconst) hVpnn
    calc (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ ((p - 2) / p)
          * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
        ≤ ((p / (p - 1)) ^ (p - 2)
            * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p))
          * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p) := hle
      _ = (p / (p - 1)) ^ (p - 2)
            * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
            * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p) := by ring
  exact hbase.trans hstep

end LatticeProb
