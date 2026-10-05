/-
# The maximal-form cross-term helper for the Bernstein/Rosenthal bound

Real martingale partial sums `S k = ∑_{i ∈ Icc 1 k} ξ i` along a filtration `F`, with the
predictable quadratic variation increments `v i`, satisfy the cumulative cross-term dominated
by the running maximum times the total variation:

  `∑_{i < n} |S i|^{p-2} · v (i+1) ≤ (max_{k ≤ n} |S k|)^{p-2} · ∑_{i < n} v (i+1)`

and, by Hölder, its integral is bounded by `(∫ (max |S|)^p)^{(p-2)/p} (∫ V^{p/2})^{2/p}`.  The
running maximum is then controlled by Doob's maximal inequality for the partial sums.  These are
the genuine objects of Pinelis's cumulative argument, not a norm sum for an unrelated adapted
process.

Nothing here is a new external input; the file is not imported by the root.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- The partial sum `S k = ∑_{i ∈ Icc 1 k} ξ i` of a sequence of increments. -/
noncomputable def crossTermPartialSum (ξ : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.Icc 1 k, ξ i ω

/-- The running maximum `max_{k ≤ n} |S k|` of the partial sums. -/
noncomputable def crossTermMax (ξ : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (n + 1)).sup' nonempty_range_add_one
    (fun k => |crossTermPartialSum ξ k ω|)

/-- The running maximum is non-negative. -/
theorem crossTermMax_nonneg (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ crossTermMax ξ n ω := by
  have h0 : |crossTermPartialSum ξ 0 ω| ≤ crossTermMax ξ n ω :=
    Finset.le_sup' (s := Finset.range (n + 1))
      (f := fun k => |crossTermPartialSum ξ k ω|)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  exact le_trans (abs_nonneg _) h0

/-- **Finite-maximum domination.**  For `p ≥ 2` and a non-negative weight `v`, the cumulative
cross term of the partial sums is dominated by `(max_{k ≤ n} |S k|)^{p-2}` times the total
weight `∑_{i<n} v (i+1)`. -/
theorem crossTerm_le_max_mul {p : ℝ} (hp : 2 ≤ p) (ξ : ℕ → Ω → ℝ)
    (v : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (hv : ∀ i, 0 ≤ v i ω) :
    ∑ i ∈ Finset.range n, |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω
      ≤ crossTermMax ξ n ω ^ (p - 2) * ∑ i ∈ Finset.range n, v (i + 1) ω := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hle : ∀ i ∈ Finset.range n,
      |crossTermPartialSum ξ i ω| ≤ crossTermMax ξ n ω := by
    intro i hi
    exact Finset.le_sup' (s := Finset.range (n + 1))
      (f := fun k => |crossTermPartialSum ξ k ω|)
      (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
  calc ∑ i ∈ Finset.range n, |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω
      ≤ ∑ i ∈ Finset.range n, crossTermMax ξ n ω ^ (p - 2) * v (i + 1) ω :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (abs_nonneg _) (hle i hi) hp2) (hv (i + 1))
    _ = crossTermMax ξ n ω ^ (p - 2) * ∑ i ∈ Finset.range n, v (i + 1) ω := by
        rw [Finset.mul_sum]

/-- **Doob's maximal inequality for the partial sums.**  If `S k = ∑_{i ≤ k} ξ i` is a
martingale for the filtration `F`, then the running maximum of `|S k|` obeys the classical
maximal bound `ε · μ{max_{k≤n}|S k| ≥ ε} ≤ ∫_{max ≥ ε} |S n|`. -/
theorem doob_maximal_crossTerm [IsProbabilityMeasure μ] {F : Filtration ℕ m₀}
    {ξ : ℕ → Ω → ℝ} (hmart : Martingale (crossTermPartialSum ξ) F μ)
    (n : ℕ) {ε : ℝ≥0} :
    ε * μ {ω | (ε : ℝ) ≤ crossTermMax ξ n ω}
      ≤ ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ crossTermMax ξ n ω},
          |crossTermPartialSum ξ n ω| ∂μ) := by
  have hsub : Submartingale (fun k ω => |crossTermPartialSum ξ k ω|) F μ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      exact continuous_abs.comp_stronglyMeasurable (hmart.stronglyMeasurable k)
    · intro i j hij
      filter_upwards [hmart.condExp_ae_eq hij,
        abs_condExp_ae_le_condExp_abs (μ := μ) (m := F i) (crossTermPartialSum ξ j)]
        with ω h1 h2
      simp only [Pi.abs_apply] at h2
      rw [h1] at h2
      exact h2
    · intro k
      exact (hmart.integrable k).abs
  have h := maximal_ineq (μ := μ) (ε := ε) (𝒢 := F)
    (f := fun k ω => |crossTermPartialSum ξ k ω|) hsub
    (fun k ω => abs_nonneg (crossTermPartialSum ξ k ω)) n
  simpa only [crossTermMax] using h

/-- **Hölder bound for the cross term.**  With `M = max_{k≤n}|S k|` and `V = ∑_{i<n} v (i+1)`,
`∫ M^{p-2} V ≤ (∫ M^p)^{(p-2)/p} (∫ V^{p/2})^{2/p}` for `p > 2`, by Hölder with the
conjugate exponents `p/(p-2)` and `p/2`.  Combined with the two results above it bounds the
cumulative cross term by the Doob maximum and the predictable variation. -/
theorem crossTerm_integral_le [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 < p)
    {ξ v : ℕ → Ω → ℝ} (n : ℕ)
    (hv : ∀ i, 0 ≤ᵐ[μ] v i)
    (hMmem : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 2))
      (ENNReal.ofReal (p / (p - 2))) μ)
    (hVmem : MemLp (fun ω => ∑ i ∈ Finset.range n, v (i + 1) ω)
      (ENNReal.ofReal (p / 2)) μ)
    (hint : Integrable (fun ω => crossTermMax ξ n ω ^ (p - 2)
      * (∑ i ∈ Finset.range n, v (i + 1) ω)) μ)
    (hintL : Integrable (fun ω => ∑ i ∈ Finset.range n,
      |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) μ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) ∂μ
      ≤ (∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ ((p - 2) / p)
        * (∫ ω, (∑ i ∈ Finset.range n, v (i + 1) ω) ^ (p / 2) ∂μ) ^ (2 / p) := by
  have hp2 : 0 < p - 2 := by linarith
  have hp0 : 0 < p := by linarith
  -- pointwise domination, a.e., from the non-negativity of the weights
  have hpoint : ∀ᵐ ω ∂μ, (∑ i ∈ Finset.range n,
        |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω)
      ≤ crossTermMax ξ n ω ^ (p - 2) * ∑ i ∈ Finset.range n, v (i + 1) ω := by
    filter_upwards [ae_all_iff.mpr hv] with ω hω
    exact crossTerm_le_max_mul hp.le ξ v n ω (fun i => hω i)
  have hmono := integral_mono_ae hintL hint hpoint
  -- Hölder with exponents p/(p-2) and p/2
  have hconj : Real.HolderConjugate (p / (p - 2)) (p / 2) := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp2]; linarith
    · field_simp
      ring
  have hMnn : 0 ≤ᵐ[μ] fun ω => crossTermMax ξ n ω ^ (p - 2) :=
    Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (crossTermMax_nonneg ξ n ω) (p - 2)
  have hVnn : 0 ≤ᵐ[μ] fun ω => ∑ i ∈ Finset.range n, v (i + 1) ω := by
    filter_upwards [ae_all_iff.mpr hv] with ω hω
    exact Finset.sum_nonneg fun i _ => hω (i + 1)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj hMnn hVnn hMmem hVmem
  -- identify the two right-hand powers
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

end LatticeProb
