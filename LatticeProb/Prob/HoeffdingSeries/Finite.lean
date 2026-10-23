import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Finite estimates for weighted independent bounded variables

Centered random variables bounded in absolute value by one have sub-Gaussian parameter one.
Their independent weighted sums have variance at most the sum of the squared weights.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}

/-- The partial sum with indices strictly less than `N`. -/
def seriesPartialSum (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range N, a n * X n ω

/-- The canonical pointwise limit of the partial sums, wherever they converge. -/
noncomputable def seriesLimit (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (ω : Ω) : ℝ :=
  limUnder atTop (fun N => seriesPartialSum X a N ω)

omit [MeasurableSpace Ω] in
/-- On every convergent path, the canonical series limit is its unique real limit. -/
theorem seriesLimit_eq_of_tendsto {ω : Ω} {L : ℝ}
    (h : Tendsto (fun N => seriesPartialSum X a N ω) atTop (𝓝 L)) :
    seriesLimit X a ω = L := h.limUnder_eq

omit [IsProbabilityMeasure P] in
/-- An absolute bound by one gives membership in the interval `[-1, 1]` almost surely. -/
theorem ae_mem_Icc_of_abs_le_one {Y : Ω → ℝ}
    (hb : ∀ᵐ ω ∂P, |Y ω| ≤ 1) : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc (-1) 1 := by
  filter_upwards [hb] with ω hω using abs_le.mp hω

/-- A centered variable bounded by one has sub-Gaussian parameter one. -/
theorem hasSubgaussianMGF_of_abs_le_one {Y : Ω → ℝ} (hm : Measurable Y)
    (hc : ∫ ω, Y ω ∂P = 0) (hb : ∀ᵐ ω ∂P, |Y ω| ≤ 1) :
    HasSubgaussianMGF Y 1 P := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    (ae_mem_Icc_of_abs_le_one hb) hc
  norm_num [show (‖(1 : ℝ) - -1‖₊ : ℝ≥0) = 2 by
    apply NNReal.eq; norm_num] at h
  exact h

omit [IsProbabilityMeasure P] in
/-- Multiplying each independent variable by a deterministic weight preserves independence. -/
theorem iIndepFun_weighted (hi : iIndepFun X P) (a : ℕ → ℝ) :
    iIndepFun (fun n ω => a n * X n ω) P :=
  hi.comp (fun n x => a n * x) (fun _ => measurable_const.mul measurable_id)

/-- Every finite weighted sum has the sum of the squared weights as sub-Gaussian parameter. -/
theorem hasSubgaussianMGF_weighted_sum (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (a : ℕ → ℝ) (s : Finset ℕ) :
    HasSubgaussianMGF (fun ω => ∑ n ∈ s, a n * X n ω)
      (∑ n ∈ s, (⟨a n ^ 2, sq_nonneg (a n)⟩ : ℝ≥0)) P := by
  apply HasSubgaussianMGF.sum_of_iIndepFun (iIndepFun_weighted hi a)
  intro n _
  simpa using (hasSubgaussianMGF_of_abs_le_one (hm n) (hc n) (hb n)).const_mul (a n)

/-- Centered bounded variables and all their finite weighted sums belong to `L²`. -/
theorem memLp_weighted_sum (hm : ∀ n, Measurable (X n))
    (hc : ∀ n, ∫ ω, X n ω ∂P = 0) (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    MemLp (fun ω => ∑ n ∈ s, a n * X n ω) 2 P := by
  apply memLp_finsetSum
  intro n _
  exact ((hasSubgaussianMGF_of_abs_le_one (hm n) (hc n) (hb n)).memLp 2).const_mul _

/-- A finite weighted sum of the centered variables is centered. -/
theorem integral_weighted_sum (hm : ∀ n, Measurable (X n))
    (hc : ∀ n, ∫ ω, X n ω ∂P = 0) (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    ∫ ω, (∑ n ∈ s, a n * X n ω) ∂P = 0 := by
  rw [integral_finsetSum]
  · simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero]
  · intro n _
    exact (hasSubgaussianMGF_of_abs_le_one (hm n) (hc n) (hb n)).integrable.const_mul _

/-- Independence removes the cross terms in the variance of a finite weighted sum. -/
theorem variance_weighted_sum_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (a : ℕ → ℝ) (s : Finset ℕ) :
    variance (fun ω => ∑ n ∈ s, a n * X n ω) P ≤ ∑ n ∈ s, a n ^ 2 := by
  have hmem n : MemLp (fun ω => a n * X n ω) 2 P :=
    ((hasSubgaussianMGF_of_abs_le_one (hm n) (hc n) (hb n)).memLp 2).const_mul _
  have hv := IndepFun.variance_sum (s := s) (fun n _ => hmem n)
    (fun i _ j _ hij => (iIndepFun_weighted hi a).indepFun hij)
  have heq : (∑ n ∈ s, fun ω => a n * X n ω) =
      (fun ω => ∑ n ∈ s, a n * X n ω) := by ext ω; simp only [Finset.sum_apply]
  rw [heq] at hv
  rw [hv]
  apply Finset.sum_le_sum
  intro n _
  rw [variance_const_mul]
  have hvar : variance (X n) P ≤ 1 := by
    simpa using variance_le_sq_of_bounded (ae_mem_Icc_of_abs_le_one (hb n))
      (hm n).aemeasurable
  simpa using mul_le_mul_of_nonneg_left hvar (sq_nonneg (a n))

/-- For a centered variable, the `L²` seminorm is the square root of its variance. -/
theorem eLpNorm_two_eq_variance_rpow {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hc : ∫ ω, Y ω ∂P = 0) :
    eLpNorm Y 2 P = ENNReal.ofReal (variance Y P) ^ (1 / 2 : ℝ) := by
  rw [hY.ofReal_variance_eq, evariance,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [hc, sub_zero, ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- The `L²` bound for a finite weighted sum, with the exact square-sum normalization. -/
theorem eLpNorm_weighted_sum_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (a : ℕ → ℝ) (s : Finset ℕ) :
    eLpNorm (fun ω => ∑ n ∈ s, a n * X n ω) 2 P ≤
      ENNReal.ofReal (∑ n ∈ s, a n ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_two_eq_variance_rpow (memLp_weighted_sum hm hc hb a s)
    (integral_weighted_sum hm hc hb a s)]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (variance_weighted_sum_le hm hi hc hb a s)) (by norm_num)

end LatticeProb
