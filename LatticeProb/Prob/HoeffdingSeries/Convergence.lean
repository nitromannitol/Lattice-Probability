import LatticeProb.Prob.HoeffdingSeries.Finite
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence

/-!
# Convergence of independent series with square-summable weights

The inclusive partial sums form a martingale for the natural filtration of the summands.
The finite variance estimate gives an `L¹` bound and hence almost sure convergence.
Fatou's lemma applied to the tails then gives convergence in `L²`.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}

omit [IsProbabilityMeasure P] in
/-- The partial sums are measurable whenever each summand is measurable. -/
theorem measurable_seriesPartialSum (hm : ∀ n, Measurable (X n)) (a : ℕ → ℝ) (N : ℕ) :
    Measurable (seriesPartialSum X a N) := by
  exact Finset.measurable_fun_sum _ fun n _ => measurable_const.mul (hm n)

/-- Finite partial sums have uniformly bounded `L²` seminorms under square summability. -/
theorem eLpNorm_seriesPartialSum_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) (N : ℕ) :
    eLpNorm (seriesPartialSum X a N) 2 P ≤
      ENNReal.ofReal (∑' n, a n ^ 2) ^ (1 / 2 : ℝ) := by
  apply (eLpNorm_weighted_sum_le hm hi hc hb a (Finset.range N)).trans
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (ha.sum_le_tsum _ (fun n _ => sq_nonneg (a n)))) (by norm_num)

/-- Inclusive partial sums are a martingale for the natural filtration of the weighted terms. -/
theorem martingale_seriesPartialSum_succ (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (a : ℕ → ℝ) :
    Martingale (fun N => seriesPartialSum X a (N + 1))
      (Filtration.natural (fun n ω => a n * X n ω)
        (fun n => (measurable_const.mul (hm n)).stronglyMeasurable)) P := by
  let Y : ℕ → Ω → ℝ := fun n ω => a n * X n ω
  have hYm n : StronglyMeasurable (Y n) :=
    (measurable_const.mul (hm n)).stronglyMeasurable
  let F := Filtration.natural Y hYm
  have had : StronglyAdapted F (fun N => seriesPartialSum X a (N + 1)) := by
    intro N
    apply Finset.stronglyMeasurable_fun_sum
    intro n hn
    exact (Filtration.stronglyAdapted_natural hYm n).mono
      (F.mono (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  have hint N : Integrable (seriesPartialSum X a N) P :=
    (memLp_weighted_sum hm hc hb a (Finset.range N)).integrable (by norm_num)
  apply martingale_of_condExp_sub_eq_zero_nat had (fun N => hint (N + 1))
  intro N
  have heq : seriesPartialSum X a (N + 1 + 1) - seriesPartialSum X a (N + 1) =
      Y (N + 1) := by
    ext ω
    simp only [seriesPartialSum, Pi.sub_apply, Finset.sum_range_succ, add_sub_cancel_left, Y]
  rw [heq]
  have hcond := iIndepFun.condExp_natural_ae_eq_of_lt hYm
    (iIndepFun_weighted hi a) (Nat.lt_succ_self N)
  filter_upwards [hcond] with ω hω
  simpa only [Y, integral_const_mul, hc, mul_zero, Pi.zero_apply] using hω

/-- Square-summable independent centered bounded summands converge almost surely. -/
theorem ae_exists_tendsto_seriesPartialSum (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, Tendsto (fun N => seriesPartialSum X a N ω) atTop (𝓝 L) := by
  have hbdd N : eLpNorm (seriesPartialSum X a (N + 1)) 1 P ≤
      ENNReal.ofReal (∑' n, a n ^ 2) ^ (1 / 2 : ℝ) := by
    apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (measurable_seriesPartialSum hm a (N + 1)).aestronglyMeasurable).trans
    exact eLpNorm_seriesPartialSum_le hm hi hc hb ha (N + 1)
  have hmart := (martingale_seriesPartialSum_succ hm hi hc hb a).submartingale
  have hconv := hmart.exists_ae_tendsto_of_bdd (R :=
      (ENNReal.ofReal (∑' n, a n ^ 2) ^ (1 / 2 : ℝ)).toNNReal) (by
        intro N
        rw [ENNReal.coe_toNNReal
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne]
        exact hbdd N)
  filter_upwards [hconv] with ω hω
  obtain ⟨L, hL⟩ := hω
  exact ⟨L, (tendsto_add_atTop_iff_nat 1).mp hL⟩

/-- The canonical limit agrees almost surely with the convergent series. -/
theorem ae_tendsto_seriesLimit (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => seriesPartialSum X a N ω) atTop
      (𝓝 (seriesLimit X a ω)) := by
  filter_upwards [ae_exists_tendsto_seriesPartialSum hm hi hc hb ha] with ω hω
  exact tendsto_nhds_limUnder hω

/-- The canonical limit is almost everywhere measurable. -/
theorem aemeasurable_seriesLimit (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    AEMeasurable (seriesLimit X a) P :=
  aemeasurable_of_tendsto_metrizable_ae'
    (fun N => (measurable_seriesPartialSum hm a N).aemeasurable)
    (ae_tendsto_seriesLimit hm hi hc hb ha)

/-- The almost sure limit belongs to `L²`, by Fatou and the uniform variance bound. -/
theorem memLp_seriesLimit (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    MemLp (seriesLimit X a) 2 P := by
  refine ⟨(aemeasurable_seriesLimit hm hi hc hb ha).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (eLpNorm_seriesPartialSum_le hm hi hc hb ha))
    (fun N => (measurable_seriesPartialSum hm a N).aestronglyMeasurable)
    (ae_tendsto_seriesLimit hm hi hc hb ha))
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- Finite increments satisfy the square-sum tail bound. -/
theorem eLpNorm_seriesPartialSum_sub_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2))
    {N M : ℕ} (hNM : N ≤ M) :
    eLpNorm (seriesPartialSum X a M - seriesPartialSum X a N) 2 P ≤
      ENNReal.ofReal ((∑' n, a n ^ 2) - ∑ n ∈ Finset.range N, a n ^ 2) ^
        (1 / 2 : ℝ) := by
  have heq : seriesPartialSum X a M - seriesPartialSum X a N =
      (fun ω => ∑ n ∈ Finset.Ico N M, a n * X n ω) := by
    ext ω
    exact (Finset.sum_Ico_eq_sub _ hNM).symm
  rw [heq]
  apply (eLpNorm_weighted_sum_le hm hi hc hb a (Finset.Ico N M)).trans
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_Ico_eq_sub _ hNM]
  exact sub_le_sub_right (ha.sum_le_tsum _ (fun n _ => sq_nonneg (a n))) _

/-- Fatou transfers the finite increment bound to the error from the infinite sum. -/
theorem eLpNorm_seriesPartialSum_sub_limit_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) (N : ℕ) :
    eLpNorm (seriesPartialSum X a N - seriesLimit X a) 2 P ≤
      ENNReal.ofReal ((∑' n, a n ^ 2) - ∑ n ∈ Finset.range N, a n ^ 2) ^
        (1 / 2 : ℝ) := by
  have heq : seriesPartialSum X a N - seriesLimit X a =
      -(seriesLimit X a - seriesPartialSum X a N) := by abel
  rw [heq, eLpNorm_neg]
  apply Lp.eLpNorm_le_of_ae_tendsto
    (eventually_atTop.mpr ⟨N, fun M hNM =>
      eLpNorm_seriesPartialSum_sub_le hm hi hc hb ha hNM⟩)
    (fun M => ((measurable_seriesPartialSum hm a M).sub
      (measurable_seriesPartialSum hm a N)).aestronglyMeasurable)
  filter_upwards [ae_tendsto_seriesLimit hm hi hc hb ha] with ω hω
  exact hω.sub_const _

/-- Partial sums converge in `L²` to the same canonical limit as their almost sure limit. -/
theorem tendsto_eLpNorm_seriesPartialSum_sub_limit (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    Tendsto (fun N => eLpNorm (seriesPartialSum X a N - seriesLimit X a) 2 P)
      atTop (𝓝 0) := by
  let varianceSum : ℝ := ∑' n, a n ^ 2
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, a n ^ 2)
      atTop (𝓝 varianceSum) := ha.hasSum.tendsto_sum_nat
  have hconstant : Tendsto (fun _ : ℕ => varianceSum) atTop (𝓝 varianceSum) :=
    tendsto_const_nhds
  have htailReal : Tendsto
      (fun N => varianceSum - ∑ n ∈ Finset.range N, a n ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self] using hconstant.sub hsum
  have htail : Tendsto (fun N =>
      ENNReal.ofReal ((∑' n, a n ^ 2) - ∑ n ∈ Finset.range N, a n ^ 2) ^
        (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal htailReal).ennrpow_const (1 / 2 : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le) (eLpNorm_seriesPartialSum_sub_limit_le hm hi hc hb ha)

end LatticeProb
