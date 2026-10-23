import LatticeProb.Prob.HoeffdingSeries.Convergence

/-!
# Hoeffding bounds for the infinite sum

Fatou's lemma passes the finite sub-Gaussian moment-generating function bounds to the almost
sure limit. Applying the two one-sided Chernoff bounds gives the stated absolute tail estimate.
The zero square-sum case gives an almost surely zero limit.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}

omit [IsProbabilityMeasure P] in
/-- The `L¹` seminorm of an exponential is its moment-generating function. -/
theorem eLpNorm_exp_mul_one {Y : Ω → ℝ} {c : ℝ≥0} (hY : HasSubgaussianMGF Y c P)
    (t : ℝ) :
    eLpNorm (fun ω => Real.exp (t * Y ω)) 1 P = ENNReal.ofReal (mgf Y P t) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (hY.integrable_exp_mul t)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => Real.norm_of_nonneg (Real.exp_nonneg _)

/-- Uniform sub-Gaussian bounds pass to an almost sure limit by Fatou's lemma. -/
theorem hasSubgaussianMGF_of_ae_tendsto {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    {c : ℕ → ℝ≥0} {C : ℝ≥0} (hY : ∀ n, HasSubgaussianMGF (Y n) (c n) P)
    (hc : ∀ n, c n ≤ C) (hz : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    HasSubgaussianMGF Z C P := by
  have hm : AEMeasurable Z P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hY n).aemeasurable) hz
  have hbound t : eLpNorm (fun ω => Real.exp (t * Z ω)) 1 P ≤
      ENNReal.ofReal (Real.exp (C * t ^ 2 / 2)) := by
    have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Real.exp (t * Y n ω)) atTop
        (𝓝 (Real.exp (t * Z ω))) := by
      filter_upwards [hz] with ω hω
      exact (tendsto_const_nhds.mul hω).rexp
    have hfinite n : eLpNorm (fun ω => Real.exp (t * Y n ω)) 1 P ≤
        ENNReal.ofReal (Real.exp (C * t ^ 2 / 2)) := by
      rw [eLpNorm_exp_mul_one (hY n) t]
      apply ENNReal.ofReal_le_ofReal
      apply ((hY n).mgf_le t).trans
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hc n)) (sq_nonneg t))
        (by norm_num)
    exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hfinite)
      (fun n => ((hY n).integrable_exp_mul t).aestronglyMeasurable) hconv
  have hint t : Integrable (fun ω => Real.exp (t * Z ω)) P := by
    apply (show MemLp (fun ω => Real.exp (t * Z ω)) 1 P from
      ⟨(hm.const_mul t).exp.aestronglyMeasurable,
        (hbound t).trans_lt ENNReal.ofReal_lt_top⟩).integrable le_rfl
  refine ⟨hint, fun t => ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp
  calc
    ENNReal.ofReal (mgf Z P t) = eLpNorm (fun ω => Real.exp (t * Z ω)) 1 P := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hint t)]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun ω =>
        (Real.norm_of_nonneg (Real.exp_nonneg _)).symm)
    _ ≤ ENNReal.ofReal (Real.exp (C * t ^ 2 / 2)) := hbound t

/-- The infinite weighted series has sub-Gaussian parameter equal to its square-sum. -/
theorem hasSubgaussianMGF_seriesLimit (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    HasSubgaussianMGF (seriesLimit X a)
      ⟨∑' n, a n ^ 2, tsum_nonneg (fun n => sq_nonneg (a n))⟩ P := by
  apply hasSubgaussianMGF_of_ae_tendsto
    (fun N => hasSubgaussianMGF_weighted_sum hm hi hc hb a (Finset.range N)) _
    (ae_tendsto_seriesLimit hm hi hc hb ha)
  intro N
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum]
  change (∑ n ∈ Finset.range N, a n ^ 2) ≤ (∑' n, a n ^ 2)
  exact ha.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg (a n))

/-- A sub-Gaussian variable satisfies the two-sided Chernoff bound. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF {Y : Ω → ℝ} {c : ℝ≥0}
    (hY : HasSubgaussianMGF Y c P) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Y ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c))) := by
  have hpos : P {ω | t ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hY.measure_ge_le ht)
  have hneg : P {ω | t ≤ -Y ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hY.neg.measure_ge_le ht)
  calc
    P {ω | t ≤ |Y ω|} ≤ P ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω}) := by
      apply measure_mono
      intro ω hω
      change t ≤ |Y ω| at hω
      change t ≤ Y ω ∨ t ≤ -Y ω
      by_cases hy : 0 ≤ Y ω
      · exact Or.inl (by simpa only [abs_of_nonneg hy] using hω)
      · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hy)] using hω)
    _ ≤ P {ω | t ≤ Y ω} + P {ω | t ≤ -Y ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := add_le_add hpos hneg
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c))) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1
      ring

/-- Hoeffding's inequality for the limit, with denominator twice the sum of squared weights. -/
theorem measure_abs_seriesLimit_ge_le (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2))
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |seriesLimit X a ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑' n, a n ^ 2))) :=
  measure_abs_ge_le_of_hasSubgaussianMGF (hasSubgaussianMGF_seriesLimit hm hi hc hb ha) ht.le

/-- If the square-sum vanishes, the infinite series vanishes almost surely. -/
theorem seriesLimit_ae_eq_zero_of_tsum_sq_eq_zero (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2))
    (hz : (∑' n, a n ^ 2) = 0) : seriesLimit X a =ᵐ[P] 0 := by
  have h := hasSubgaussianMGF_seriesLimit hm hi hc hb ha
  have heq : (⟨∑' n, a n ^ 2, tsum_nonneg (fun n => sq_nonneg (a n))⟩ : ℝ≥0) = 0 :=
    NNReal.eq hz
  rw [heq] at h
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

/-- The canonical limit supplies the almost sure, `L²`, and tail conclusions together. -/
theorem hoeffding_series (hm : ∀ n, Measurable (X n))
    (hi : iIndepFun X P) (hc : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) (ha : Summable (fun n => a n ^ 2)) :
    MemLp (seriesLimit X a) 2 P ∧
      Tendsto (fun N => eLpNorm (seriesPartialSum X a N - seriesLimit X a) 2 P)
        atTop (𝓝 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => seriesPartialSum X a N ω) atTop
        (𝓝 (seriesLimit X a ω))) ∧
      (∀ t : ℝ, 0 < t → P {ω | t ≤ |seriesLimit X a ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑' n, a n ^ 2)))) :=
  ⟨memLp_seriesLimit hm hi hc hb ha,
    tendsto_eLpNorm_seriesPartialSum_sub_limit hm hi hc hb ha,
    ae_tendsto_seriesLimit hm hi hc hb ha,
    fun _ ht => measure_abs_seriesLimit_ge_le hm hi hc hb ha ht⟩

end LatticeProb
