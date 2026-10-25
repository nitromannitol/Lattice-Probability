module

public import LatticeProb.Prob.McLeish.ProductLimit
public import LatticeProb.Prob.McLeish.TruncProduct
public import LatticeProb.Prob.McLeish.RatioLimit
public import LatticeProb.Prob.McLeish.CharFunLimit

@[expose] public section

/-!
# Central limit theorem for martingale difference arrays

For a triangular array of real random variables whose row partial sums are martingales, the
row sums converge in distribution to a centred Gaussian law when the largest squared increment
of each row is integrable with expectations bounded uniformly in the row index, the largest
absolute increment tends to zero in probability, and the sum of squared increments converges in
probability to a constant.

The proof truncates each row by dropping every increment at which the accumulated sum of squares
already exceeds the limit plus one. The truncated row sums agree with the original sums except on
an event of vanishing probability, and their characteristic functions are controlled by the
product `∏ (1 + i t X k)` through the ratio `truncRatio`.
-/

namespace LatticeProb.McLeish

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The increments of a martingale of partial sums are measurable. -/
theorem measurable_increment {P : Measure Ω} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (k : ℕ) :
    Measurable (X k) :=
  ((stronglyMeasurable_increment hX k).mono (ℱ.le (k + 1))).measurable

/-- The partial sums of a martingale of partial sums are measurable. -/
theorem measurable_sum_range {P : Measure Ω} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (n : ℕ) :
    Measurable (fun ω => ∑ k ∈ Finset.range n, X k ω) :=
  Finset.measurable_sum _ fun k _ => measurable_increment hX k

/-- The partial sums of the predictably truncated array are measurable. -/
theorem measurable_sum_trunc {P : Measure Ω} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c : ℝ)
    (n : ℕ) : Measurable (fun ω => ∑ k ∈ Finset.range n, trunc X c k ω) :=
  Finset.measurable_sum _ fun k _ =>
    ((stronglyMeasurable_trunc hX c k).mono (ℱ.le (k + 1))).measurable

/-- If the maximal absolute term of each row tends to zero in probability, then for every
`δ > 0` the probability that some term of the first `t n` exceeds `δ` tends to zero. -/
theorem tendsto_measure_exists_abs_gt (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (t : ℕ → ℕ)
    (ht : ∀ n, 0 < t n)
    (hmax : TendstoInMeasure P
      (fun n ω => (Finset.range (t n)).sup' (Finset.nonempty_range_iff.mpr (ht n).ne')
        (fun k => |X n k ω|))
      atTop (fun _ => 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | ∃ k < t n, δ < |X n k ω|}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hmax
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hmax δ hδ)
    (fun _ => zero_le) fun n => measure_mono ?_
  rintro ω ⟨k, hk, hlt⟩
  have hle := Finset.le_sup' (fun k => |X n k ω|) (Finset.mem_range.2 hk)
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
  exact hlt.le.trans (hle.trans (le_abs_self _))

/-- If the squared sums of a row converge in probability to `σsq` and `c = σsq + 1`, then the
row sums and the sums of the predictably truncated terms differ on an event of vanishing
probability. -/
theorem tendsto_measure_sum_ne_trunc (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (t : ℕ → ℕ)
    (σsq c : ℝ) (hc : c = σsq + 1)
    (hsq : TendstoInMeasure P (fun n ω => ∑ k ∈ Finset.range (t n), X n k ω ^ 2) atTop
      (fun _ => σsq)) :
    Tendsto (fun n => P {ω | ∑ k ∈ Finset.range (t n), X n k ω ≠
      ∑ k ∈ Finset.range (t n), trunc (X n) c k ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hsq
  have hsub : ∀ n, {ω | ∑ k ∈ Finset.range (t n), X n k ω ≠
      ∑ k ∈ Finset.range (t n), trunc (X n) c k ω} ⊆
      {ω | 1 ≤ dist (∑ k ∈ Finset.range (t n), X n k ω ^ 2) σsq} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    apply hω
    have hlt : dist (∑ k ∈ Finset.range (t n), X n k ω ^ 2) σsq < 1 := not_le.mp hcon
    rw [Real.dist_eq, abs_lt] at hlt
    exact (sum_trunc_eq_of_sqSum_le (X n) c (t n) ω (by unfold sqSum; linarith [hlt.2])).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsq 1 one_pos)
    (fun _ => zero_le) fun n => measure_mono (hsub n)

/-- The truncated product is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_prodOneAddI_trunc_row {P : Measure Ω} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c t : ℝ)
    (n : ℕ) : AEStronglyMeasurable (prodOneAddI (trunc X c) t n) P :=
  ((stronglyMeasurable_prodOneAddI (Y := trunc X c) (fun k => stronglyMeasurable_trunc hX c k) t
    n).mono (ℱ.le n)).aestronglyMeasurable

/-- The truncated ratio is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_truncRatio {P : Measure Ω} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c t : ℝ)
    (n : ℕ) : AEStronglyMeasurable (truncRatio X c t n) P := by
  have hnum : Measurable (fun ω =>
      Complex.exp (Complex.I * ((t * ∑ k ∈ Finset.range n, trunc X c k ω : ℝ) : ℂ))) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (measurable_const.mul
        (measurable_sum_trunc hX c n))))
  have hden : Measurable (prodOneAddI (trunc X c) t n) :=
    ((stronglyMeasurable_prodOneAddI (Y := trunc X c) (fun k => stronglyMeasurable_trunc hX c k) t
      n).mono (ℱ.le n)).measurable
  exact (hnum.stronglyMeasurable.div hden.stronglyMeasurable).aestronglyMeasurable

omit [MeasurableSpace Ω] in
/-- The truncated product times the truncated ratio has modulus at most one. -/
theorem norm_prodOneAddI_mul_truncRatio_le (X : ℕ → Ω → ℝ) (c t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodOneAddI (trunc X c) t n ω * truncRatio X c t n ω‖ ≤ 1 := by
  rw [prodOneAddI_mul_truncRatio]
  exact (Complex.norm_exp_I_mul_ofReal _).le

/-- The second moment of the truncated product is bounded by a constant once the mean of the
dominating variable is bounded. -/
theorem memLp_bound_prodOneAddI_trunc {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c t : ℝ) (hc0 : 0 ≤ c)
    (n : ℕ) (M : Ω → ℝ) (hMint : Integrable M P) (hM0 : ∀ ω, 0 ≤ M ω)
    (hM : ∀ ω, ∀ k < n, X k ω ^ 2 ≤ M ω) (C₀ : ℝ) (hC₀ : ∫ ω, M ω ∂P ≤ C₀) :
    MemLp (prodOneAddI (trunc X c) t n) 2 P ∧
      ∫ ω, ‖prodOneAddI (trunc X c) t n ω‖ ^ 2 ∂P ≤
        Real.exp (t ^ 2 * c) * (1 + t ^ 2 * C₀) := by
  obtain ⟨h1, h2⟩ := memLp_prodOneAddI_trunc hX c t hc0 n M hMint hM0 hM
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)⟩
  linarith [mul_le_mul_of_nonneg_left hC₀ (sq_nonneg t)]

/-- **McLeish's central limit theorem for martingale difference arrays** (D. L. McLeish,
*Dependent central limit theorems and invariance principles*, Ann. Probab. 2 (1974),
Theorem 2.3). The row sums of a triangular array whose row partial sums are martingales converge
in distribution to the centred Gaussian law with variance `σsq` when the maximal squared
increments are integrable with means bounded uniformly in the row, the maximal absolute
increments tend to zero in probability, and the sums of squared increments tend to `σsq` in
probability. The case `σsq = 0` is included. -/
theorem tendstoInDistribution_martingale_clt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (𝒳 : ℕ → ℕ → Ω → ℝ) (t : ℕ → ℕ) (ht : ∀ n, 0 < t n) (σsq : ℝ≥0)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ Finset.range k, 𝒳 n j ω) (ℱ n) P)
    (hint : ∀ n, Integrable (fun ω => (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => 𝒳 n k ω ^ 2)) P)
    (hbdd : ∃ C : ℝ, ∀ n, ∫ ω, (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => 𝒳 n k ω ^ 2) ∂P ≤ C)
    (hmax : TendstoInMeasure P
      (fun n ω => (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => |𝒳 n k ω|))
      atTop (fun _ => 0))
    (hsq : TendstoInMeasure P
      (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω ^ 2) atTop (fun _ => (σsq : ℝ))) :
    TendstoInDistribution
      (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (σsq : ℝ) + 1 := ⟨_, rfl⟩
  have hσ : (0 : ℝ) ≤ (σsq : ℝ) := NNReal.coe_nonneg σsq
  have hc0 : 0 ≤ c := by linarith
  have hσc : (σsq : ℝ) < c := by linarith
  obtain ⟨C₀, hC₀⟩ := hbdd
  have hmeas : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω) :=
    fun n => measurable_sum_range (hmart n) (t n)
  have hmeas' : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range (t n), trunc (𝒳 n) c k ω) :=
    fun n => measurable_sum_trunc (hmart n) c (t n)
  have hne := tendsto_measure_sum_ne_trunc P 𝒳 t σsq c hc hsq
  refine tendstoInDistribution_gaussianReal_of_tendsto_integral_exp
    (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω) (fun n => (hmeas n).aemeasurable) σsq
    fun u => ?_
  have hU := tendstoInMeasure_truncRatio 𝒳 t (σsq : ℝ) c u hσ hσc
    (fun δ hδ => tendsto_measure_exists_abs_gt P 𝒳 t ht hmax hδ) hsq
  have hT1 : Tendsto (fun n => ∫ ω, prodOneAddI (trunc (𝒳 n) c) u (t n) ω ∂P) atTop (𝓝 1) :=
    Tendsto.congr (fun n => (integral_prodOneAddI_trunc (hmart n) c u (t n)).symm)
      tendsto_const_nhds
  have hT := tendsto_integral_mul_of_bdd (fun n => prodOneAddI (trunc (𝒳 n) c) u (t n))
    (fun n => truncRatio (𝒳 n) c u (t n)) (Complex.exp ((-((σsq : ℝ) * u ^ 2 / 2) : ℝ) : ℂ))
    (fun n => aestronglyMeasurable_prodOneAddI_trunc_row (hmart n) c u (t n))
    (fun n => aestronglyMeasurable_truncRatio (hmart n) c u (t n))
    ⟨Real.exp (u ^ 2 * c) * (1 + u ^ 2 * C₀), fun n =>
      memLp_bound_prodOneAddI_trunc (hmart n) c u hc0 (t n) _ (hint n)
        (fun ω => le_trans (sq_nonneg (𝒳 n 0 ω))
          (Finset.le_sup' (fun k => 𝒳 n k ω ^ 2) (Finset.mem_range.2 (ht n))))
        (fun ω k hk => Finset.le_sup' (fun k => 𝒳 n k ω ^ 2) (Finset.mem_range.2 hk))
        C₀ (hC₀ n)⟩
    hT1 (fun n ω => norm_prodOneAddI_mul_truncRatio_le (𝒳 n) c u (t n) ω) hU
  have hcongr : ∀ n, ∫ ω, prodOneAddI (trunc (𝒳 n) c) u (t n) ω * truncRatio (𝒳 n) c u (t n) ω ∂P =
      ∫ ω, Complex.exp (Complex.I * ((u * ∑ k ∈ Finset.range (t n), trunc (𝒳 n) c k ω : ℝ) : ℂ))
        ∂P := by
    intro n
    congr 1
    funext ω
    exact prodOneAddI_mul_truncRatio (𝒳 n) c u (t n) ω
  have h' := Tendsto.congr hcongr hT
  exact tendsto_integral_exp_of_tendsto_measure_ne
    (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω)
    (fun n ω => ∑ k ∈ Finset.range (t n), trunc (𝒳 n) c k ω) hmeas hmeas' u _ hne h'

end LatticeProb.McLeish
