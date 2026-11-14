import Mathlib

/-!
# Strong `L^p` Lebesgue points

A measurable function `G : E → F` on a finite-dimensional real normed space whose `p`-th power of
the norm is integrable over every compact subset of an open set `U` (`1 ≤ p`) has strong `L^p`
Lebesgue points at almost every point of `U`:
`⨍_{B_r(x)} ‖G y - G x‖ ^ p ∂μ → 0` as `r → 0+`, for the closed balls `B_r(x)` and an additive Haar
measure `μ`.

The proof compares `G` with the elements `A` of a countable dense subset of `F`. For each `A`,
the Lebesgue differentiation theorem of Mathlib (`VitaliFamily.ae_tendsto_lintegral_div` for the
Vitali family of closed balls) applies to the integrable function
`K.indicator (‖G - A‖ ^ p)` for a compact `K`. The elementary inequality
`‖a + b‖ ^ p ≤ 2 ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p)` transfers the limit from `A` to `G x`.

## Main statement

* `LatticeProb.PegdenSmart.lp_lebesgue_points`: the strong `L^p` Lebesgue points are almost all
  of `U`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal

namespace LatticeProb.PegdenSmart

section Pointwise

variable {F : Type*} [NormedAddCommGroup F]

/-- The `p`-th power of the extended norm of a difference, bounded through an intermediate point,
for `1 ≤ p`. -/
theorem enorm_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c : F) :
    ‖a - c‖ₑ ^ p ≤ 2 ^ (p - 1) * (‖a - b‖ₑ ^ p + ‖b - c‖ₑ ^ p) := by
  have h : ‖a - c‖ₑ ≤ ‖a - b‖ₑ + ‖b - c‖ₑ := by
    simpa [sub_add_sub_cancel] using enorm_add_le (a - b) (b - c)
  exact (ENNReal.rpow_le_rpow h (by linarith)).trans
    (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)

variable {α : Type*} [MeasurableSpace α]

/-- Integrated form of `enorm_sub_rpow_le` for a function `G`. -/
theorem lintegral_enorm_sub_rpow_le {p : ℝ} (hp : 1 ≤ p) (ν : Measure α) (G : α → F)
    (A B : F) :
    ∫⁻ y, ‖G y - B‖ₑ ^ p ∂ν ≤
      2 ^ (p - 1) * (∫⁻ y, ‖G y - A‖ₑ ^ p ∂ν + ‖A - B‖ₑ ^ p * ν univ) := by
  calc ∫⁻ y, ‖G y - B‖ₑ ^ p ∂ν
      ≤ ∫⁻ y, 2 ^ (p - 1) * (‖G y - A‖ₑ ^ p + ‖A - B‖ₑ ^ p) ∂ν :=
        lintegral_mono fun y => enorm_sub_rpow_le hp _ _ _
    _ = 2 ^ (p - 1) * (∫⁻ y, ‖G y - A‖ₑ ^ p ∂ν + ‖A - B‖ₑ ^ p * ν univ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
          lintegral_add_right _ measurable_const, lintegral_const]

end Pointwise

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]

/-- Lebesgue differentiation for `‖G - A‖ ^ p` at the interior points of a compact set `K`. -/
theorem ae_tendsto_lintegral_enorm_sub_rpow_div {p : ℝ} (hp : 1 ≤ p) {G : E → F}
    (hG : Measurable G) {K : Set E} (hK : IsCompact K) (hint : ∫⁻ x in K, ‖G x‖ₑ ^ p ∂μ < ⊤)
    (A : F) : ∀ᵐ x ∂μ, x ∈ interior K → Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖G y - A‖ₑ ^ p ∂μ) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 (‖G x - A‖ₑ ^ p)) := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hmeas : Measurable fun y => ‖G y - A‖ₑ ^ p :=
    ((hG.sub_const A).enorm).pow_const p
  have hfin : ∫⁻ y in K, ‖G y - A‖ₑ ^ p ∂μ ≠ ⊤ := by
    have h := lintegral_enorm_sub_rpow_le hp (μ.restrict K) G 0 A
    simp only [sub_zero, zero_sub, enorm_neg] at h
    refine ne_top_of_le_ne_top ?_ h
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
      (ENNReal.add_ne_top.2 ⟨hint.ne, ENNReal.mul_ne_top ?_ ?_⟩)
    · exact (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
    · simpa [Measure.restrict_apply_univ] using hK.measure_lt_top.ne
  have hv := (IsUnifLocDoublingMeasure.vitaliFamily μ 1).ae_tendsto_lintegral_div
    (f := K.indicator fun y => ‖G y - A‖ₑ ^ p) (hmeas.indicator hKm).aemeasurable
    (by rwa [lintegral_indicator hKm])
  filter_upwards [hv] with x hx hxK
  have hlim : Tendsto (fun r : ℝ => closedBall x r) (𝓝[>] 0)
      ((IsUnifLocDoublingMeasure.vitaliFamily μ 1).filterAt x) :=
    IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt μ (fun _ => x) (fun r => r)
      tendsto_id (by
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [one_mul]
        exact mem_closedBall_self (le_of_lt hr))
  have hx' := hx.comp hlim
  rw [indicator_of_mem (interior_subset hxK)] at hx'
  refine hx'.congr' ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hxK)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ε := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hε)] with r hr using hr
  filter_upwards [hev] with r hr
  simp only [Function.comp_apply]
  congr 1
  refine setLIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
  exact indicator_of_mem (hball (closedBall_subset_ball hr hy)) _

omit [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- If the averages of `‖G - A‖ ^ p` over the closed balls around `x` converge to `‖G x - A‖ ^ p`
for every `A` in a dense sequence of `F`, then the averages of `‖G - G x‖ ^ p` tend to `0`. -/
theorem tendsto_lintegral_enorm_sub_rpow_div_zero {p : ℝ} (hp : 1 ≤ p) {G : E → F} {x : E}
    (D : ℕ → F) (hD : DenseRange D)
    (hx : ∀ n, Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖G y - D n‖ₑ ^ p ∂μ) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 (‖G x - D n‖ₑ ^ p))) :
    Tendsto (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p ∂μ) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hne : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  have hc0 : Continuous fun A : F => ‖G x - A‖ₑ ^ p :=
    ENNReal.continuous_rpow_const.comp (continuous_enorm.comp (continuous_const.sub continuous_id))
  have hcont : Continuous fun A : F => 2 ^ (p - 1) * (‖G x - A‖ₑ ^ p + ‖G x - A‖ₑ ^ p) :=
    (ENNReal.continuous_const_mul hne).comp (hc0.add hc0)
  have hzero : 2 ^ (p - 1) * (‖G x - G x‖ₑ ^ p + ‖G x - G x‖ₑ ^ p) = 0 := by
    simp [ENNReal.zero_rpow_of_pos hp0]
  obtain ⟨n, hn⟩ := hD.exists_mem_open (isOpen_lt hcont continuous_const)
    (⟨G x, by change _ < ε; rw [hzero]; exact hε⟩ : {A : F |
      2 ^ (p - 1) * (‖G x - A‖ₑ ^ p + ‖G x - A‖ₑ ^ p) < ε}.Nonempty)
  have hlt : 2 ^ (p - 1) * (‖G x - D n‖ₑ ^ p + ‖G x - D n‖ₑ ^ p) < ε := hn
  have hup : Tendsto (fun r => 2 ^ (p - 1) *
      ((∫⁻ y in closedBall x r, ‖G y - D n‖ₑ ^ p ∂μ) / μ (closedBall x r) +
        ‖G x - D n‖ₑ ^ p)) (𝓝[>] 0)
      (𝓝 (2 ^ (p - 1) * (‖G x - D n‖ₑ ^ p + ‖G x - D n‖ₑ ^ p))) :=
    ENNReal.Tendsto.const_mul ((hx n).add tendsto_const_nhds)
      (Or.inr hne)
  filter_upwards [hup.eventually (gt_mem_nhds hlt), self_mem_nhdsWithin] with r hr hr0
  refine le_trans ?_ hr.le
  have hm0 : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr0).ne'
  have hmt : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p ∂μ
      ≤ 2 ^ (p - 1) * (∫⁻ y in closedBall x r, ‖G y - D n‖ₑ ^ p ∂μ +
        ‖D n - G x‖ₑ ^ p * (μ.restrict (closedBall x r)) univ) :=
        lintegral_enorm_sub_rpow_le hp _ G (D n) (G x)
    _ = 2 ^ (p - 1) * ((∫⁻ y in closedBall x r, ‖G y - D n‖ₑ ^ p ∂μ) / μ (closedBall x r) +
        ‖G x - D n‖ₑ ^ p) * μ (closedBall x r) := by
        rw [mul_assoc, add_mul, ENNReal.div_mul_cancel hm0 hmt, Measure.restrict_apply_univ,
          enorm_sub_rev (D n) (G x), mul_comm (‖G x - D n‖ₑ ^ p)]

variable [SecondCountableTopology F]

/-- Strong `L^p` Lebesgue points of a measurable function on an open set `U`, for the closed balls
and an additive Haar measure: the averages `⨍_{B_r(x)} ‖G - G x‖ ^ p` tend to `0` for almost
every `x ∈ U`, provided `‖G‖ ^ p` is integrable over each compact subset of `U`. -/
theorem lp_lebesgue_points_of_haar {p : ℝ} (hp : 1 ≤ p) {U : Set E} {G : E → F}
    (hU : IsOpen U) (hG : Measurable G)
    (hint : ∀ C : Set E, IsCompact C → C ⊆ U → ∫⁻ x in C, ‖G x‖ₑ ^ p ∂μ < ⊤) :
    ∀ᵐ x ∂(μ.restrict U), Tendsto
      (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p ∂μ) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  rw [ae_restrict_iff' hU.measurableSet]
  have hr : ∀ x : E, ∃ r : ℝ, 0 < r ∧ (x ∈ U → closedBall x r ⊆ U) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 hU x hx
      exact ⟨ε / 2, half_pos hε, fun _ => (closedBall_subset_ball (half_lt_self hε)).trans h⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr0 hrU using hr
  obtain ⟨t, htU, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := U)
    (f := fun x => ball x (r x)) fun x _ => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x))
  have : Countable t := htc.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ (c : t) (n : ℕ), x ∈ interior (closedBall (c : E) (r c)) → Tendsto
      (fun s => (∫⁻ y in closedBall x s, ‖G y - TopologicalSpace.denseSeq F n‖ₑ ^ p ∂μ) /
        μ (closedBall x s)) (𝓝[>] 0) (𝓝 (‖G x - TopologicalSpace.denseSeq F n‖ₑ ^ p)) :=
    ae_all_iff.2 fun c => ae_all_iff.2 fun n =>
      ae_tendsto_lintegral_enorm_sub_rpow_div hp hG (isCompact_closedBall _ _)
        (hint _ (isCompact_closedBall _ _) (hrU c (htU c.2))) _
  filter_upwards [hall] with x hx hxU
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.1 (hcov hxU)
  exact tendsto_lintegral_enorm_sub_rpow_div_zero hp (TopologicalSpace.denseSeq F)
    (TopologicalSpace.denseRange_denseSeq F)
    fun n => hx ⟨c, hct⟩ n (ball_subset_interior_closedBall hxc)

end Haar

universe u v

/-- Strong `L^p` Lebesgue points (`1 ≤ p`): for a measurable `G` with `‖G‖ ^ p` integrable over
every compact subset of an open set `U`, the averages of `‖G y - G x‖ ^ p` over the closed balls
around `x` tend to `0` for almost every `x ∈ U`. -/
theorem lp_lebesgue_points :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ), 1 ≤ p →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F]
        [MeasurableSpace F] [BorelSpace F] (U : Set E) (G : E → F), IsOpen U → Measurable G →
        (∀ C : Set E, IsCompact C → C ⊆ U → ∫⁻ x in C, ‖G x‖ₑ ^ p ∂μ < ⊤) →
        ∀ᵐ x ∂(μ.restrict U), Tendsto
          (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p ∂μ) / μ (closedBall x r))
          (𝓝[>] 0) (𝓝 0) := by
  intro E _ _ _ _ _ μ _ p hp F _ _ _ _ _ U G hU hG hint
  exact lp_lebesgue_points_of_haar hp hU hG hint

end LatticeProb.PegdenSmart
