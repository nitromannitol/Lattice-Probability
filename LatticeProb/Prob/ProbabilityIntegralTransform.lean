import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The probability integral transform

If a probability measure `μ` on `ℝ` has a continuous cumulative distribution function `F = cdf μ`,
then `F` pushes `μ` forward to the uniform distribution on the unit interval: if `Y` has law `μ`,
then `F(Y)` is uniform on `[0, 1]`. In particular this holds for every law without atoms, for
instance a nondegenerate Gaussian law, so a nondegenerate real Gaussian variable is a measurable
function of itself with uniform law; any variable independent of it is then independent of a
uniform variable.

## Main results

* `ProbabilityTheory.cdfUnit μ`: the cumulative distribution function as a map `ℝ → [0, 1]`.
* `ProbabilityTheory.continuous_cdf`: the cdf of an atomless probability measure is continuous.
* `ProbabilityTheory.measure_cdf_le`: if `cdf μ` is continuous then `μ {F ≤ t} = t` for `t ∈ [0, 1]`.
* `ProbabilityTheory.map_cdfUnit`: if `cdf μ` is continuous then `μ.map (cdfUnit μ) = volume`.
* `ProbabilityTheory.map_cdfUnit_comp`, `ProbabilityTheory.map_cdfUnit_gaussianReal_comp`: the same
  for a random variable `Y`, `F(Y)` being uniform on `[0, 1]`.
-/

open MeasureTheory Set Filter Topology unitInterval
open scoped NNReal

namespace ProbabilityTheory

variable {μ : Measure ℝ}

/-- The cumulative distribution function of `μ`, as a map into the unit interval. -/
noncomputable def cdfUnit (μ : Measure ℝ) (x : ℝ) : I :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩

@[simp]
theorem coe_cdfUnit (μ : Measure ℝ) (x : ℝ) : (cdfUnit μ x : ℝ) = cdf μ x := rfl

theorem measurable_cdfUnit (μ : Measure ℝ) : Measurable (cdfUnit μ) :=
  (monotone_cdf μ).measurable.subtype_mk

/-- **The cdf of an atomless law is continuous.** -/
theorem continuous_cdf [IsProbabilityMeasure μ] [NullSingletonClass μ] : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) h

/-- **The sublevel sets of a continuous cdf.** If `F = cdf μ` is continuous, then for
`0 ≤ t ≤ 1` the set `{x | F x ≤ t}` has `μ`-measure `t`. -/
theorem measure_cdf_le [IsProbabilityMeasure μ] (hF : Continuous (cdf μ)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : μ {x | cdf μ x ≤ t} = ENNReal.ofReal t := by
  rcases ht1.eq_or_lt with rfl | ht1
  · have h1 : {x | cdf μ x ≤ 1} = univ := eq_univ_of_forall fun x => cdf_le_one μ x
    rw [h1, measure_univ, ENNReal.ofReal_one]
  set S := {x | cdf μ x ≤ t} with hS
  have hclosed : IsClosed S := isClosed_le hF continuous_const
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x ≥ x₀, t < cdf μ x :=
    ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1)).exists_forall_of_atTop
  have hbdd : BddAbove S := ⟨x₀, fun x hx => by
    by_contra h
    exact absurd (hx₀ x (not_le.1 h).le) (not_lt.2 hx)⟩
  rcases S.eq_empty_or_nonempty with hempty | hne
  · have ht : t = 0 := by
      refine le_antisymm (ge_of_tendsto' (tendsto_cdf_atBot μ) fun x => ?_) ht0
      by_contra h
      have hx : x ∈ S := (not_le.1 h).le
      rw [hempty] at hx
      exact hx
    rw [hempty, measure_empty, ht, ENNReal.ofReal_zero]
  · have hs : sSup S ∈ S := hclosed.csSup_mem hne hbdd
    have hSeq : S = Iic (sSup S) := by
      ext x
      exact ⟨fun hx => le_csSup hbdd hx, fun hx => le_trans (monotone_cdf μ hx) hs⟩
    have hFs : cdf μ (sSup S) = t := by
      refine le_antisymm hs ?_
      by_contra h
      obtain ⟨ε, hε, hball⟩ :=
        Metric.eventually_nhds_iff.1 (hF.continuousAt.eventually (gt_mem_nhds (not_le.1 h)))
      have hmem : sSup S + ε / 2 ∈ S := (hball (by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
        linarith)).le
      have := le_csSup hbdd hmem
      linarith
    rw [hSeq, ← ofReal_cdf, hFs]

/-- **The probability integral transform.** If `cdf μ` is continuous, the cdf pushes `μ`
forward to the uniform distribution on the unit interval. -/
theorem map_cdfUnit [IsProbabilityMeasure μ] (hF : Continuous (cdf μ)) :
    μ.map (cdfUnit μ) = volume := by
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply (measurable_cdfUnit μ) measurableSet_Iic, unitInterval.volume_Iic a]
  have h1 : cdfUnit μ ⁻¹' Iic a = {x | cdf μ x ≤ a} := by
    ext x
    show cdfUnit μ x ≤ a ↔ cdf μ x ≤ (a : ℝ)
    exact Subtype.coe_le_coe.symm
  rw [h1, measure_cdf_le hF a.2.1 a.2.2]

/-- **The probability integral transform of a random variable.** If `Y` has a law with
continuous cdf `F`, then `F(Y)` is uniform on the unit interval. -/
theorem map_cdfUnit_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : Measurable Y) (hF : Continuous (cdf (P.map Y))) :
    P.map (fun ω => cdfUnit (P.map Y) (Y ω)) = volume := by
  rw [← map_cdfUnit hF, Measure.map_map (measurable_cdfUnit _) hY]
  rfl

/-- **A nondegenerate Gaussian variable gives a uniform variable.** If `Y` has the law
`𝒩(m, v)` with `v ≠ 0` and `Φ` is the cdf of that law, then `Φ(Y)` is uniform on the unit
interval. -/
theorem map_cdfUnit_gaussianReal_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : P.map Y = gaussianReal m v) :
    P.map (fun ω => cdfUnit (gaussianReal m v) (Y ω)) = volume := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have h := map_cdfUnit_comp hY (P := P) (by rw [hlaw]; exact continuous_cdf)
  rwa [hlaw] at h

end ProbabilityTheory
