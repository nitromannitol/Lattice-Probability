import Mathlib
import LatticeProb.Prob.ProbabilityMeasureMixture

/-!
# Interpolation of a family of probability measures indexed by a cover

Let `Z` be a pseudo-metric space and `H : ι → Set Z` a family of nonempty sets covering `Z` such
that every ball meets only finitely many of them. Given probability measures `Q k` and `ε > 0`,
the *interpolated law* at `z ∈ Z` is the mixture of the `Q k` with weights proportional to
`(ε - dist(z, H k))₊`. Only the indices with `dist(z, H k) < ε` carry positive weight.

* the interpolated law depends continuously on `z` for the weak topology;
* a probability measure that is within `L` of `Q k` for each `k` with `dist(z, H k) < ε` is within
  `L` of the interpolated law at `z` in the Lévy–Prokhorov distance.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LatticeProb

section Interp

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*}

/-- The weight `(ε - dist(z, H k))₊` of the `k`-th set at the point `z`. -/
noncomputable def interpWeight (H : ι → Set Z) (ε : ℝ) (k : ι) (z : Z) : ℝ≥0 :=
  Real.toNNReal (ε - Metric.infDist z (H k))

theorem continuous_interpWeight (H : ι → Set Z) (ε : ℝ) (k : ι) :
    Continuous (interpWeight H ε k) :=
  continuous_real_toNNReal.comp (continuous_const.sub (Metric.continuous_infDist_pt (H k)))

theorem interpWeight_ne_zero_iff (H : ι → Set Z) (ε : ℝ) (k : ι) (z : Z) :
    interpWeight H ε k z ≠ 0 ↔ Metric.infDist z (H k) < ε := by
  simp [interpWeight, Real.toNNReal_eq_zero]

/-- A ball meets only finitely many of the sets, so the weights are locally finite. -/
theorem interpWeight_locallyFinite {H : ι → Set Z} (hne : ∀ k, (H k).Nonempty) (ε : ℝ)
    (hfin : ∀ (z : Z) (R : ℝ), {k | ∃ x ∈ H k, dist x z < R}.Finite) (z : Z) :
    ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite := by
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, (hfin z (ε + 1)).subset ?_⟩
  rintro k ⟨y, hy, hk⟩
  rw [interpWeight_ne_zero_iff, Metric.infDist_lt_iff (hne k)] at hk
  obtain ⟨x, hx, hxy⟩ := hk
  refine ⟨x, hx, ?_⟩
  have := dist_triangle x y z
  rw [dist_comm x y] at this
  have hy' := Metric.mem_ball.1 hy
  linarith

/-- If the sets cover `Z` and `ε > 0`, some weight is positive at every point. -/
theorem exists_interpWeight_ne_zero {H : ι → Set Z} {ε : ℝ} (hε : 0 < ε)
    (hcov : ∀ z, ∃ k, z ∈ H k) (z : Z) : ∃ k, interpWeight H ε k z ≠ 0 := by
  obtain ⟨k, hk⟩ := hcov z
  exact ⟨k, (interpWeight_ne_zero_iff H ε k z).2 (by rwa [Metric.infDist_zero_of_mem hk])⟩

variable {E : Type*} [MeasurableSpace E]

/-- The interpolated law at `z`: the mixture of the `Q k` with weights proportional to
`(ε - dist(z, H k))₊`. -/
noncomputable def interpLaw (H : ι → Set Z) (ε : ℝ)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) (z : Z) :
    ProbabilityMeasure E :=
  weightedMixturePM (hasSum_normalizedWeight hloc hpos z) Q

/-- The interpolated law depends continuously on the point. -/
theorem continuous_interpLaw [TopologicalSpace E] [OpensMeasurableSpace E] {H : ι → Set Z}
    {ε : ℝ} (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) :
    Continuous (interpLaw H ε hloc hpos Q) :=
  continuous_normalizedMixturePM (continuous_interpWeight H ε) hloc hpos Q

/-- A probability measure within Lévy–Prokhorov distance `L` of every `Q k` with
`dist(z, H k) < ε` is within `L` of the interpolated law at `z`. -/
theorem levyProkhorovDist_interpLaw_le [PseudoMetricSpace E] [OpensMeasurableSpace E]
    {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E)
    (ν : ProbabilityMeasure E) (z : Z) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ k, Metric.infDist z (H k) < ε →
      levyProkhorovDist (ν : Measure E) (Q k : Measure E) ≤ L) :
    levyProkhorovDist (ν : Measure E) (interpLaw H ε hloc hpos Q z : Measure E) ≤ L := by
  unfold interpLaw
  rw [coe_weightedMixturePM]
  refine levyProkhorovDist_weightedMixture_le (hasSum_normalizedWeight hloc hpos z)
    (ν : Measure E) (fun k => (Q k : Measure E)) hL0 (fun k hk => hL k ?_)
  rw [← interpWeight_ne_zero_iff]
  intro h0
  exact hk (by simp [normalizedWeight, h0])

end Interp

end LatticeProb
