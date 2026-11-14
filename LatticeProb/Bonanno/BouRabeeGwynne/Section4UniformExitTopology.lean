/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Section4UniformExitTopology at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-! Compact starting sets turn uniform continuous-test estimates into uniform
Lévy–Prokhorov estimates. No assertion about masses of discontinuous cells is made. -/

open MeasureTheory Filter
open scoped Topology Classical BoundedContinuousFunction

namespace BouRabeeGwynne

/-- Uniform bounded-continuous-test comparison with a continuous probability
kernel on a compact starting space implies uniform LP comparison. The finite
or varying discrete starting spaces need no topology. -/
theorem uniform_levyProkhorovDist_of_uniform_test_error
    {d : ℕ} {P : Type*} [PseudoMetricSpace P] [CompactSpace P]
    (V : ℕ → Type*) (p : ∀ n, V n → P)
    (μ : ∀ n, V n → ProbabilityMeasure (Euc d))
    (ν : P → ProbabilityMeasure (Euc d)) (hν : Continuous ν)
    (htest : ∀ f : Euc d →ᵇ ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ v : V n, |(∫ x, f x ∂(μ n v : Measure (Euc d))) -
        ∫ x, f x ∂(ν (p n v) : Measure (Euc d))| < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      levyProkhorovDist (μ n v : Measure (Euc d))
        (ν (p n v) : Measure (Euc d)) < ε := by
  intro ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ∃ v : V n,
      ε ≤ levyProkhorovDist (μ n v : Measure (Euc d))
        (ν (p n v) : Measure (Euc d)) := by
    simpa only [Filter.Frequently, not_exists, not_le] using hnot
  obtain ⟨σ, hσ, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose v hv using hbad
  obtain ⟨z, φ, hφ, hp⟩ := SeqCompactSpace.tendsto_subseq (fun j => p (σ j) (v j))
  let μs : ℕ → ProbabilityMeasure (Euc d) := fun j => μ (σ (φ j)) (v (φ j))
  let νs : ℕ → ProbabilityMeasure (Euc d) := fun j => ν (p (σ (φ j)) (v (φ j)))
  have hn : Tendsto (σ ∘ φ) atTop atTop := hσ.tendsto_atTop.comp hφ.tendsto_atTop
  have hνs : Tendsto νs atTop (𝓝 (ν z)) := by
    simpa only [νs, Function.comp_def] using (hν.tendsto z).comp hp
  have hμs : Tendsto μs atTop (𝓝 (ν z)) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have herr : Tendsto (fun j =>
        (∫ x, f x ∂(μs j : Measure (Euc d))) -
          ∫ x, f x ∂(νs j : Measure (Euc d))) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro η hη
      filter_upwards [hn.eventually (htest f η hη)] with j hj
      simpa only [μs, νs, Real.dist_eq, sub_zero, Function.comp_apply] using hj (v (φ j))
    have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hνs f
    simpa only [sub_add_cancel, zero_add] using herr.add hlim
  have hμLP : Tendsto (fun j => LevyProkhorov.ofMeasure (μs j)) atTop
      (𝓝 (LevyProkhorov.ofMeasure (ν z))) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hμs
  have hνLP : Tendsto (fun j => LevyProkhorov.ofMeasure (νs j)) atTop
      (𝓝 (LevyProkhorov.ofMeasure (ν z))) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hνs
  have hdist : Tendsto (fun j => levyProkhorovDist
      (μs j : Measure (Euc d)) (νs j : Measure (Euc d))) atTop (𝓝 0) := by
    simpa only [LevyProkhorov.dist_probabilityMeasure_def, dist_self] using hμLP.dist hνLP
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hdist).2 ε hε).exists
  exact (not_lt_of_ge (hv (φ j))) hj

end BouRabeeGwynne
