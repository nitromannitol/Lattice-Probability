import Mathlib
import LatticeProb.Prob.ConvergingTogetherProjection

/-!
# Integrals against random probability measures that are close in the Lévy-Prokhorov distance

Let `D n` be random elements of a pseudo-metrizable second countable space `S` that converge in law,
`π : S → Prob(E)` a continuous map into the probability measures on a separable pseudo-metric space `E`
(weak topology), and `κ n` random probability measures on `E` with
`levyProkhorovDist (κ n) (π (D n)) → 0` in probability.  Then for every bounded *continuous* `f`
(not only Lipschitz ones)

`E |∫ f d(κ n) - ∫ f d(π (D n))| → 0`.

For a bounded Lipschitz `f` this is immediate from `|∫ f dμ - ∫ f dν| ≤ (L + 2‖f‖) levyProkhorovDist μ ν`
(the integrand is also bounded); for a bounded continuous `f` it needs the convergence in law of `π (D n)`:
the pair `(π (D n), κ n)` converges in law to a pair on the diagonal (converging together, with the
Lévy-Prokhorov metric on `Prob(E)`, which metrizes the weak topology on a separable `E`).

* `LatticeProb.tendsto_integral_abs_integral_sub_of_tendstoInMeasure_levyProkhorovDist`: this statement.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- **Closeness of integrals against random measures.**  If `D n` converges in law, `π` is a continuous
map into the probability measures of a separable pseudo-metric space `E`, and the random probability
measures `κ n` are within Lévy-Prokhorov distance of `π (D n)` tending to `0` in probability, then for
every bounded continuous `f` the mean absolute difference `E |∫ f d(κ n) - ∫ f d(π (D n))|` tends
to `0`. -/
theorem tendsto_integral_abs_integral_sub_of_tendstoInMeasure_levyProkhorovDist
    {Ω S E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure E))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure E))]
    {D : ℕ → Ω → S} (hD : ∀ n, AEMeasurable (D n) P)
    {κ : ℕ → Ω → ProbabilityMeasure E}
    (hκ : ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure (κ n ω)) P)
    {π : S → ProbabilityMeasure E} (hπ : Continuous π) {ν : Measure S}
    (hlaw : ∀ g : S →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω) ∂P) atTop (𝓝 (∫ d, g d ∂ν)))
    (hκπ : TendstoInMeasure P
      (fun n ω => levyProkhorovDist (κ n ω : Measure E) (π (D n ω) : Measure E)) atTop 0)
    (f : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, |∫ x, f x ∂(κ n ω : Measure E) - ∫ x, f x ∂(π (D n ω) : Measure E)| ∂P)
      atTop (𝓝 0) := by
  classical
  have hπ' : Continuous fun d => LevyProkhorov.ofMeasure (π d) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hπ
  -- the trivial second coordinate
  have hι : Continuous fun d : S => (d, PUnit.unit) := continuous_id.prodMk continuous_const
  have hlaw' : ∀ g : (S × PUnit) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω, (fun _ : Ω => PUnit.unit) ω) ∂P) atTop
        (𝓝 (∫ p, g p ∂(ν.map fun d : S => (d, PUnit.unit)))) := by
    intro g
    have h := hlaw (g.compContinuous ⟨fun d : S => (d, PUnit.unit), hι⟩)
    have e : ∫ p, g p ∂(ν.map fun d : S => (d, PUnit.unit)) = ∫ d, g (d, PUnit.unit) ∂ν :=
      integral_map hι.measurable.aemeasurable g.continuous.aestronglyMeasurable
    rw [e]
    exact h
  have key := tendsto_integral_projection_of_tendstoInMeasure_dist (P := P)
    (M := LevyProkhorov (ProbabilityMeasure E)) (𝒞 := PUnit) hD
    (Y := fun n ω => LevyProkhorov.ofMeasure (κ n ω)) hκ
    (Q := fun _ _ => PUnit.unit) (fun _ => aemeasurable_const) (s := fun _ => 0) (s₀ := 0)
    (π := fun d => LevyProkhorov.ofMeasure (π d)) hπ' hlaw' hκπ tendsto_const_nhds
  -- the test function
  have hbd : ∀ μ : ProbabilityMeasure E, |∫ x, f x ∂(μ : Measure E)| ≤ ‖f‖ := fun μ => by
    have := norm_integral_le_of_norm_le_const (μ := (μ : Measure E)) (f := fun x => f x)
      (C := ‖f‖) (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    simpa using this
  have hc1 : Continuous fun m : LevyProkhorov (ProbabilityMeasure E) =>
      ∫ x, f x ∂((LevyProkhorov.toMeasure m : ProbabilityMeasure E) : Measure E) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
      LevyProkhorov.continuous_toMeasure_probabilityMeasure
  have hc2 : Continuous fun d : S => ∫ x, f x ∂(π d : Measure E) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hπ
  let Gf : (S × LevyProkhorov (ProbabilityMeasure E) × PUnit × ℝ≥0) → ℝ := fun p =>
    |∫ x, f x ∂((LevyProkhorov.toMeasure p.2.1 : ProbabilityMeasure E) : Measure E) -
      ∫ x, f x ∂(π p.1 : Measure E)|
  have hGc : Continuous Gf :=
    (((hc1.comp (continuous_fst.comp continuous_snd))).sub (hc2.comp continuous_fst)).abs
  have hu : ∀ p, Gf p ≤ 2 * ‖f‖ := fun p => by
    have h1 := hbd (LevyProkhorov.toMeasure p.2.1)
    have h2 := hbd (π p.1)
    show |_ - _| ≤ _
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hn : ∀ p, 0 ≤ Gf p := fun p => abs_nonneg _
  let G : (S × LevyProkhorov (ProbabilityMeasure E) × PUnit × ℝ≥0) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨Gf, hGc⟩ (2 * ‖f‖) (fun p q => by
      rw [Real.dist_eq, abs_le]
      have h1 := hu p
      have h2 := hu q
      have h3 := hn p
      have h4 := hn q
      show -(2 * ‖f‖) ≤ Gf p - Gf q ∧ Gf p - Gf q ≤ 2 * ‖f‖
      constructor <;> linarith)
  have hz : ∫ p, G (p.1, LevyProkhorov.ofMeasure (π p.1), p.2, 0)
      ∂(ν.map fun d : S => (d, PUnit.unit)) = 0 := by
    have h0 : ∀ p : S × PUnit, G (p.1, LevyProkhorov.ofMeasure (π p.1), p.2, 0) = 0 := fun p => by
      show |(∫ x, f x ∂(π p.1 : Measure E)) - ∫ x, f x ∂(π p.1 : Measure E)| = 0
      simp
    simp [h0]
  have hk := key G
  rw [hz] at hk
  exact Tendsto.congr (fun n => rfl) hk

end LatticeProb
