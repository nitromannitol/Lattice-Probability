import Mathlib
import LatticeProb.Prob.ConditionalLawApproxKernelLimit
import LatticeProb.Prob.ConditionalExpectationContraction
import LatticeProb.Prob.RandomMeasureIntegralCloseness

/-!
# Conditional law of a limit of Markov chains in a random environment (Markov step)

Let `D n` be random elements of a pseudo-metrizable second countable space `S` converging in law to `νS`,
and let `Φ : S → E`, `Ψ : S → F` be continuous, so that `(Φ (D n), Ψ (D n))` converges in law to
`ν = νS.map (Φ, Ψ)`.  Suppose there are σ-algebras `G n` with `σ(Ψ (D n)) ≤ G n` (the past of a chain
together with its environment) and random probability measures `κ n` (quenched transition laws) such that
`E[f (Φ (D n)) | G n] = ∫ f d(κ n)` almost surely for every bounded continuous `f`, while `κ n` is close
in probability, in the Lévy-Prokhorov distance, to `p (Ψ (D n))` for a continuous map `p` from `F` to the
probability measures on `E` (weak topology).  Then the conditional law of the limit `Φ` given `Ψ` under `ν` is
`p`: `ν.map swap = ν.snd ⊗ₘ p`.

* `LatticeProb.compProd_eq_of_markov_step`: this statement.  It combines the criterion for convergence of
  conditional laws with approximate conditional expectations
  (`LatticeProb.compProd_eq_of_approx_condexp_tendsto`), the `L¹` contraction of conditional expectations
  towards the coarser σ-algebra `σ(Ψ (D n))` (`LatticeProb.integral_abs_condExpGiven_sub_le`) and the
  closeness of integrals against random measures
  (`LatticeProb.tendsto_integral_abs_integral_sub_of_tendstoInMeasure_levyProkhorovDist`).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- **Markov step for limits of chains in a random environment.**  See the module documentation.  The data
`D n` converge in law to `νS`; `Φ, Ψ` are continuous; `G n` are σ-algebras between `σ(Ψ (D n))` and the
ambient one; `κ n` are random probability measures with the conditional expectation identity
`E[f (Φ (D n)) | G n] = ∫ f d(κ n)` for bounded continuous `f`; and `levyProkhorovDist (κ n) (p (Ψ (D n)))`
tends to `0` in probability for a continuous `p : F → Prob(E)`.  Then the limit pair `(Φ, Ψ)`, with law
`νS.map (Φ, Ψ)`, has the Markov kernel `p` as regular conditional law of the first coordinate given the
second. -/
theorem compProd_eq_of_markov_step
    {Ω S E F : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure E))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure E))]
    {D : ℕ → Ω → S} (hD : ∀ n, Measurable (D n))
    {νS : Measure S} [IsProbabilityMeasure νS]
    (hlawS : ∀ g : S →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω) ∂μ) atTop (𝓝 (∫ d, g d ∂νS)))
    {Φ : S → E} (hΦ : Continuous Φ) {Ψ : S → F} (hΨ : Continuous Ψ)
    {p : F → ProbabilityMeasure E} (hp : Continuous p)
    {G : ℕ → MeasurableSpace Ω}
    (hYG : ∀ n, MeasurableSpace.comap (fun ω => Ψ (D n ω)) inferInstance ≤ G n)
    (hG : ∀ n, G n ≤ m₀)
    {κ : ℕ → Ω → ProbabilityMeasure E}
    (hκ : ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure (κ n ω)) μ)
    (hMarkov : ∀ (n : ℕ) (f : E →ᵇ ℝ),
      μ[fun ω => f (Φ (D n ω)) | G n] =ᵐ[μ] fun ω => ∫ x, f x ∂(κ n ω : Measure E))
    (hclose : TendstoInMeasure μ
      (fun n ω => levyProkhorovDist (κ n ω : Measure E) (p (Ψ (D n ω)) : Measure E)) atTop 0) :
    ∃ κ' : Kernel F E, IsMarkovKernel κ' ∧ (∀ y, κ' y = p y) ∧
      (νS.map fun d => (Φ d, Ψ d)).map Prod.swap =
        (νS.map fun d => (Φ d, Ψ d)).snd ⊗ₘ κ' := by
  classical
  have hΦm : Measurable Φ := hΦ.measurable
  have hΨm : Measurable Ψ := hΨ.measurable
  have hΘ : Continuous fun d => (Φ d, Ψ d) := hΦ.prodMk hΨ
  have hΘm : Measurable fun d => (Φ d, Ψ d) := hΘ.measurable
  have hνS : IsProbabilityMeasure (νS.map fun d => (Φ d, Ψ d)) :=
    inferInstance
  have hlaw : ∀ g : (E × F) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (Φ (D n ω), Ψ (D n ω)) ∂μ) atTop
        (𝓝 (∫ q, g q ∂(νS.map fun d => (Φ d, Ψ d)))) := fun g => by
    have h := hlawS (g.compContinuous ⟨_, hΘ⟩)
    have h2 : ∫ q, g q ∂(νS.map fun d => (Φ d, Ψ d)) = ∫ d, g (Φ d, Ψ d) ∂νS :=
      integral_map hΘm.aemeasurable g.continuous.aestronglyMeasurable
    rw [h2]
    exact h
  have hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂(p y : Measure E) := fun f =>
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hp).measurable
  have hB : ∀ f : E →ᵇ ℝ, ∃ B : ℕ → Ω → ℝ, (∀ n, Measurable (B n)) ∧ (∀ n, Integrable (B n) μ) ∧
      Tendsto (fun n => ∫ ω, |condExpGiven μ (fun ω => Φ (D n ω)) (fun ω => Ψ (D n ω)) f ω
        - B n ω| ∂μ) atTop (𝓝 0) ∧
      ∀ g : (ℝ × F) →ᵇ ℝ, Tendsto (fun n => ∫ ω, g (B n ω, Ψ (D n ω)) ∂μ) atTop
        (𝓝 (∫ q, g (∫ x, f x ∂(p q.2 : Measure E), q.2) ∂(νS.map fun d => (Φ d, Ψ d)))) := by
    intro f
    have hb : Continuous fun y : F => ∫ x, f x ∂(p y : Measure E) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hp
    have hbm : Measurable fun y : F => ∫ x, f x ∂(p y : Measure E) := hb.measurable
    have hbd : ∀ y : F, ‖∫ x, f x ∂(p y : Measure E)‖ ≤ ‖f‖ := fun y => by
      have := norm_integral_le_of_norm_le_const (μ := (p y : Measure E)) (f := ⇑f) (C := ‖f‖)
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
      simpa using this
    have hBm : ∀ n, Measurable fun ω => ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E) := fun n =>
      hbm.comp (hΨm.comp (hD n))
    have hBi : ∀ n, Integrable (fun ω => ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E)) μ := fun n =>
      Integrable.of_bound (hBm n).aestronglyMeasurable ‖f‖
        (Filter.Eventually.of_forall fun ω => hbd _)
    refine ⟨fun n ω => ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E), hBm, hBi, ?_, ?_⟩
    · have hcl := tendsto_integral_abs_integral_sub_of_tendstoInMeasure_levyProkhorovDist
        (P := μ) (D := D) (fun n => (hD n).aemeasurable) hκ (π := fun d => p (Ψ d))
        (hp.comp hΨ) hlawS hclose f
      refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_) hcl
      calc ∫ ω, |condExpGiven μ (fun ω => Φ (D n ω)) (fun ω => Ψ (D n ω)) f ω
              - ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E)| ∂μ
          ≤ ∫ ω, |μ[fun ω => f (Φ (D n ω)) | G n] ω
              - ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E)| ∂μ :=
            integral_abs_condExpGiven_sub_le (G := G n) (m₀ := m₀) (fun ω => Φ (D n ω))
              (fun ω => Ψ (D n ω)) f (hYG n) (hG n) hbm (hBi n)
        _ = ∫ ω, |∫ x, f x ∂(κ n ω : Measure E)
              - ∫ x, f x ∂(p (Ψ (D n ω)) : Measure E)| ∂μ :=
            integral_congr_ae (by
              filter_upwards [hMarkov n f] with ω h
              rw [h])
    · intro g
      have hgc : Continuous fun q : E × F => g (∫ x, f x ∂(p q.2 : Measure E), q.2) :=
        g.continuous.comp ((hb.comp continuous_snd).prodMk continuous_snd)
      have h := hlawS (g.compContinuous
        ⟨fun d => (∫ x, f x ∂(p (Ψ d) : Measure E), Ψ d), (hb.comp hΨ).prodMk hΨ⟩)
      have h2 : ∫ q, g (∫ x, f x ∂(p q.2 : Measure E), q.2) ∂(νS.map fun d => (Φ d, Ψ d)) =
          ∫ d, g (∫ x, f x ∂(p (Ψ d) : Measure E), Ψ d) ∂νS :=
        integral_map hΘm.aemeasurable hgc.aestronglyMeasurable
      rw [h2]
      exact h
  exact compProd_eq_of_approx_condexp_tendsto (ι := ℕ) (l := atTop) (Ω := fun _ => Ω)
    (μ := fun _ => μ) (X := fun n ω => Φ (D n ω)) (Y := fun n ω => Ψ (D n ω))
    (fun n => hΦm.comp (hD n)) (fun n => hΨm.comp (hD n)) hlaw
    (P := fun y => (p y : Measure E)) hP hB

end LatticeProb
