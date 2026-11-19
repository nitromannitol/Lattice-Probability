import Mathlib
import LatticeProb.Prob.RandomMeasureIntegralCloseness
import LatticeProb.Prob.ProbabilityMeasureFamilyIntegralContinuity

/-!
# Joint convergence in law from a conditional law that is close to a continuous function of the datum

Let `D n` be random elements of a pseudo-metrizable second countable space `S` converging in law to `ν`,
`π : S → Prob(E)` a continuous map into the probability measures on a separable pseudo-metric space `E`
(weak topology), and `κ n` random probability measures on `E` with
`levyProkhorovDist (κ n) (π (D n)) → 0` in probability.  If `X n` is a random element of `E` whose
conditional law given the environment is `κ n`, then `(D n, X n)` converges in law to the law
`ν ⊗ π` on `S × E` with first marginal `ν` and conditional law `π d` given `d`.  In integral form, for
every bounded continuous `g : S × E → ℝ`,

`E ∫ g (D n, x) d(κ n)(x) → ∫ ∫ g (d, x) d(π d)(x) dν(d)`.

The ingredient is the joint continuity of `(d, μ) ↦ ∫ g (d, x) dμ(x)` on `S × Prob(E)`, which holds without
local compactness of `S` (`continuous_integral_probabilityMeasure_of_continuous_of_seq`), combined with the
converging-together theorem for the pair `(D n, κ n)`.

* `LatticeProb.continuous_integral_prod_levyProkhorov`: the pairing is continuous on `S × LevyProkhorov`.
* `LatticeProb.tendsto_integral_integral_of_tendstoInMeasure_levyProkhorovDist`: the statement above.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- **Joint continuity of the pairing on `S × Prob(E)` with the Lévy-Prokhorov metric.**  For a bounded
continuous `g : S × E → ℝ` on a pseudo-metrizable `S` and a separable pseudo-metrizable `E`, the map
`(d, m) ↦ ∫ g (d, x) dm(x)` is continuous on `S × LevyProkhorov (ProbabilityMeasure E)`. -/
theorem continuous_integral_prod_levyProkhorov {S E : Type*} [TopologicalSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S] [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (g : (S × E) →ᵇ ℝ) :
    Continuous fun p : S × LevyProkhorov (ProbabilityMeasure E) =>
      ∫ x, g (p.1, x) ∂((LevyProkhorov.toMeasure p.2 : ProbabilityMeasure E) : Measure E) := by
  let _ : PseudoMetricSpace S := TopologicalSpace.pseudoMetrizableSpacePseudoMetric S
  have h := continuous_integral_probabilityMeasure_of_continuous_of_seq (E := E) (T := S)
    (G := fun s x => g (s, x)) g.continuous (C := ‖g‖) (fun s x => by
      simpa using g.norm_coe_le_norm (s, x))
  exact h.comp ((LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp continuous_snd).prodMk
    continuous_fst)

/-- **Joint convergence in law from a close conditional law.**  Let `D n` be a.e. measurable random
elements of a pseudo-metrizable second countable Borel space `S` converging in law to `ν`, `π : S → Prob(E)` a
continuous map into the probability measures of a separable pseudo-metric space `E`, and `κ n` random
probability measures on `E` with `levyProkhorovDist (κ n) (π (D n)) → 0` in probability.  Then for every
bounded continuous `g : S × E → ℝ`
`E ∫ g (D n, x) d(κ n)(x) → ∫ ∫ g (d, x) d(π d)(x) dν(d)`. -/
theorem tendsto_integral_integral_of_tendstoInMeasure_levyProkhorovDist
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
    (hlaw : ∀ f : S →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω) ∂P) atTop (𝓝 (∫ d, f d ∂ν)))
    (hκπ : TendstoInMeasure P
      (fun n ω => levyProkhorovDist (κ n ω : Measure E) (π (D n ω) : Measure E)) atTop 0)
    (g : (S × E) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, ∫ x, g (D n ω, x) ∂(κ n ω : Measure E) ∂P) atTop
      (𝓝 (∫ d, ∫ x, g (d, x) ∂(π d : Measure E) ∂ν)) := by
  classical
  have hπ' : Continuous fun d => LevyProkhorov.ofMeasure (π d) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hπ
  have hι : Continuous fun d : S => (d, PUnit.unit) := continuous_id.prodMk continuous_const
  have hlaw' : ∀ f : (S × PUnit) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω, (fun _ : Ω => PUnit.unit) ω) ∂P) atTop
        (𝓝 (∫ p, f p ∂(ν.map fun d : S => (d, PUnit.unit)))) := by
    intro f
    have h := hlaw (f.compContinuous ⟨fun d : S => (d, PUnit.unit), hι⟩)
    have e : ∫ p, f p ∂(ν.map fun d : S => (d, PUnit.unit)) = ∫ d, f (d, PUnit.unit) ∂ν :=
      integral_map hι.measurable.aemeasurable f.continuous.aestronglyMeasurable
    rw [e]
    exact h
  have key := tendsto_integral_projection_of_tendstoInMeasure_dist (P := P)
    (M := LevyProkhorov (ProbabilityMeasure E)) (𝒞 := PUnit) hD
    (Y := fun n ω => LevyProkhorov.ofMeasure (κ n ω)) hκ
    (Q := fun _ _ => PUnit.unit) (fun _ => aemeasurable_const) (s := fun _ => 0) (s₀ := 0)
    (π := fun d => LevyProkhorov.ofMeasure (π d)) hπ' hlaw' hκπ tendsto_const_nhds
  have hbd : ∀ (d : S) (μ : ProbabilityMeasure E),
      |∫ x, g (d, x) ∂(μ : Measure E)| ≤ ‖g‖ := fun d μ => by
    have := norm_integral_le_of_norm_le_const (μ := (μ : Measure E)) (f := fun x => g (d, x))
      (C := ‖g‖) (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm (d, x))
    simpa using this
  let Gf : S × LevyProkhorov (ProbabilityMeasure E) × PUnit × ℝ≥0 → ℝ := fun p =>
    ∫ x, g (p.1, x) ∂((LevyProkhorov.toMeasure p.2.1 : ProbabilityMeasure E) : Measure E)
  have hGc : Continuous Gf :=
    (continuous_integral_prod_levyProkhorov g).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  let G : (S × LevyProkhorov (ProbabilityMeasure E) × PUnit × ℝ≥0) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨Gf, hGc⟩ (2 * ‖g‖) (fun p q => by
      rw [Real.dist_eq, abs_le]
      have h1 := abs_le.1 (hbd p.1 (LevyProkhorov.toMeasure p.2.1))
      have h2 := abs_le.1 (hbd q.1 (LevyProkhorov.toMeasure q.2.1))
      show -(2 * ‖g‖) ≤ Gf p - Gf q ∧ Gf p - Gf q ≤ 2 * ‖g‖
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
  have hk := key G
  have e : ∫ p, G (p.1, LevyProkhorov.ofMeasure (π p.1), p.2, 0)
      ∂(ν.map fun d : S => (d, PUnit.unit)) = ∫ d, ∫ x, g (d, x) ∂(π d : Measure E) ∂ν := by
    rw [integral_map hι.measurable.aemeasurable]
    · rfl
    · have hcf : Continuous fun p : S × PUnit =>
          ((p.1, LevyProkhorov.ofMeasure (π p.1), p.2, (0 : ℝ≥0)) :
            S × LevyProkhorov (ProbabilityMeasure E) × PUnit × ℝ≥0) :=
        continuous_fst.prodMk (((hπ'.comp continuous_fst)).prodMk
          (continuous_snd.prodMk continuous_const))
      exact (G.continuous.comp hcf).aestronglyMeasurable
  rw [e] at hk
  exact hk

end LatticeProb
