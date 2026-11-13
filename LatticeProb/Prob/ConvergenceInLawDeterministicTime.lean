import Mathlib
import LatticeProb.Prob.ConvergingTogetherProjection

/-!
# Convergence in law with a deterministic convergent coordinate

If random elements `D n` of a pseudo-metrizable second countable space `S` converge in law to `ν` and
`s n → s₀` are deterministic nonnegative numbers, then the pairs `(D n, s n)` converge in law to the pair
`(D, s₀)`, that is to the image of `ν` under `d ↦ (d, s₀)`.  This is the special case of converging
together (`LatticeProb.tendsto_integral_projection_of_tendstoInMeasure_dist`) in which the other
coordinates are trivial.  It is used to freeze a discretized time parameter `s n → s₀` as a coordinate
of the data.

* `LatticeProb.tendsto_integral_prod_of_tendsto_nnreal`: this statement.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- **Convergence in law with a deterministic time coordinate.**  If `D n` converges in law to `ν` and
`s n → s₀` in `ℝ≥0`, then `∫ G (D n, s n) → ∫ G (d, s₀) dν` for every bounded continuous
`G : S × ℝ≥0 → ℝ`. -/
theorem tendsto_integral_prod_of_tendsto_nnreal {Ω S : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    {D : ℕ → Ω → S} (hD : ∀ n, AEMeasurable (D n) P) {ν : Measure S}
    (hlaw : ∀ g : S →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω) ∂P) atTop (𝓝 (∫ d, g d ∂ν)))
    {s : ℕ → ℝ≥0} {s₀ : ℝ≥0} (hs : Tendsto s atTop (𝓝 s₀)) (G : (S × ℝ≥0) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, G (D n ω, s n) ∂P) atTop (𝓝 (∫ d, G (d, s₀) ∂ν)) := by
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
    (M := PUnit) (𝒞 := PUnit) hD (Y := fun _ _ => PUnit.unit) (fun _ => aemeasurable_const)
    (Q := fun _ _ => PUnit.unit) (fun _ => aemeasurable_const) (s := s) (s₀ := s₀)
    (π := fun _ => PUnit.unit) continuous_const hlaw'
    (fun ε hε => (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr
      (fun n => by simp [not_le_of_gt hε])) hs
  let c : S × PUnit × PUnit × ℝ≥0 → S × ℝ≥0 := fun p => (p.1, p.2.2.2)
  have hc : Continuous c := continuous_fst.prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hk := key (G.compContinuous ⟨c, hc⟩)
  have e : ∫ p, G (p.1, s₀) ∂(ν.map fun d : S => (d, PUnit.unit)) = ∫ d, G (d, s₀) ∂ν :=
    integral_map hι.measurable.aemeasurable
      (G.continuous.comp (continuous_fst.prodMk continuous_const)).aestronglyMeasurable
  rw [show (∫ p, (G.compContinuous ⟨c, hc⟩) (p.1, PUnit.unit, p.2, s₀)
      ∂(ν.map fun d : S => (d, PUnit.unit))) =
    ∫ p, G (p.1, s₀) ∂(ν.map fun d : S => (d, PUnit.unit)) from rfl, e] at hk
  exact hk

end LatticeProb
