import LatticeProb.Topology.PolishContinuousMap
import LatticeProb.Prob.SkorokhodRepresentation
import LatticeProb.Topology.BallExitOscillationLimit

/-! # Neighboring ball-exit oscillations under weak path convergence -/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- Weak convergence of path laws admits a coupling on which oscillations between
neighboring ball exits vanish whenever the limiting path is unbounded and has
a radius-continuous exit clock. -/
theorem exists_coupling_eventually_ballClock_neighbor_oscillation_lt
    {d : ℕ} {μ : ProbabilityMeasure (Path d)} {μs : ℕ → ProbabilityMeasure (Path d)}
    (hweak : Tendsto μs atTop (𝓝 μ))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) {r : ℝ}
    (hregular : ∀ᵐ (f : Path d) ∂(μ : Measure (Path d)),
      ¬ Bornology.IsBounded (Set.range f) ∧
        ContinuousAt (fun s : ℝ => ballClock f s) r) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y : ℕ → Ω → Path d) (Y₀ : Ω → Path d),
      (∀ n, Measurable (Y n)) ∧ Measurable Y₀ ∧
      (∀ n, P.map (Y n) = (μs n : Measure (Path d))) ∧
      P.map Y₀ = (μ : Measure (Path d)) ∧
      ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s ∈ Icc (ballClock (Y n ω) (r - δ n)).toNNReal
            (ballClock (Y n ω) (r + δ n)).toNNReal,
          ∀ t ∈ Icc (ballClock (Y n ω) (r - δ n)).toNNReal
            (ballClock (Y n ω) (r + δ n)).toNNReal,
          dist (Y n ω s) (Y n ω t) < ε := by
  let : PolishSpace (Path d) := LatticeProb.polishSpace_continuousMap _ _
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (Path d)
  obtain ⟨Ω, mΩ, P, hP, Y, Y₀, hY, hY₀, hmap, hmap₀, hconv⟩ :=
    LatticeProb.Skorokhod.exists_skorokhod_representation hweak
  refine ⟨Ω, mΩ, P, hP, Y, Y₀, hY, hY₀, hmap, hmap₀, ?_⟩
  have hreg : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (Y₀ ω)) ∧
      ContinuousAt (fun s : ℝ => ballClock (Y₀ ω) s) r := by
    have hpull : ∀ᵐ (f : Path d) ∂P.map Y₀,
        ¬ Bornology.IsBounded (Set.range f) ∧
          ContinuousAt (fun s : ℝ => ballClock f s) r := by
      rw [hmap₀]
      exact hregular
    exact ae_of_ae_map hY₀.aemeasurable hpull
  filter_upwards [hconv, hreg] with ω hconvω hregω ε hε
  exact eventually_ballClock_neighbor_oscillation_lt hconvω hδ hregω.1 hregω.2 hε

end LatticeProb.UnboundedRayIntervalIntegrand
