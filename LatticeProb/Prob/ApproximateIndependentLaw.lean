import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Ind
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Independent weak limits of nearby laws

Weak convergence transfers between probability measures whose Lévy–Prokhorov distance
vanishes. In particular, a weak limit of joint laws is independent if it is approximated
in this distance by joint laws of independent pairs.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

namespace LatticeProb

/-- Weak convergence transfers across a vanishing Lévy–Prokhorov distance. -/
theorem tendsto_probabilityMeasure_of_levyProkhorovDist {E : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]
    {μ ν : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (hclose : Tendsto (fun n => levyProkhorovDist (ν n : Measure E) (μ n : Measure E))
      atTop (𝓝 0)) : Tendsto ν atTop (𝓝 μ₀) := by
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)
  have hμ' : Tendsto (fun n => e (μ n)) atTop (𝓝 (e μ₀)) := (e.continuous.tendsto μ₀).comp hμ
  have hν' : Tendsto (fun n => e (ν n)) atTop (𝓝 (e μ₀)) := by
    rw [Metric.tendsto_nhds] at hμ' ⊢
    intro ε hε
    have hc := hclose.eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [hc, hμ' (ε / 2) (half_pos hε)] with n hn hm
    have ht := dist_triangle (e (ν n)) (e (μ n)) (e μ₀)
    have hn' : dist (e (ν n)) (e (μ n)) < ε / 2 := by
      change levyProkhorovDist (ν n : Measure E) (μ n : Measure E) < ε / 2
      exact hn
    linarith
  have h := (e.symm.continuous.tendsto (e μ₀)).comp hν'
  simpa only [Function.comp_def, e.symm_apply_apply] using h

/-- Independence passes to a joint weak limit when its approximating laws are close to
joint laws of independent pairs. -/
theorem indepFun_of_tendsto_law_of_levyProkhorovDist {S T Ω Ω' : Type*}
    [PseudoMetricSpace S] [PseudoMetricSpace T] [MeasurableSpace S] [MeasurableSpace T]
    [BorelSpace S] [BorelSpace T] [SecondCountableTopology S] [SecondCountableTopology T]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Xn : ℕ → Ω → S} {Yn : ℕ → Ω → T} {X : Ω' → S} {Y : Ω' → T}
    (hXn : ∀ n, AEMeasurable (Xn n) P) (hYn : ∀ n, AEMeasurable (Yn n) P)
    (hX : AEMeasurable X P') (hY : AEMeasurable Y P')
    (hind : ∀ n, IndepFun (Xn n) (Yn n) P)
    {ρ σ : ℕ → ProbabilityMeasure (S × T)} {ρ₀ : ProbabilityMeasure (S × T)}
    (hσ : ∀ n, (σ n : Measure (S × T)) = P.map fun ω => (Xn n ω, Yn n ω))
    (hρ₀ : (ρ₀ : Measure (S × T)) = P'.map fun ω => (X ω, Y ω))
    (hρ : Tendsto ρ atTop (𝓝 ρ₀))
    (hclose : Tendsto (fun n => levyProkhorovDist (σ n : Measure (S × T))
      (ρ n : Measure (S × T))) atTop (𝓝 0)) : IndepFun X Y P' := by
  exact LQGMetric.DFGPS.L217.indepFun_of_tendsto_law hXn hYn hX hY hind hσ hρ₀
    (tendsto_probabilityMeasure_of_levyProkhorovDist hρ hclose)

end LatticeProb
