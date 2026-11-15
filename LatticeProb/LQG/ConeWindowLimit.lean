import LatticeProb.LQG.ConeWindowBounds
import LatticeProb.LQG.ConeWindowParameters

/-! # Convergence of coupled cone window probabilities -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

/-- For power-law windows, the probability of an outer escape or an inner
half-window containment tends to zero as the scale tends to zero. -/
theorem tendsto_measure_cone_window_failure
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    {p q ρ r e s a : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) {N : ℕ} (hN : 0 < N)
    (he : 0 < e) (heupper : e < p ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) (ha : 0 < a) :
    Tendsto (fun δ : ℝ =>
      let w := δ ^ (2 + γ ^ 2 / 2 + p) / 4
      let b := w * δ ^ a
      P {ω | let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
        ¬ η ω '' Icc (-(b * w)) (b * w) ⊆ ball 0 L ∨
          η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
          η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Cexit, Carea, Cinner, hfinite, hbound⟩ :=
    measure_cone_window_failure_le D hstd hγ μ hμ hp hq hqρ hρ1 hr N heupper hs hsγ
  have ht := tendsto_power_window_bound (k := 2 + γ ^ 2 / 2 + p) ha he hs hN
    Cexit Carea (ne_of_lt hfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · filter_upwards [eventually_power_window_parameters
        (k := 2 + γ ^ 2 / 2 + p) (a := a) hq hr.2] with δ hδ
    exact hbound hδ.1 hδ.2.1 hδ.2.2.1 hδ.2.2.2.1 hδ.2.2.2.2

end LatticeProb.LQG
