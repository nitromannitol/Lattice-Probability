import LatticeProb.LQG.ConeOuterWindowCanonical
import LatticeProb.LQG.ConeExitWitnessTail

/-! # Quantitative outer-window bounds for the coupled quantum cone -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.CellScaling
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- The scaled window escape probability is bounded by the sum of a
segment-ball tail and a cone-area lower-tail estimate. -/
theorem measure_cone_scaled_window_escape_le_polynomial_add
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    {p q ρ r e : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ Cexit Carea : ℝ, ∀ {δ w b : ℝ}, δ ∈ Ioo (0 : ℝ) 1 →
      δ ^ (1 - r) ≤ q → 0 ≤ w →
      2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) → 0 < b →
      P {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} ≤
      ENNReal.ofReal (Cexit * δ ^ N) + ENNReal.ofReal (Carea * δ ^ e) := by
  obtain ⟨Carea, harea⟩ :=
    measure_cone_scaled_window_escape_le_exit_failure_add_canonical D hstd hγ hp
      (lt_trans hq hqρ) hρ1 he
  obtain ⟨Cexit, hexit⟩ := measure_joint_exit_witness_failure_le D hq hqρ hρ1 hr N
  refine ⟨Cexit, Carea, ?_⟩
  intro δ w b hδ hδq hw hwidth hb
  exact (harea hδ hw hwidth hb).trans (add_le_add (hexit hδ hδq) le_rfl)

end LatticeProb.LQG
