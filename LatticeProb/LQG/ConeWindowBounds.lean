import LatticeProb.LQG.ConeOuterWindowPolynomial
import LatticeProb.LQG.ConeInnerWindowPowerTail

/-! # Inner and outer window bounds for the coupled quantum cone -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- The probability of an outer-window escape or an inner half-window
containment is bounded by the sum of their respective tails. -/
theorem measure_cone_window_failure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    {p q ρ r e s : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) :
    ∃ Cexit Carea : ℝ, ∃ Cinner : ℝ≥0∞, Cinner < ⊤ ∧
      ∀ {δ w b : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      0 < w → 2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) → 0 < b →
      P {ω | let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
        ¬ η ω '' Icc (-(b * w)) (b * w) ⊆ ball 0 L ∨
          η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
          η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} ≤
      (ENNReal.ofReal (Cexit * δ ^ N) + ENNReal.ofReal (Carea * δ ^ e)) +
        Cinner * ENNReal.ofReal ((b⁻¹ * (w / 2)) ^ (-s)) := by
  obtain ⟨Cexit, Carea, houter⟩ :=
    measure_cone_scaled_window_escape_le_polynomial_add D hstd hγ hp hq hqρ hρ1 hr N he
  obtain ⟨Cinner, hfinite, hinner⟩ :=
    cone_inner_window_containment_power_tail D hstd hγ μ hμ s hs hsγ
  refine ⟨Cexit, Carea, Cinner, hfinite, ?_⟩
  intro δ w b hδ hδq hw hwidth hb
  calc
    _ ≤ P {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} +
      P {ω | let L := CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
        η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
          η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} := measure_union_le _ _
    _ ≤ _ := add_le_add (houter hδ hδq hw.le hwidth hb) (hinner b w hb hw)

end LatticeProb.LQG
