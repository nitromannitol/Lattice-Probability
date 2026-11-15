import LatticeProb.LQG.ConeOuterWindowCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel

/-! # Outer-window bounds for the canonical coupled quantum cone -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.CellScaling
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- The canonical cell model gives the scaled window bound directly on the
coupling's probability space. -/
theorem measure_cone_scaled_window_escape_le_exit_failure_add_canonical
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    {p ρ e : ℝ} (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ {δ w b : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → 0 ≤ w →
      2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) → 0 < b →
      P {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} ≤
      P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (1 : ℝ)}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (1 : ℝ)})))} +
      ENNReal.ofReal (C * δ ^ e) := by
  let M := MoTInput.cellModelOfCoupling D hγ
  have harea : ∀ᵐ ω ∂M.P, M.area ω =
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) :=
    Filter.Eventually.of_forall fun _ => rfl
  exact measure_cone_scaled_window_escape_le_exit_failure_add_of_coupling
    M D hstd hγ harea hp hρ0 hρ1 he

end LatticeProb.LQG
