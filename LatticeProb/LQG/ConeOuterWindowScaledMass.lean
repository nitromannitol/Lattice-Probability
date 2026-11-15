import LatticeProb.LQG.ConeOuterWindowMass
import LatticeProb.LQG.ConeOuterWindowScaling

/-! # Scaled outer-window bounds for quantum cones -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.CellScaling
open scoped NNReal ENNReal

namespace LatticeProb.LQG

/-- Joint scaling transfers the unit-ball exit-witness and small-ball mass bound
    to the corresponding random cone radius and area-time window. -/
theorem measure_cone_scaled_window_escape_le_exit_failure_add
    {γ : ℝ} (M : MatedCRTHarmonic.GMSLemma27.CellModel γ)
    {X X₀ hIG₀ : M.Ω → Field} {B B' B₀ B₀' : ℝ≥0 → M.Ω → ℝ}
    {U : M.Ω → ℝ} {ηL η η₀ : M.Ω → C(ℝ, ℂ)} {bm : M.Ω → Path2}
    (D : IsMatingOfTreesCoupling γ M.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace M.Ω) (hγ : γ ∈ Ioo 0 2)
    (harea : ∀ᵐ ω ∂M.P, M.area ω =
      lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
    (hparam : ∀ᵐ ω ∂M.P, ∀ s t : ℝ, s ≤ t →
      M.area ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    {p ρ e : ℝ} (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ {δ w b : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → 0 ≤ w →
      2 * w ≤ δ ^ (2 + γ ^ 2 / 2 + p) → 0 < b →
      M.P {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} ≤
      M.P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (1 : ℝ)}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (1 : ℝ)})))} +
      ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨C, hC⟩ := measure_cone_window_escape_le_exit_failure_add M hγ.1 hγ.2
    D.gff D.bm_B D.bm_B' D.indep_cone harea (fun ω => η ω) (fun _ => ball 0 1)
    hparam hp hρ0 hρ1 he
  refine ⟨C, fun hδ hw hq hb => ?_⟩
  rw [measure_cone_window_escape_scaling D hstd hγ hb hw]
  exact hC hδ hw hq

end LatticeProb.LQG
