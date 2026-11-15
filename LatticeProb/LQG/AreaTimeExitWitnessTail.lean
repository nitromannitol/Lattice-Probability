import LatticeProb.LQG.ConeExitWitnessTail

/-! # Exit witnesses for an area-time curve -/

set_option autoImplicit false

open MeasureTheory Filter Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal Topology

namespace LatticeProb.LQG

/-- The segment-ball estimate bounds joint first-exit witness failure for the
Lebesgue-area parametrization of the curve. -/
theorem measure_areaTime_joint_exit_witness_failure_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        ηL ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ ηL ω t ∉ ball 0 (1 : ℝ)}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ηL ω t ∉ ball 0 (1 : ℝ)})))} ≤
      ENNReal.ofReal (C * δ ^ N) := by
  obtain ⟨C, hC⟩ := measure_joint_exit_witness_failure_le D hq hqρ hρ hr N
  refine ⟨C, ?_⟩
  intro δ hδ hδq
  calc
    _ = P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η ω t ∉ ball 0 (1 : ℝ)}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
        η ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η ω t ∉ ball 0 (1 : ℝ)})))} := by
          apply measure_congr
          filter_upwards [D.areaParam] with ω hω
          obtain ⟨φ, hφ0, hη⟩ := hω.1
          have hfun : (η ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ φ := funext hη
          have htr := rooted_exit_traces_comp_orderIso (ηL ω) (ball 0 (1 : ℝ)) φ hφ0
          rw [hfun, htr.1, htr.2]
    _ ≤ _ := hC hδ hδq

end LatticeProb.LQG
