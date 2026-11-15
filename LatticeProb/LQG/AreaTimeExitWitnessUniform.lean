import LatticeProb.LQG.AreaTimeExitWitnessTail
import LatticeProb.LQG.AreaTimeExitWitnessScaling
import LatticeProb.Topology.MeasurableComplexExitWitness
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii

/-! # Scale-uniform area-time exit witnesses -/

set_option autoImplicit false

open MeasureTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw
open scoped NNReal ENNReal Topology

namespace LatticeProb.LQG

/-- The joint first-exit witness bound for an area-time curve holds with the
same constant at every positive deterministic scale. -/
theorem measure_areaTime_joint_exit_witness_failure_uniform_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      ∀ {s : ℝ}, 0 < s →
      P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) (s * ρ), ball z (s * δ) ⊆
        ηL ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ ηL ω t ∉ ball 0 s}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) (s * ρ), ball z (s * δ) ⊆
        ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ηL ω t ∉ ball 0 s})))} ≤
      ENNReal.ofReal (C * δ ^ N) := by
  obtain ⟨C, hC⟩ := measure_areaTime_joint_exit_witness_failure_le D hq hqρ hρ hr N
  refine ⟨C, ?_⟩
  intro δ hδ hδq s hs
  let A : Set C(ℝ, ℂ) := {f | ¬ ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f t ∉ ball 0 (1 : ℝ)}) 0) ∧
      (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f t ∉ ball 0 (1 : ℝ)})))}
  have hA : MeasurableSet A :=
    (measurableSet_joint_rooted_exit_ball_witnesses measurable_id _ isOpen_ball ρ δ hδ.1).compl
  have hm : Measurable (fun ω => GMS4b.curveRescale s (s ^ 2) (ηL ω)) :=
    measurable_curveRescale_sq_pos.comp
      ((measurable_const : Measurable (fun _ : Ω => (⟨s, hs⟩ : Ioi (0 : ℝ)))).prodMk
        D.measurable_curves.1)
  have hlaw := IsMatingOfTreesCoupling.map_curveRescale_sq_of_igMapPositiveRadii D
    (IsMatingOfTreesCoupling.igMapPositiveRadii D) hs
  have heq : P ((fun ω => GMS4b.curveRescale s (s ^ 2) (ηL ω)) ⁻¹' A) =
      P (ηL ⁻¹' A) := by
    rw [← Measure.map_apply hm hA, ← Measure.map_apply D.measurable_curves.1 hA, hlaw]
  calc
    _ = P ((fun ω => GMS4b.curveRescale s (s ^ 2) (ηL ω)) ⁻¹' A) := by
      congr 1
      ext ω
      exact not_congr (areaTimeScale_joint_exit_ball_witnesses (ηL ω) hs ρ δ).symm
    _ = P (ηL ⁻¹' A) := heq
    _ ≤ _ := hC hδ hδq

end LatticeProb.LQG
