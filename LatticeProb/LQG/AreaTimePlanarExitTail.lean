import LatticeProb.LQG.AreaTimeExitWitnessUniform
import LatticeProb.Topology.ComplexProperExitBall

/-! # Planar exit-ball failure bounds -/

set_option autoImplicit false

open MeasureTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal Topology

namespace LatticeProb.LQG

/-- The joint witness estimate bounds planar finite-exit failure at every
integer exponential scale. -/
theorem measure_areaTime_planar_exit_failure_uniform_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ v t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {q ρ r : ℝ} (hq : 0 < q) (hqρ : q < ρ) (hρ : ρ < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (N : ℕ) :
    ∃ C : ℝ, ∀ {δ : ℝ}, δ ∈ Ioo (0 : ℝ) 1 → δ ^ (1 - r) ≤ q →
      ∀ k : ℤ, P (firstExitBallFailure (F ∘ ηL) δ k) ≤
        ENNReal.ofReal (C * δ ^ N) := by
  obtain ⟨C, hC⟩ := measure_areaTime_joint_exit_witness_failure_uniform_le D hq hqρ hρ hr N
  refine ⟨C, ?_⟩
  intro δ hδ hδq k
  calc
    _ ≤ P {ω | ¬ ((∃ z ∈ ball (0 : ℂ) (Real.exp (k : ℝ) * ρ),
        ball z (Real.exp (k : ℝ) * δ) ⊆
          ηL ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ ηL ω t ∉ ball 0 (Real.exp (k : ℝ))}) 0) ∧
        (∃ z ∈ ball (0 : ℂ) (Real.exp (k : ℝ) * ρ),
        ball z (Real.exp (k : ℝ) * δ) ⊆
          ηL ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ ηL ω t ∉ ball 0 (Real.exp (k : ℝ))})))} := by
      apply measure_mono_ae
      filter_upwards [D.spaceFilling] with ω hω hbad
      intro hgood
      apply not_mem_firstExitBallFailure_of_complex_proper_witnesses
        (F ∘ ηL) ω (ηL ω) (hF (ηL ω)) hω.2.1 hδ.1 k _ _ hbad
      · obtain ⟨z, _, hz⟩ := hgood.1
        exact ⟨z, by simpa only [mul_comm] using hz⟩
      · obtain ⟨z, _, hz⟩ := hgood.2
        exact ⟨z, by simpa only [mul_comm] using hz⟩
    _ ≤ _ := hC hδ hδq (Real.exp_pos _)

end LatticeProb.LQG
