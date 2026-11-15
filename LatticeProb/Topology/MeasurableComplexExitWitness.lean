import LatticeProb.Topology.MeasurableRootedRealExitClock
import LatticeProb.Topology.MeasurableCenteredSegmentBall
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Measurable witnesses in rooted complex exit segments -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- Rooted real exit endpoints of measurable complex paths are measurable. -/
theorem measurable_complex_rooted_real_exits
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → C(ℝ, ℂ)} (hf : Measurable f)
    (U : Set ℂ) (hU : IsOpen U) :
    Measurable (fun ω => sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ U}) ∧
    Measurable (fun ω => sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ U}) := by
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  let g : Ω → C(ℝ, EuclideanSpace ℝ (Fin 2)) := fun ω =>
    (⟨e, e.continuous⟩ : C(ℂ, EuclideanSpace ℝ (Fin 2))).comp (f ω)
  let V : Set (EuclideanSpace ℝ (Fin 2)) := e.symm ⁻¹' U
  have hg : Measurable g :=
    (ContinuousMap.continuous_postcomp (⟨e, e.continuous⟩ :
      C(ℂ, EuclideanSpace ℝ (Fin 2)))).measurable.comp hf
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have heq (ω : Ω) (t : ℝ) : g ω t ∈ V ↔ f ω t ∈ U := by
    change e.symm (e (f ω t)) ∈ U ↔ f ω t ∈ U
    rw [e.symm_apply_apply]
  constructor
  · have h := measurable_rooted_backward_real_exit hg V hV
    simpa only [heq] using h
  · have h := measurable_rooted_forward_real_exit hg V hV
    simpa only [heq] using h

/-- Simultaneous centered-ball witnesses in both rooted exit segments form a
measurable event. Real exit endpoints use their usual zero value on empty sets. -/
theorem measurableSet_joint_rooted_exit_ball_witnesses
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → C(ℝ, ℂ)} (hf : Measurable f)
    (U : Set ℂ) (hU : IsOpen U) (ρ δ : ℝ) (hδ : 0 < δ) :
    MeasurableSet {ω | (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f ω '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ U}) 0) ∧
      (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ U}))} := by
  let a : Ω → ℝ := fun ω => sSup {t : ℝ | t ≤ 0 ∧ f ω t ∉ U}
  let b : Ω → ℝ := fun ω => sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ U}
  obtain ⟨ha, hb⟩ := measurable_complex_rooted_real_exits hf U hU
  have ha0 (ω : Ω) : a ω ≤ 0 := by
    by_cases h : {t : ℝ | t ≤ 0 ∧ f ω t ∉ U}.Nonempty
    · exact csSup_le h (fun _ ht => ht.1)
    · simp only [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty, le_refl, a]
  have hb0 (ω : Ω) : 0 ≤ b ω := by
    by_cases h : {t : ℝ | 0 ≤ t ∧ f ω t ∉ U}.Nonempty
    · exact le_csInf h (fun _ ht => ht.1)
    · simp only [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty, le_refl, b]
  have hback := measurableSet_exists_centered_ball_subset_segment hf ha (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))) ρ δ hδ
  have hforward := measurableSet_exists_centered_ball_subset_segment hf (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))) hb ρ δ hδ
  convert hback.inter hforward using 1
  ext ω
  simp only [mem_ofPred_eq, mem_inter_iff, ha0 ω, hb0 ω, true_and, a, b]

end LatticeProb
