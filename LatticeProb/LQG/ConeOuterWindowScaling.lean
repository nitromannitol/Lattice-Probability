import LatticeProb.LQG.ConeActualJointScaling
import LatticeProb.LQG.MatingOfTreesCouplingDegrees

/-! # Scaling of compact-window escape probabilities -/

set_option autoImplicit false

open MeasureTheory Set Metric LQGMetric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.CellScaling
open scoped NNReal

namespace LatticeProb

/-- Escape from an open ball over a compact time interval is a Borel event. -/
theorem measurableSet_curve_window_escape (a c r : ℝ) :
    MeasurableSet {f : C(ℝ, ℂ) | ¬ f '' Icc a c ⊆ ball 0 r} := by
  have h := (ContinuousMap.isOpen_setOf_image_subset_ball (E := ℂ)
    (K := Icc a c) isCompact_Icc).preimage
    (show Continuous (fun f : C(ℝ, ℂ) => (f, r)) by fun_prop)
  exact h.measurableSet.compl

/-- Positive space and time dilations transport compact-window containment. -/
theorem coneRescaleCurve_window_subset_iff {R b w : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hw : 0 ≤ w) (η : C(ℝ, ℂ)) :
    CellScaling.coneRescaleCurve R b η '' Icc (-w) w ⊆ ball 0 1 ↔
      η '' Icc (-(b * w)) (b * w) ⊆ ball 0 R := by
  have hi := JointScalingO.image_mul_coneRescaleCurve hR hb η (show -w ≤ w by linarith)
  have hball (z : ℂ) : (R : ℂ) * z ∈ ball 0 R ↔ z ∈ ball 0 1 := by
    simp only [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR, mul_lt_iff_lt_one_right hR]
  constructor
  · intro h
    rw [← show b * (-w) = -(b * w) by ring, ← hi]
    rintro _ ⟨z, hz, rfl⟩
    exact (hball z).2 (h hz)
  · intro h z hz
    apply (hball z).1
    apply h
    rw [← show b * (-w) = -(b * w) by ring, ← hi]
    exact ⟨z, hz, rfl⟩

/-- The cone joint scaling law transfers the escape probability to the ball
with the random cone radius and the corresponding area-time window. -/
theorem measure_cone_window_escape_scaling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {b w : ℝ} (hb : 0 < b)
    (hw : 0 ≤ w) :
    P {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} =
      P {ω | ¬ η ω '' Icc (-w) w ⊆ ball 0 1} := by
  let E : Set C(ℝ, ℂ) := {f | ¬ f '' Icc (-w) w ⊆ ball 0 1}
  have hE : MeasurableSet E := measurableSet_curve_window_escape _ _ _
  have h := cone_actual_joint_scaling D hstd hγ hb (univ ×ˢ E)
    (MeasurableSet.univ.prod hE)
  have heq : {ω | (CellScaling.coneRescaleField γ
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω)) ∈
          univ ×ˢ E} =
      {ω | ¬ η ω '' Icc (-(b * w)) (b * w) ⊆
        ball 0 (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and, E]
    exact not_congr (coneRescaleCurve_window_subset_iff
      (Real.exp_pos _) hb hw (η ω))
  rw [heq] at h
  simpa only [mem_ofPred_eq, mem_prod, mem_univ, true_and, E] using h

end LatticeProb
