import LatticeProb.LQG.CouplingRationalDiskSegments
import LatticeProb.Topology.DiskSegmentEvent

/-! # Disk-shaped segments under equality of curve laws -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- Fixed rational disk-shaped segments transfer from an equal-law curve to both
area-parametrized curves. The source law and its disk geometry are hypotheses. -/
theorem ae_connected_segments_of_equal_curve_law
    {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure Q]
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2} {ξ : Ω' → C(ℝ, ℂ)}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hξ : Measurable ξ) (hlaw : P.map ηL = Q.map ξ)
    (hdisk : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂Q, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
        (ξ ω '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      (IsConnected (interior (η ω '' Icc a b)) ∧
        closure (interior (η ω '' Icc a b)) = η ω '' Icc a b) ∧
      (IsConnected (interior (η₀ ω '' Icc a b)) ∧
        closure (interior (η₀ ω '' Icc a b)) = η₀ ω '' Icc a b) := by
  apply ae_connected_segments_of_rational_disk_segments D
  intro p q hpq
  let S : Set C(ℝ, ℂ) := {f | Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
    (f '' Icc (p : ℝ) (q : ℝ)))}
  have : IsFiniteMeasure (Q.map ξ) := Q.isFiniteMeasure_map ξ
  have hS : NullMeasurableSet S (Q.map ξ) := by
    have h := LatticeProb.nullMeasurableSet_disk_shaped_curve_segment
      (Q.map ξ) id measurable_id (p : ℝ) (q : ℝ)
    change NullMeasurableSet {f : C(ℝ, ℂ) | Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
      (f '' uIcc (p : ℝ) (q : ℝ)))} (Q.map ξ) at h
    rw [uIcc_of_le hpq.le] at h
    exact h
  have hSP : NullMeasurableSet S (P.map ηL) := by rw [hlaw]; exact hS
  have hz : Q (ξ ⁻¹' Sᶜ) = 0 := by
    have h := hdisk p q hpq
    rw [Filter.Eventually, mem_ae_iff] at h
    exact h
  have heq : P (ηL ⁻¹' Sᶜ) = Q (ξ ⁻¹' Sᶜ) := by
    rw [← Measure.map_apply₀ D.measurable_curves.1.aemeasurable hSP.compl,
      hlaw, Measure.map_apply₀ hξ.aemeasurable hS.compl]
  have hresult : ∀ᵐ ω ∂P, ηL ω ∈ S := by
    rw [Filter.Eventually, mem_ae_iff]
    exact heq.trans hz
  exact hresult

end MatedCRTHarmonic.MoTInput
