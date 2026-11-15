import LatticeProb.LQG.CouplingRegularClosedSegments
import LatticeProb.Topology.RationalSegmentTimeChange
import LatticeProb.Topology.EmbeddedDiskConnectedInterior

/-! # Segment interiors under area parametrization -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- Disk-shaped rational segments of the Lebesgue-parametrized curve imply
connected regular-closed segments for both area-parametrized curves, even when
their increasing clocks depend on the curve. -/
theorem ae_connected_segments_of_rational_disk_segments
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂P, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
        (ηL ω '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      (IsConnected (interior (η ω '' Icc a b)) ∧
        closure (interior (η ω '' Icc a b)) = η ω '' Icc a b) ∧
      (IsConnected (interior (η₀ ω '' Icc a b)) ∧
        closure (interior (η₀ ω '' Icc a b)) = η₀ ω '' Icc a b) := by
  have hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂P, IsConnected (interior (ηL ω '' Icc (p : ℝ) (q : ℝ))) ∧
        closure (interior (ηL ω '' Icc (p : ℝ) (q : ℝ))) =
          ηL ω '' Icc (p : ℝ) (q : ℝ) := by
    intro p q hpq
    filter_upwards [hdisk p q hpq, ae_regularClosed_segments_of_coupling D] with ω hd hr
    exact ⟨LatticeProb.isConnected_interior_of_homeomorph_closedDisk hd.some,
      (hr p q hpq).1⟩
  have hcont : ∀ᵐ ω ∂P, Continuous (ηL ω) :=
    Filter.Eventually.of_forall fun ω => (ηL ω).continuous
  filter_upwards [LatticeProb.ae_connected_interior_image_comp_orderIso_of_rational_segments
    P (fun ω => ⇑(ηL ω)) hcont hrat, D.areaParam, D.areaParam₀] with ω hg ha ha₀
  obtain ⟨φ, _, hφ⟩ := ha.1
  obtain ⟨ψ, _, hψ⟩ := ha₀.1
  intro a b hab
  constructor
  · have h := hg φ a b hab
    have he : (η ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ φ := funext hφ
    rw [← he] at h
    exact h
  · have h := hg ψ a b hab
    have he : (η₀ ω : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ ψ := funext hψ
    rw [← he] at h
    exact h

end MatedCRTHarmonic.MoTInput
