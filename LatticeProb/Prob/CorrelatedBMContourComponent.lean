import LatticeProb.Prob.CorrelatedBMContourFiber
import Mathlib.Topology.Connected.Basic

/-! # Interior components at fixed Brownian contour times -/

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- At each fixed time, the image point almost surely belongs to a nonempty
interior component of every enclosing segment image. -/
theorem ae_mem_component_interior_image_Icc_of_contour_relation
    {Ω Y : Type*} [MeasurableSpace Ω] [TopologicalSpace Y] {P : Measure Ω}
    {γ : ℝ} {Z : Ω → Path2} {η : Ω → ℝ → Y}
    (hZ : AEMeasurable Z P) (hLaw : IsCorrelatedBM2 γ (P.map Z)) (a : ℝ)
    (hrel : ∀ᵐ ω ∂P, ∀ t, η ω t = η ω a → Relation.EqvGen
      (fun s t => DirectRel (fun u => lrCoord 0 u (Z ω)) s t ∨
        DirectRel (fun u => lrCoord 1 u (Z ω)) s t) a t)
    (hproper : ∀ᵐ ω ∂P, IsProperMap (η ω))
    (hsurj : ∀ᵐ ω ∂P, Function.Surjective (η ω)) :
    ∀ᵐ ω ∂P, ∀ l r, l < a → a < r →
      η ω a ∈ connectedComponentIn (interior (η ω '' Icc l r)) (η ω a) ∧
      (connectedComponentIn (interior (η ω '' Icc l r)) (η ω a)).Nonempty := by
  filter_upwards [ae_mem_interior_image_Icc_of_contour_relation hZ hLaw a hrel hproper hsurj] with ω hω
  intro l r hl hr
  have h := mem_connectedComponentIn (hω l r hl hr)
  exact ⟨h, ⟨η ω a, h⟩⟩

end LatticeProb.CorrelatedBM
