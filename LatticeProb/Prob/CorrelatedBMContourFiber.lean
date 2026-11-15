import LatticeProb.Prob.CorrelatedBMContourSingleton
import LatticeProb.Topology.ClosedMapFiberInterior

/-! # Singleton fibres from Brownian contour classes -/

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- If each fibre identification belongs to the contour relation of a correlated
Brownian pair, the fibre at each fixed time is almost surely a singleton. -/
theorem ae_singleton_fiber_of_contour_relation
    {Ω Y : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {Z : Ω → Path2} {η : Ω → ℝ → Y}
    (hZ : AEMeasurable Z P) (hLaw : IsCorrelatedBM2 γ (P.map Z)) (a : ℝ)
    (hrel : ∀ᵐ ω ∂P, ∀ t, η ω t = η ω a → Relation.EqvGen
      (fun s t => DirectRel (fun u => lrCoord 0 u (Z ω)) s t ∨
        DirectRel (fun u => lrCoord 1 u (Z ω)) s t) a t) :
    ∀ᵐ ω ∂P, ∀ t, η ω t = η ω a → t = a := by
  filter_upwards [ae_of_ae_map hZ (ae_eqvGen_directRel_anchor_iff hLaw a), hrel] with ω hω hη
  intro t ht
  exact (hω t).1 (hη t ht)

/-- Under properness and surjectivity, a fixed-time Brownian contour singleton
is an interior point of the image of every interval containing that time. -/
theorem ae_mem_interior_image_Icc_of_contour_relation
    {Ω Y : Type*} [MeasurableSpace Ω] [TopologicalSpace Y] {P : Measure Ω}
    {γ : ℝ} {Z : Ω → Path2} {η : Ω → ℝ → Y}
    (hZ : AEMeasurable Z P) (hLaw : IsCorrelatedBM2 γ (P.map Z)) (a : ℝ)
    (hrel : ∀ᵐ ω ∂P, ∀ t, η ω t = η ω a → Relation.EqvGen
      (fun s t => DirectRel (fun u => lrCoord 0 u (Z ω)) s t ∨
        DirectRel (fun u => lrCoord 1 u (Z ω)) s t) a t)
    (hproper : ∀ᵐ ω ∂P, IsProperMap (η ω))
    (hsurj : ∀ᵐ ω ∂P, Function.Surjective (η ω)) :
    ∀ᵐ ω ∂P, ∀ l r, l < a → a < r → η ω a ∈ interior (η ω '' Icc l r) := by
  filter_upwards [ae_singleton_fiber_of_contour_relation hZ hLaw a hrel, hproper, hsurj] with
    ω hω hp hs
  intro l r hl hr
  exact mem_interior_image_Icc_of_singleton_fiber (η ω) hp hs hl hr hω

end LatticeProb.CorrelatedBM
