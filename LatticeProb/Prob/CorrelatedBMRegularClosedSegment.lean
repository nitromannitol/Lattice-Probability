import LatticeProb.Prob.CorrelatedBMContourFiber

/-! # Regular closed images of curve segments -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb

/-- A proper surjective curve with singleton fibres at all rational times maps
any nondegenerate closed interval to the closure of its interior. -/
theorem closure_interior_image_Icc_of_singleton_rational_fibers
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (hf : IsProperMap f) (hs : Function.Surjective f)
    (hpoint : ∀ q : ℚ, ∀ u, f u = f q → u = q)
    {a b : ℝ} (hab : a < b) :
    closure (interior (f '' Icc a b)) = f '' Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset (isCompact_Icc.image hf.continuous).isClosed
  · have hsub : Ioo a b ⊆ f ⁻¹' closure (interior (f '' Icc a b)) := by
      apply (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo).trans
      apply closure_minimal _ (isClosed_closure.preimage hf.continuous)
      rintro x ⟨hx, q, rfl⟩
      exact subset_closure (mem_interior_image_Icc_of_singleton_fiber f hf hs
        hx.1 hx.2 (hpoint q))
    have hcc : Icc a b ⊆ f ⁻¹' closure (interior (f '' Icc a b)) := by
      calc
        Icc a b = closure (Ioo a b) := (closure_Ioo hab.ne).symm
        _ ⊆ f ⁻¹' closure (interior (f '' Icc a b)) :=
          closure_minimal hsub (isClosed_closure.preimage hf.continuous)
    rintro y ⟨x, hx, rfl⟩
    exact hcc hx

namespace CorrelatedBM

/-- With Brownian contour fibres, all nondegenerate segment images are almost
surely regular closed, on a common event for all real endpoints. -/
theorem ae_closure_interior_image_Icc_of_contour_relation
    {Ω Y : Type*} [MeasurableSpace Ω] [TopologicalSpace Y] [T2Space Y] {P : Measure Ω}
    {γ : ℝ} {Z : Ω → Path2} {η : Ω → ℝ → Y}
    (hZ : AEMeasurable Z P) (hLaw : IsCorrelatedBM2 γ (P.map Z))
    (hrel : ∀ q : ℚ, ∀ᵐ ω ∂P, ∀ t, η ω t = η ω q → Relation.EqvGen
      (fun s t => DirectRel (fun u => lrCoord 0 u (Z ω)) s t ∨
        DirectRel (fun u => lrCoord 1 u (Z ω)) s t) q t)
    (hproper : ∀ᵐ ω ∂P, IsProperMap (η ω))
    (hsurj : ∀ᵐ ω ∂P, Function.Surjective (η ω)) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      closure (interior (η ω '' Icc a b)) = η ω '' Icc a b := by
  have hsingle : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ t, η ω t = η ω q → t = q :=
    ae_all_iff.2 fun q => ae_singleton_fiber_of_contour_relation hZ hLaw q (hrel q)
  filter_upwards [hsingle, hproper, hsurj] with ω hω hp hs
  intro a b hab
  exact closure_interior_image_Icc_of_singleton_rational_fibers (η ω) hp hs hω hab

end CorrelatedBM
end LatticeProb
