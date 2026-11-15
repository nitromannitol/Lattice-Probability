import LatticeProb.Topology.CurveComponentVisitCode
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Component visit codes under homeomorphisms -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A time-preserving ambient homeomorphism preserves all rational visits to the
selected component, including when the anchor is outside the image interior. -/
theorem curveComponentVisitCode_comp_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F) (f : C(ℝ, E)) (x : E) (K : Set ℝ) :
    curveComponentVisitCode K ((⟨e, e.continuous⟩ : C(E, F)).comp f) (e x) =
      curveComponentVisitCode K f x := by
  classical
  have hi : interior (((⟨e, e.continuous⟩ : C(E, F)).comp f) '' K) = e '' interior (f '' K) := by
    change interior ((e ∘ f) '' K) = e '' interior (f '' K)
    simpa only [image_image, Function.comp_def] using (e.image_interior (f '' K)).symm
  have hc : e '' connectedComponentIn (interior (f '' K)) x =
      connectedComponentIn (interior (((⟨e, e.continuous⟩ : C(E, F)).comp f) '' K)) (e x) := by
    rw [hi]
    by_cases hx : x ∈ interior (f '' K)
    · exact e.image_connectedComponentIn hx
    · have hxe : e x ∉ e '' interior (f '' K) := by
        simpa only [e.injective.mem_set_image] using hx
      rw [connectedComponentIn_eq_empty hx, connectedComponentIn_eq_empty hxe, image_empty]
  funext q
  have hv : ((⟨e, e.continuous⟩ : C(E, F)).comp f) q ∈
      connectedComponentIn (interior (((⟨e, e.continuous⟩ : C(E, F)).comp f) '' K)) (e x) ↔
      f q ∈ connectedComponentIn (interior (f '' K)) x := by
    rw [← hc]
    exact e.injective.mem_set_image
  simp only [curveComponentVisitCode, hv]

end LatticeProb
