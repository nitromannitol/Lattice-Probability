import LatticeProb.Topology.SubspaceHomeomorphComponents
import LatticeProb.Topology.CurveComponentVisitCode

/-! # Component visits under homeomorphisms of curve images -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A time-preserving homeomorphism of curve images preserves the component
visit code at times in the parameter set, if it preserves ambient interiors. -/
theorem curveComponentVisitCode_eq_of_subspace_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(ℝ, E)) (g : C(ℝ, F)) (K : Set ℝ)
    (e : (f '' K) ≃ₜ (g '' K))
    (hparam : ∀ (t : ℝ) (ht : t ∈ K),
      (e ⟨f t, mem_image_of_mem f ht⟩).1 = g t)
    (hinterior : ∀ x : f '' K,
      x.1 ∈ interior (f '' K) ↔ (e x).1 ∈ interior (g '' K))
    (u : ℝ) (hu : u ∈ K) (q : ℚ) (hq : (q : ℝ) ∈ K) :
    curveComponentVisitCode K f (f u) q =
      curveComponentVisitCode K g (g u) q := by
  classical
  let x : f '' K := ⟨f u, mem_image_of_mem f hu⟩
  let z : f '' K := ⟨f q, mem_image_of_mem f hq⟩
  have hx : (e x).1 = g u := hparam u hu
  have hz : (e z).1 = g q := hparam q hq
  have hv : f q ∈ connectedComponentIn (interior (f '' K)) (f u) ↔
      g q ∈ connectedComponentIn (interior (g '' K)) (g u) := by
    by_cases hxu : f u ∈ interior (f '' K)
    · by_cases hzq : f q ∈ interior (f '' K)
      · have h := homeomorph_subspace_mem_connectedComponentIn_iff e
          interior_subset interior_subset hinterior ⟨f u, hxu⟩ ⟨f q, hzq⟩
        simpa only [hparam u hu, hparam (q : ℝ) hq] using h.symm
      · have hzg : g q ∉ interior (g '' K) := by
          intro hg
          exact hzq ((hinterior z).mpr (hz ▸ hg))
        constructor <;> intro h
        · exact (hzq (connectedComponentIn_subset _ _ h)).elim
        · exact (hzg (connectedComponentIn_subset _ _ h)).elim
    · have hxg : g u ∉ interior (g '' K) := by
        intro hg
        exact hxu ((hinterior x).mpr (hx ▸ hg))
      rw [connectedComponentIn_eq_empty hxu, connectedComponentIn_eq_empty hxg]
      simp only [mem_empty_iff_false, iff_self]
  simp only [curveComponentVisitCode, hv]

end LatticeProb
