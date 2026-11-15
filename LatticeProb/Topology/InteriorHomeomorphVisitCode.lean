import LatticeProb.Topology.SubspaceHomeomorphComponents
import LatticeProb.Topology.CurveComponentVisitCode

/-! # Component visits under homeomorphisms of image interiors -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A time-preserving homeomorphism of image interiors preserves restricted
component visit codes when the two curves visit their interiors at the same times. -/
theorem restricted_curveComponentVisitCode_eq_of_interior_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (f : C(ℝ, E)) (g : C(ℝ, F)) (K : Set ℝ)
    (e : interior (f '' K) ≃ₜ interior (g '' K))
    (hinterior : ∀ t ∈ K, f t ∈ interior (f '' K) ↔ g t ∈ interior (g '' K))
    (hparam : ∀ (t : ℝ) (_ht : t ∈ K) (hi : f t ∈ interior (f '' K)),
      (e ⟨f t, hi⟩).1 = g t)
    (u : ℝ) (hu : u ∈ K) :
    (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K f (f u) q.1) =
      (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K g (g u) q.1) := by
  classical
  funext q
  have hv : f q.1 ∈ connectedComponentIn (interior (f '' K)) (f u) ↔
      g q.1 ∈ connectedComponentIn (interior (g '' K)) (g u) := by
    by_cases hxu : f u ∈ interior (f '' K)
    · by_cases hzq : f q.1 ∈ interior (f '' K)
      · have h := homeomorph_subspace_mem_connectedComponentIn_iff e
          (Subset.rfl) (Subset.rfl) (fun y => ⟨fun _ => (e y).2, fun _ => y.2⟩)
          ⟨f u, hxu⟩ ⟨f q.1, hzq⟩
        simpa only [hparam u hu hxu, hparam (q.1 : ℝ) q.2 hzq] using h.symm
      · have hzg : g q.1 ∉ interior (g '' K) := fun hg => hzq ((hinterior q.1 q.2).mpr hg)
        constructor <;> intro h
        · exact (hzq (connectedComponentIn_subset _ _ h)).elim
        · exact (hzg (connectedComponentIn_subset _ _ h)).elim
    · have hxg : g u ∉ interior (g '' K) := fun hg => hxu ((hinterior u hu).mpr hg)
      rw [connectedComponentIn_eq_empty hxu, connectedComponentIn_eq_empty hxg]
      simp only [mem_empty_iff_false, iff_self]
  simp only [curveComponentVisitCode, hv]

end LatticeProb
