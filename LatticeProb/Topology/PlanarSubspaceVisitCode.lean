import LatticeProb.Topology.SubspaceHomeomorphInterior
import LatticeProb.Topology.SubspaceHomeomorphVisitCode

/-! # Component visit codes under planar image homeomorphisms -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A time-preserving homeomorphism between planar curve images preserves the
rational component-visit code restricted to the parameter set. -/
theorem restricted_curveComponentVisitCode_eq_of_planar_subspace_homeomorph
    (f g : C(ℝ, ℂ)) (K : Set ℝ)
    (e : (f '' K) ≃ₜ (g '' K))
    (hparam : ∀ (t : ℝ) (ht : t ∈ K),
      (e ⟨f t, mem_image_of_mem f ht⟩).1 = g t)
    (u : ℝ) (hu : u ∈ K) :
    (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K f (f u) q.1) =
      (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K g (g u) q.1) := by
  funext q
  exact curveComponentVisitCode_eq_of_subspace_homeomorph f g K e hparam
    (homeomorph_subspace_mem_interior_iff e) u hu q.1 q.2

end LatticeProb
