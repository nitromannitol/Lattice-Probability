import LatticeProb.Topology.QuotientFiberHomeomorphism
import LatticeProb.Topology.PlanarSubspaceVisitCode

/-! # Component visits determined by compact curve fibres -/

set_option autoImplicit false

open Set Topology

namespace LatticeProb

/-- Continuous planar curves with the same fibres on a compact parameter set
have the same component visit code at rational times in that set. -/
theorem restricted_curveComponentVisitCode_eq_of_compact_same_fibers
    (f g : C(ℝ, ℂ)) (K : Set ℝ) (hK : IsCompact K)
    (hfg : ∀ s ∈ K, ∀ t ∈ K, f s = f t ↔ g s = g t)
    (u : ℝ) (hu : u ∈ K) :
    (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K f (f u) q.1) =
      (fun q : {q : ℚ // (q : ℝ) ∈ K} => curveComponentVisitCode K g (g u) q.1) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → f '' K := fun t => ⟨f t, mem_image_of_mem f t.property⟩
  let G : K → g '' K := fun t => ⟨g t, mem_image_of_mem g t.property⟩
  have hF : Continuous F := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hG : Continuous G := (g.continuous.comp continuous_subtype_val).subtype_mk _
  have hFs : Function.Surjective F := by
    rintro ⟨x, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hGs : Function.Surjective G := by
    rintro ⟨x, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨e, he⟩ := exists_homeomorph_of_quotient_maps_same_fibers F G
    (IsQuotientMap.of_surjective_continuous hFs hF)
    (IsQuotientMap.of_surjective_continuous hGs hG) (by
      intro s t
      simpa only [Subtype.ext_iff, F, G] using hfg s s.property t t.property)
  apply restricted_curveComponentVisitCode_eq_of_planar_subspace_homeomorph f g K e
  · intro t ht
    exact congrArg Subtype.val (he ⟨t, ht⟩)
  · exact hu

end LatticeProb
