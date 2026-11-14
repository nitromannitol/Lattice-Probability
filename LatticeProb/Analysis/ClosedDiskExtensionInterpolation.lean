import LatticeProb.Analysis.UniformSegmentImage
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Disk-valued extensions and interpolation

A continuous map from a closed planar set to the closed unit disk extends to
all of the plane with values in the disk. On a compact convex enclosure, its
image of a short chord is close to the chord joining the images of its ends.
-/

namespace LatticeProb

/-- A disk-valued extension gives a uniform interpolation estimate even when
its original domain is nonconvex. -/
theorem exists_disk_extension_dist_lineMap_lt {K B : Set ℂ}
    (hK : IsClosed K) (hB : IsCompact B) (hconv : Convex ℝ B) (hsub : K ⊆ B)
    (f : C(K, Metric.closedBall (0 : ℂ) 1)) :
    ∃ F : C(ℂ, Metric.closedBall (0 : ℂ) 1),
      F.restrict K = f ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist x y < δ →
        dist ((F (AffineMap.lineMap x y t) : ℂ))
          (AffineMap.lineMap (F x : ℂ) (F y : ℂ) t) < ε := by
  obtain ⟨F, hF⟩ := f.exists_restrict_eq hK
  refine ⟨F, hF, ?_⟩
  have hcont : Continuous (fun z : ℂ => (F z : ℂ)) := F.continuous.subtype_val
  have huc := hB.uniformContinuousOn_of_continuous hcont.continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := UniformContinuousOn.dist_image_lineMap_lt huc hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy t ht hxy
  exact hbound x (hsub hx) y (hsub hy) t ht (hconv.lineMap_mem (hsub hx) (hsub hy) ht) hxy

end LatticeProb
