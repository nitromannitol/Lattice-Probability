import LatticeProb.Prob.Percolation.LatticeBondTranslation
import LatticeProb.Prob.Percolation.LatticeBondFiniteFlip

/-!
# Conjugation of finite bond flips by translations

Finite patches consist of genuine unordered nearest-neighbor bonds. Translating a
configuration after flipping a patch flips its positive translate after translation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- Membership in a translated finite patch is inverse translation membership. -/
theorem mem_image_bondTranslation_iff (z : Vertex d) (F : Finset (Bond d)) (e : Bond d) :
    e ∈ F.image (bondTranslation z) ↔ bondTranslation (-z) e ∈ F := by
  classical
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa only [bondTranslation_add, neg_add_cancel, bondTranslation_zero] using ha
  · intro he
    apply Finset.mem_image.mpr
    refine ⟨bondTranslation (-z) e, he, ?_⟩
    rw [bondTranslation_add, add_neg_cancel, bondTranslation_zero]

/-- The full configuration identity conjugates every finite unordered bond patch. -/
theorem configurationTranslation_finiteBondFlip (z : Vertex d) (F : Finset (Bond d))
    (ω : Configuration d) :
    configurationTranslation z (finiteBondFlip F ω) =
      finiteBondFlip (F.image (bondTranslation z)) (configurationTranslation z ω) := by
  classical
  funext e
  simp only [configurationTranslation_apply, finiteBondFlip, BernoulliFiniteFlip.flip_apply,
    mem_image_bondTranslation_iff]

end LatticeProb.Percolation
