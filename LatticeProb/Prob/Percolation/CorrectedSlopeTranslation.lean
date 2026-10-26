import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.MeasurableCorrectorGradients

/-!
# Translation covariance of actual integer-gradient slopes

The source existential uses the actual unique infinite component and every actual edge.
Translation transports the entire existential, including its dependent component carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Literal existence of a source corrected plane with integer drops on all actual edges. -/
def HasIntegerGradientCorrectedPlane (h : HasUniqueInfiniteOpenComponent ω)
    (q : Fin d → ℝ) : Prop :=
  ∃ u : uniqueInfiniteComponent h → ℝ,
    IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
    ∀ x y : uniqueInfiniteComponent h, (openGraph ω).Adj x.val y.val →
      ∃ n : ℤ, u y - u x = (n : ℝ)

/-- Actual unique-component transport preserves and reflects every real source slope. -/
theorem hasIntegerGradientCorrectedPlane_translation_iff (z : Vertex d)
    (h : HasUniqueInfiniteOpenComponent ω)
    (ht : HasUniqueInfiniteOpenComponent (configurationTranslation z ω))
    (q : Fin d → ℝ) :
    HasIntegerGradientCorrectedPlane ht q ↔ HasIntegerGradientCorrectedPlane h q := by
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent ht := openComponentTranslation_uniqueInfiniteComponent z h
  unfold HasIntegerGradientCorrectedPlane
  rw [← hC]
  exact exists_integer_gradient_correctedPlane_translation_iff z (uniqueInfiniteComponent h) q

/-- Actual measurable gradient coefficients have full subgroup covariance on an invariant
valid set, derived solely from their complete source-existential characterization. -/
theorem integerSlopeSubgroup_translation_on_valid_set
    (G : Set (Configuration d)) (hvalid : G ⊆ correctorValidEvent d)
    (hinv : ∀ z ω, configurationTranslation z ω ∈ G ↔ ω ∈ G)
    (g : G → (Vertex d × Vertex d) → Fin d → ℝ)
    (hsource : ∀ (ω : G) q,
      q ∈ LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) ↔
        HasIntegerGradientCorrectedPlane (hvalid ω.property).1 q)
    (ω : G) (z : Vertex d) :
    LatticeProb.Prob.Percolation.integerSlopeSubgroup
        (g ⟨configurationTranslation z ω.val, (hinv z ω.val).mpr ω.property⟩) =
      LatticeProb.Prob.Percolation.integerSlopeSubgroup (g ω) := by
  ext q
  rw [hsource, hsource]
  exact hasIntegerGradientCorrectedPlane_translation_iff z _ _ q

end

end LatticeProb.Percolation
