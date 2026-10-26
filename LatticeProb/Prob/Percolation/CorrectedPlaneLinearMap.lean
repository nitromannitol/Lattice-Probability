import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Unique normalized linear maps of corrected planes

On a fixed actual component, normalized existence and uniqueness give a unique linear
map from slopes to corrected planes. The separate unique-slope property makes every
characterized map injective. Both existence and unique-slope properties remain hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Unique normalized planes, when available, assemble into a unique real linear map.
The choice in this existential proof uses the full normalized existence-and-uniqueness. -/
theorem existsUnique_normalized_correctedPlane_linearMap (C : OpenComponent ω) (o : C)
    (hnormalized : ∀ q : Fin d → ℝ,
      ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0) :
    ∃! F : (Fin d → ℝ) →ₗ[ℝ] (C → ℝ),
      ∀ q, IsCorrectedPlane C q (F q) ∧ F q o = 0 := by
  classical
  choose u hu hunique using hnormalized
  let F : (Fin d → ℝ) →ₗ[ℝ] (C → ℝ) :=
    { toFun := u
      map_add' := by
        intro p q
        apply (hunique (p + q) (u p + u q) _).symm
        exact ⟨isCorrectedPlane_add C (hu p).1 (hu q).1,
          by simp only [Pi.add_apply, (hu p).2, (hu q).2, add_zero]⟩
      map_smul' := by
        intro r q
        apply (hunique (r • q) (r • u q) _).symm
        exact ⟨isCorrectedPlane_smul C (hu q).1 r,
          by simp only [Pi.smul_apply, (hu q).2, smul_zero]⟩ }
  refine ⟨F, hu, ?_⟩
  intro G hG
  apply LinearMap.ext
  intro q
  exact hunique q (G q) (hG q)

/-- The exact unique-slope property on A₁ makes any characterized linear map injective.
No separation of gradients or independent slope-injectivity assumption is needed. -/
theorem correctedPlane_linearMap_injective (C : OpenComponent ω)
    (hslope : ∀ u : C → ℝ, u ∈ harmonicGrowthSpace C 1 →
      ∃! q : Fin d → ℝ, IsCorrectedPlane C q u)
    (F : (Fin d → ℝ) →ₗ[ℝ] (C → ℝ))
    (hF : ∀ q, IsCorrectedPlane C q (F q)) : Function.Injective F := by
  intro p q hpq
  obtain ⟨s, _, hunique⟩ := hslope (F p) (hF p).1
  have hq : IsCorrectedPlane C q (F p) := hpq.symm ▸ hF q
  exact (hunique p (hF p)).trans (hunique q hq).symm

/-- Every nonzero slope gives a nonzero plane for a map with the unique-slope property. -/
theorem correctedPlane_linearMap_apply_ne_zero (C : OpenComponent ω)
    (hslope : ∀ u : C → ℝ, u ∈ harmonicGrowthSpace C 1 →
      ∃! q : Fin d → ℝ, IsCorrectedPlane C q u)
    (F : (Fin d → ℝ) →ₗ[ℝ] (C → ℝ))
    (hF : ∀ q, IsCorrectedPlane C q (F q))
    (q : Fin d → ℝ) (hq : q ≠ 0) : F q ≠ 0 := by
  intro heq
  apply hq
  apply correctedPlane_linearMap_injective C hslope F hF
  exact heq.trans (map_zero F).symm

end

end LatticeProb.Percolation
