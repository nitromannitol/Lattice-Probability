/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.CurveAdapters at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0SideStrict
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Brownian and Peanosphere adapters for the mating-of-trees bundle

The Brownian-only fields of `RouteM.Peanosphere` and `RouteM.SideStrict` are derived from
the bundle's frozen correlated-Brownian law. The curve fields are transported through the
bundle's increasing area reparameterization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, the area-parametrized curve and its boundary-length process satisfy the
complete Peanosphere interface consumed by Route M. -/
theorem ae_peanosphere
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, RouteM.Peanosphere (bm ω) (η ω) := by
  have hL := MatedCRT.ae_liminf_L D.boundaryLawBM
  have hR := MatedCRT.ae_liminf_R D.boundaryLawBM
  have hMin := MatedCRT.ae_locMinDistinct D.boundaryLawBM
  have hLΩ := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hL
  have hRΩ := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hR
  have hMinΩ := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hMin
  filter_upwards [D.spaceFilling, D.areaParam, D.merge, D.onlyMerge, hLΩ, hRΩ, hMinΩ]
    with ω hspace harea hmerge honly hlimL hlimR hmin
  rcases hspace with ⟨hsurjL, htransL, hzeroL, _⟩
  rcases harea with ⟨⟨φ, hφ0, hηeq⟩, _⟩
  refine ⟨(η ω).continuous, ?_, ?_, ?_, ?_, hlimL, hlimR, hmin⟩
  · intro z
    obtain ⟨t, ht⟩ := hsurjL z
    refine ⟨φ.symm t, ?_⟩
    rw [hηeq, φ.apply_symm_apply, ht]
  · have hφ : Tendsto φ (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hcomp := htransL.comp hφ
    have hηfun : (η ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hηeq
    rw [hηfun]
    exact hcomp
  · exact hmerge
  · exact honly

/-- The strict Brownian side condition holds simultaneously at every dyadic mesh on the
bundle's sample space. -/
theorem ae_sideStrict_allMeshes
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, RouteM.SideStrict (CellFamily.mesh k) (bm ω) := by
  have hpath : ∀ᵐ w ∂(P.map bm), ∀ k : ℕ,
      RouteM.SideStrict (CellFamily.mesh k) w := by
    refine ae_all_iff.2 fun k => ?_
    exact MatedCRT.ae_sideStrict D.boundaryLawBM (CellFamily.mesh k) (by
      dsimp [CellFamily.mesh]
      positivity)
  exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hpath

end MatedCRTHarmonic.MoTInput
