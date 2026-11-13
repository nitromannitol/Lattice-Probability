/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SquareCovariationPolarization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinSquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.PredictableJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import Mathlib.Analysis.BoundedVariation

/-!
# Polarization of square-compensation martingales

This module turns three global compensated-square martingales, for `M`, `N`,
and `M + N`, into the mixed compensated-product martingale.  It then packages
the result in the project's exact continuous predictable covariation predicate.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

namespace SquareCovariationPolarization

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The compensator obtained by polarizing the three diagonal compensators. -/
noncomputable def polarizedCompensator (A B C : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ (C t ω - A t ω - B t ω) / 2

/-- Bounded variation is closed under addition.  This small adapter is absent
from the pinned high-level bounded-variation API. -/
theorem boundedVariationOn_add {α : Type*} [LinearOrder α]
    {f g : α → ℝ} {s : Set α} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) : BoundedVariationOn (f + g) s := by
  unfold BoundedVariationOn at hf hg ⊢
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((f + g) (u (i + 1))) ((f + g) (u i))) ≤
        ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Pi.add_apply] using
        edist_add_add_le (f (u (i + 1))) (g (u (i + 1)))
          (f (u i)) (g (u i))
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- Bounded variation is closed under multiplication by a real constant. -/
theorem boundedVariationOn_const_smul {α : Type*} [LinearOrder α]
    (c : ℝ) {f : α → ℝ} {s : Set α} (hf : BoundedVariationOn f s) :
    BoundedVariationOn (c • f) s := by
  have hc : BoundedVariationOn (fun _ : α ↦ c) s := by
    unfold BoundedVariationOn
    rw [eVariationOn.constant_on]
    · exact ENNReal.zero_ne_top
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rfl
  exact hc.smul hf

end SquareCovariationPolarization

end ReflectedGMS
