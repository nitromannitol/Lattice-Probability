/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.BundleExcursions at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Bundle S7 excursion reconstruction from the restricted IG field

This converts the bundle's S7 circle-process witness to a measurable function
of the IG field restricted to a thickening of the excursion region and its
additive constant. The area-measure and quantum-cell reconstruction of Lemma
4.3 are separate steps.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4c

attribute [local instance] Classical.propDecidable

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The excursion coordinate of the actual coupling factors measurably
through the IG field restricted to a thickening, together with its constant.
The equality is simultaneous for every rational point in the region. -/
theorem ae_bundle_excursions_from_localIG
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : (LQGMetric.DistOn
        (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ) × ℝ) →
          (ℚ × ℚ → ℝ → ℂ),
      Measurable F ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ratPt q ∈ V →
        excursionSegment (ηL ω) V (ratPt q) =
          F (LQGMetric.restrictTo
              (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ)
              (hIG₀ ω), U ω) q := by
  obtain ⟨_Φ, _hΦ, _hpos, _hη, hrest⟩ := D.igMap
  obtain ⟨g, hg, hseg⟩ := hrest.2 V V.isOpen hVb δ hδ
  let W : TopologicalSpace.Opens ℂ := ⟨thickening δ (V : Set ℂ), isOpen_thickening⟩
  refine ⟨fun x => g (localIGCircleProcess W x),
    hg.comp (measurable_localIGCircleProcess W), ?_⟩
  filter_upwards [hseg] with ω hω
  intro q hq
  simpa [ratPt, W, localIGCircleProcess_restrictTo] using hω q hq

end MatedCRTHarmonic.GMS4c
