/-
Resampling one coordinate of an infinite product, and the Fubini identity it gives.

Under `Measure.infinitePi μ`, overwriting the coordinate `i` with an independent draw
from `μ i` leaves the product law unchanged (`LatticeProb.measurePreserving_update_infinitePi`,
in `LatticeProb/Prob/Splice.lean`).  This file records the two consequences used by the
sandpile formalization: the integral of a function of the resampled field equals the
integral of the function itself, and a function of the resampled field may be averaged
over the fresh coordinate first.
-/
import LatticeProb.Prob.Splice

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **Resampling one coordinate does not change an integral.**  For an integrable
`g` of the field, the integral of `g` against the product law equals the integral of
`g` against the law of the field with coordinate `i` overwritten by an independent
draw from `μ i`. -/
theorem integral_infinitePi_update [DecidableEq ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    {g : (Π j, X j) → ℝ} (hg : Integrable g (Measure.infinitePi μ)) :
    ∫ ζ, g ζ ∂(Measure.infinitePi μ)
      = ∫ q : X i × (Π j, X j), g (Function.update q.2 i q.1)
          ∂((μ i).prod (Measure.infinitePi μ)) := by
  have hmp := measurePreserving_update_infinitePi μ i
  have hswap : ∫ q : X i × (Π j, X j), g (Function.update q.2 i q.1)
      ∂((μ i).prod (Measure.infinitePi μ))
      = ∫ q : (Π j, X j) × X i, g (Function.update q.1 i q.2)
      ∂((Measure.infinitePi μ).prod (μ i)) := by
    rw [← Measure.prod_swap]
    exact integral_map_equiv (MeasurableEquiv.prodComm) _
  have hg' : AEStronglyMeasurable g
      (Measure.map (fun q : (Π j, X j) × X i => Function.update q.1 i q.2)
        ((Measure.infinitePi μ).prod (μ i))) := by
    rw [hmp.map_eq]; exact hg.aestronglyMeasurable
  rw [hswap]
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hg']

/-- **Averaging over the fresh coordinate.**  For a function of the resampled field
that is integrable against the product law, the integral may be taken over the fresh
coordinate first: the inner integral is a function of the field alone. -/
theorem integral_infinitePi_update_eq_integral_integral [DecidableEq ι]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    {g : (Π j, X j) → ℝ} (hg : Integrable g (Measure.infinitePi μ)) :
    ∫ ζ, g ζ ∂(Measure.infinitePi μ)
      = ∫ ω : Π j, X j, ∫ y : X i, g (Function.update ω i y) ∂(μ i)
          ∂(Measure.infinitePi μ) := by
  rw [integral_infinitePi_update μ i hg]
  have hswap : ∫ q : X i × (Π j, X j), g (Function.update q.2 i q.1)
      ∂((μ i).prod (Measure.infinitePi μ))
      = ∫ q : (Π j, X j) × X i, g (Function.update q.1 i q.2)
      ∂((Measure.infinitePi μ).prod (μ i)) := by
    rw [← Measure.prod_swap]
    exact integral_map_equiv (MeasurableEquiv.prodComm) _
  rw [hswap]
  exact integral_prod _ ((measurePreserving_update_infinitePi μ i).integrable_comp_of_integrable hg)

/-- **Resampling one coordinate preserves the product law, coordinate first.**  The
same statement as `measurePreserving_update_infinitePi` with the fresh coordinate
carried on the left, which is the order in which the Fubini identity is applied. -/
theorem measurePreserving_update_infinitePi_swap [DecidableEq ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun q : X i × (Π j, X j) => Function.update q.2 i q.1)
      ((μ i).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  have hswap : MeasurePreserving (Prod.swap : X i × (Π j, X j) → (Π j, X j) × X i)
      ((μ i).prod (Measure.infinitePi μ)) ((Measure.infinitePi μ).prod (μ i)) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  exact (measurePreserving_update_infinitePi μ i).comp hswap

end LatticeProb
