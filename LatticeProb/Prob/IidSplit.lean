/-
The Fubini identity for an i.i.d. field split at one site.

`Pw_n(0)` is a function of the scenery that does not read the coordinate `i`; the
step of case (b) of `prop:dgt4-contact-asymptotics` is Fubini for the i.i.d. field
split at that site.  This file records the identity in the shape the sandpile
formalization consumes.
-/
import LatticeProb.Prob.UpdateSite
import LatticeProb.IID

noncomputable section

set_option linter.unusedVariables false

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-- **Resampling one site of an i.i.d. field preserves its law.**  Overwriting the
coordinate `i` of the field by an independent draw from `ν` leaves the i.i.d. law
unchanged. -/
theorem measurePreserving_updateSite (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (i : Site d) :
    MeasurePreserving (fun q : ℝ × (Site d → ℝ) => Function.update q.2 i q.1)
      (ν.prod (iidLaw d ν)) (iidLaw d ν) :=
  measurePreserving_update_infinitePi_swap (fun _ : Site d => ν) i

/-- **One coordinate against the rest of an i.i.d. field.**  For a measurable
`f : ℝ → ℝ → ℝ`, a measurable `W` of the field that does not read the coordinate
`i`, and an integrable `ζ ↦ f (ζ i) (W ζ)`, the integral against the i.i.d. law
equals the iterated integral that averages the fresh coordinate first. -/
theorem integral_iidLaw_split {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (i : Site d) {f : ℝ → ℝ → ℝ} (hf : Measurable fun q : ℝ × ℝ => f q.1 q.2)
    {W : (Site d → ℝ) → ℝ} (hW : Measurable W)
    (hWloc : ∀ ζ η : Site d → ℝ, (∀ z, z ≠ i → ζ z = η z) → W ζ = W η)
    (hint : Integrable (fun ζ => f (ζ i) (W ζ)) (iidLaw d ν)) :
    (∫ ζ, f (ζ i) (W ζ) ∂(iidLaw d ν))
      = ∫ ζ, (∫ z, f z (W ζ) ∂ν) ∂(iidLaw d ν) := by
  have hloc : ∀ (ζ : Site d → ℝ) (y : ℝ), f y (W (Function.update ζ i y)) = f y (W ζ) := by
    intro ζ y
    congr 1
    exact hWloc _ _ (fun z hz => by simp [Function.update, hz])
  simp only [iidLaw]
  rw [integral_infinitePi_update_eq_integral_integral (fun _ : Site d => ν) i hint]
  refine integral_congr_ae ?_
  filter_upwards with ζ
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
    simp only [Function.update_self]
    exact hloc ζ y)

end LatticeProb
