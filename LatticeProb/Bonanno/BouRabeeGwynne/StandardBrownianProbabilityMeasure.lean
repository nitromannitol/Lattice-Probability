/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StandardBrownianProbabilityMeasure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.EuclideanWienerLaw

/-!
# The standard Brownian law as a `ProbabilityMeasure`

`euclideanWienerLaw` is a `Measure` carrying an `IsProbabilityMeasure`
instance.  Downstream statements — in particular the reflected-GMS
`AnisotropicBrownianTarget` — take a bundled `ProbabilityMeasure` together with
`IsStandardBrownianLaw` for its underlying measure.  This file packages the
already-constructed law in that form, so those statements have an
unconditional, machine-checked inhabitant rather than a hypothesis supplying
one.

Nothing here is a new probabilistic construction: every mathematical content is
`isStandardBrownianLaw_euclideanWienerLaw`.
-/

open MeasureTheory

set_option autoImplicit false

namespace BouRabeeGwynne

/-- The constructed Euclidean Wiener law, bundled as a `ProbabilityMeasure`. -/
noncomputable def standardBrownianProbabilityMeasure (d : ℕ) :
    ProbabilityMeasure (BrownianPath d) :=
  ⟨euclideanWienerLaw d, inferInstance⟩

@[simp] lemma standardBrownianProbabilityMeasure_coe (d : ℕ) :
    ((standardBrownianProbabilityMeasure d : ProbabilityMeasure (BrownianPath d)) :
      Measure (BrownianPath d)) = euclideanWienerLaw d := rfl

/-- The bundled law is a standard Brownian law. -/
theorem isStandardBrownianLaw_standardBrownianProbabilityMeasure (d : ℕ) :
    IsStandardBrownianLaw
      ((standardBrownianProbabilityMeasure d : ProbabilityMeasure (BrownianPath d)) :
        Measure (BrownianPath d)) :=
  isStandardBrownianLaw_euclideanWienerLaw d

/-- A standard Brownian law exists as a bundled probability measure, in every
dimension.  This discharges hypotheses of the form
`(μBM : ProbabilityMeasure (BrownianPath d)) (hBM : IsStandardBrownianLaw μBM)`
with no probabilistic premise. -/
theorem exists_standardBrownianProbabilityMeasure (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianPath d),
      IsStandardBrownianLaw (μ : Measure (BrownianPath d)) :=
  ⟨standardBrownianProbabilityMeasure d,
    isStandardBrownianLaw_standardBrownianProbabilityMeasure d⟩

end BouRabeeGwynne
