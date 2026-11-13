/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianProjectiveLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.Upstream.KolmogorovExtension.KolmogorovExtension
import Mathlib.Probability.BrownianMotion.Basic

/-!
# An actual projective Brownian law

The pinned Mathlib Gaussian finite-dimensional laws are extended by the proved
Kolmogorov extension theorem. This constructs a probability measure on the
entire coordinate-function space. Continuity is a separate construction step.

The extension proof is adapted from Degenne and Pfaffelhuber's
`kolmogorov_extension4`; its exact source and Apache license are retained in
`Upstream/KolmogorovExtension/PROVENANCE.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BouRabeeGwynne

/-- The genuine projective limit of the finite centered Gaussian Brownian laws. -/
noncomputable def brownianProjectiveLaw : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

instance brownianProjectiveLaw_isProbabilityMeasure :
    IsProbabilityMeasure brownianProjectiveLaw := by
  unfold brownianProjectiveLaw
  infer_instance

lemma isProjectiveLimit_brownianProjectiveLaw :
    IsProjectiveLimit brownianProjectiveLaw BrownianReal.projectiveFamily :=
  isProjectiveLimit_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily

/-- The canonical evaluation process has the actual Brownian Gaussian laws at
every finite set of nonnegative real times. No process law is assumed. -/
theorem isPreBrownianReal_brownianProjectiveLaw :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) ↦ ω t) brownianProjectiveLaw where
  hasLaw I := ⟨I.measurable_restrict.aemeasurable,
    isProjectiveLimit_brownianProjectiveLaw I⟩

end BouRabeeGwynne
