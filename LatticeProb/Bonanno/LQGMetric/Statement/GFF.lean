/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.GFF at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Statement layer, part 2: the whole-plane GFF and "GFF plus a continuous function"

`FOUNDATIONS.md` §2 (block copied verbatim). Source: GM (arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex`) l. 211–214: "We say that a random distribution
h on ℂ is a whole-plane GFF plus a continuous function if there exists a coupling of h with a
random continuous function f : ℂ → ℝ such that the law of h − f is that of a whole-plane GFF. We
similarly define a whole-plane GFF plus a bounded continuous function, except we require that f
is bounded. … the whole-plane GFF is defined only modulo a global additive constant"; l. 223–224
"a whole-plane GFF normalized so that its circle average over ∂𝔻 is zero".
Normalization of the covariance `−log|x − y|`: Duplantier–Sheffield / Miller–Sheffield (IG4,
`literature/src/1302.4738`, l. 1082). Decisions D3; deviations F2, F3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal

namespace LQGMetric

/-- mean-zero test functions -/
def TestC0 : Type := {φ : TestC // ∫ z, φ z = 0}
/-- `∫∫ φ(x) (−log|x−y|) ψ(y) dx dy` -/
def logCov (φ ψ : ℂ → ℝ) : ℝ := ∫ x, ∫ y, φ x * (-Real.log ‖x - y‖) * ψ y

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `h` is a whole-plane GFF (any additive constant, possibly random): its pairings with
mean-zero test functions form a centered Gaussian process with covariance `logCov`. -/
structure IsWholePlaneGFF (h : Ω → DistC) (P : Measure Ω) : Prop where
  measurable : Measurable h
  gaussian : IsGaussianProcess (fun (φ : TestC0) (ω : Ω) => h ω φ.1) P
  centered : ∀ φ : TestC0, ∫ ω, h ω φ.1 ∂P = 0
  covariance_eq : ∀ φ ψ : TestC0,
    cov[fun ω => h ω φ.1, fun ω => h ω ψ.1; P] = logCov φ.1 ψ.1

/-- normalized so that `h_1(0) = 0` (GM l. 223–224) -/
def IsNormalizedWPGFF (h : Ω → DistC) (P : Measure Ω) : Prop :=
  IsWholePlaneGFF h P ∧ ∀ᵐ ω ∂P, circleAvg (h ω) 1 0 = 0

/-- whole-plane GFF plus a continuous function (GM l. 211) -/
def IsGFFPlusCont (h : Ω → DistC) (P : Measure Ω) : Prop :=
  Measurable h ∧ ∃ f : Ω → C(ℂ, ℝ), Measurable f ∧
    IsWholePlaneGFF (fun ω => h ω - ofCont (f ω)) P

/-- … plus a bounded continuous function (GM l. 212) -/
def IsGFFPlusBddCont (h : Ω → DistC) (P : Measure Ω) : Prop :=
  Measurable h ∧ ∃ f : Ω → C(ℂ, ℝ), Measurable f ∧ (∀ ω, ∃ M, ∀ z, |f ω z| ≤ M) ∧
    IsWholePlaneGFF (fun ω => h ω - ofCont (f ω)) P

end LQGMetric
