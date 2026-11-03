/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Field.Law at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Field.Sample

/-!
# Laws of random fields

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797.  This file implements `FOUNDATIONS.md` §2's notion of "law of a random field
as a random distribution": the joint law of the pairings `(⟨X, ρ⟩)_{ρ ∈ TestFun U}` on the
product σ-algebra. Two random fields "agree in law as random distributions on `U`" exactly when
their `fieldLaw`s coincide; "modulo additive constants" restricts the test functions to mass
zero (`fieldLawMod0`).

The pairing used here is the *raw* pairing `pairRaw` (evaluation of the sample at the test
measures `ρ± dz`). No regularization is needed for laws: the law of finitely many fixed
coordinates does not depend on the choice of version of the field. Regularization (`evalReg`)
is only needed where a field is evaluated at random or field-dependent measures, i.e. inside
`coordChange` and friends, and it is already built into those constructions: the raw
coordinates of `coordChange x ψ Q` are regularized evaluations of `x` at pushforward measures.
-/

noncomputable section

open MeasureTheory

namespace QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Raw pairing of a field sample with a real test function `ρ`: evaluate the sample at the
positive and negative parts of the measure `ρ(z) dz`. -/
def pairRaw (x : FieldSample) (ρ : ℂ → ℝ) : ℝ :=
  x (volume.withDensity fun z => ENNReal.ofReal (ρ z)) -
  x (volume.withDensity fun z => ENNReal.ofReal (-ρ z))

/-- The law of a random field `X : Ω → FieldSample` on a probability space `(Ω, P)`, seen only
through its (raw) pairings with test functions on the open set `U`: the pushforward of `P`
under `ω ↦ (ρ ↦ ⟨X ω, ρ.1⟩)`. This is exactly the law of `X` as a random distribution on `U`,
since the target σ-algebra on `TestFun U → ℝ` is the cylinder σ-algebra determined by its
finite-dimensional marginals. "`X` and `Y` agree in law as random distributions on `U`" means
`fieldLaw U X P = fieldLaw U Y P'`. -/
def fieldLaw (U : Set ℂ) (X : Ω → FieldSample) (P : Measure Ω) : Measure (TestFun U → ℝ) :=
  P.map fun ω ρ => pairRaw (X ω) ρ.1

/-- The law of a random field `X` modulo additive constants: as `fieldLaw`, but paired only
against mass-zero test functions (`TestFun0`), so that adding a global constant to `X` does not
change the law. This is how the paper states couplings such as Theorem 1.2, which only hold
"modulo additive constants". -/
def fieldLawMod0 (U : Set ℂ) (X : Ω → FieldSample) (P : Measure Ω) : Measure (TestFun0 U → ℝ) :=
  P.map fun ω ρ => pairRaw (X ω) ρ.1.1

/-- If every coordinate `ω ↦ X ω μ` of a random field is measurable, then so is every raw
pairing `ω ↦ pairRaw (X ω) ρ`. This makes `fieldLaw U X P` an honest pushforward along a
measurable map. -/
theorem measurable_pairRaw_comp {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (ρ : ℂ → ℝ) :
    Measurable fun ω => pairRaw (X ω) ρ :=
  (hX _).sub (hX _)

/-- If every coordinate of `X` is measurable, then for every test function `ρ` the regularized
pairing `ω ↦ pairTest (X ω) ρ.1` is measurable. -/
theorem measurable_pairTest_comp {U : Set ℂ} {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (ρ : TestFun U) :
    Measurable fun ω => pairTest (X ω) ρ.1 :=
  (measurable_pairTest ρ.1).comp (measurable_pi_iff.mpr hX)

/-- The `TestFun0` analogue of `measurable_pairTest_comp`. -/
theorem measurable_pairTest_comp0 {U : Set ℂ} {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (ρ : TestFun0 U) :
    Measurable fun ω => pairTest (X ω) ρ.1.1 :=
  (measurable_pairTest ρ.1.1).comp (measurable_pi_iff.mpr hX)

end QuantumZipper
