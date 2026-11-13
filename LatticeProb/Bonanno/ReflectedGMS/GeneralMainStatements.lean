/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeneralMainStatements at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CodeGeneralValid
import LatticeProb.Bonanno.ReflectedGMS.HarmonicMainStatement
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainStatement
import LatticeProb.Bonanno.ReflectedGMS.Geometry.EndSpatialImage

/-!
# Theorems 1.2 and 1.3 of the general-cell singular-set manuscript — statements

Manuscript text: `work/general/manuscript-text.txt`, lines 141–231.

**Hypotheses.**
* The environment law `P` is carried by codes satisfying **Definition 1.1 and (LCS)** with canonical
  labels (`GeneralLaws.SupportedOnValidGeneral`, built on `Code.ValidGeneral` and
  `GeneralGeometry`): compact connected cells with nonempty interiors meeting pairwise in null sets,
  a closed `H¹`-null singular set off which the cells cover and are spatially locally finite,
  arbitrary symmetric adjacency with intersecting adjacent cells and finite positive conductances,
  and connectivity of `H(L)` for every axis-parallel compact segment `L` avoiding the singular set.
  No face/incidence rule, no exceptional vertex set, no assumed graph connectedness and no
  almost-everywhere line connectivity.
* Mass transport modulo scaling (1.4), the moment (FE) with the conductance sums read as extended
  nonnegative sums, and for Theorem 1.3 ergodicity modulo scaling — `GeneralLaws.MassTransport`,
  `GeneralLaws.FiniteEnergyMoment`, `GeneralLaws.EnvironmentErgodic`, on the general environment
  space `Code.EnvGeneral`.

`GeneralHarmonicCoordinateMainTheorem` and `GeneralReflectedInvarianceMainTheorem` carry exactly
these hypotheses; **graph local finiteness is not assumed** — it is derived (Lemma 2.5,
`GeneralLaws.ae_finiteRows`), and the conclusion records it through `∃ hV : SupportedOnValid P`.

The `…OfLocallyFinite` variants are an intermediate form that assumes graph local finiteness
(`∀ᵐ r ∂P, Code.FiniteRows r`) and states (1.4), (FE) and ergodicity with the earlier predicates
`AmbientMassTransport`, `FiniteEnergyMoment`, `AmbientEnvironmentErgodic` on `validLaw P _`.  They
are proved too, and are implied by the paper-faithful theorems' ingredients; they are kept because
on the GMS class local finiteness is automatic (`GMSGeometry.locallyFiniteGraph`).

**Conclusions.**  Clause-for-clause those of `HarmonicMainStatement.HarmonicCoordinateConclusions`
and `InvarianceMainStatement.ReflectedInvarianceConclusions`, plus the first sentence of 1.3(b):
every graph end has a unique spatial image in `Ssing ∪ {∞}` "as in Proposition 2.6"
(`EndSpatialImageConclusions`).  The end-image sentence is stated **deterministically** for every
environment satisfying Definition 1.1 and (LCS) with a locally finite graph, and for **every**
singular witness, which is stronger than the manuscript's "conditionally on almost every
environment".
-/

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS.GeneralMainStatements

open Code EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement InvarianceMainStatement
open EndSpatialImage SpatialEnds GeneralLaws CellConfiguration

/-- A law carried by Definition 1.1 + (LCS) codes with locally finite graphs is carried by valid
codes in the sense of the earlier formalization (`Code.valid_of_validGeneral`: Lemma 2.1 and
Proposition 2.3). -/
theorem supportedOnValid_of_general {P : Measure RawCode} (hP : SupportedOnValidGeneral P)
    (hLF : ∀ᵐ r ∂P, FiniteRows r) : SupportedOnValid P :=
  (hP.and hLF).mono fun _ hr => valid_of_validGeneral hr.1 hr.2

/-- **Theorem 1.3(b), first sentence** (Proposition 2.6): for every singular-set witness of
Definition 1.1(ii) and every graph end, the nested spherical closures of the end's cell components
shrink to one point of the Riemann sphere; that point lies in `Ssing ∪ {∞}`; it is `∞` exactly for
the ends at spatial infinity; and the end-to-sphere map is continuous (every open neighbourhood of
the image contains the images of all ends agreeing on a suitable finite vertex set — the basic
neighbourhoods of the end topology).  The image `endImage F e` depends only on the configuration and
the end, not on the witness or an exhaustion. -/
def EndSpatialImageConclusions {V : Type*} [Countable V] (F : IndexedCells V) : Prop :=
  ∀ (w : SingularSet F.toCellConfiguration) (e : GraphEnd F),
    (⋂ K : Finset V, endCellClosure F e K) = {endImage F e} ∧
    (endImage F e = OnePoint.infty ∨ ∃ z ∈ w.sing, endImage F e = (z : OnePoint Plane)) ∧
    (endImage F e = OnePoint.infty ↔ AtSpatialInfinity F e) ∧
    (∀ U : Set (OnePoint Plane), IsOpen U → endImage F e ∈ U →
      ∃ K : Finset V, ∀ e' : GraphEnd F,
        e'.val (Opposite.op K) = e.val (Opposite.op K) → endImage F e' ∈ U)

/-- **Theorem 1.2 with graph local finiteness assumed** (intermediate form).  Definition 1.1, (LCS),
graph local finiteness, (1.4) and (FE) imply the harmonic-coordinate conclusions (a)–(d).

This declaration states a proposition; it does not assert that it has been proved. -/
def GeneralHarmonicCoordinateMainTheoremOfLocallyFinite : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P)
    (hLF : ∀ᵐ r ∂P, FiniteRows r),
    AmbientMassTransport P (supportedOnValid_of_general hP hLF) →
    FiniteEnergyMoment (validLaw P (supportedOnValid_of_general hP hLF)) →
      HarmonicCoordinateConclusions (validLaw P (supportedOnValid_of_general hP hLF))

/-- **Theorem 1.3 with graph local finiteness assumed** (intermediate form).  Definition 1.1, (LCS),
graph local finiteness, (1.4), (FE) and ergodicity modulo scaling imply clauses (a)–(e), together with the
spatial images of graph ends (first sentence of (b)).

This declaration states a proposition; it does not assert that it has been proved. -/
def GeneralReflectedInvarianceMainTheoremOfLocallyFinite : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P)
    (hLF : ∀ᵐ r ∂P, FiniteRows r),
    AmbientMassTransport P (supportedOnValid_of_general hP hLF) →
    FiniteEnergyMoment (validLaw P (supportedOnValid_of_general hP hLF)) →
    AmbientEnvironmentErgodic P (supportedOnValid_of_general hP hLF) →
      ReflectedInvarianceConclusions (validLaw P (supportedOnValid_of_general hP hLF)) ∧
        ∀ e : Env, ValidGeneral e.val → EndSpatialImageConclusions (decode e)

/-- **Theorem 1.2** (harmonic coordinates), with exactly the manuscript's hypotheses: Definition 1.1,
(LCS), (1.4) and (FE) (extended conductance sums), all on the general environment space, with **no**
graph-local-finiteness hypothesis.  The conclusion asserts that almost every environment is valid in
the earlier sense — in particular has a locally finite graph (Lemma 2.5) — and the
harmonic-coordinate conclusions (a)–(d) for the environment law (`(validLaw P hV).map val = P`).

This declaration states a proposition; it does not assert that it has been proved. -/
def GeneralHarmonicCoordinateMainTheorem : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P),
    GeneralLaws.MassTransport (generalLaw P hP) →
    GeneralLaws.FiniteEnergyMoment (generalLaw P hP) →
      ∃ hV : SupportedOnValid P, HarmonicCoordinateConclusions (validLaw P hV)

/-- **Theorem 1.3** (reflected invariance principle), with exactly the manuscript's hypotheses:
Definition 1.1, (LCS), (1.4), (FE) and ergodicity modulo scaling on the general environment space,
with **no** graph-local-finiteness hypothesis.

This declaration states a proposition; it does not assert that it has been proved. -/
def GeneralReflectedInvarianceMainTheorem : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P),
    GeneralLaws.MassTransport (generalLaw P hP) →
    GeneralLaws.FiniteEnergyMoment (generalLaw P hP) →
    GeneralLaws.EnvironmentErgodic (generalLaw P hP) →
      ∃ hV : SupportedOnValid P,
        ReflectedInvarianceConclusions (validLaw P hV) ∧
          ∀ e : Env, ValidGeneral e.val → EndSpatialImageConclusions (decode e)

end ReflectedGMS.GeneralMainStatements
