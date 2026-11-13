/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.HarmonicMainStatement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicLawIngredients
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicApproximation
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Util.AssertNoSorry

/-!
The full harmonic-coordinate main statement, manuscript Theorem `s:thm:main`.
This file defines the proposition to be proved; it does not provide its proof.
Every construction and convergence witness is in the conclusion. The only
random-law assumptions are almost-sure geometric validity, full mass transport,
and the FE moment condition. In particular there is no ergodicity assumption.

The physical similarity relation is the existing relation on canonically
labelled environments. The canonical relabeling action is a total, single-valued,
measurable group action (proved since this file was written: `exists_isSimilarity`,
`IsSimilarity.target_unique`, `measurable_similarityActionEnv`), so the covariance and
mass-transport clauses quantify over exactly the manuscript's similarities.
-/
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ReflectedGMS.HarmonicMainStatement
open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation

/-- The independent auxiliary marking uses the actual product probability law. -/
abbrev MarkedEnvironment := Env × Grid

/-- The actual Section 4 interpolation at a fixed canonical cell label, extended
by zero at absent labels. Its almost-sure specification and measurability are
conclusions below, never hypotheses about a free approximating sequence. -/
noncomputable def approximationAtLabel (m : ℕ) (ω : MarkedEnvironment) (n : ℕ) :
    Plane := by
  classical
  exact if hn : (ω.1.val.1 n).isSome then
    phi (decode ω.1) ω.2 m ⟨n, hn⟩ else 0

/-- Uniform error on the graph-distance ball of integer radius `radius` about
H_0. The open graph ball of radius `radius + 1` contains precisely those vertices
at graph distance at most `radius`. Clipping the norm at 1 preserves convergence
to zero and makes the supremum bounded before graph-ball finiteness is used.
All boundary-root errors are zero by the shared boundary-mask convention. -/
noncomputable def graphNeighborhoodError (Φ : CellField) (radius m : ℕ)
    (ω : MarkedEnvironment) : ℝ :=
  (rootAt (decode ω.1) 0).elim 0 fun r =>
    ⨆ v : (decode ω.1).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      min 1 ‖normalizedPhi (decode ω.1) ω.2 r m v.val - Φ.at ω.1 v.val‖

/-- The rooted specific energy of the actual approximating gradient error.
Subtracting a root constant has no effect on this gradient quantity. -/
noncomputable def specificGradientError (Φ : CellField) (m : ℕ)
    (ω : MarkedEnvironment) : ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode ω.1)
    (fun v => phi (decode ω.1) ω.2 m v - Φ.at ω.1 v) 0

/-- Full induced-patch energy of the same gradient error. The patch need not be
finite or connected, and no finite-support closure is introduced. -/
noncomputable def spatialPatchError (Φ : CellField) (m : ℕ)
    (ω : MarkedEnvironment) (A : Set Plane) : ℝ≥0∞ :=
  vectorEnergy (restrictGraph (decode ω.1).graph {v | Hits (decode ω.1) A v})
    (fun v => phi (decode ω.1) ω.2 m v.val - Φ.at ω.1 v.val)

/-- The specific-energy convergence in clause (d), including finiteness at
every approximation stage. Expectations are extended nonnegative integrals. -/
def SpecificEnergyConvergence (ν : Measure Env) (σ : Measure Grid)
    (Φ : CellField) : Prop :=
  (∀ m : ℕ,
    AEMeasurable (fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1)
        (phi (decode ω.1) ω.2 m) 0) (ν.prod σ) ∧
    (∫⁻ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1)
        (phi (decode ω.1) ω.2 m) 0 ∂ν.prod σ) < ∞) ∧
  (∀ m : ℕ, AEMeasurable (specificGradientError Φ m) (ν.prod σ)) ∧
  Tendsto (fun m => ∫⁻ ω : MarkedEnvironment, specificGradientError Φ m ω ∂ν.prod σ)
    atTop (𝓝 0)

/-- One deterministic increasing subsequence works simultaneously on every
bounded spatial patch and at every vertex, almost surely for the independent
marked law. The subsequence is chosen outside the almost-sure quantifier. -/
def DeterministicSubsequenceConvergence (ν : Measure Env) (σ : Measure Grid)
    (Φ : CellField) : Prop :=
  ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod σ,
      (∀ A : Set Plane, Bornology.IsBounded A →
        Tendsto (fun j => spatialPatchError Φ (subsequence j) ω A) atTop (𝓝 0)) ∧
      ∀ r : Vertex ω.1.val, rootAt (decode ω.1) 0 = some r →
        ∀ v : Vertex ω.1.val,
          Tendsto (fun j => normalizedPhi (decode ω.1) ω.2 r (subsequence j) v)
            atTop (𝓝 (Φ.at ω.1 v))

/-- Clause (d) for any actual uniform dyadic-grid law independent of the
unmarked environment. The specification refers to the fixed concrete `phi`,
and existence and uniqueness of its full minimizer are conclusions. -/
def ApproximationConclusions (ν : Measure Env) (σ : Measure Grid)
    (Φ : CellField) : Prop :=
  (∀ m n : ℕ, AEMeasurable (fun ω => approximationAtLabel m ω n) (ν.prod σ)) ∧
  (∀ᵐ ω : MarkedEnvironment ∂ν.prod σ,
    FinitePositiveIndices (decode ω.1) ω.2 ∧
    ∀ m : ℕ,
      IsBlockInterpolation (decode ω.1) ω.2 m (phi (decode ω.1) ω.2 m) ∧
      ∀ f : Vertex ω.1.val → Plane,
        IsBlockInterpolation (decode ω.1) ω.2 m f → f = phi (decode ω.1) ω.2 m) ∧
  (∀ radius m : ℕ, AEMeasurable (graphNeighborhoodError Φ radius m) (ν.prod σ)) ∧
  (∀ radius : ℕ, TendstoInMeasure (ν.prod σ)
    (fun m ω => graphNeighborhoodError Φ radius m ω) atTop (fun _ => 0)) ∧
  SpecificEnergyConvergence ν σ Φ ∧
  DeterministicSubsequenceConvergence ν σ Φ

/-- All conclusions for one measurable environment-only coordinate field.
The same Φ is used for every auxiliary uniform-grid law and can also be reused
in the process theorem. Existence of a uniform-grid law is included so that
the last clause cannot hold merely because that law class is empty. -/
def IsHarmonicCoordinate (ν : Measure Env) (Φ : CellField) : Prop :=
    GradientCovariant Φ ∧
    NormalizedCovariant Φ ∧
    AEMeasurable (fun e => rootedSpecificEnergyDensity (decode e) (Φ.at e) 0) ν ∧
    FiniteSpecificEnergy ν Φ ∧
    (∀ᵐ e : Env ∂ν,
      (0 : Plane) ∉ boundaryMask (decode e) ∧
      RootNormalized Φ e ∧
      FullSpatialHarmonicity Φ e ∧
      DiscreteHarmonicity Φ e ∧
      SublinearCorrector Φ e) ∧
    (∃ σ : Measure Grid, UniformGridLaw σ) ∧
    ∀ σ : Measure Grid, UniformGridLaw σ → ApproximationConclusions ν σ Φ

/-- One unmarked measurable field simultaneously satisfies every clause,
including approximation using every independent uniform-grid law. -/
def HarmonicCoordinateConclusions (ν : Measure Env) : Prop :=
  ∃ Φ : CellField, IsHarmonicCoordinate ν Φ

/-- The complete ambient-law harmonic-coordinate target. This declaration is
a proposition, not a proof of it. Almost-sure validity includes all Geometry
clauses and AE-LC with its simultaneous-all-real-endpoints quantifier order.
Full trace-measurable mass transport and FE are the only further hypotheses. -/
def HarmonicCoordinateMainTheorem : Prop :=
  ∀ (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P),
    AmbientMassTransport P hP →
    FiniteEnergyMoment (validLaw P hP) →
    HarmonicCoordinateConclusions (validLaw P hP)

end ReflectedGMS.HarmonicMainStatement

-- These audit the statement definitions, not proofs of the main proposition.
assert_no_sorry ReflectedGMS.HarmonicMainStatement.IsHarmonicCoordinate
assert_no_sorry ReflectedGMS.HarmonicMainStatement.HarmonicCoordinateMainTheorem
#print axioms ReflectedGMS.HarmonicMainStatement.IsHarmonicCoordinate
#print axioms ReflectedGMS.HarmonicMainStatement.HarmonicCoordinateMainTheorem
