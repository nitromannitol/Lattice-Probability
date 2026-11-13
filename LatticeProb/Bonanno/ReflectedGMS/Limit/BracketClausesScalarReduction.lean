/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketClausesScalarReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketRegularity
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssemblyFourInputs
import LatticeProb.Bonanno.ReflectedGMS.Limit.PlaneCoordinateMartingale

/-!
# Bracket clauses one and five, reduced to scalar diagonal statements

`Limit/CanonicalBracketClauses.OrdinaryEdgeBracketClauses` lists five clauses behind
the `hbracket` input of the invariance assembly; `Limit/LocalizedBracketRegularity`
closes clauses two, three and four from `CanonicalOccupationLocallyFinite`, leaving

1. `IsLocallySquareIntegrableMartingale P.completion F M` for the **plane-valued**
   harmonic path `M`, and
5. `IsLocalMartingale P.completion F (M^i M^j − ⟨M^i, M^j⟩)` for **every pair** `i j`,
   with the bracket written as the manuscript's integral `ordinaryEdgeBracket`.

Every martingale producer in `Forms/` is scalar and diagonal: it speaks about one real
coordinate function `u : V → ℝ`, the path value `u(X)`, and the canonical adapted
occupation `adaptedJumpOccupation PF G m u` as the compensator of its *square*
(`vertexDynkinSquareCompensation_isMartingale`,
`fullEnergyMartingaleLimit_squareCompensation_isMartingale`, …).  This module reduces
the two open clauses to that vocabulary:

* clause one from the two scalar coordinates of `M`
  (`Limit/PlaneCoordinateMartingale`);
* clause five for the pair `i j` from the **three diagonal** compensated squares of the
  coordinates `Φ^i`, `Φ^j` and `Φ^i + Φ^j`, by polarization: pathwise
  `M^i M^j = ½((M^i + M^j)² − (M^i)² − (M^j)²)`, and almost surely at every time
  `ordinaryEdgeBracket i j = ½(A_{i+j} − A_i − A_j)` for the adapted occupations
  `A_u` — this is exactly the occupation identification
  `CanonicalBracketClauses.BracketOccupationIdentification`, already produced from
  `CanonicalOccupationLocallyFinite` by `Limit/LocalizedBracketOccupation`.  The
  linear combination of local martingales and the almost-sure modification are
  `Limit/LocalMartingaleCombination`.

## Discharge or reduction?

**This is a REDUCTION, not a discharge.**  The two open clauses are replaced by the
named inputs `CoordinateLocallySquareIntegrable` and `DiagonalCompensatedSquares`
below, which are scalar and diagonal but carry the same mathematical content: that the
harmonic path is a locally square-integrable local martingale with the ordinary-edge
occupation as its predictable square compensator.  Nothing here certifies them.  What
is discharged is the plumbing between the two vocabularies — plane-valued versus
scalar, cross terms versus diagonal, manuscript bracket integral versus canonical
adapted occupation — and the new inputs are never harder to satisfy than the old
clauses (they are implied by them).

## Why the new inputs are satisfiable, and where their content lives

Both inputs are stated on the completed area filtration under the completed canonical
law, for the process `M` pinned by `PathwiseClockClauses` to be the càdlàg spatial
extension of `Φ` along the lifted path.  No `Summable (cellArea …)` and no
`HasFiniteEnergy` hypothesis appears anywhere.  The manuscript's own proof of these
statements (`p:lem:localharm`, `p:thm:martingale`) localizes by *spatial* exit times,
which pass through reflection times, and excludes a boundary drift at those times by
the full spatial variational test `FullSpatialHarmonicity` (clause `H5c` of
`IsHarmonicCoordinate`), not by vertex harmonicity alone.  See the handoff
`outputs/fable-bracket-clauses-1-5-handoff.md` for the accounting of what is missing.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.BracketClausesScalarReduction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.CanonicalBracketClauses
open ReflectedGMS.LocalizedBracketOccupation
open ReflectedGMS.LocalizedBracketRegularity
open ReflectedGMS.LocalMartingaleCombination
open ReflectedGMS.PlaneCoordinateMartingale

/-! ## The two scalar diagonal inputs -/

/-- **Clause one, coordinatewise.**  Each real coordinate of the harmonic path is a
locally square-integrable martingale of the completed area filtration under the
completed canonical law. -/
def CoordinateLocallySquareIntegrable (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) : Prop :=
  ∀ i : Fin 2,
    IsLocallySquareIntegrableMartingale
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => M t ω i)

/-- **One diagonal compensated square.**  For a real coordinate function `u` on the
vertices and a real path `Z`, the square of `Z` compensated by the canonical adapted
ordinary-edge occupation of `u` is a local martingale of the completed area filtration
under the completed canonical law. -/
def CompensatedSquareClause (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)
    (u : Vertex e.val → ℝ) (Z : ℝ≥0 → Existence.Sample (Vertex e.val) → ℝ) : Prop :=
  IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
    (areaFiltration e D (areaSampleLaw (decode e) D hG start))
    (fun t ω => Z t ω ^ 2 -
      adaptedJumpOccupation (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e)) u t ω)

/-- **Clause five, diagonalized.**  The compensated squares of the two coordinates and
of every coordinate sum.  The sums are what the polarization consumes; the pair
`i = j` is covered by the second clause as well, at no extra cost to a producer. -/
def DiagonalCompensatedSquares (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) : Prop :=
  (∀ i : Fin 2, CompensatedSquareClause e D hG start
      (fun v => Φ.at e v i) (fun t ω => M t ω i)) ∧
  (∀ i j : Fin 2, CompensatedSquareClause e D hG start
      ((fun v => Φ.at e v i) + (fun v => Φ.at e v j)) (fun t ω => M t ω i + M t ω j))

/-! ## Ambient facts about the completed canonical law and filtration -/

section Ambient

variable (e : Env) [Nontrivial (Vertex e.val)]
  (D : (decode e).graph.Exhaustion)
  (hG : (decode e).graph.toSimpleGraph.Connected) (start : Vertex e.val)

/-- The canonical sample law is a probability measure (it is the starting law of the
constructed process family). -/
theorem isProbabilityMeasure_areaSampleLaw :
    IsProbabilityMeasure (areaSampleLaw (decode e) D hG start) :=
  (Existence.processFamily D hG (areaRate (decode e))).isProbabilityMeasure start

/-- The completed canonical law is finite. -/
theorem isFiniteMeasure_areaSampleLaw_completion :
    IsFiniteMeasure (areaSampleLaw (decode e) D hG start).completion := by
  haveI := isProbabilityMeasure_areaSampleLaw e D hG start
  exact ⟨(Measure.completion_apply (areaSampleLaw (decode e) D hG start) Set.univ).trans_lt
    (measure_lt_top _ Set.univ)⟩

/-- The completed area filtration contains every null event of the completed law. -/
theorem measurableSet_areaFiltration_of_null (t : ℝ≥0)
    (A : Set (NullMeasurableSpace (Existence.Sample (Vertex e.val))
      (areaSampleLaw (decode e) D hG start)))
    (hA : (areaSampleLaw (decode e) D hG start).completion A = 0) :
    MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t] A :=
  measurableSet_completedNaturalFiltration_of_null
    (areaSampleLaw (decode e) D hG start)
    (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
    (fun t => (measurable_of_countable (observedState e)).comp
      (measurable_exponentialAreaPath (decode e) D t)) t A hA

end Ambient

/-! ## Path regularity supplied by the pathwise clock clauses -/

section Regularity

variable (e : Env) [Nontrivial (Vertex e.val)]
  (D : (decode e).graph.Exhaustion)
  (hG : (decode e).graph.toSimpleGraph.Connected)
  (Φ : CellField) (start : Vertex e.val)
  (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
  (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)

/-- The harmonic path is almost surely right continuous, under the completed law. -/
theorem ae_isRightContinuous_of_pathwiseClockClauses
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
      IsRightContinuous (fun t => M t ω) :=
  (SpatialExtensionCadlagClause.ae_isCadlag_of_pathwiseClockClauses
    e D hG Φ start Xexp Xexact M hpcc).mono fun _ hω => hω.isRightContinuous

/-- Each coordinate of the harmonic path is almost surely right continuous. -/
theorem ae_isRightContinuous_coord_of_pathwiseClockClauses
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M) (i : Fin 2) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
      IsRightContinuous (fun t => M t ω i) :=
  (ae_isRightContinuous_of_pathwiseClockClauses e D hG Φ start Xexp Xexact M hpcc).mono
    fun _ hω => isRightContinuous_coord hω i

/-- The canonical adapted occupation of each coordinate function, and of each coordinate
sum, is almost surely continuous in time — from `CanonicalOccupationLocallyFinite`. -/
theorem ae_continuous_adaptedJumpOccupation_of_canonicalOccupationLocallyFinite
    (hdat : EnvironmentWalkData e D hG)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start) :
    (∀ i : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Continuous (fun t => adaptedJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e)) (fun v => Φ.at e v i) t ω)) ∧
    (∀ i j : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Continuous (fun t => adaptedJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        ((fun v => Φ.at e v i) + (fun v => Φ.at e v j)) t ω)) := by
  obtain ⟨hmin, -, hwalk, -⟩ := hdat
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · exact (adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      (G := (decode e).graph) (m := cellArea (decode e)) (hmin := hmin)
      (PF := Existence.processFamily D hG (areaRate (decode e))) hwalk
      (fun v => Φ.at e v i) start (hocc.1 i)).mono fun _ hω => hω.2.1
  · exact (adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      (G := (decode e).graph) (m := cellArea (decode e)) (hmin := hmin)
      (PF := Existence.processFamily D hG (areaRate (decode e))) hwalk
      ((fun v => Φ.at e v i) + (fun v => Φ.at e v j)) start (hocc.2 i j)).mono
      fun _ hω => hω.2.1

end Regularity

/-! ## Clause one from the coordinates -/

section ClauseOne

variable (e : Env) [Nontrivial (Vertex e.val)]
  (D : (decode e).graph.Exhaustion)
  (hG : (decode e).graph.toSimpleGraph.Connected)
  (Φ : CellField) (start : Vertex e.val)
  (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
  (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)

/-- **Clause one of `OrdinaryEdgeBracketClauses` from its two scalar coordinates.**
CONDITIONAL on `hmart`; nothing here certifies it. -/
theorem isLocallySquareIntegrableMartingale_of_coordinates
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hmart : CoordinateLocallySquareIntegrable e D hG start M) :
    IsLocallySquareIntegrableMartingale
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M := by
  haveI := isFiniteMeasure_areaSampleLaw_completion e D hG start
  exact isLocallySquareIntegrableMartingale_euclidean_of_coords hmart
    (measurableSet_areaFiltration_of_null e D hG start)
    (ae_isRightContinuous_of_pathwiseClockClauses e D hG Φ start Xexp Xexact M hpcc)

end ClauseOne

/-! ## Clause five from the three diagonal compensated squares -/

section ClauseFive

variable (e : Env) [Nontrivial (Vertex e.val)]
  (D : (decode e).graph.Exhaustion)
  (hG : (decode e).graph.toSimpleGraph.Connected)
  (Φ : CellField) (start : Vertex e.val)
  (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
  (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)

/-- A compensated square `Z² − A` is almost surely right continuous when `Z` is right
continuous and `A` is continuous. -/
theorem ae_isRightContinuous_compensatedSquare
    {P : Measure (Existence.Sample (Vertex e.val))}
    {Z A : ℝ≥0 → Existence.Sample (Vertex e.val) → ℝ}
    (hZ : ∀ᵐ ω ∂P, IsRightContinuous (fun t => Z t ω))
    (hA : ∀ᵐ ω ∂P, Continuous (fun t => A t ω)) :
    ∀ᵐ ω ∂P, IsRightContinuous (fun t => Z t ω ^ 2 - A t ω) := by
  filter_upwards [hZ, hA] with ω hωZ hωA
  exact hωZ.continuous_comp₂ hωA.isRightContinuous
    (φ := fun z a => z ^ 2 - a)
    (by first | fun_prop | exact (continuous_fst.pow 2).sub continuous_snd)

/-- **Clause five of `OrdinaryEdgeBracketClauses` for one pair, from the three diagonal
compensated squares.**  CONDITIONAL on `hsq`; nothing here certifies it.

The polarization is exact: pathwise `M^i M^j = ½((M^i+M^j)² − (M^i)² − (M^j)²)`, and
almost surely at every time the manuscript's bracket integral is
`½(A_{i+j} − A_i − A_j)` for the canonical adapted occupations, by the occupation
identification produced from `CanonicalOccupationLocallyFinite`. -/
theorem isLocalMartingale_compensatedProduct_of_diagonal
    (hdat : EnvironmentWalkData e D hG)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start)
    (hsq : DiagonalCompensatedSquares e D hG Φ start M) (i j : Fin 2) :
    IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => M t ω i * M t ω j -
        ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j t ω) := by
  haveI := isFiniteMeasure_areaSampleLaw_completion e D hG start
  have hnull := measurableSet_areaFiltration_of_null e D hG start
  have hcont := ae_continuous_adaptedJumpOccupation_of_canonicalOccupationLocallyFinite
    e D hG Φ start hdat hocc
  have hri := ae_isRightContinuous_coord_of_pathwiseClockClauses
    e D hG Φ start Xexp Xexact M hpcc
  -- right continuity of the three diagonal processes, under the completed law
  have hrI := ae_isRightContinuous_compensatedSquare e (hri i) (hcont.1 i)
  have hrJ := ae_isRightContinuous_compensatedSquare e (hri j) (hcont.1 j)
  have hrIJ := ae_isRightContinuous_compensatedSquare e
    ((hri i).and (hri j) |>.mono fun _ hω => hω.1.add hω.2) (hcont.2 i j)
  -- the linear combination ½ (N_{i+j} − N_i − N_j)
  have hlin := isLocalMartingale_const_mul
    (isLocalMartingale_sub (isLocalMartingale_sub (hsq.2 i j) (hsq.1 i) hnull hrIJ hrI)
      (hsq.1 j) hnull (hrIJ.and hrI |>.mono fun _ hω => hω.1.sub hω.2) hrJ) (1 / 2)
  -- identification with the compensated product, almost surely at all times
  refine isLocalMartingale_of_ae_eq hlin hnull ?_
  have hid := bracketOccupationIdentification_of_canonicalOccupationLocallyFinite
    e D hG Φ start hdat hocc i j
  filter_upwards [hid] with ω hω
  intro t
  rw [← hω t]
  simp only [polarizedJumpOccupation, SquareCovariationPolarization.polarizedCompensator]
  ring

end ClauseFive

/-! ## The assembled clause list and the consumer welds -/

section Assembly

variable (e : Env) [Nontrivial (Vertex e.val)]
  (D : (decode e).graph.Exhaustion)
  (hG : (decode e).graph.toSimpleGraph.Connected)
  (Φ : CellField) (start : Vertex e.val)
  (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
  (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)

/-- **The `hbracket` input of the invariance assembly from the scalar diagonal inputs.**

CONDITIONAL on `hlocal`; this certifies neither `hlocal`, nor `hbracket`, nor either
main theorem.  The conclusion is, verbatim, the `hbracket` hypothesis of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` and of
`InvarianceAssemblyFourInputs.reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged`;
compared with `LocalizedBracketRegularity.hbracket_of_ae_local_inputs`, clauses one and
five are replaced by their scalar diagonal forms. -/
theorem hbracket_of_ae_scalar_inputs (ν : Measure Env) (Φ : CellField)
    (hlocal : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          CanonicalOccupationLocallyFinite e D hG Φ start ∧
          CoordinateLocallySquareIntegrable e D hG start M ∧
          DiagonalCompensatedSquares e D hG Φ start M) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M := by
  refine hbracket_of_ae_local_inputs ν Φ ?_
  filter_upwards [hlocal] with e he
  intro hnt D hG hdat start Xexp Xexact M hpcc
  have : Nontrivial (Vertex e.val) := hnt
  obtain ⟨hocc, hmart, hsq⟩ := he hnt D hG hdat start Xexp Xexact M hpcc
  exact ⟨hocc,
    isLocallySquareIntegrableMartingale_of_coordinates e D hG Φ start Xexp Xexact M
      hpcc hmart,
    isLocalMartingale_compensatedProduct_of_diagonal e D hG Φ start Xexp Xexact M
      hdat hpcc hocc hsq⟩

end Assembly

/-! ## Machine-checked weld with the four-input invariance assembly

This is `Limit/LocalBracketInvarianceWeld.reflectedInvarianceConclusions_of_local_bracket_inputs`
with its `hlocal` binder replaced by the scalar diagonal form; the `hreg` and
`hlimit` binders are copied verbatim.  Its elaboration is the machine check that the
scalar producer fits the assembly.  Nothing here proves a main theorem: the four inputs
`hΦ`, `hreg`, `hlocal`, `hlimit` remain open. -/

theorem reflectedInvarianceConclusions_of_scalar_bracket_inputs
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hreg : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω))
    (hlocal : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          CanonicalOccupationLocallyFinite e D hG Φ start ∧
          CoordinateLocallySquareIntegrable e D hG start M ∧
          DiagonalCompensatedSquares e D hG Φ start M)
    (hlimit : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            ∀ target : AnisotropicBrownianTarget,
              target.covariance = meanCovariance ν Φ →
              ∀ z : CellField, IsCellRepresentative z →
                RepresentativePathConclusions e z
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact) :
    ReflectedInvarianceConclusions ν :=
  InvarianceAssemblyFourInputs.reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged
    ν hmt hFE Φ hΦ hreg (hbracket_of_ae_scalar_inputs ν Φ hlocal) hlimit

end ReflectedGMS.BracketClausesScalarReduction
