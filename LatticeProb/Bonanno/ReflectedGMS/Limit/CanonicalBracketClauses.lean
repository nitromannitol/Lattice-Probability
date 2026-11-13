/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CanonicalBracketClauses at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly
import LatticeProb.Bonanno.ReflectedGMS.Forms.PredictableCompletionModification

/-!
# The `hbracket` input of the invariance assembly, reduced to atomic clauses

`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` (and its
recurrence-free form `InvarianceAssemblyNoReturn`) carries an input `hbracket`
whose conclusion is `InvarianceMainStatement.CanonicalBracket e D Φ P M`, i.e.
`MartingaleIngredients.HasOrdinaryEdgeBracket` on the completed natural
filtration of the exponential area clock.  This file reduces that input to a
**per-environment** list of five atomic clauses, `OrdinaryEdgeBracketClauses`,
and discharges the predictability clause of
`MartingaleIngredients.IsContinuousPredictableCovariation` from the fourth of
them.

Nothing here proves `hbracket`, `p:thm:areaclt` or either main theorem: the
statements below are implications whose hypotheses are open, and none of them
certifies any hypothesis.

## Why the existing discharge of predictability is not usable

`Limit/ActualArrayBracketLimit.canonicalBracket_of_parts` discharges the same
predictability clause through
`PredictableCompletionModification.isStronglyPredictable_ordinaryEdgeBracket_exponentialAreaPath`.
That route carries two hypotheses which are **false at the canonical data**, so
it is vacuous there and cannot be used by a consumer:

* `hsum : Summable (StatementIngredients.cellArea (Code.decode e))`.  The cells
  of a coded environment are compact, have pairwise disjoint interiors and
  satisfy `⋃ v, cell v = Set.univ` (clause five of `Environment.Geometry`, which
  `Code.decode_geometry` supplies for **every** `e : Env`).  Countable
  subadditivity then gives `∑' v, volume (cell v) ≥ volume (univ : Set Plane) = ∞`,
  so the cell areas are never summable.  The project already works around this
  elsewhere: `Process/LocalAreaSummability` proves only the *local* bound, area
  of the cells meeting a ball, and several `Temporal/` modules record "no finite
  total area" explicitly.
* `hFE : ∀ i, (Code.decode e).graph.HasFiniteEnergy fun v => Φ.at e v i`.
  `ReflectedWalk.ConductanceGraph.HasFiniteEnergy f` is `Summable (G.gradSq f)`,
  the **total** Dirichlet energy over the infinite vertex set.  The harmonic
  coordinate of `HarmonicMainStatement.IsHarmonicCoordinate` is only asked to
  have finite *specific* energy, `FiniteSpecificEnergy ν Φ`, i.e. a finite
  rooted energy *density*; a coordinate with positive specific energy on an
  infinite environment has infinite total energy.

Both hypotheses enter that lane through
`ActualHarmonicBracketIdentification.polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket`,
which is the a.e. identification of the manuscript's bracket integral with the
canonical occupation.  The *predictability of the occupation itself* needs
neither: `stronglyPredictable_rightCont_polarizedJumpOccupation` has no
hypotheses at all.  So the fix is to carry the identification as a named input
(`BracketOccupationIdentification`) rather than to derive it from `Summable` and
`HasFiniteEnergy`, and that is what this file does.  The resulting reduction
uses **no** `Summable` and **no** `HasFiniteEnergy` hypothesis anywhere.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Function
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.CanonicalBracketClauses

open Code EnvironmentFields EnvironmentLaws
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk ProcessFiltration
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.PredictableCompletionModification

/-! ## The occupation-identification clause -/

/-- **The identification clause.**  On one full-probability event the
manuscript's ordinary-edge bracket integral `p:eq:fastPhibracket` agrees, at
*every* time, with the canonical predictable occupation
`ReflectedGMS.polarizedJumpOccupation` of the constructed area-clock family.

This is exactly the conclusion of
`ActualHarmonicBracketIdentification.polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket`,
whose own proof needs `Summable (cellArea …)` and total finite energy of the
coordinate; both fail at the canonical data (see the module docstring), so the
clause is carried as a named input here. -/
def BracketOccupationIdentification (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val) : Prop :=
  ∀ i j : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
    polarizedJumpOccupation (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        (fun v => Φ.at e v i) (fun v => Φ.at e v j) t ω =
      ordinaryEdgeBracket (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D) i j t ω

/-- **Predictability of the ordinary-edge bracket from the identification
clause alone.**

CONDITIONAL on `hocc`; nothing here certifies it.

The predictable representative is the canonical occupation, whose predictability
in the right-continuous natural filtration of the path
(`stronglyPredictable_rightCont_polarizedJumpOccupation`) carries **no**
hypotheses; `hdom` is discharged because `observedState` is an injective code of
the path, and `hjoint` by `BracketJointMeasurability`.  So the only input is the
a.e. identity itself — in particular neither `Summable (cellArea …)` nor total
finite energy of `Φ` is used. -/
theorem isStronglyPredictable_ordinaryEdgeBracket_of_occupationIdentification
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (hocc : BracketOccupationIdentification e D hG Φ start) (i j : Fin 2) :
    IsStronglyPredictable
      (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (ordinaryEdgeBracket (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D) i j) :=
  isStronglyPredictable_completedNaturalFiltration_of_ae_eq
    (areaSampleLaw (decode e) D hG start)
    (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
    (fun t => (measurable_of_countable (observedState e)).comp
      (measurable_exponentialAreaPath (decode e) D t))
    (A := polarizedJumpOccupation (Existence.processFamily D hG (areaRate (decode e)))
      (decode e).graph (cellArea (decode e))
      (fun v => Φ.at e v i) (fun v => Φ.at e v j))
    (isStronglyPredictable_mono
      (fun t => naturalFiltration_rightCont_le_completedNaturalFiltration
        (areaSampleLaw (decode e) D hG start)
        (Existence.processFamily D hG (areaRate (decode e))).X
        (Existence.processFamily D hG (areaRate (decode e))).measurable_X
        (observedState_injective e)
        (fun t => (measurable_of_countable (observedState e)).comp
          (measurable_exponentialAreaPath (decode e) D t)) t)
      (stronglyPredictable_rightCont_polarizedJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        (fun v => Φ.at e v i) (fun v => Φ.at e v j)))
    (BracketJointMeasurability.measurable_uncurry_ordinaryEdgeBracket_processFamily
      D hG (areaRate (decode e)) (decode e) (Φ.at e) i j)
    (hocc i j)

/-! ## The five atomic clauses -/

/-- **The atomic clause list behind `CanonicalBracket`.**

For one environment, one exhaustion, one connectivity witness, one starting cell
and one plane-valued process `M`, these are the five clauses that the checked
corpus does not supply:

* local square integrability of `M` as a martingale of the completed area
  filtration;
* pathwise càdlàg paths of `M` and interval integrability of the bracket
  density along the exponential area clock;
* the occupation identification `BracketOccupationIdentification`;
* the pathwise regularity of the bracket integral — it starts at `0`, is
  continuous, and has locally bounded variation;
* the compensated products `M^i M^j - ⟨M^i, M^j⟩` are local martingales.

Every one of them is a statement about the actual constructed process under the
actual canonical law.  None of them mentions `Summable` or `HasFiniteEnergy`. -/
def OrdinaryEdgeBracketClauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane) : Prop :=
  IsLocallySquareIntegrableMartingale
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M ∧
  (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsCadlag (fun t => M t ω) ∧
      ∀ (i j : Fin 2) (t : ℝ≥0),
        IntervalIntegrable
          (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D (Real.toNNReal s) ω) i j)
          volume 0 (t : ℝ)) ∧
  BracketOccupationIdentification e D hG Φ start ∧
  (∀ i j : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j 0 ω = 0 ∧
      Continuous (fun t => ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j t ω) ∧
      ∀ T : ℝ≥0, BoundedVariationOn
        (fun t => ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j t ω) (Set.Icc 0 T)) ∧
  (∀ i j : Fin 2,
      IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (fun t ω => M t ω i * M t ω j -
          ordinaryEdgeBracket (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D) i j t ω))

/-- **`CanonicalBracket` from the five atomic clauses**, with the predictability
clause discharged.

CONDITIONAL on `OrdinaryEdgeBracketClauses`; nothing here certifies it.

This is the honest replacement for
`Limit/ActualArrayBracketLimit.canonicalBracket_of_parts`, whose `hsum` and
`hFE` hypotheses are false at the canonical data (module docstring). -/
theorem canonicalBracket_of_clauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (h : OrdinaryEdgeBracketClauses e D hG Φ start M) :
    CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M :=
  ⟨h.1, h.2.1, fun i j =>
    ⟨isStronglyPredictable_ordinaryEdgeBracket_of_occupationIdentification
        e D hG Φ start h.2.2.1 i j,
      h.2.2.2.1 i j, h.2.2.2.2 i j⟩⟩

/-! ## The `hbracket` input -/

/-- **The `hbracket` input of the invariance assembly, reduced.**

CONDITIONAL on `hclauses`; this certifies neither `hclauses`, nor `hbracket`,
nor either main theorem.

The conclusion is, verbatim, the `hbracket` hypothesis of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` and of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`.

`hclauses` keeps **every** hypothesis that `hbracket` gives its producer — the
walk data and the pathwise clock clauses, in particular the clause pinning `M`
as the spatial extension of `Φ` along the lift, without which the clause list is
false for a general `M`.  What it drops is the packaging:

* the per-label quantifier `∀ n : ℕ, ∀ hn : (e.val.1 n).isSome` is replaced by a
  quantifier over actual starting cells, and the per-label almost-sure
  statements by one almost-sure environment statement;
* the conclusion `CanonicalBracket`, i.e.
  `MartingaleIngredients.HasOrdinaryEdgeBracket` on the completed filtration, is
  replaced by the five atomic clauses of `OrdinaryEdgeBracketClauses`, of which
  the predictability clause of `IsContinuousPredictableCovariation` — the one
  measure-theoretic clause, on the predictable σ-algebra of a *completed*
  filtration — no longer appears at all. -/
theorem hbracket_of_ae_ordinaryEdgeBracketClauses (ν : Measure Env) (Φ : CellField)
    (hclauses : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          OrdinaryEdgeBracketClauses e D hG Φ start M) :
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
  intro n
  filter_upwards [hclauses] with e he
  intro hn hnt D hG hdat Xexp Xexact M hpcc
  have : Nontrivial (Vertex e.val) := hnt
  exact canonicalBracket_of_clauses e D hG Φ ⟨n, hn⟩ M
    (he hnt D hG hdat ⟨n, hn⟩ Xexp Xexact M hpcc)

end ReflectedGMS.CanonicalBracketClauses
