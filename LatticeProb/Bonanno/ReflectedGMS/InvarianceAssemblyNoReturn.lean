/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceAssemblyNoReturn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockRecurrence

/-!
# The invariance assembly with the recurrence input discharged

`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` carries four
process-level inputs: `hlift`, `hreturn`, `hbracket`, `hlimit`.  This file
removes `hreturn` — recurrence at **every** vertex for **both** area clocks —
from that list.

The two halves of `hreturn` are obtained as follows.

* The exponential clock is the constructed reflected walk itself, so
  `AreaClockRecurrence.returnsToEveryVertex_exponentialAreaPath` proves its
  recurrence at every vertex from the project's own residual clock clause
  `EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`, which is the
  finiteness half of (3.16) for the area rate.  Nothing probabilistic beyond
  that clause is used: Remark 3.1 supplies recurrence of every level chain, and
  the passage from the level chain to the continuous-time path is the
  deterministic `AreaClockRecurrence.exists_ge_X_eq_level`.
* The exact-holding clock is a pathwise homeomorphic time change of the
  exponential one, and that time change is the eighth clause of
  `InvarianceAssembly.PathwiseClockClauses`, i.e. part of the `hlift` input
  already present.  So the exact clock needs no hypothesis of its own
  (`AreaClockRecurrence.returnsToEveryVertex_of_isHomeomorphicTimeChange`).

The single new input `hclock` is therefore strictly weaker than `hreturn`: it
is a statement about the area **clock** alone (every level-`0` index is reached
in finite time), with no reference to the path's range, and it is the *same*
residual that already reduces the `hdata` input through
`EnvironmentWalkDataProducer.environmentWalkData_of_areaClockReachesLevelZeroIndices`.

This file proves no main theorem; it is an implication whose remaining
hypotheses `hΦ`, `hdata`, `hclock`, `hlift`, `hbracket`, `hlimit` are open, and
nothing here certifies any of them.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.InvarianceAssemblyNoReturn

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.AreaClockRecurrence

/-- **The recurrence input of the invariance assembly, discharged.**

From the area-clock residual `hclock` and the lift input `hlift`, both clauses
of `hreturn` follow, in the exact shape
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` consumes. -/
theorem hreturn_of_hclock_of_hlift (ν : Measure Env) (Φ : CellField)
    (hclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG)
    (hlift : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ReturnsToEveryVertex (areaSampleLaw (decode e) D hG ⟨n, hn⟩)
              (exponentialAreaPath (decode e) D) ∧
            ReturnsToEveryVertex (areaSampleLaw (decode e) D hG ⟨n, hn⟩)
              (exactAreaPath (decode e) D) := by
  intro n
  filter_upwards [hclock, hlift n] with e hc hl
  intro hn hnt D hG hdat
  have : Nontrivial (Vertex e.val) := hnt
  obtain ⟨Xexp, Xexact, M, hP⟩ := hl hn hnt D hG hdat
  refine returnsToEveryVertex_both e D hG (hc hnt D hG hdat) ⟨n, hn⟩ ?_
  filter_upwards [hP] with ω hω
  exact hω.2.2.2.2.2.2.2.1

/-- **Reduction of `ReflectedInvarianceConclusions` to named inputs, with the
recurrence input removed.**

This is `InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`
with `hreturn` replaced by the strictly weaker area-clock clause `hclock`.
The three remaining process-level inputs are `hlift`, `hbracket` and `hlimit`;
`hΦ` is the harmonic-coordinate clause, owned elsewhere, and `hmt`, `hFE` are
the main theorem's own environment hypotheses.

It is an implication, not a proof of the reflected invariance principle. -/
theorem reflectedInvarianceConclusions_of_named_inputs_no_return
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hdata : ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG)
    (hclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG)
    (hlift : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M)
    (hbracket : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M)
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
  reflectedInvarianceConclusions_of_named_inputs ν hmt hFE Φ hΦ hdata hlift
    (hreturn_of_hclock_of_hlift ν Φ hclock hlift) hbracket hlimit

end ReflectedGMS.InvarianceAssemblyNoReturn
