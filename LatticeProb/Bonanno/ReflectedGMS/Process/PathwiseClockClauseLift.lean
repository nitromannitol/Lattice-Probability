/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.PathwiseClockClauseLift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssemblyNoReturn
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExponentialAreaEndLift
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy

/-!
# The `hlift` input of the invariance assembly, reduced to four atomic inputs

`InvarianceAssembly.PathwiseClockClauses e D hG Φ start Xexp Xexact M` is a
conjunction of **ten** almost-sure pathwise clauses.  The `hlift` input of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`
asserts, for almost every environment and every starting label, that some triple
`(Xexp, Xexact, M)` satisfies all ten.  This file replaces that single monolithic
input by **four named atomic inputs**, and discharges the remaining six clauses.

## Status of the ten conjuncts

| # | clause | status |
|---|--------|--------|
| 1 | `collapse ∘ Xexp = exponentialAreaPath` | **discharged** from `MassTransport ν` + (FE) |
| 2 | `collapse ∘ Xexact = exactAreaPath` | **derived** from input (8) |
| 3 | `IsEndLabeling Xexp` | **discharged** from `MassTransport ν` + (FE) |
| 4 | `IsEndLabeling Xexact` | **derived** from input (8) |
| 5 | `AvoidsSpatialInfinity Xexp` | **discharged** from `MassTransport ν` + (FE) |
| 6 | `AvoidsSpatialInfinity Xexact` | **derived** from input (8) |
| 7 | `IsHomeomorphicTimeChange exponentialAreaPath canonicalFastPath` | **open input** `hfast` |
| 8 | `IsHomeomorphicTimeChange exactAreaPath exponentialAreaPath` | **open input** `hexact` |
| 9 | exact holding lengths `t - s = a_v/π(v)` | **open input** `hhold` |
| 10 | `RegularSpatialExtension Φ Xexp M` | **open input** `hreg` |

Clauses 1, 3, 5 are the checked
`ExponentialAreaEndLift.ae_exists_expLift_of_massTransport`, whose ball-bound
hypothesis is itself discharged by the checked
`SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity`; so
they cost **nothing beyond the main theorem's own environment hypotheses**
(`MassTransport ν` and the finite (FE) moment).

Clauses 2, 4, 6 cost nothing at all.  Input (8) says the exact-holding path is a
pathwise homeomorphic time change of the exponential one, so the *exact* lift can
be taken to be the exponential lift precomposed with that time change
(`exactLift`): lifting, end labelling and avoidance of spatial infinity are all
stable under precomposition by a homeomorphism of `[0,∞)`
(`isEndLabeling_comp_homeomorph`, `avoidsSpatialInfinity_comp`).  This is the same
economy that `AreaClockRecurrence.returnsToEveryVertex_exactAreaPath` exploits for
the recurrence clause.

Inputs (9) and (10) are stated **without reference to any lift**: clause 9 is
transported to the collapsed `Option`-valued path by
`isHoldingInterval_iff_isCollapsedHoldingInterval` (the holding-interval predicate
depends on a `State`-valued path only through its collapse), and clause 10 is
required of an arbitrary lift satisfying clauses 1, 3, 5 — which is a.s. unique,
so nothing is lost.

## What this file does not do

It proves no main theorem and certifies none of the four inputs.  The final
statement is an implication whose hypotheses `hΦ`, `hdata`, `hclock`, `hfast`,
`hexact`, `hhold`, `hreg`, `hbracket`, `hlimit` are open.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.PathwiseClockClauseLift

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer

/-! ## Holding intervals depend on the path only through its collapse -/

section HoldingIntervals

variable {V : Type*}

/-- `SpatialEnds.IsHoldingInterval` written directly on the collapsed,
`Option V`-valued path.  This is the form in which the exact-holding-length
clause can be stated without naming a lift. -/
def IsCollapsedHoldingInterval (F : IndexedCells V) (X : ℝ≥0 → Option V)
    (v w : V) (s t : ℝ≥0) : Prop :=
  s < t ∧
  (∀ r ∈ Ico s t, X r = some v) ∧
  X t = some w ∧ F.graph.toSimpleGraph.Adj v w ∧
  (s = 0 ∨ ∀ r < s, ∃ q ∈ Ioo r s, X q ≠ some v)

/-- A `State`-valued path has exactly the holding intervals of its collapse. -/
theorem isHoldingInterval_iff_isCollapsedHoldingInterval {F : IndexedCells V}
    {Y : ℝ≥0 → State F} {X : ℝ≥0 → Option V} (hc : ∀ t, collapse (Y t) = X t)
    (v w : V) (s t : ℝ≥0) :
    IsHoldingInterval F Y v w s t ↔ IsCollapsedHoldingInterval F X v w s t := by
  have key : ∀ r : ℝ≥0, Y r = Sum.inl v ↔ X r = some v := by
    intro r
    rw [← hc r]
    exact (EndLabelConstruction.collapse_eq_some_iff (F := F)).symm
  have keyw : ∀ r : ℝ≥0, Y r = Sum.inl w ↔ X r = some w := by
    intro r
    rw [← hc r]
    exact (EndLabelConstruction.collapse_eq_some_iff (F := F)).symm
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun r hr => (key r).1 (h2 r hr), (keyw t).1 h3, h4, ?_⟩
    rcases h5 with h5 | h5
    · exact Or.inl h5
    · refine Or.inr fun r hr => ?_
      obtain ⟨q, hq, hqv⟩ := h5 r hr
      exact ⟨q, hq, fun hcon => hqv ((key q).2 hcon)⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun r hr => (key r).2 (h2 r hr), (keyw t).2 h3, h4, ?_⟩
    rcases h5 with h5 | h5
    · exact Or.inl h5
    · refine Or.inr fun r hr => ?_
      obtain ⟨q, hq, hqv⟩ := h5 r hr
      exact ⟨q, hq, fun hcon => hqv ((key q).1 hcon)⟩

end HoldingIntervals

/-! ## The three lift clauses are stable under a homeomorphic time change -/

section TimeChange

variable {V : Type*}

/-- End labelling is stable under precomposition with a homeomorphism of
`[0,∞)`: the defining neighbourhood condition is pulled back along the
continuous reparametrisation. -/
theorem isEndLabeling_comp_homeomorph {F : IndexedCells V} (h : ℝ≥0 ≃ₜ ℝ≥0)
    {Y : ℝ≥0 → State F} (hY : IsEndLabeling F Y) :
    IsEndLabeling F (fun t => Y (h t)) := by
  intro t ε hε K
  exact (h.continuous.tendsto t).eventually (hY (h t) ε hε K)

/-- Avoidance of spatial infinity is a pointwise condition on the range of the
path, so it is stable under any reparametrisation. -/
theorem avoidsSpatialInfinity_comp {F : IndexedCells V} (h : ℝ≥0 → ℝ≥0)
    {Y : ℝ≥0 → State F} (hY : AvoidsSpatialInfinity F Y) :
    AvoidsSpatialInfinity F (fun t => Y (h t)) :=
  fun t ε hε => hY (h t) ε hε

open Classical in
/-- A pathwise choice of the homeomorphism realising a homeomorphic time change,
junk (the identity) where no such time change exists.  Only the almost-sure
behaviour is ever used, so the junk value is harmless. -/
noncomputable def timeChangeHomeo (X Y : ℝ≥0 → Option V) : ℝ≥0 ≃ₜ ℝ≥0 :=
  if h : IsHomeomorphicTimeChange X Y then h.choose else Homeomorph.refl ℝ≥0

theorem timeChangeHomeo_apply {X Y : ℝ≥0 → Option V}
    (h : IsHomeomorphicTimeChange X Y) (t : ℝ≥0) :
    X t = Y (timeChangeHomeo X Y t) := by
  have hd : timeChangeHomeo X Y = h.choose := by
    rw [timeChangeHomeo]
    exact dif_pos h
  rw [hd]
  exact h.choose_spec.2.2 t

end TimeChange

/-! ## The exact lift, built from the exponential lift and the time change -/

section ExactLift

variable {V : Type*}

/-- The exact-holding lift: the exponential lift read along the pathwise time
change of clause (8) of `InvarianceAssembly.PathwiseClockClauses`.  No
measurability is required of it, and none is asserted. -/
noncomputable def exactLift (F : IndexedCells V) (D : F.graph.Exhaustion)
    (Xexp : ℝ≥0 → Existence.Sample V → State F) (t : ℝ≥0)
    (ω : Existence.Sample V) : State F :=
  Xexp (timeChangeHomeo (fun r => exactAreaPath F D r ω)
    (fun r => exponentialAreaPath F D r ω) t) ω

/-- **Clauses 2, 4, 6 of `PathwiseClockClauses` for the exact lift**, pathwise:
from clauses 1, 3, 5 for the exponential lift together with clause 8. -/
theorem exactLift_clauses (F : IndexedCells V) (D : F.graph.Exhaustion)
    (Xexp : ℝ≥0 → Existence.Sample V → State F) (ω : Existence.Sample V)
    (hexp : (∀ t, collapse (Xexp t ω) = exponentialAreaPath F D t ω) ∧
      IsEndLabeling F (fun t => Xexp t ω) ∧
      AvoidsSpatialInfinity F (fun t => Xexp t ω))
    (htc : IsHomeomorphicTimeChange (fun t => exactAreaPath F D t ω)
      (fun t => exponentialAreaPath F D t ω)) :
    (∀ t, collapse (exactLift F D Xexp t ω) = exactAreaPath F D t ω) ∧
      IsEndLabeling F (fun t => exactLift F D Xexp t ω) ∧
      AvoidsSpatialInfinity F (fun t => exactLift F D Xexp t ω) := by
  obtain ⟨hcol, hlab, havo⟩ := hexp
  refine ⟨fun t => ?_, isEndLabeling_comp_homeomorph _ hlab,
    avoidsSpatialInfinity_comp _ havo⟩
  rw [exactLift, hcol]
  exact (timeChangeHomeo_apply htc t).symm

end ExactLift

/-! ## The pathwise assembly at one environment and one start -/

/-- **`PathwiseClockClauses` from the three checked exponential-lift clauses and
the four atomic inputs**, for one environment, one exhaustion and one start.

Only clauses 7, 8, 9 and 10 are hypotheses about the process here: clauses 1, 3,
5 come in as `hexp` (discharged unconditionally downstream) and clauses 2, 4, 6
are constructed from `hexact`. -/
theorem pathwiseClockClauses_of_atomic_inputs (e : Env)
    [hnt : Nontrivial (Vertex e.val)] (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (Φ : CellField)
    (start : Vertex e.val)
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
      AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω))
    (hfast : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
        (fun t => canonicalFastPath (decode e) D hG t ω))
    (hexact : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
        (fun t => exponentialAreaPath (decode e) D t ω))
    (hhold : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ∀ v w s t, IsCollapsedHoldingInterval (decode e)
          (fun r => exactAreaPath (decode e) D r ω) v w s t →
        (t : ℝ) - s = areaHoldingLength (decode e) v)
    (hreg : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      RegularSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω)
        (fun t => M t ω)) :
    PathwiseClockClauses e D hG Φ start Xexp
      (exactLift (decode e) D Xexp) M := by
  filter_upwards [hexp, hfast, hexact, hhold, hreg] with ω h135 hf hx hh hr
  obtain ⟨hcol2, hlab2, havo2⟩ := exactLift_clauses (decode e) D Xexp ω h135 hx
  refine ⟨h135.1, hcol2, h135.2.1, hlab2, h135.2.2, havo2, hf, hx, ?_, hr⟩
  intro v w s t hI
  exact hh v w s t
    ((isHoldingInterval_iff_isCollapsedHoldingInterval hcol2 v w s t).1 hI)

/-! ## The `hlift` input, reduced to four atomic inputs -/

/-- **The `hlift` input of the invariance assembly, from four atomic inputs.**

The three clauses of the end-labelled exponential lift are discharged here from
the main theorem's own environment hypotheses `hmt` and `hFE`; the exact lift and
its three clauses are constructed from `hexact`.  The four hypotheses `hfast`,
`hexact`, `hhold`, `hreg` are open, and nothing here certifies any of them. -/
theorem ae_hlift_of_atomic_inputs (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hfast : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
              (fun t => canonicalFastPath (decode e) D hG t ω))
    (hexact : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
              (fun t => exponentialAreaPath (decode e) D t ω))
    (hhold : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            ∀ v w s t, IsCollapsedHoldingInterval (decode e)
                (fun r => exactAreaPath (decode e) D r ω) v w s t →
              (t : ℝ) - s = areaHoldingLength (decode e) v)
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
                  (fun t => Xexp t ω) (fun t => M t ω)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M := by
  intro n
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [ExponentialAreaEndLift.ae_exists_expLift_of_massTransport ν hmt hFE.ne
      hMax lexMinField isCellRepresentative_lexMinField n,
    hfast n, hexact n, hhold n, hreg n] with e h135 hf hx hh hr
  intro hn hnt D hG hdat
  letI := hnt
  obtain ⟨Xexp, hXexp⟩ := h135 hn hnt D hG hdat
  obtain ⟨M, hM⟩ := hr hn hnt D hG hdat Xexp hXexp
  exact ⟨Xexp, exactLift (decode e) D Xexp, M,
    pathwiseClockClauses_of_atomic_inputs e D hG Φ ⟨n, hn⟩ Xexp M hXexp
      (hf hn hnt D hG hdat) (hx hn hnt D hG hdat) (hh hn hnt D hG hdat) hM⟩

end ReflectedGMS.PathwiseClockClauseLift
