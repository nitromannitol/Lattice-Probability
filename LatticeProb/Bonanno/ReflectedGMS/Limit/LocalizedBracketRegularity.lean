/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizedBracketRegularity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketOccupation
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly

/-!
# Clauses two and four of `OrdinaryEdgeBracketClauses`, from the *same* local input as clause three

`Limit/CanonicalBracketClauses.OrdinaryEdgeBracketClauses` lists the five atomic
clauses behind the `hbracket` input of the invariance assembly:

1. local square integrability of `M`;
2. `∀ᵐ ω`, `M` is càdlàg **and** the bracket density is interval integrable along
   the exponential area path;
3. `CanonicalBracketClauses.BracketOccupationIdentification`;
4. `∀ᵐ ω`, the bracket starts at `0`, is continuous, and has locally bounded
   variation;
5. the compensated products are local martingales.

Clause three was reduced by
`Limit/LocalizedBracketOccupation.bracketOccupationIdentification_of_canonicalOccupationLocallyFinite`
to the single pathwise input `CanonicalOccupationLocallyFinite` (plus the
environment's own `EnvironmentWalkData`).  This module closes **clauses two and
four with no further input at all**:

* the càdlàg conjunct of clause two is
  `Limit/SpatialExtensionCadlagClause.ae_isCadlag_of_pathwiseClockClauses`, which
  reads it off clause ten of `InvarianceAssembly.PathwiseClockClauses` — data the
  consumer already holds;
* the interval-integrability conjunct is the `ENNReal.toReal` transport of the
  very `IntegrableOn` statement that
  `LocalizedBracketOccupation.adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top`
  already produces from `CanonicalOccupationLocallyFinite`;
* clause four is transported along the clause-three identity from the canonical
  polarized occupation, whose three diagonal pieces are *monotone* — so bounded
  variation is free, and no absolute-continuity argument for a primitive is
  needed.

The net effect: `hbracket` now needs only clauses **one and five** beyond
`EnvironmentWalkData`, `PathwiseClockClauses` and `CanonicalOccupationLocallyFinite`.

## Why the two pieces below are the honest replacements

`Forms/PolarizedJumpOccupation.polarizedJumpOccupation_ae_zero_continuous_boundedVariation`
already proves the occupation half of clause four, but it carries
`hmsum : Summable m` and two `HasFiniteEnergy` hypotheses, and **both are false at
`cells = Code.decode e`** for the reasons recorded in the module docstrings of
`Limit/CanonicalBracketClauses` and `Limit/LocalizedBracketOccupation` (the coded
cells cover the plane, so their areas are never summable; the harmonic coordinate
has finite *specific*, not total, energy).  Tracing the consumers shows that both
enter only through `ReflectedGMS.stationaryJumpOccupation_lt_top_ae`, i.e. only to
produce pathwise finiteness of the occupation — exactly the content of
`CanonicalOccupationLocallyFinite`.  So the replacement below is the same
pattern as `LocalizedBracketOccupation.adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top`:
substitute the conclusion those hypotheses were only ever used to produce.
`ReflectedGMS.adaptedJumpOccupation_eq_stationary_of_rightRegular`,
`ReflectedGMS.continuous_stationaryJumpOccupation_toReal` and
`ReflectedGMS.stationaryJumpOccupation_mono` are unconditional.

## THIS IS AN HONESTLY CONDITIONAL RESULT

Nothing below certifies `CanonicalOccupationLocallyFinite`, `PathwiseClockClauses`,
the two remaining clauses, `hbracket`, `p:thm:areaclt` or either main theorem.
No hypothesis introduced here is new: every input of the final weld is either an
input of the already-recorded clause-three producer, or an input the consumer
`CanonicalBracketClauses.hbracket_of_ae_ordinaryEdgeBracketClauses` already hands
to its clause-list producer, or one of clauses one and five verbatim.
-/

-- Merged from `ReflectedGMS/Limit/SpatialExtensionCadlagClause.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SpatialExtensionCadlagClause

/-!
# The càdlàg half of clause two of `OrdinaryEdgeBracketClauses`

`Limit/CanonicalBracketClauses.OrdinaryEdgeBracketClauses` lists five atomic
clauses behind the `hbracket` input of the invariance assembly.  Its second
clause is the conjunction

```
∀ᵐ ω, IsCadlag (fun t ↦ M t ω) ∧ ∀ i j t, IntervalIntegrable (bracket density) …
```

The first conjunct is **already supplied** by the `hlift` input of the same
assembly and needs no new hypothesis: clause ten of
`InvarianceAssembly.PathwiseClockClauses` pins `M` as a
`InvarianceMainStatement.RegularSpatialExtension` of `Φ` along the lifted
exponential path, and `Process/SpatialEnds.IsSpatialExtension` has `IsCadlag`
as its *first* field.  The corpus had the fact but no named lemma; this module
packages it.

Nothing here certifies `hbracket`, `hlift`, `p:thm:areaclt` or either main
theorem: the statement is an implication whose hypothesis is the open input
`PathwiseClockClauses`.  No new hypothesis is introduced — the càdlàg clause is
*free* relative to the clause list's own ambient data.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Function
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.SpatialExtensionCadlagClause

open Code EnvironmentFields
open StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly

/-- **A regular spatial extension is càdlàg.**  This is the first field of the
first component of `InvarianceMainStatement.RegularSpatialExtension`, namely the
`IsCadlag` field of `SpatialEnds.IsSpatialExtension`. -/
theorem isCadlag_of_regularSpatialExtension {V : Type*}
    {F : IndexedCells V} {z : V → Plane} {X : ℝ≥0 → State F} {Z : ℝ≥0 → Plane}
    (h : RegularSpatialExtension F z X Z) : IsCadlag Z :=
  h.1.1

/-- **The càdlàg conjunct of clause two of `OrdinaryEdgeBracketClauses`, from
the pathwise clock clauses alone.**

CONDITIONAL on `hpcc`; nothing here certifies it.  `hpcc` is exactly the
hypothesis that `CanonicalBracketClauses.hbracket_of_ae_ordinaryEdgeBracketClauses`
already hands to a producer of the clause list, so this conjunct costs the
consumer nothing beyond what it already has. -/
theorem ae_isCadlag_of_pathwiseClockClauses (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), IsCadlag (fun t => M t ω) := by
  filter_upwards [hpcc] with ω hω
  obtain ⟨-, -, -, -, -, -, -, -, -, hreg⟩ := hω
  exact isCadlag_of_regularSpatialExtension hreg

end ReflectedGMS.SpatialExtensionCadlagClause

end Merged_SpatialExtensionCadlagClause

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal

namespace ReflectedGMS.LocalizedBracketRegularity

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open MartingaleIngredients StatementIngredients
open SquareCovariationPolarization
open ReflectedGMS.LocalizedBracketOccupation

/-! ## Part 1: pathwise regularity of the canonical occupations -/

section General

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- **The diagonal occupation starts at zero, is continuous, and has bounded
variation on every finite horizon — from pathwise finiteness alone.**

This is `ReflectedGMS.adaptedJumpOccupation_ae_zero_continuous_boundedVariation`
with `Summable m` and `HasFiniteEnergy u` replaced by the conclusion they were
only ever used to produce, namely `hfinite`.  Connectedness of the graph is not
needed either: it was used only inside
`ReflectedGMS.stationaryJumpOccupation_lt_top_ae`. -/
theorem adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (u : V → ℝ) (z : V)
    (hfinite : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m u t ω < ∞) :
    ∀ᵐ ω ∂PF.P z,
      adaptedJumpOccupation PF G m u 0 ω = 0 ∧
      Continuous (fun t ↦ adaptedJumpOccupation PF G m u t ω) ∧
      ∀ T : ℝ≥0, BoundedVariationOn
        (fun t ↦ adaptedJumpOccupation PF G m u t ω) (Icc 0 T) := by
  have hversions : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ, ∀ t : ℝ≥0,
      boundedStateOccupationVersion PF
          (truncatedStateVertexCarreDuChamp G m u n) t ω =
        ∫ r : ℝ in Icc 0 (t : ℝ),
          truncatedStateVertexCarreDuChamp G m u n
            (PF.X (Real.toNNReal r) ω) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
        h (truncatedStateVertexCarreDuChamp G m u n)
          (C := (n : ℝ)) (fun q ↦ by
            simpa [Real.norm_eq_abs] using
              norm_truncatedStateVertexCarreDuChamp_le G m u n q) z] with ω hω
    exact hω.1
  filter_upwards [hversions, hfinite,
      ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hver hfin hreg
  have heqStationary : ∀ t : ℝ≥0,
      adaptedJumpOccupation PF G m u t ω =
        (stationaryJumpOccupation PF G m u t ω).toReal := fun t ↦
    adaptedJumpOccupation_eq_stationary_of_rightRegular
      PF G m u t ω hreg (fun n ↦ hver n t)
  have hfun : (fun t : ℝ≥0 ↦ adaptedJumpOccupation PF G m u t ω) =
      fun t ↦ (stationaryJumpOccupation PF G m u t ω).toReal :=
    funext heqStationary
  have hmono : Monotone (fun t : ℝ≥0 ↦ adaptedJumpOccupation PF G m u t ω) := by
    intro s t hst
    change adaptedJumpOccupation PF G m u s ω ≤
      adaptedJumpOccupation PF G m u t ω
    rw [heqStationary s, heqStationary t]
    exact ENNReal.toReal_mono (hfin t).ne
      (stationaryJumpOccupation_mono PF G m u ω hst)
  refine ⟨adaptedJumpOccupation_zero PF G m u ω, ?_, ?_⟩
  · rw [hfun]
    exact continuous_stationaryJumpOccupation_toReal PF G m u ω hreg hfin
  · intro T
    have hloc := hmono.monotoneOn (univ : Set ℝ≥0) |>.locallyBoundedVariationOn
    simpa using hloc (a := (0 : ℝ≥0)) (b := T) (mem_univ _) (mem_univ _)

/-- **The polarized occupation starts at zero, is continuous, and has bounded
variation on every finite horizon — from pathwise finiteness alone.**

This is `ReflectedGMS.polarizedJumpOccupation_ae_zero_continuous_boundedVariation`
with its `Summable` and `HasFiniteEnergy` hypotheses removed; the polarization
step is the same three-term algebra. -/
theorem polarizedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (u w : V → ℝ) (z : V)
    (hfinU : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m u t ω < ∞)
    (hfinW : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m w t ω < ∞)
    (hfinUW : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m (u + w) t ω < ∞) :
    ∀ᵐ ω ∂PF.P z,
      polarizedJumpOccupation PF G m u w 0 ω = 0 ∧
      Continuous (fun t ↦ polarizedJumpOccupation PF G m u w t ω) ∧
      ∀ T : ℝ≥0, BoundedVariationOn
        (fun t ↦ polarizedJumpOccupation PF G m u w t ω) (Icc 0 T) := by
  filter_upwards
    [adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      h u z hfinU,
     adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      h w z hfinW,
     adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      h (u + w) z hfinUW] with ω hU hW hUW
  refine ⟨polarizedJumpOccupation_zero PF G m u w ω, ?_, ?_⟩
  · convert ((hUW.2.1.sub hU.2.1).sub hW.2.1).const_smul (1 / 2 : ℝ) using 1 <;>
      funext t <;>
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        polarizedJumpOccupation, polarizedCompensator] <;> ring
  · intro T
    have hBV := boundedVariationOn_const_smul (1 / 2 : ℝ)
      (boundedVariationOn_add
        (boundedVariationOn_add (hUW.2.2 T)
          (boundedVariationOn_const_smul (-1) (hU.2.2 T)))
        (boundedVariationOn_const_smul (-1) (hW.2.2 T)))
    convert hBV using 1 <;> funext t <;>
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        polarizedJumpOccupation, polarizedCompensator] <;> ring

/-! ## Part 2: interval integrability of the bracket density -/

/-- **Interval integrability of the manuscript's bracket density along the path,
from pathwise finiteness of the occupation alone.**

This is the second conjunct of clause two of
`CanonicalBracketClauses.OrdinaryEdgeBracketClauses`, in general form.  The three
`IntegrableOn` statements come from
`LocalizedBracketOccupation.adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top`,
and the density is their polarization by
`LocalizedBracketOccupation.polarizedStateVertexCarreDuChamp_eq_stateBracketDensity_of_finite_neighborSet`,
whose only geometric input is finite degree — clause seven of
`Environment.Geometry`, free at `Code.decode e`.

No `Summable` and no `HasFiniteEnergy` hypothesis is used. -/
theorem ae_intervalIntegrable_stateBracketDensity_of_ae_occupation_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x ↦ G.pi x / m x) hmin PF)
    (hm : ∀ x, 0 < m x)
    (cells : IndexedCells V) (Φ : V → Plane)
    (hgraph : cells.graph = G) (harea : ∀ x, cellArea cells x = m x)
    (hdeg : ∀ x : V, (G.toSimpleGraph.neighborSet x).Finite)
    (i j : Fin 2) (z : V)
    (hfinI : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m (fun y ↦ Φ y i) t ω < ∞)
    (hfinJ : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m (fun y ↦ Φ y j) t ω < ∞)
    (hfinIJ : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m
        ((fun y ↦ Φ y i) + (fun y ↦ Φ y j)) t ω < ∞) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ ↦ stateBracketDensity cells Φ (PF.X (Real.toNNReal s) ω) i j)
        volume 0 (t : ℝ) := by
  filter_upwards
    [adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      (fun y ↦ Φ y i) z hfinI,
     adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      (fun y ↦ Φ y j) z hfinJ,
     adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      ((fun y ↦ Φ y i) + (fun y ↦ Φ y j)) z hfinIJ] with ω hU hW hUW
  intro t
  have hiU := hU.1 t
  have hiW := hW.1 t
  have hiUW := hUW.1 t
  have hdiv : IntegrableOn
      (fun r : ℝ ↦
        (((stateVertexCarreDuChamp G m ((fun y ↦ Φ y i) + (fun y ↦ Φ y j))
              (PF.X (Real.toNNReal r) ω)).toReal -
            (stateVertexCarreDuChamp G m (fun y ↦ Φ y i)
              (PF.X (Real.toNNReal r) ω)).toReal) -
          (stateVertexCarreDuChamp G m (fun y ↦ Φ y j)
            (PF.X (Real.toNNReal r) ω)).toReal) / 2)
      (Icc 0 (t : ℝ)) volume :=
    ((hiUW.sub hiU).sub hiW).div_const (2 : ℝ)
  have hint : IntegrableOn
      (fun r : ℝ ↦ stateBracketDensity cells Φ (PF.X (Real.toNNReal r) ω) i j)
      (Icc 0 (t : ℝ)) volume := by
    refine hdiv.congr_fun ?_ measurableSet_Icc
    intro r _
    exact polarizedStateVertexCarreDuChamp_eq_stateBracketDensity_of_finite_neighborSet
      hm cells Φ hgraph harea hdeg i j (PF.X (Real.toNNReal r) ω)
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le t.coe_nonneg]
  exact hint

end General

/-! ## Part 3: the canonical data -/

section Canonical

open Code EnvironmentFields AreaClocks QuenchedFormulation SpatialEnds
open InvarianceMainStatement
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.CanonicalBracketClauses

/-- **The interval-integrability conjunct of clause two, at the canonical data.**

CONDITIONAL on `hocc`; nothing here certifies it.  Its inputs are exactly those
of `LocalizedBracketOccupation.bracketOccupationIdentification_of_canonicalOccupationLocallyFinite`
(clause three) — no new hypothesis. -/
theorem ae_intervalIntegrable_bracketDensity_of_canonicalOccupationLocallyFinite
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (hdat : EnvironmentWalkData e D hG)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ∀ (i j : Fin 2) (t : ℝ≥0),
        IntervalIntegrable
          (fun s : ℝ ↦ stateBracketDensity (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D (Real.toNNReal s) ω) i j)
          volume 0 (t : ℝ) := by
  obtain ⟨hmin, -, hwalk, -⟩ := hdat
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  exact ae_intervalIntegrable_stateBracketDensity_of_ae_occupation_lt_top
    (G := (decode e).graph) (m := cellArea (decode e)) (hmin := hmin)
    (PF := Existence.processFamily D hG (areaRate (decode e)))
    hwalk (cellArea_pos (decode e) (decode_geometry e))
    (decode e) (Φ.at e) rfl (fun _ ↦ rfl)
    (decode_geometry e).2.2.2.2.2.2.1 i j start
    (hocc.1 i) (hocc.1 j) (hocc.2 i j)

/-- **Clause two of `OrdinaryEdgeBracketClauses`, in full.**

CONDITIONAL on `hpcc` and `hocc`; nothing here certifies either.  The càdlàg
conjunct is free from `hpcc` (clause ten of `PathwiseClockClauses`), and the
integrability conjunct costs exactly the clause-three input. -/
theorem ae_isCadlag_and_intervalIntegrable_of_local_inputs
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdat : EnvironmentWalkData e D hG)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsCadlag (fun t ↦ M t ω) ∧
      ∀ (i j : Fin 2) (t : ℝ≥0),
        IntervalIntegrable
          (fun s : ℝ ↦ stateBracketDensity (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D (Real.toNNReal s) ω) i j)
          volume 0 (t : ℝ) := by
  filter_upwards
    [SpatialExtensionCadlagClause.ae_isCadlag_of_pathwiseClockClauses
      e D hG Φ start Xexp Xexact M hpcc,
     ae_intervalIntegrable_bracketDensity_of_canonicalOccupationLocallyFinite
      e D hG Φ start hdat hocc] with ω hcad hint
  exact ⟨hcad, hint⟩

/-- **Clause four of `OrdinaryEdgeBracketClauses`: the bracket starts at `0`, is
continuous, and has locally bounded variation.**

CONDITIONAL on `hocc`; nothing here certifies it.

The route is: the clause-three identity
(`LocalizedBracketOccupation.bracketOccupationIdentification_of_canonicalOccupationLocallyFinite`)
identifies the bracket, *at every time on one full-probability event*, with the
canonical polarized occupation; and that occupation is a fixed real linear
combination of three **monotone** continuous processes, so all three assertions
of clause four hold for it.  Because the identity holds at every time on a single
event, the transport is a pathwise rewriting of one function of `t`, not an
a.e.-modification argument — contrast
`Forms/HarmonicPathBracketIdentification`, where a `Locally` witness genuinely
cannot be moved across an a.e. identity. -/
theorem ae_ordinaryEdgeBracket_zero_continuous_boundedVariation_of_local_inputs
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (hdat : EnvironmentWalkData e D hG)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start) :
    ∀ i j : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j 0 ω = 0 ∧
      Continuous (fun t ↦ ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j t ω) ∧
      ∀ T : ℝ≥0, BoundedVariationOn
        (fun t ↦ ordinaryEdgeBracket (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D) i j t ω) (Icc 0 T) := by
  intro i j
  have hid := bracketOccupationIdentification_of_canonicalOccupationLocallyFinite
    e D hG Φ start hdat hocc i j
  obtain ⟨hmin, -, hwalk, -⟩ := hdat
  have hpol := polarizedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
    (G := (decode e).graph) (m := cellArea (decode e)) (hmin := hmin)
    (PF := Existence.processFamily D hG (areaRate (decode e)))
    hwalk (fun v ↦ Φ.at e v i) (fun v ↦ Φ.at e v j) start
    (hocc.1 i) (hocc.1 j) (hocc.2 i j)
  filter_upwards [hid, hpol] with ω hω hreg
  have hfun : (fun t : ℝ≥0 ↦ ordinaryEdgeBracket (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D) i j t ω) =
      fun t ↦ polarizedJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        (fun v ↦ Φ.at e v i) (fun v ↦ Φ.at e v j) t ω :=
    funext fun t ↦ (hω t).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← hω 0]
    exact hreg.1
  · rw [hfun]
    exact hreg.2.1
  · intro T
    rw [hfun]
    exact hreg.2.2 T

/-! ## Part 4: the weld -/

/-- **`OrdinaryEdgeBracketClauses` from clauses one and five, the walk data, the
pathwise clock clauses and the local occupation finiteness.**

CONDITIONAL on all five hypotheses; nothing here certifies any of them, nor
`hbracket`, nor `p:thm:areaclt`, nor either main theorem.

Three of the five clauses — two, three and four — are discharged.  `hdat` and
`hpcc` are data the consumer
`CanonicalBracketClauses.hbracket_of_ae_ordinaryEdgeBracketClauses` already hands
to a clause-list producer, so the only genuinely new input is `hocc`, which is
the single input of the clause-three producer.  `hmart` and `hcomp` are clauses
one and five verbatim. -/
theorem ordinaryEdgeBracketClauses_of_local_inputs
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdat : EnvironmentWalkData e D hG)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start)
    (hmart : IsLocallySquareIntegrableMartingale
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M)
    (hcomp : ∀ i j : Fin 2,
      IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (fun t ω ↦ M t ω i * M t ω j -
          ordinaryEdgeBracket (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D) i j t ω)) :
    OrdinaryEdgeBracketClauses e D hG Φ start M :=
  ⟨hmart,
    ae_isCadlag_and_intervalIntegrable_of_local_inputs
      e D hG Φ start Xexp Xexact M hdat hpcc hocc,
    bracketOccupationIdentification_of_canonicalOccupationLocallyFinite
      e D hG Φ start hdat hocc,
    ae_ordinaryEdgeBracket_zero_continuous_boundedVariation_of_local_inputs
      e D hG Φ start hdat hocc,
    hcomp⟩

/-- **Machine-checked weld with the clause-list consumer**: the producer above
plugs into `CanonicalBracketClauses.canonicalBracket_of_clauses` with no
adaptation. -/
example (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hdat : EnvironmentWalkData e D hG)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start)
    (hmart : IsLocallySquareIntegrableMartingale
      (areaSampleLaw (decode e) D hG start).completion
      (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M)
    (hcomp : ∀ i j : Fin 2,
      IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (fun t ω ↦ M t ω i * M t ω j -
          ordinaryEdgeBracket (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D) i j t ω)) :
    CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M :=
  canonicalBracket_of_clauses e D hG Φ start M
    (ordinaryEdgeBracketClauses_of_local_inputs
      e D hG Φ start Xexp Xexact M hdat hpcc hocc hmart hcomp)

/-- **The `hbracket` input of the invariance assembly from clauses one and five
plus the local occupation finiteness.**

CONDITIONAL on `hlocal`; this certifies neither `hlocal`, nor `hbracket`, nor
either main theorem.  The conclusion is, verbatim, the `hbracket` hypothesis of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`,
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`
and `InvarianceAssemblyFourInputs.reflectedInvarianceConclusions_of_named_inputs_data_and_clocks_discharged`.

Compared with `CanonicalBracketClauses.hbracket_of_ae_ordinaryEdgeBracketClauses`,
the càdlàg clause, the interval-integrability clause, the occupation
identification and the pathwise regularity of the bracket have all disappeared
from the hypothesis: what remains is local square integrability of `M`, the
compensated-product local-martingale clause, and the pathwise occupation
finiteness `CanonicalOccupationLocallyFinite`. -/
theorem hbracket_of_ae_local_inputs (ν : Measure Env) (Φ : CellField)
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
          IsLocallySquareIntegrableMartingale
            (areaSampleLaw (decode e) D hG start).completion
            (areaFiltration e D (areaSampleLaw (decode e) D hG start)) M ∧
          ∀ i j : Fin 2,
            IsLocalMartingale (areaSampleLaw (decode e) D hG start).completion
              (areaFiltration e D (areaSampleLaw (decode e) D hG start))
              (fun t ω ↦ M t ω i * M t ω j -
                ordinaryEdgeBracket (decode e) (Φ.at e)
                  (exponentialAreaPath (decode e) D) i j t ω)) :
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
  refine hbracket_of_ae_ordinaryEdgeBracketClauses ν Φ ?_
  filter_upwards [hlocal] with e he
  intro hnt D hG hdat start Xexp Xexact M hpcc
  have : Nontrivial (Vertex e.val) := hnt
  obtain ⟨hocc, hmart, hcomp⟩ := he hnt D hG hdat start Xexp Xexact M hpcc
  exact ordinaryEdgeBracketClauses_of_local_inputs
    e D hG Φ start Xexp Xexact M hdat hpcc hocc hmart hcomp

end Canonical

end ReflectedGMS.LocalizedBracketRegularity
