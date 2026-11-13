/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.LocalizedBracketOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CanonicalBracketClauses
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalNondegeneracy

/-!
# The occupation-identification clause from *local* data only

`Limit/CanonicalBracketClauses` reduces the `hbracket` input of the invariance
assembly to five atomic clauses, of which the only one the checked corpus does
not supply is
`CanonicalBracketClauses.BracketOccupationIdentification e D hG Φ start` — the
a.e. identity, at *every* time, between the canonical predictable occupation
`ReflectedGMS.polarizedJumpOccupation` and the manuscript's ordinary-edge
bracket integral `MartingaleIngredients.ordinaryEdgeBracket` of
`p:eq:fastPhibracket`.

This module proves that clause from hypotheses that are **satisfiable at the
canonical data** `Code.decode e`.

## What was wrong with the existing route, and what replaces it

The checked producer of the same identity,
`ReflectedGMS.polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket`, carries

* `hmsum : Summable m` with `m = StatementIngredients.cellArea cells`, and
* `hi hj : cells.graph.HasFiniteEnergy fun v ↦ Φ v i`,

and **both are false at `cells = Code.decode e`**: clause five of
`Environment.Geometry` (supplied unconditionally by `Code.decode_geometry`)
forces `(⋃ v, cell v) = Set.univ`, so countably many compact cells cover the
plane and `∑' v, cellArea v = ∞`; and `HasFiniteEnergy` is *total* Dirichlet
energy over the infinite vertex set, whereas `IsHarmonicCoordinate` only asks
for a finite specific energy, a rooted density.  A theorem with those
hypotheses is vacuous at the only data anyone wants to instantiate it with.

Tracing where the two hypotheses are actually consumed shows that they are used
for exactly **one** purpose.  In
`ReflectedGMS.adaptedJumpOccupation_ae_eq_all_continuous_monotone` they enter
only through `ReflectedGMS.stationaryJumpOccupation_lt_top_ae`, i.e. only to
produce the pathwise finiteness

```
  ∀ᵐ ω, ∀ t, stationaryJumpOccupation PF G m u t ω < ∞ ,
```

and in `ReflectedGMS.polarized_vertexCarreDuChamp_eq_tsum` they enter only
through `ReflectedGMS.summable_vertexCarreDuChamp_row`, i.e. only to make the
**single conductance row at one vertex** summable.  Both consumers are replaced
here:

* the row summability is *proved outright* from finite degree,
  `(G.toSimpleGraph.neighborSet x).Finite`, which is clause seven of
  `Environment.Geometry` and therefore free at `Code.decode e`
  (`summable_vertexCarreDuChamp_row_of_finite_neighborSet`);
* the pathwise finiteness of the occupation is carried as the single named
  input `CanonicalOccupationLocallyFinite`.

The result, `bracketOccupationIdentification_of_canonicalOccupationLocallyFinite`,
therefore uses **no** `Summable` and **no** `HasFiniteEnergy` hypothesis
anywhere.

## THIS IS AN HONESTLY CONDITIONAL RESULT

Nothing below certifies `CanonicalOccupationLocallyFinite`, `hbracket`,
`p:thm:areaclt` or either main theorem.  What is claimed is only that the
occupation clause follows from local finiteness of the ordinary-edge occupation
along the path.

### Why the single remaining input IS satisfiable at `Code.decode e`

`CanonicalOccupationLocallyFinite` says that, almost surely and at every finite
horizon, `∫₀ᵗ Γ(Y_r) dr < ∞` for the ordinary-edge rate `Γ` of each coordinate.
Unlike `Summable (cellArea …)` and `HasFiniteEnergy`, this is a **local,
pathwise** statement, and it is exactly what the manuscript's own localization
gives:

* at a single vertex, `stateVertexCarreDuChamp G m u (some x)` is a *finite*
  real number for every coordinate, because `Geometry` gives finite degree and
  hence a finitely supported conductance row — no global energy is involved;
* the collapsed end state contributes nothing, `stateVertexCarreDuChamp … none
  = 0`, so reflection times carry no occupation;
* on `[0, t]` a non-exploding path meets only finitely many vertices, so the
  integral is bounded by `t` times a maximum over a finite vertex set.

So the input is a non-explosion/localization statement about the constructed
area-clock path, in the same family as `Process/LocalAreaSummability` (the
strongest *true* area bound: local, not total) and the level-zero clock
finiteness of `Recurrence/AreaClockLevelZeroFiniteness`.  It is emphatically
*not* a disguised global summability hypothesis, and it is not contradicted by
plane coverage.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal

namespace ReflectedGMS.LocalizedBracketOccupation

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open MartingaleIngredients StatementIngredients

/-! ## Part 1: the pointwise density identity from finite degree -/

section General

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- **Row summability of the square-increment rate from finite degree alone.**

`ReflectedGMS.summable_vertexCarreDuChamp_row` derives the same conclusion from
total finite Dirichlet energy, which is false for the manuscript's harmonic
coordinate on an infinite environment.  Finite degree is clause seven of
`Environment.Geometry` and is therefore free at `Code.decode e`. -/
theorem summable_vertexCarreDuChamp_row_of_finite_neighborSet
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) {x : V}
    (hx : (G.toSimpleGraph.neighborSet x).Finite) :
    Summable (fun y : V ↦ (G.c x y / m x) * (u y - u x) ^ 2) := by
  classical
  refine summable_of_ne_finset_zero (s := hx.toFinset) fun y hy ↦ ?_
  have hnadj : ¬ G.toSimpleGraph.Adj x y := fun hadj ↦
    hy (hx.mem_toFinset.mpr ((SimpleGraph.mem_neighborSet _ _ _).mpr hadj))
  have h1 : ¬ (0 < G.c x y) := fun hpos ↦ hnadj (G.toSimpleGraph_adj.mpr hpos)
  have h0 : G.c x y = 0 := le_antisymm (not_lt.mp h1) (G.c_nonneg x y)
  simp [h0]

/-- **Polarization of the ordinary-edge carré du champ from finite degree.**

This is `ReflectedGMS.polarized_vertexCarreDuChamp_eq_tsum` with its two
`HasFiniteEnergy` hypotheses replaced by finite degree at the single vertex `x`.
The proof is the same three-row polarization; only the source of the row
summability changes. -/
theorem polarized_vertexCarreDuChamp_eq_tsum_of_finite_neighborSet
    (G : ConductanceGraph V) (m : V → ℝ) (u w : V → ℝ) {x : V}
    (hx : (G.toSimpleGraph.neighborSet x).Finite) :
    (vertexCarreDuChamp G m (u + w) x - vertexCarreDuChamp G m u x -
        vertexCarreDuChamp G m w x) / 2 =
      (m x)⁻¹ * ∑' y : V, G.c x y * (u y - u x) * (w y - w x) := by
  have hP := summable_vertexCarreDuChamp_row_of_finite_neighborSet G m (u + w) hx
  have hA := summable_vertexCarreDuChamp_row_of_finite_neighborSet G m u hx
  have hB := summable_vertexCarreDuChamp_row_of_finite_neighborSet G m w hx
  have hkey : ∀ y : V, (m x)⁻¹ * (G.c x y * (u y - u x) * (w y - w x)) =
      ((G.c x y / m x) * ((u + w) y - (u + w) x) ^ 2 -
          (G.c x y / m x) * (u y - u x) ^ 2 -
          (G.c x y / m x) * (w y - w x) ^ 2) / 2 := by
    intro y
    simp only [Pi.add_apply]
    ring
  rw [← tsum_mul_left, tsum_congr hkey, tsum_div_const,
    Summable.tsum_sub (hP.sub hA) hB, Summable.tsum_sub hP hA]
  rfl

/-- **The canonical polarized rate is the manuscript's `bracketDensity`, from
finite degree.**

Same conclusion as
`ReflectedGMS.polarizedStateVertexCarreDuChamp_eq_stateBracketDensity`, with the
two `HasFiniteEnergy` hypotheses removed.  The value at a collapsed end state is
`0`: that is the manuscript's `1_{Y_r ∈ V}` factor, so no reflection time
carries any bracket density. -/
theorem polarizedStateVertexCarreDuChamp_eq_stateBracketDensity_of_finite_neighborSet
    {G : ConductanceGraph V} {m : V → ℝ} (hm : ∀ x, 0 < m x)
    (cells : IndexedCells V) (Φ : V → Plane)
    (hgraph : cells.graph = G) (harea : ∀ x, cellArea cells x = m x)
    (hdeg : ∀ x : V, (G.toSimpleGraph.neighborSet x).Finite)
    (i j : Fin 2) (q : Option V) :
    polarizedStateVertexCarreDuChamp G m (fun v ↦ Φ v i) (fun v ↦ Φ v j) q =
      stateBracketDensity cells Φ q i j := by
  subst hgraph
  cases q with
  | none =>
    simp [polarizedStateVertexCarreDuChamp, stateVertexCarreDuChamp]
  | some x =>
    have hnonneg : ∀ f : V → ℝ, 0 ≤ vertexCarreDuChamp cells.graph m f x :=
      fun f ↦ vertexCarreDuChamp_nonneg cells.graph m hm f x
    simp only [polarizedStateVertexCarreDuChamp, stateVertexCarreDuChamp,
      ENNReal.toReal_ofReal (hnonneg _), stateBracketDensity_some,
      bracketDensity]
    rw [polarized_vertexCarreDuChamp_eq_tsum_of_finite_neighborSet cells.graph m
      (fun v ↦ Φ v i) (fun v ↦ Φ v j) (hdeg x), harea x]

/-! ## Part 2: the occupation-density identity from pathwise finiteness -/

/-- **The adapted occupation is the time integral of the rate, from pathwise
finiteness of the occupation alone.**

This is `ReflectedGMS.adaptedJumpOccupation_ae_eq_all_continuous_monotone` with
`Summable m` and `HasFiniteEnergy u` replaced by the *conclusion they were only
ever used to produce*, namely `hfinite`.  Inspecting that proof shows the two
hypotheses enter through `ReflectedGMS.stationaryJumpOccupation_lt_top_ae` and
nowhere else; the version identification
`adaptedJumpOccupation_eq_stationary_of_rightRegular` and the raw-integral
identity `stationaryJumpOccupation_toReal_eq_rawIntegral` are unconditional.

The integrability clause is recorded here because the polarization step below
needs it, and it is exactly `hfinite` transported through `ENNReal.toReal`. -/
theorem adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (u : V → ℝ) (z : V)
    (hfinite : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m u t ω < ∞) :
    ∀ᵐ ω ∂PF.P z,
      (∀ t : ℝ≥0, IntegrableOn (fun r : ℝ ↦
          (stateVertexCarreDuChamp G m u
            (PF.X (Real.toNNReal r) ω)).toReal) (Icc 0 (t : ℝ))) ∧
      ∀ t : ℝ≥0, adaptedJumpOccupation PF G m u t ω =
        ∫ r : ℝ in Icc 0 (t : ℝ),
          (stateVertexCarreDuChamp G m u
            (PF.X (Real.toNNReal r) ω)).toReal := by
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
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦
        dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  have hgamma : Measurable (fun r : ℝ ↦
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) :=
    (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · apply integrable_toReal_of_lintegral_ne_top hgamma.aemeasurable.restrict
    have heq : (∫⁻ r : ℝ in Icc 0 (t : ℝ),
        stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) =
        stationaryJumpOccupation PF G m u t ω := by
      unfold stationaryJumpOccupation
      apply lintegral_congr
      intro r
      simp only [dyadicVertexCarreDuChamp,
        dyadicLimit_eq_of_rightRegular hreg]
    rw [heq]
    exact (hfin t).ne
  · rw [adaptedJumpOccupation_eq_stationary_of_rightRegular PF G m u t ω hreg
      (fun n ↦ hver n t)]
    exact stationaryJumpOccupation_toReal_eq_rawIntegral PF G m u t ω hreg

/-- **The occupation identification of `p:eq:fastPhibracket`, with no global
summability and no finite-energy hypothesis.**

CONDITIONAL on `hfinI`, `hfinJ`, `hfinIJ`; nothing here certifies them.

This is `ReflectedGMS.polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket` with
`hmsum : Summable m` and `hi hj : HasFiniteEnergy …` — both false at
`Code.decode e` — replaced by finite degree (free at `Code.decode e`) together
with pathwise local finiteness of the occupation.  Graph connectedness is not
needed either: it was used only inside `stationaryJumpOccupation_lt_top_ae`. -/
theorem polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket_of_ae_occupation_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x ↦ G.pi x / m x) hmin PF)
    (hm : ∀ x, 0 < m x)
    (cells : IndexedCells V) (Φ : V → Plane)
    (hgraph : cells.graph = G) (harea : ∀ x, cellArea cells x = m x)
    (hdeg : ∀ x : V, (G.toSimpleGraph.neighborSet x).Finite)
    (i j : Fin 2) (z : V)
    (hfinI : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m (fun v ↦ Φ v i) t ω < ∞)
    (hfinJ : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m (fun v ↦ Φ v j) t ω < ∞)
    (hfinIJ : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      stationaryJumpOccupation PF G m
        ((fun v ↦ Φ v i) + (fun v ↦ Φ v j)) t ω < ∞) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      polarizedJumpOccupation PF G m (fun v ↦ Φ v i) (fun v ↦ Φ v j) t ω =
        ordinaryEdgeBracket cells Φ PF.X i j t ω := by
  filter_upwards
    [adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      (fun v ↦ Φ v i) z hfinI,
     adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      (fun v ↦ Φ v j) z hfinJ,
     adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top h
      ((fun v ↦ Φ v i) + (fun v ↦ Φ v j)) z hfinIJ] with ω hU hV hUV
  intro t
  have hiU := hU.1 t
  have hiV := hV.1 t
  have hiUV := hUV.1 t
  have hsplitU := integral_sub (μ := volume.restrict (Icc 0 (t : ℝ))) hiUV hiU
  have hsplitV := integral_sub (μ := volume.restrict (Icc 0 (t : ℝ)))
    (hiUV.sub hiU) hiV
  simp only [Pi.sub_apply] at hsplitV
  have hpol : polarizedJumpOccupation PF G m
      (fun v ↦ Φ v i) (fun v ↦ Φ v j) t ω =
      ∫ r : ℝ in Icc 0 (t : ℝ),
        polarizedStateVertexCarreDuChamp G m (fun v ↦ Φ v i) (fun v ↦ Φ v j)
          (PF.X (Real.toNNReal r) ω) := by
    have hunfold : polarizedJumpOccupation PF G m
          (fun v ↦ Φ v i) (fun v ↦ Φ v j) t ω =
        (adaptedJumpOccupation PF G m
              ((fun v ↦ Φ v i) + (fun v ↦ Φ v j)) t ω -
            adaptedJumpOccupation PF G m (fun v ↦ Φ v i) t ω -
            adaptedJumpOccupation PF G m (fun v ↦ Φ v j) t ω) / 2 := rfl
    rw [hunfold, hUV.2 t, hU.2 t, hV.2 t]
    calc
      ((∫ r : ℝ in Icc 0 (t : ℝ),
            (stateVertexCarreDuChamp G m ((fun v ↦ Φ v i) + (fun v ↦ Φ v j))
              (PF.X (Real.toNNReal r) ω)).toReal) -
          (∫ r : ℝ in Icc 0 (t : ℝ),
            (stateVertexCarreDuChamp G m (fun v ↦ Φ v i)
              (PF.X (Real.toNNReal r) ω)).toReal) -
          (∫ r : ℝ in Icc 0 (t : ℝ),
            (stateVertexCarreDuChamp G m (fun v ↦ Φ v j)
              (PF.X (Real.toNNReal r) ω)).toReal)) / 2 =
          (∫ r : ℝ in Icc 0 (t : ℝ),
            ((stateVertexCarreDuChamp G m ((fun v ↦ Φ v i) + (fun v ↦ Φ v j))
                (PF.X (Real.toNNReal r) ω)).toReal -
              (stateVertexCarreDuChamp G m (fun v ↦ Φ v i)
                (PF.X (Real.toNNReal r) ω)).toReal -
              (stateVertexCarreDuChamp G m (fun v ↦ Φ v j)
                (PF.X (Real.toNNReal r) ω)).toReal)) / 2 := by
        rw [hsplitV, hsplitU]
      _ = ∫ r : ℝ in Icc 0 (t : ℝ),
            (((stateVertexCarreDuChamp G m
                  ((fun v ↦ Φ v i) + (fun v ↦ Φ v j))
                  (PF.X (Real.toNNReal r) ω)).toReal -
              (stateVertexCarreDuChamp G m (fun v ↦ Φ v i)
                (PF.X (Real.toNNReal r) ω)).toReal -
              (stateVertexCarreDuChamp G m (fun v ↦ Φ v j)
                (PF.X (Real.toNNReal r) ω)).toReal) / 2) := by
        rw [integral_div]
      _ = ∫ r : ℝ in Icc 0 (t : ℝ),
            polarizedStateVertexCarreDuChamp G m
              (fun v ↦ Φ v i) (fun v ↦ Φ v j)
              (PF.X (Real.toNNReal r) ω) := by
        rfl
  have hfun : (fun r : ℝ ↦ polarizedStateVertexCarreDuChamp G m
        (fun v ↦ Φ v i) (fun v ↦ Φ v j) (PF.X (Real.toNNReal r) ω)) =
      fun r : ℝ ↦ stateBracketDensity cells Φ
        (PF.X (Real.toNNReal r) ω) i j := by
    funext r
    exact polarizedStateVertexCarreDuChamp_eq_stateBracketDensity_of_finite_neighborSet
      hm cells Φ hgraph harea hdeg i j _
  rw [hpol, hfun, ordinaryEdgeBracket,
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc]

end General

/-! ## Part 3: the canonical data -/

section Canonical

open Code EnvironmentFields AreaClocks QuenchedFormulation

/-- **The single remaining input: local finiteness of the ordinary-edge
occupation along the canonical area-clock path.**

Almost surely, and simultaneously at every finite horizon, the integrated
ordinary-edge rate of each coordinate — and of each coordinate sum, which is
what the polarization consumes — is finite.

This is a *pathwise, local* statement.  It contains no summability of the cell
areas and no total Dirichlet energy, and it is not contradicted by the
plane-covering clause of `Environment.Geometry`; see the module docstring for
why `Code.decode e` can satisfy it. -/
def CanonicalOccupationLocallyFinite (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val) : Prop :=
  (∀ i : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      stationaryJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        (fun v ↦ Φ.at e v i) t ω < ∞) ∧
  (∀ i j : Fin 2, ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      stationaryJumpOccupation
        (Existence.processFamily D hG (areaRate (decode e)))
        (decode e).graph (cellArea (decode e))
        ((fun v ↦ Φ.at e v i) + (fun v ↦ Φ.at e v j)) t ω < ∞)

/-- **`BracketOccupationIdentification` at the canonical data.**

CONDITIONAL on `hocc`; nothing here certifies it.

Beyond the environment's own walk data this consumes only
`Code.decode_geometry`, which holds for *every* code: positivity of the cell
areas (clause two of `Geometry`, through `cellArea_pos`) and finite degree
(clause seven).  In particular no hypothesis of this theorem is false at
`Code.decode e`, which is what went wrong with
`Limit/ActualArrayBracketLimit.canonicalBracket_of_parts`. -/
theorem bracketOccupationIdentification_of_canonicalOccupationLocallyFinite
    (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val)
    (hdat : EnvironmentWalkData e D hG)
    (hocc : CanonicalOccupationLocallyFinite e D hG Φ start) :
    CanonicalBracketClauses.BracketOccupationIdentification e D hG Φ start := by
  obtain ⟨hmin, _hrate, hwalk, _hwalk2⟩ := hdat
  intro i j
  exact polarizedJumpOccupation_ae_eq_ordinaryEdgeBracket_of_ae_occupation_lt_top
    (G := (decode e).graph) (m := cellArea (decode e)) (hmin := hmin)
    (PF := Existence.processFamily D hG (areaRate (decode e)))
    hwalk
    (cellArea_pos (decode e) (decode_geometry e))
    (decode e) (Φ.at e) rfl (fun _ ↦ rfl)
    (decode_geometry e).2.2.2.2.2.2.1 i j start
    (hocc.1 i) (hocc.1 j) (hocc.2 i j)

end Canonical

end ReflectedGMS.LocalizedBracketOccupation
