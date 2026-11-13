/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedDifferenceIncrementsFromMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.RestrictedEnergyBridge
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageDifferenceWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import Mathlib.Topology.Algebra.InfiniteSum.Real
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateSevenInputs

/-!
# `hconv` from the stage-difference weak-`L¹` maximal inequality

This module discharges `Corrector/MarkedDifferenceSubsequence.MarkedDifferenceIncrementsSummable`
— hence, through `markedDifferencesConverge_of_summable`, the input `hconv`
(`HarmonicCoordinateAssembly.MarkedDifferencesConverge`) of the harmonic-coordinate assembly —
from the *same* single open input that `Corrector/StageDifferenceWeakMaximal` uses for `hpatch`:
`MarkedStageDifferenceWeakMaximal`, the manuscript's `s:eq:maximal` at the specific-energy
density of a stage difference.

## The missing step, and what supplied it

`hpatch` needs only *energy* convergence on bounded patches, and
`StageDifferenceWeakMaximal.hasCauchyPatchEnergy_of_geometric_ballMaximal` delivers that.  `hconv`
needs the *pointwise* statement: at every pair of labels, the difference
`φ_{ms j}(H_b) − φ_{ms j}(H_a)` converges.  The classical route from energy to pointwise control
is the anchored-walk estimate, and the project has it —
`Forms/FiniteMinimizerPointwiseConvergence.abs_sub_le_walkConst_mul_restrictedEnergy` — but stated
for a **real** field and the **real** `restrictedEnergy`, whereas every patch bound in the
corrector programme is an `ℝ≥0∞`-valued `vectorEnergy` of a `Plane`-valued field.  No bridge
between the two existed anywhere in the three trees.  `Corrector/RestrictedEnergyBridge` is that
bridge; this module is its first consumer.

## The chain

1. `exists_pos_radius_walk_support_hits` — a walk has finite support and every cell is compact,
   so the union of the cells along a walk lies in a closed ball.  Consequently the walk support
   is contained in `hittingVertices F (B̄_R)` for some `R > 0`: the "walk support is bounded"
   step, and it costs nothing beyond compactness of cells.
2. `summable_norm_increments_of_geometric_ballMaximal` — the pathwise heart, at one fixed
   `IndexedCells` and with the maximal function abstracted into a bare sequence `Mf : ℕ → ℝ≥0∞`
   (the same hoisting `StageDifferenceWeakMaximal` uses; inlining `decode ω.1` into the calc
   blocks provokes `whnf` heartbeat timeouts).  `Geometry` supplies a walk between any two
   vertices, step 1 supplies the patch, `s:eq:localcontrol` bounds the patch energy by
   `(R + D_R)² · 2^{-2i}`, and the bridge turns that into
   `‖Δ_i(b) − Δ_i(a)‖ ≤ C · 2^{-i}`, which is summable.
3. `markedDifferenceIncrementsSummable_of_stageDifferenceWeakMaximal` — the marked assembly, the
   exact analogue of `markedPatchEnergyCauchy_of_stageDifferenceWeakMaximal`: Borel–Cantelli at
   the level `2^{-2j}` against the geometric rate of the subsequence, one almost-sure event for
   all labels at once (the Borel–Cantelli threshold `N` is a functional of the environment, not
   of the label pair, so the label quantifier stays *inside* the almost-sure statement without
   any further countability argument).

Note the direction of the gain: the almost-sure event does not depend on `k`, so the conclusion
is genuinely `∀ᵐ ω, ∀ k`, which is what `MarkedDifferenceIncrementsSummable` asks.

## Anti-vacuity

* Every hypothesis is realised at the actual data.  `hgeom` is produced outright by
  `Corrector/SpecificEnergyConvergence.exists_strictMono_geometric_markedStageDefect`;
  `exists_strictMono_markedDifferencesConverge_of_weakMaximal` below composes them, so hypothesis
  and conclusion are **jointly** realisable.
* `MarkedStageDifferenceWeakMaximal` is not vacuous and not a "uniform constant" trap: the
  project proves the same display with the absolute constant `512`
  (`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le`), and the constant here is merely
  existentially quantified and required finite.  See `StageDifferenceWeakMaximal`'s docstring.
* No hypothesis of the form `∀ n, markedStageEnergy ν n ≠ ∞` is used anywhere below, so the
  circular satisfiability argument flagged for `Corrector/MarkedStagePythagoras`'s `hfin` is not
  imported.  The string `markedStageEnergy` does not occur in this file.
* The walk hypothesis of the bridge is satisfiable for **every** pair of vertices, not just some:
  step 1 proves it unconditionally from compactness of cells, so the pointwise conclusion covers
  every paired label, which is exactly the quantifier `hconv` needs.
* **The join is machine-checked.**  `hconv_join_shape_check` partially applies the consumer
  `Corrector/HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs` to the
  producer of this file in the `hconv` slot (and to `StageDifferenceWeakMaximal`'s producer in the
  `hpatch` slot); if it elaborates, the shapes genuinely match.

## What is still open

`MarkedStageDifferenceWeakMaximal` itself, and `MarkedNestedProjectionBound` (only in the
satisfiability corollary, where it produces the subsequence).  This file proves no main theorem.
-/

-- Merged from `ReflectedGMS/Corrector/MarkedDifferenceSubsequence.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MarkedDifferenceSubsequence

/-!
# `MarkedDifferencesConverge` by diagonal extraction (`s:prop:limit`, pointwise half)

`HarmonicCoordinateAssembly.MarkedDifferencesConverge ν ms` is the `hconv` input of
`harmonicCoordinateConclusions_of_named_inputs`.  Unfolded, it says that for almost every
marked environment `ω` **every** paired label converges along `ms`:

  `∀ k, ∃ c, Tendsto (fun j => differenceApproximant ms j ω k) atTop (𝓝 c)`,

and on the good event `SublinearEvent` the approximant at `k = Nat.pair a b` is exactly the
manuscript's `φ_{ms j}(H_b) − φ_{ms j}(H_a)`.

## The structural point

The assembly quantifies over `ms` **universally**: `hconv` is asked of a subsequence that is
handed to it.  No producer can supply that, because the manuscript's proof of `s:prop:limit`
*constructs* the subsequence — it is the output of an energy-compactness argument, not an
input to it.  The honest target is therefore the **existential** form

  `∃ ms, StrictMono ms ∧ MarkedDifferencesConverge ν ms`,

which is what `exists_strictMono_markedDifferencesConverge` below produces.  This does **not**
match the `∀ ms` shape of `harmonicCoordinateConclusions_of_named_inputs`, and
`harmonicCoordinateConclusions_of_compactness` records exactly the adapter that is needed: a
producer of the nine remaining inputs must supply them *for whatever subsequence the
compactness argument returns*, i.e. in the `∀ ms, StrictMono ms → MarkedDifferencesConverge ν
ms → …` form, rather than for a subsequence fixed in advance.

## What is proved here and what is assumed

Proved outright (no hypothesis beyond the two named inputs below):

* `exists_strictMono_ae_limitGood` — the **diagonal extraction**.  From a labelwise
  refinement property ("every subsequence of the stages admits a further subsequence along
  which the approximants at *one* given label converge almost surely") it produces a *single*
  deterministic strictly increasing subsequence along which *every* label converges almost
  surely.  This is the nested-extraction-plus-diagonal step; it is the only place where the
  countability of the label set `ℕ` is used, through `MeasureTheory.ae_all_iff`.
* `markedDifferencesConverge_of_summable` — the quantitative route: almost-sure summability
  of the increments along a **given** `ms` gives `MarkedDifferencesConverge ν ms` for that
  same `ms`, by the Cauchy criterion and completeness of `Plane`.  Unlike the extraction, this
  one *does* match the assembly's `∀ ms` shape, so it is the cheapest honest producer whenever
  the subsequence has already been pinned down by a rate.

Assumed (named, atomic, and not certified anywhere in this file):

* `MarkedLabelSubsequentialCompactness ν` — relative sequential compactness, for almost-sure
  convergence at each single paired label, of the family of difference approximants.  Its
  intended producer is the uniform energy bound on the interpolants (the first conjunct of
  `MarkedSpecificEnergyConvergence`, i.e. `sup_m E[ρ(φ_m)] < ∞`) together with the usual
  Banach–Alaoglu/Mazur extraction and the passage from convergence in measure to almost-sure
  convergence along a subsequence.  Nothing in the checked corpus supplies it;
  `Corrector/MinimizerStrongGradientConvergence` does **not**, since its index is an
  exhaustion level of one fixed graph with one fixed boundary datum, whereas `phi F D m` are
  block interpolants at successively finer dyadic scales with the competitor class changing
  with `m`.
* `MarkedDifferenceIncrementsSummable ν ms` — the summable-increment input of the second
  route.

**This file proves no main theorem** and certifies neither named input.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ReflectedGMS

namespace MarkedDifferenceSubsequence

open Code EnvironmentFields EnvironmentLaws DyadicApproximation RootDensities
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedLimitingCoordinateMeasurability

/-! ### The abstract diagonal extraction -/

/-! ### The named inputs -/

/-- **NAMED INPUT (audited gap 1, `s:prop:limit`, quantitative form along a fixed `ms`).**
Along the *given* subsequence the increments of the difference approximants are almost surely
absolutely summable at every paired label.  This is the shape the manuscript's own proof
produces once the subsequence has been pinned down by a rate. -/
def MarkedDifferenceIncrementsSummable (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ k : ℕ,
    Summable fun j =>
      ‖differenceApproximant ms (j + 1) ω k - differenceApproximant ms j ω k‖

/-! ### The two producers -/

/-- **`hconv` along a given subsequence, from summable increments.**  Unlike the extraction,
this matches the `∀ ms` shape demanded by `harmonicCoordinateConclusions_of_named_inputs`:
the subsequence is an input on both sides.  The proof is the Cauchy criterion together with
completeness of the plane. -/
theorem markedDifferencesConverge_of_summable (ν : Measure Env) (ms : ℕ → ℕ)
    (hsum : MarkedDifferenceIncrementsSummable ν ms) : MarkedDifferencesConverge ν ms := by
  filter_upwards [hsum] with ω hω
  refine mem_limitGood_iff.2 fun k => ?_
  have hcs : CauchySeq fun j => differenceApproximant ms j ω k := by
    refine cauchySeq_of_summable_dist ?_
    refine (hω k).congr fun j => ?_
    rw [dist_eq_norm, norm_sub_rev]
  exact cauchySeq_tendsto_of_complete hcs

/-! ### The adapter the assembly needs -/

end MarkedDifferenceSubsequence

end ReflectedGMS

end Merged_MarkedDifferenceSubsequence

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.MarkedDifferenceIncrementsFromMaximal

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly

/-! ### The support of a walk is spatially bounded -/

/-- **A walk meets only a bounded region of the plane.**  Its support is a finite list of
vertices, each cell is compact, and a finite union of compact sets is compact, hence bounded.
So every vertex of the walk lies in the patch `ℍ(B̄_R)` of some radius `R > 0`.

This is the only geometric input needed to apply the anchored-walk estimate on a *patch*: no
connectivity, no diameter bound and no mass transport. -/
theorem exists_pos_radius_walk_support_hits {V : Type*} (F : IndexedCells V)
    {a b : V} (p : F.graph.toSimpleGraph.Walk a b) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ p.support,
      y ∈ hittingVertices F (Metric.closedBall (0 : Plane) R) := by
  classical
  have hcpt : IsCompact (⋃ y ∈ ((p.support.toFinset : Finset V) : Set V),
      (F.cell y : Set Plane)) :=
    (p.support.toFinset.finite_toSet).isCompact_biUnion fun y _ => (F.cell y).isCompact
  obtain ⟨r, hr⟩ := hcpt.isBounded.subset_closedBall (0 : Plane)
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right r 1), fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := (F.cell y).nonempty
  refine mem_hittingVertices.2 ⟨z, hz, ?_⟩
  have hyT : y ∈ ((p.support.toFinset : Finset V) : Set V) := by
    simpa using hy
  exact Metric.closedBall_subset_closedBall (le_max_left r 1) (hr (Set.mem_biUnion hyT hz))

/-! ### The pathwise summability -/

/-- **The pathwise heart.**  At one fixed cell family, with the maximal function abstracted into
a bare sequence `Mf`, geometric decay of the ball integrals of the successive stage-difference
densities makes the increments of *every* pairwise difference absolutely summable.

The proof: `Geometry` gives a walk from `a` to `b`; the walk support sits in a patch `ℍ(B̄_R)`
by `exists_pos_radius_walk_support_hits`; `s:eq:localcontrol`
(`Corrector/SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal`) bounds the
patch energy of the increment by `(R + D_R)² · 2^{-2i}`; and
`Corrector/RestrictedEnergyBridge.norm_sub_le_of_vectorEnergy_le` converts that patch energy
bound into the pointwise bound `C · 2^{-i}` along the walk.  Geometric, hence summable.

No measure and no good event occur: this is a statement about one `IndexedCells`. -/
theorem summable_norm_increments_of_geometric_ballMaximal
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (u : ℕ → V → Plane)
    (hdiam : ∀ R : ℝ, 0 < R → ∃ DR : ℝ, 0 ≤ DR ∧
      ∀ v ∈ hittingVertices F (Metric.closedBall (0 : Plane) R),
        Metric.diam (F.cell v : Set Plane) ≤ DR)
    (Mf : ℕ → ℝ≥0∞) (N : ℕ)
    (hMf : ∀ (i : ℕ) (s : ℝ), 0 < s →
      (∫⁻ z in Metric.closedBall (0 : Plane) s,
          rootedSpecificEnergyDensity F (fun v => u i v - u (i + 1) v) z ∂volume)
        ≤ ENNReal.ofReal (s ^ 2) * Mf i)
    (hNbd : ∀ i : ℕ, N ≤ i → Mf i ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i))
    (a b : V) :
    Summable fun i : ℕ => ‖(u (i + 1) b - u (i + 1) a) - (u i b - u i a)‖ := by
  classical
  obtain ⟨p⟩ := (hF.2.2.2.2.2.1).preconnected a b
  obtain ⟨R, hRpos, hsupp⟩ := exists_pos_radius_walk_support_hits F p
  obtain ⟨DR, hDR0, hD⟩ := hdiam R hRpos
  have hpos : (0 : ℝ) < R + DR := by linarith
  -- the patch energy of the `i`-th increment, along the geometric tail
  have hEi : ∀ i : ℕ, N ≤ i →
      vectorEnergy (restrictGraph F.graph
            (hittingVertices F (Metric.closedBall (0 : Plane) R)))
          (fun v => (fun w => u i w - u (i + 1) w) v.1)
        ≤ ENNReal.ofReal ((R + DR) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
    intro i hi
    refine le_trans (SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal
      F hF (fun w => u i w - u (i + 1) w) hpos hD (hMf i)) ?_
    gcongr
    exact hNbd i hi
  have hKtop : ∀ i : ℕ,
      ENNReal.ofReal ((R + DR) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) ≠ ∞ := fun i =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by simp))
  have hinv : ((2 : ℝ≥0∞)⁻¹).toReal = ((2 : ℝ))⁻¹ := by
    rw [ENNReal.toReal_inv]
    norm_num
  have hKreal : ∀ i : ℕ,
      (ENNReal.ofReal ((R + DR) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i)).toReal
        = (R + DR) ^ 2 * ((2 : ℝ))⁻¹ ^ (2 * i) := by
    intro i
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, hinv]
  have hsqrt : ∀ i : ℕ,
      Real.sqrt (2 * ((R + DR) ^ 2 * ((2 : ℝ))⁻¹ ^ (2 * i)))
        = Real.sqrt (2 * (R + DR) ^ 2) * ((2 : ℝ))⁻¹ ^ i := by
    intro i
    have hp : ((2 : ℝ))⁻¹ ^ (2 * i) = (((2 : ℝ))⁻¹ ^ i) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hp, show 2 * ((R + DR) ^ 2 * (((2 : ℝ))⁻¹ ^ i) ^ 2)
          = (2 * (R + DR) ^ 2) * (((2 : ℝ))⁻¹ ^ i) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the pointwise increment bound along the walk
  have hbnd : ∀ i : ℕ, N ≤ i →
      ‖(u (i + 1) b - u (i + 1) a) - (u i b - u i a)‖
        ≤ (Real.sqrt 2 * (F.graph.walkConst p * Real.sqrt (2 * (R + DR) ^ 2)))
            * ((2 : ℝ))⁻¹ ^ i := by
    intro i hi
    have hnorm := RestrictedEnergyBridge.norm_sub_le_of_vectorEnergy_le F.graph
      (fun w => u i w - u (i + 1) w) p hsupp (hKtop i) (hEi i hi)
    have hrev : (u (i + 1) b - u (i + 1) a) - (u i b - u i a)
        = -(((u i b - u (i + 1) b) - (u i a - u (i + 1) a))) := by
      abel
    rw [hrev, norm_neg]
    refine le_trans hnorm (le_of_eq ?_)
    rw [hKreal i, hsqrt i]
    ring
  -- geometric comparison
  have hgeo : Summable fun i : ℕ =>
      (Real.sqrt 2 * (F.graph.walkConst p * Real.sqrt (2 * (R + DR) ^ 2)))
        * ((2 : ℝ))⁻¹ ^ i :=
    (summable_geometric_of_abs_lt_one (by norm_num : |((2 : ℝ))⁻¹| < 1)).mul_left _
  refine (summable_nat_add_iff N).mp ?_
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => hbnd (i + N) (Nat.le_add_left N i)) ((summable_nat_add_iff N).mpr hgeo)

/-! ### `MarkedDifferenceIncrementsSummable` -/

/-- **`hconv`'s quantitative input, from the weak-`L¹` maximal inequality.**  Almost surely, at
every paired label, the increments of the marked difference approximants along the geometric
subsequence are absolutely summable.

The environment hypotheses are only `s:eq:MTP` and the finite (FE) moment: they enter through
`HarmonicCoordinateAssembly.ae_marked_geometry` (which supplies `D_R < ∞` at every radius) and
`ae_mem_sublinearEvent` (which puts the environment on the good event, where `phi` is the
canonical block interpolant and `differenceApproximant` is the manuscript's
`φ_{ms j}(H_b) − φ_{ms j}(H_a)`). -/
theorem markedDifferenceIncrementsSummable_of_stageDifferenceWeakMaximal
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν) :
    MarkedDifferenceSubsequence.MarkedDifferenceIncrementsSummable ν ms := by
  classical
  obtain ⟨C, hC, hbound⟩ := hmax
  have hBC := StageDifferenceWeakMaximal.ae_eventually_le_geometric_const (ν.prod gridLaw) hC
    (fun j (ω : MarkedEnvironment) =>
      StageDifferenceWeakMaximal.markedStageDifferenceMaximal (ms j) (ms (j + 1)) ω)
    (StageDifferenceWeakMaximal.tail_le_of_weakMaximal hbound hms hgeom)
  have hgeo := ae_marked_geometry ν hν hFE.ne (spatialMaximalBound_of_massTransport ν hν hFE)
  have hgood := ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE.ne)
  filter_upwards [hBC, hgeo, hgood] with ω hev hgeoω hGω
  intro k
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  by_cases hk : (ω.1.val.1 (Nat.unpair k).1).isSome ∧ (ω.1.val.1 (Nat.unpair k).2).isSome
  · have hpair : Nat.pair (Nat.unpair k).1 (Nat.unpair k).2 = k := Nat.pair_unpair k
    have hkey : ∀ j : ℕ, differenceApproximant ms j ω k
        = phi (decode ω.1) ω.2 (ms j) ⟨(Nat.unpair k).2, hk.2⟩
          - phi (decode ω.1) ω.2 (ms j) ⟨(Nat.unpair k).1, hk.1⟩ := by
      intro j
      have hp := differenceApproximant_pair ms j ω hGω
        (⟨(Nat.unpair k).1, hk.1⟩ : Vertex ω.1.val)
        (⟨(Nat.unpair k).2, hk.2⟩ : Vertex ω.1.val)
      simpa [hpair] using hp
    simp only [hkey]
    refine summable_norm_increments_of_geometric_ballMaximal (decode ω.1)
      (decode_geometry ω.1) (fun j => phi (decode ω.1) ω.2 (ms j)) ?_
      (fun i => StageDifferenceWeakMaximal.markedStageDifferenceMaximal (ms i) (ms (i + 1)) ω)
      N
      (fun i s hs =>
        StageDifferenceWeakMaximal.setLIntegral_stageDifference_le (ms i) (ms (i + 1)) ω hs)
      hN (⟨(Nat.unpair k).1, hk.1⟩ : Vertex ω.1.val)
      (⟨(Nat.unpair k).2, hk.2⟩ : Vertex ω.1.val)
    intro R hRpos
    refine ⟨(Spatial.maxDiamHittingBall (decode ω.1) R).toReal, ENNReal.toReal_nonneg, ?_⟩
    intro v hv
    have hDfin : Spatial.maxDiamHittingBall (decode ω.1) R < ∞ := hgeoω.1 R hRpos.le
    have hle : ENNReal.ofReal (Metric.diam ((decode ω.1).cell v : Set Plane))
        ≤ Spatial.maxDiamHittingBall (decode ω.1) R :=
      le_iSup (f := fun w : {w // Hits (decode ω.1)
          (Metric.closedBall (0 : Plane) R) w} =>
        ENNReal.ofReal (Metric.diam ((decode ω.1).cell w.1 : Set Plane))) ⟨v, hv⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hDfin.ne).1 hle
  · have hzero : ∀ j : ℕ, differenceApproximant ms j ω k = 0 := fun j =>
      differenceApproximant_of_not ms j ω k fun h => hk h.2
    have hfun : (fun j : ℕ =>
        ‖differenceApproximant ms (j + 1) ω k - differenceApproximant ms j ω k‖)
        = fun _ : ℕ => (0 : ℝ) := by
      funext j
      rw [hzero (j + 1), hzero j, sub_zero, norm_zero]
    rw [hfun]
    exact summable_zero

/-! ### `hconv` -/

/-- **`hconv` from the stage-difference maximal inequality.**  Composed with
`Corrector/MarkedDifferenceSubsequence.markedDifferencesConverge_of_summable`, which matches the
assembly's `∀ ms` shape: the subsequence is an input on both sides. -/
theorem markedDifferencesConverge_of_stageDifferenceWeakMaximal
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν) :
    MarkedDifferencesConverge ν ms :=
  MarkedDifferenceSubsequence.markedDifferencesConverge_of_summable ν ms
    (markedDifferenceIncrementsSummable_of_stageDifferenceWeakMaximal ν hν hFE ms hms hgeom hmax)

/-! ### The machine-checked join -/

end ReflectedGMS.MarkedDifferenceIncrementsFromMaximal
