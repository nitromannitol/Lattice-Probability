/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DirectionalBracketLLNGates at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalBracketLLNWeld
import LatticeProb.Bonanno.ReflectedGMS.Limit.CanonicalOccupationDischarge
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedBracketRegularity
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainTheoremTwoAtoms
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer
import LatticeProb.Bonanno.ReflectedWalk.Step1
import LatticeProb.Bonanno.ReflectedWalk.HoldingDivergence

/-!
# The directional bracket-LLN weld with REPAIRED gates (one exhaustion, path-law read-off)

`Limit/DirectionalBracketLLNWeld.uniformDirectionalBracketLLN_of_regeneration` produces
`hlln : UniformDirectionalBracketLLN ν` from a kernel `κ` and per-coordinate density data whose
read-off gates (`RootReadOffGate`, `OriginRootedFibre`) have two defects, both about the gates and
not about the mathematics:

1. **Every exhaustion.**  The gates are quantified over EVERY exhaustion `D` with walk data, but
   the regeneration kernel `Temporal/RegenerationKernel.rootedKernel` is built from ONE canonical
   exhaustion (`TwoSidedRegenerationCoding.exhaustion e`).
2. **Read-off on the full sample.**  `∀ s, κ e (π ⁻¹' s) = 0 → areaSampleLaw … s = 0` lives on the
   full `Existence.Sample`; a sample is not a function of its path (unused exponentials at
   unrealized indices), so no read-off from a path-space coding satisfies it.

## Route for (1): exhaustion-independence of the path law (route (a))

The conclusion of the atom, `RescaledBracketLLN` of the directional bracket, depends on the sample
only through the area-clock trajectory, and the LAW of that trajectory does not depend on the
exhaustion: both constructed families are reflected walks with the same rate `areaRate` on the
same graph, so the **uniqueness half of Gwynne–Sung Theorem 1.6** (`Theorem16.step1`,
`Theorem16.identDistrib_of_approximatedBy`, with the holding-time divergence
`Theorem16.ae_tsum_stepHolding_eq_top`) identifies them (`identDistrib_of_isReflectedWalk`,
`areaTrajectory_law_eq`).  The energy minimizers of the two walk data are reconciled by
`isReflectedWalk_congr_energyMinimizer` (Proposition 1.3 uniqueness).

The raw-path LLN event is not cylinder-measurable, so it cannot be moved along the law directly;
it is moved through the MEASURABLE good event `BracketLLNAllStarts.goodSet` (dyadic right-limit
regularization + rational times), which on right-regular paths is exactly
"locally integrable ∧ `A(T)/T → C`" (`ae_ratio_of_law_eq`).  So the gate is needed at ONE
exhaustion only — existentially quantified, hence met at the kernel's own canonical exhaustion —
while the atom `AeDirectionalBracketLLN` is delivered UNCHANGED (every exhaustion, every start),
so no consumer up to `InvarianceMainTheoremTwoAtoms` is restated.  Route (b) (restating the
atoms at one exhaustion) would have required re-proving the packet chain
`AnalyticPacketAssembly → InvarianceAssembly`, all of which quantify over every `D`.

## Route for (2): the read-off at the PATH law

`PathRootReadOffGate` reads the fibre off into the raw path space `Trajectory (Vertex e.val)`
through `π : X → Trajectory`, with the density clause stated through `pathForwardDensity` and the
absolute continuity `κ e (π ⁻¹' E) = 0 → areaSampleLaw … (areaTrajectory … ⁻¹' E) = 0`.  The
core (`ae_forall_ratio_limit_of_regeneration_pathReadOff`) re-runs the disintegrated weld with
this read-off: the transported predicate is a predicate of the trajectory, so the path read-off is
all it ever used.  Bridge: every sample-level read-off induces a path-level one
(`pathReadOff_of_sampleReadOff`), so the new gate is implied by the old one at one exhaustion
(`ae_pathOriginRootedFibre_of_originRootedFibre`).

The local integrability of the bracket density at the root, which the old gate carried as
`CanonicalBracket` at the root, is no longer a gate clause: it is PROVED from MTP + FE at every
exhaustion with walk data (`CanonicalOccupationWeld.ae_intervalIntegrable_bracketDensity`).

## Remaining named inputs (all owned by the regeneration lane)

`hsys`, `hθ`, `hS`, `hregen` (kernel and flows), `herg`, and per harmonic `Φ`:
`hF`, `hdensscale` and `∀ᵐ e, PathOriginRootedFibre` (or `RootTimeDensity` +
`∀ᵐ e, PathRootReadOffGate`).  `Limit/DirectionalBracketLLNGatesCoding` checks that the
path-space coding `rootedLaw` meets every clause of `PathOriginRootedFibre` structurally.

**This is an implication.**  Nothing here certifies `p:lem:regeninvariant`,
`ScaledRootChainSystem` at the actual annealed law, the kernel's `hmeas`, or either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/CanonicalOccupationWeld.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_CanonicalOccupationWeld

/-!
# Welding the occupation discharge into the bracket lane

`Limit/CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite` proves
`CanonicalOccupationLocallyFinite` for `ν`-almost every environment from
`MassTransport ν`, `FiniteEnergyMoment ν` and `IsHarmonicCoordinate ν Φ`.  This
file re-states the three consumers of that atom in
`Limit/LocalizedBracketRegularity` and `Limit/LocalizedBracketOccupation` with
the atom removed from their hypotheses:

* `hbracket_of_ae_martingale_inputs` — the `hbracket` input of the four-input
  invariance assembly now follows from the two *martingale* clauses alone
  (local square integrability of `M`, and the compensated products being local
  martingales); the occupation conjunct of
  `LocalizedBracketRegularity.hbracket_of_ae_local_inputs` is gone;
* `ae_intervalIntegrable_bracketDensity` — the interval-integrability conjunct
  of bracket clause two, unconditionally on `hmt`, `hFE`, `hΦ`;
* `ae_ordinaryEdgeBracket_zero_continuous_boundedVariation` — bracket clause
  four, unconditionally on `hmt`, `hFE`, `hΦ`.

Everything here is plumbing over checked producers; the mathematics is in
`CanonicalOccupationDischarge`.  Nothing here certifies the martingale clauses,
`hbracket` itself, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal

namespace ReflectedGMS.CanonicalOccupationWeld

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open MartingaleIngredients StatementIngredients
open ReflectedGMS.LocalizedBracketOccupation
open Code EnvironmentFields AreaClocks QuenchedFormulation SpatialEnds
open InvarianceMainStatement
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.CanonicalBracketClauses
open EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open ReflectedGMS.CanonicalOccupationDischarge

/-- **The interval-integrability conjunct of bracket clause two**, for almost
every environment, at every exhaustion, connectivity witness, walk datum and
start, from `hmt`, `hFE`, `hΦ` alone. -/
theorem ae_intervalIntegrable_bracketDensity (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ start : Vertex e.val,
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
            ∀ (i j : Fin 2) (t : ℝ≥0),
              IntervalIntegrable
                (fun s : ℝ ↦ stateBracketDensity (decode e) (Φ.at e)
                  (exponentialAreaPath (decode e) D (Real.toNNReal s) ω) i j)
                volume 0 (t : ℝ) := by
  filter_upwards [ae_canonicalOccupationLocallyFinite ν hmt hFE Φ hΦ] with e hocc
  intro hnt D hG hdat start
  letI := hnt
  exact LocalizedBracketRegularity.ae_intervalIntegrable_bracketDensity_of_canonicalOccupationLocallyFinite
    e D hG Φ start hdat (hocc hnt D hG hdat start)

end ReflectedGMS.CanonicalOccupationWeld

end Merged_CanonicalOccupationWeld

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.DirectionalBracketLLNGates

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients AreaClocks InvarianceMainStatement QuenchedFormulation RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.BracketTimeAverage ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.ScaledRootChain
open ReflectedGMS.BracketLLNPolarizedWeld ReflectedGMS.MartingaleIngredients
open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.BracketClausesScalarReduction ReflectedGMS.BracketLLNAllStarts
open ReflectedGMS.DirectionalBracketLLNWeld ReflectedGMS.RootBlockGridProbability

/-! ## 1. The area-clock trajectory and the path-level forward density -/

section PathObjects

variable {V : Type*}

/-- The area-clock trajectory of a sample: the point of the raw path space `Trajectory V` that
every bracket functional of the canonical construction reads. -/
noncomputable def areaTrajectory (F : IndexedCells V) (D : F.graph.Exhaustion)
    (ω : Existence.Sample V) : Trajectory V :=
  fun t => exponentialAreaPath F D t ω

end PathObjects

/-- The canonical one-sided directional density of a raw trajectory — `forwardDensity` with the
sample replaced by its path.  It does not mention the exhaustion. -/
noncomputable def pathForwardDensity (e : Env) (Φ : CellField) (ξ : Fin 2 → ℝ)
    (x : Trajectory (Vertex e.val)) (s : ℝ) : ℝ :=
  dirForm (stateBracketDensity (decode e) (Φ.at e) (x (Real.toNNReal s))) ξ

/-! ## 2. The area-clock path law does not depend on the exhaustion (Theorem 1.6 uniqueness) -/

section Uniqueness

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **The energy minimizer in `IsReflectedWalk` is immaterial** on a connected graph: every
`EnergyMinimizer` bundle is Proposition 1.3's `energyMin` on non-empty sets. -/
theorem isReflectedWalk_congr_energyMinimizer (hG : G.toSimpleGraph.Connected) {w : V → ℝ}
    {hmin hmin' : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
    (h : IsReflectedWalk G w hmin 𝓧) : IsReflectedWalk G w hmin' 𝓧 := by
  intro z
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h z
  refine ⟨h0, h1, h2, h3, h4, h5, h6, fun A hA => ?_⟩
  obtain ⟨hA1, hA2⟩ := h7 A hA
  refine ⟨hA1, fun φ => ?_⟩
  obtain ⟨hi, heq⟩ := hA2 φ
  refine ⟨hi, ?_⟩
  rw [ReflectedWalk.Theorem16.EnergyMinimizer.eq_energyMin hmin' hG hA φ,
    ← ReflectedWalk.Theorem16.EnergyMinimizer.eq_energyMin hmin hG hA φ]
  exact heq

/-- **Uniqueness in law (Gwynne–Sung Theorem 1.6, uniqueness half) at ANY positive rate.**  Two
reflected walks on the same connected graph with the same rate have identically distributed
trajectories from every start, whatever their energy-minimizer bundles.  Assembled from
`Theorem16.step1` (Step 1), `Theorem16.ae_tsum_stepHolding_eq_top` (holding divergence) and
`Theorem16.identDistrib_of_approximatedBy` (Step 2); no lower bound `w ≥ w*` is needed. -/
theorem identDistrib_of_isReflectedWalk (hG : G.toSimpleGraph.Connected) {w : V → ℝ}
    (hw : ∀ x, 0 < w x) {hmin hmin' : G.EnergyMinimizer} {𝓧 𝓧' : ProcessFamily V}
    (h : IsReflectedWalk G w hmin 𝓧) (h' : IsReflectedWalk G w hmin' 𝓧') (z : V) :
    IdentDistrib 𝓧'.trajectory 𝓧.trajectory (𝓧'.P z) (𝓧.P z) := by
  have h'' : IsReflectedWalk G w hmin 𝓧' := isReflectedWalk_congr_energyMinimizer hG h'
  obtain ⟨E⟩ := Existence.exists_exhaustion hG
  have hdiv : HoldingTimesDiverge G hmin E := fun w hw 𝓨 h𝓨 x n =>
    ae_tsum_stepHolding_eq_top h𝓨 hG hw (fun v => (h𝓨 v).2.2.2.1) E x n
  obtain ⟨q, hq⟩ := step1 hmin hG E hdiv w hw
  exact identDistrib_of_approximatedBy h h'' (approximatedBy_of_approximated (hq 𝓧 h))
    (approximatedBy_of_approximated (hq 𝓧' h'')) z

end Uniqueness

/-! ## 3. Moving the ratio LLN along an identity of path laws -/

section Transfer

variable {V : Type*} [Countable V]

/-- **The ratio LLN of an additive functional depends only on the path law** (for reflected
walks).  Read through the measurable good event `goodSet f C`: under a right-regular process it is
exactly "locally integrable ∧ `A(T)/T → C`". -/
theorem ae_ratio_of_law_eq {G G' : ConductanceGraph V} {w w' : V → ℝ}
    {hmin : G.EnergyMinimizer} {hmin' : G'.EnergyMinimizer} {PF PF' : ProcessFamily V}
    (h : IsReflectedWalk G w hmin PF) (h' : IsReflectedWalk G' w' hmin' PF') (v : V)
    (hlaw : (PF.P v).map PF.trajectory = (PF'.P v).map PF'.trajectory)
    (f : Option V → ℝ) (C : ℝ)
    (hv : ∀ᵐ ω ∂PF.P v, LocallyIntegrablePath f (PF.trajectory ω) ∧
      Tendsto (fun T : ℝ => pathIntegral f (PF.trajectory ω) T / T) atTop (𝓝 C)) :
    ∀ᵐ ω ∂PF'.P v, LocallyIntegrablePath f (PF'.trajectory ω) ∧
      Tendsto (fun T : ℝ => pathIntegral f (PF'.trajectory ω) T / T) atTop (𝓝 C) := by
  have hS : MeasurableSet (goodSet f C) := measurableSet_goodSet f C
  have h1 : ∀ᵐ ω ∂PF.P v, PF.trajectory ω ∈ goodSet f C := by
    filter_upwards [hv, ae_rightRegularAt (h v).2.2.1 (h v).2.2.2.1] with ω hω hreg
    exact mem_goodSet_of_rightRegular hreg hω.1 hω.2
  have h2 : ∀ᵐ x ∂(PF.P v).map PF.trajectory, x ∈ goodSet f C :=
    (ae_map_iff PF.measurable_trajectory.aemeasurable hS).2 h1
  rw [hlaw] at h2
  have h3 : ∀ᵐ ω ∂PF'.P v, PF'.trajectory ω ∈ goodSet f C :=
    (ae_map_iff PF'.measurable_trajectory.aemeasurable hS).1 h2
  filter_upwards [h3, ae_rightRegularAt (h' v).2.2.1 (h' v).2.2.2.1] with ω hω hreg
  exact tendsto_ratio_of_mem_goodSet hreg hω

end Transfer

/-! ## 4. One environment: from the root at one exhaustion to every start at every exhaustion -/

section OneEnvironment

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V]

/-- **`RescaledBracketLLN` of the directional bracket at ANY exhaustion and ANY start, from the
entrywise ratio LLN at the root of ONE exhaustion.**  The root statement is moved to the other
exhaustion by the identity of path laws (`areaTrajectory_law_eq` through `ae_ratio_of_law_eq`),
then to the start by strong Markov (`ae_tendsto_ratio_of_root`), then re-expanded at every time.

CONDITIONAL on `hwalk0`, `hwalk`, `hlocr`, `hroot`, `hlocs`. -/
theorem rescaledBracketLLN_dirBracket_of_otherExhaustion (F : IndexedCells V)
    (hw : ∀ v, 0 < areaRate F v) {D0 D : F.graph.Exhaustion}
    {hG0 hG : F.graph.toSimpleGraph.Connected} {hmin0 hmin : F.graph.EnergyMinimizer}
    (hwalk0 : IsReflectedWalk F.graph (areaRate F) hmin0
      (Existence.processFamily D0 hG0 (areaRate F)))
    (hwalk : IsReflectedWalk F.graph (areaRate F) hmin
      (Existence.processFamily D hG (areaRate F)))
    (z : V → Plane) (Sig : Matrix (Fin 2) (Fin 2) ℝ) (root start : V)
    (hlocr : ∀ᵐ ω ∂areaSampleLaw F D0 hG0 root, ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => stateBracketDensity F z (exponentialAreaPath F D0 s.toNNReal ω) i j)
        volume 0 (t : ℝ))
    (hroot : ∀ᵐ ω ∂areaSampleLaw F D0 hG0 root, ∀ i j : Fin 2,
      Tendsto (fun T : ℝ => ordinaryEdgeBracket F z (exponentialAreaPath F D0) i j
        (Real.toNNReal T) ω / T) atTop (𝓝 (Sig i j)))
    (hlocs : ∀ᵐ ω ∂areaSampleLaw F D hG start, ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => stateBracketDensity F z (exponentialAreaPath F D s.toNNReal ω) i j)
        volume 0 (t : ℝ))
    (η : EuclideanSpace ℝ (Fin 2)) :
    RescaledBracketLLN (areaSampleLaw F D hG start)
      (dirBracket (ordinaryEdgeBracket F z (exponentialAreaPath F D)) η)
      (bilinForm Sig η η) := by
  -- the root statement at `D0`, in the additive-functional form
  have h0 : ∀ i j : Fin 2, ∀ᵐ ω ∂(Existence.processFamily D0 hG0 (areaRate F)).P root,
      LocallyIntegrablePath (fun o => stateBracketDensity F z o i j)
          ((Existence.processFamily D0 hG0 (areaRate F)).trajectory ω) ∧
        Tendsto (fun T : ℝ => pathIntegral (fun o => stateBracketDensity F z o i j)
          ((Existence.processFamily D0 hG0 (areaRate F)).trajectory ω) T / T) atTop
          (𝓝 (Sig i j)) := by
    intro i j
    filter_upwards [ae_locallyIntegrablePath_of_intervalIntegrable F D0 hG0 z root hlocr i j,
      hroot] with ω hloc hlim
    refine ⟨hloc, (hlim i j).congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    show pathIntegral (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D0 hG0 (areaRate F)).trajectory ω) ((Real.toNNReal T : ℝ)) / T
      = pathIntegral (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D0 hG0 (areaRate F)).trajectory ω) T / T
    rw [Real.coe_toNNReal T hT]
  -- moved to the root at `D` by the identity of path laws
  have hlaw : ((Existence.processFamily D0 hG0 (areaRate F)).P root).map
        (Existence.processFamily D0 hG0 (areaRate F)).trajectory =
      ((Existence.processFamily D hG (areaRate F)).P root).map
        (Existence.processFamily D hG (areaRate F)).trajectory :=
    (identDistrib_of_isReflectedWalk hG hw hwalk hwalk0 root).map_eq
  have h1 : ∀ i j : Fin 2, ∀ᵐ ω ∂(Existence.processFamily D hG (areaRate F)).P root,
      LocallyIntegrablePath (fun o => stateBracketDensity F z o i j)
          ((Existence.processFamily D hG (areaRate F)).trajectory ω) ∧
        Tendsto (fun T : ℝ => pathIntegral (fun o => stateBracketDensity F z o i j)
          ((Existence.processFamily D hG (areaRate F)).trajectory ω) T / T) atTop
          (𝓝 (Sig i j)) := fun i j =>
    ae_ratio_of_law_eq hwalk0 hwalk root hlaw _ _ (h0 i j)
  -- moved to the start by strong Markov at the hitting time of the root
  have h2 : ∀ i j : Fin 2, ∀ᵐ ω ∂(Existence.processFamily D hG (areaRate F)).P start,
      Tendsto (fun T : ℝ => pathIntegral (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D hG (areaRate F)).trajectory ω) T / T) atTop
        (𝓝 (Sig i j)) := fun i j =>
    ae_tendsto_ratio_of_root hwalk (fun o => stateBracketDensity F z o i j) (Sig i j) start root
      (ae_locallyIntegrablePath_of_intervalIntegrable F D hG z start hlocs i j)
      ((h1 i j).mono fun _ h => h.1) ((h1 i j).mono fun _ h => h.2)
  have hall : ∀ᵐ ω ∂(Existence.processFamily D hG (areaRate F)).P start, ∀ i j : Fin 2,
      Tendsto (fun T : ℝ => pathIntegral (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D hG (areaRate F)).trajectory ω) T / T) atTop
        (𝓝 (Sig i j)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h2 i j
  have hresc : ∀ᵐ ω ∂areaSampleLaw F D hG start, ∀ (i j : Fin 2) (t : ℝ≥0),
      Tendsto (fun e : ℝ => e ^ 2 * ordinaryEdgeBracket F z (exponentialAreaPath F D) i j
          (Real.toNNReal ((t : ℝ) / e ^ 2)) ω)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Sig i j * (t : ℝ))) := by
    filter_upwards [hall] with ω hω i j t
    exact tendsto_rescaled_of_ratio
      (F := pathIntegral (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D hG (areaRate F)).trajectory ω))
      (pathIntegral_zero _ _) (hω i j) t
  have hP : IsProbabilityMeasure (areaSampleLaw F D hG start) :=
    (Existence.processFamily D hG (areaRate F)).isProbabilityMeasure start
  have hmeas := aestronglyMeasurable_ordinaryEdgeBracket F D hG hwalk z start
  refine rescaledBracketLLN_of_ae_tendsto (fun u => ?_) (ae_tendsto_dirBracket η hresc)
  have hexp : dirBracket (ordinaryEdgeBracket F z (exponentialAreaPath F D)) η u
      = fun ω => (η 0 * ordinaryEdgeBracket F z (exponentialAreaPath F D) 0 0 u ω * η 0
          + η 0 * ordinaryEdgeBracket F z (exponentialAreaPath F D) 0 1 u ω * η 1)
        + (η 1 * ordinaryEdgeBracket F z (exponentialAreaPath F D) 1 0 u ω * η 0
          + η 1 * ordinaryEdgeBracket F z (exponentialAreaPath F D) 1 1 u ω * η 1) := by
    funext ω
    simp only [dirBracket, Fin.sum_univ_two]
  rw [hexp]
  exact ((((hmeas 0 0 u).const_mul (η 0)).mul_const (η 0)).add
      (((hmeas 0 1 u).const_mul (η 0)).mul_const (η 1))).add
    ((((hmeas 1 0 u).const_mul (η 1)).mul_const (η 0)).add
      (((hmeas 1 1 u).const_mul (η 1)).mul_const (η 1)))

end OneEnvironment

/-! ## 5. The disintegrated core with the read-off at the PATH law -/

/-- **Transfer of an almost-sure statement along a PATH read-off**: if the fibre charges no
`π`-preimage that the quenched law's trajectory preimage charges, a `Q`-a.s. predicate of `π x`
is a `P`-a.s. predicate of the trajectory.  No measurability of the predicate is needed. -/
theorem ae_comp_of_pathReadOff {Ω A Y : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {Q : Measure Ω} {P : Measure A} {π : Ω → Y} {τ : A → Y}
    (hread : ∀ E : Set Y, Q (π ⁻¹' E) = 0 → P (τ ⁻¹' E) = 0) {p : Y → Prop}
    (h : ∀ᵐ x ∂Q, p (π x)) : ∀ᵐ a ∂P, p (τ a) := by
  rw [ae_iff] at h ⊢
  exact hread {y | ¬ p y} h

/-- The three directional Cesàro limits of the path-level forward density along a raw
trajectory — the predicate the read-off transports. -/
def PathDirectionalCesaro (e : Env) (Φ : CellField) (a b c : ℝ)
    (x : Trajectory (Vertex e.val)) : Prop :=
  Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, pathForwardDensity e Φ (dirVec 1 0) x s) / T)
      atTop (𝓝 a) ∧
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, pathForwardDensity e Φ (dirVec 0 1) x s) / T)
      atTop (𝓝 b) ∧
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, pathForwardDensity e Φ (dirVec 1 1) x s) / T)
      atTop (𝓝 c)

/-! ## 6. The repaired gates -/

section Gates

variable {X : Type*} [MeasurableSpace X]

/-- **The repaired root gate.**  At ONE exhaustion with walk data (existential: the kernel's own
canonical exhaustion meets it), SOME root and a PATH read-off `π` into the raw path space carry
the density clause and the path-law absolute continuity.  No clause mentions another exhaustion
and no clause is on the full sample space; the local integrability of the bracket density at the
root is not a gate clause (it is proved, `CanonicalOccupationWeld.ae_intervalIntegrable_bracketDensity`). -/
def PathRootReadOffGate (κ : Kernel Env X) (dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ)
    (Φ : CellField) (e : Env) : Prop :=
  ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∃ (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG ∧
      ∃ (root : Vertex e.val) (π : X → Trajectory (Vertex e.val)),
        (∀ᵐ x ∂κ e, ∀ (ζ : Fin 2 → ℝ) (s : ℝ), 0 ≤ s →
          dens ζ (e, x) s = pathForwardDensity e Φ ζ (π x) s) ∧
        (∀ E : Set (Trajectory (Vertex e.val)),
          κ e (π ⁻¹' E) = 0 →
            areaSampleLaw (decode e) D hG root (areaTrajectory (decode e) D ⁻¹' E) = 0)

/-- **The repaired origin-rooted fibre** (the regeneration lane's realization, tex:1345): at ONE
exhaustion with walk data, the fibre is rooted at the ORIGIN cell, and its path read-off is
mutually absolutely continuous with the area-trajectory law from that cell (forward: every set of
paths; backward: measurable sets of paths), with the density clause. -/
def PathOriginRootedFibre (κ : Kernel Env X) (dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ)
    (Φ : CellField) (e : Env) : Prop :=
  ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∃ (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG ∧
      ∃ (root : Vertex e.val) (π : X → Trajectory (Vertex e.val)),
        rootAt (decode e) 0 = some root ∧
        (∀ᵐ x ∂κ e, ∀ (ζ : Fin 2 → ℝ) (s : ℝ), 0 ≤ s →
          dens ζ (e, x) s = pathForwardDensity e Φ ζ (π x) s) ∧
        (∀ E : Set (Trajectory (Vertex e.val)),
          κ e (π ⁻¹' E) = 0 →
            areaSampleLaw (decode e) D hG root (areaTrajectory (decode e) D ⁻¹' E) = 0) ∧
        (∀ E : Set (Trajectory (Vertex e.val)), MeasurableSet E →
          areaSampleLaw (decode e) D hG root (areaTrajectory (decode e) D ⁻¹' E) = 0 →
            κ e (π ⁻¹' E) = 0)

variable {κ : Kernel Env X} {dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ} {Φ : CellField}

theorem pathRootReadOffGate_of_pathOriginRootedFibre {e : Env}
    (h : PathOriginRootedFibre κ dens Φ e) : PathRootReadOffGate κ dens Φ e := by
  intro hnt
  obtain ⟨D, hG, hdata, root, π, -, hdens, hread, -⟩ := h hnt
  exact ⟨D, hG, hdata, root, π, hdens, hread⟩

/-- **`RootTimeDensity` from the repaired origin-rooted fibre.**  The path read-off is dominated by
the area-trajectory law from the origin cell, which starts there almost surely (property `X₀ = z`
of `IsReflectedWalk`); so the density clause at `s = 0` reads `Γ(H₀)`.  No MTP/FE is used. -/
theorem rootTimeDensity_of_pathOriginRootedFibre (ν : Measure Env)
    (hgate : ∀ᵐ e ∂ν, PathOriginRootedFibre κ dens Φ e) :
    RootTimeDensity ν κ Φ dens := by
  filter_upwards [hgate] with e hg
  have hnt := EnvironmentWalkDataProducer.nontrivial_vertex e
  obtain ⟨D, hG, hdata, root, π, hroot, hdens, -, hrev⟩ := hg hnt
  obtain ⟨_, _, hwalk, _⟩ := hdata
  have hmeas : MeasurableSet {x : Trajectory (Vertex e.val) | ¬ x 0 = some root} := by
    have h0 : Measurable fun x : Trajectory (Vertex e.val) => x 0 :=
      measurable_pi_apply (0 : ℝ≥0)
    exact (h0 (measurableSet_option {o : Option (Vertex e.val) | o = some root})).compl
  have hstart : ∀ᵐ x ∂κ e, π x 0 = some root := by
    refine ae_iff.2 (hrev _ hmeas ?_)
    exact ae_iff.1 (hwalk root).1
  filter_upwards [hdens, hstart] with x hx hxs ζ
  rw [hx ζ 0 le_rfl]
  show dirForm (stateBracketDensity (decode e) (Φ.at e) (π x (Real.toNNReal 0))) ζ = _
  rw [Real.toNNReal_zero, hxs, stateBracketDensity_some]
  simp only [rootedDirForm, rootedGamma, hroot, Option.elim]

end Gates

/-! ## 7. The weld -/

end ReflectedGMS.DirectionalBracketLLNGates
