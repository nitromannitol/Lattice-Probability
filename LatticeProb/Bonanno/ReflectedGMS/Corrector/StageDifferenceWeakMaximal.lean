/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageDifferenceWeakMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SmallBlockResidualProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyLocalControl
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedPatchEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy

/-!
# `s:eq:maximal` for the stage differences: `hpatch` from one weak-`L¹` input

This module is the *consumer* half of the manuscript's weak-`L¹` maximal inequality
`s:eq:maximal`, applied to the **stage differences** `φ_a − φ_b` of the concrete block
interpolants rather than to the residual `φ_m − Φ`.

`Corrector/SmallBlockResidualProducer.MarkedResidualWeakMaximal` is the same display for the
residual density and discharges `hsub`;
`Corrector/GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal` is the same display on
the coupled space and discharges `hcopies`.  The version below is the third instance of that
one producer shape, and it discharges the *approximant-level* patch input
`Corrector/MarkedPatchEnergyConvergence.MarkedPatchEnergyCauchy`, hence `hpatch`.

## The chain

Along the deterministic geometric subsequence of
`Corrector/SpecificEnergyConvergence.exists_strictMono_geometric_markedStageDefect` one has
`‖g_{ms j} − g_n‖_*² ≤ 2^{-4j}` for every `n ≥ ms j`, so the weak-`L¹` bound at the level
`λ = 2^{-2j}` reads

  `P[M(ρ(φ_{ms j} − φ_{ms (j+1)})) > 2^{-2j}] ≤ (C · 2^{2j}) · 2^{-4j} = C · 2^{-2j}`,

which is summable.  This is the only place where the geometric rate is used, and the
cancellation is exact (`div_mul_sq_cancel`): the constant `C` survives untouched, so no relation
between `C` and the subsequence is needed.

1. `ae_eventually_le_geometric_const` — the first Borel–Cantelli lemma with a general finite
   constant, the constant-`512` lemma
   `Corrector/SpecificEnergyLocalControl.ae_eventually_le_geometric` with `512` replaced by
   `C`.  Almost surely `M_j ≤ 2^{-2j}` for every large `j`.
2. `vectorEnergy_sub_le_of_geometric` — a purely algebraic induction on the gap, from the
   quadratic triangle inequality `Corrector/MarkedPatchEnergyConvergence.vectorEnergy_sub_le`:
   geometric increments with ratio `r` satisfying `4r ≤ 1` give `E(a_j − a_{j+d}) ≤ 4 B r^j`
   for **every** gap `d`.  With `r = 2^{-2}` this is exactly the manuscript's `4 · (2⁻¹)² = 1`.
   No Minkowski inequality and no finiteness of any single energy is used.
3. `hasCauchyPatchEnergy_of_geometric_ballMaximal` — the pathwise step, at one fixed
   configuration and with the maximal function abstracted into a sequence of numbers.
   `Corrector/SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal`
   (`s:eq:localcontrol`, checked) turns the ball bounds into `E_i ≤ (R + D_R)² · 2^{-2i}` on the
   patch of cells meeting `B̄_R`, and step 2 then gives the Cauchy property.
4. `markedPatchEnergyCauchy_of_stageDifferenceWeakMaximal` assembles them.  The Borel–Cantelli
   threshold `N` does not depend on the patch — `M_j` is a functional of the environment alone —
   so one almost-sure event serves every bounded `A` simultaneously.  The `D_R < ∞` half is
   `HarmonicCoordinateAssembly.ae_marked_geometry`, which costs only `s:eq:MTP` and the finite
   (FE) moment.

## Satisfiability of the hypotheses (anti-vacuity)

* `MarkedStageDifferenceWeakMaximal` is the manuscript's `s:eq:maximal` verbatim, at the
  specific-energy density of `φ_a − φ_b`.  The project proves that display with the **absolute**
  constant `C = 512`, uniformly in every parameter, in
  `Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le` and
  `Spatial/SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity`; the constant here is
  existentially quantified and only required to be finite, so it is weaker still.  It is in
  particular **not** a constant that would have to depend on the stage pair `(a, b)` or on the
  level `λ`: both are universally quantified inside the existential, so the usual "uniform
  constant" vacuity trap does not arise.
* The right-hand side is not identically `∞`.  Along the subsequence used here
  `markedStageDefect ν (ms j) n` is at most `2^{-4j}` — genuinely small, not merely finite — so
  the bound has content at exactly the pairs at which it is consumed.  That smallness is
  supplied by `hgeom` itself and is **not** imported from a stage-finiteness assumption:
  `markedPatchEnergyCauchy_of_stageDifferenceWeakMaximal` never mentions `markedStageEnergy`,
  and no hypothesis of the form `∀ n, markedStageEnergy ν n ≠ ∞` occurs anywhere in this file.
  (Beware the circular version of that claim: `e_m ≤ e_0 < ∞` at general `m` is *derived from*
  the projection bound, so it cannot be used to argue that the projection bound's own
  finiteness hypotheses are satisfiable.  Only the base case is unconditional, and it is proved
  as `Corrector/MarkedStageCoefficientScaling.markedStageEnergy_zero_ne_top`; finiteness of the
  defects is `markedStageDefect_ne_top` in the same module.  Neither is needed below.)
* Neither is it identically `0`, so the hypothesis does not force a degenerate conclusion: at
  small `λ` the bound is weaker than the trivial `P[·] ≤ 1`, and its content is at large `λ`,
  where it forces `M < ∞` almost surely.
* `hgeom` is satisfiable exactly as stated: `exists_strictMono_geometric_markedStageDefect`
  produces a strictly increasing `ms` with that rate from `MarkedNestedProjectionBound`,
  `s:eq:MTP` and the finite (FE) moment.  `exists_strictMono_markedPatchEnergyCauchy` below
  composes the two, so hypothesis and conclusion are jointly realisable and the implication is
  not vacuous.

## What is *not* proved here

`MarkedStageDifferenceWeakMaximal` itself is an **open input**.  Instantiating the project's
own `measure_ballMaximal_gt_le` at the stage-difference density still needs the two
identifications recorded in `Corrector/SmallBlockResidualProducer`'s docstring — translation
covariance and joint measurability of the density in the space variable.  The covariance half
is now available: `Corrector/ApproximantCovarianceFromBlockTransport.phi_similarity`, whose one
hypothesis is discharged outright by
`Corrector/BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant`, transports
`phi` along the *explicit* grid action `gridSimilarity s hs u = dilate s ∘ translate u` on
`SublinearEvent`, with no existential.  The joint measurability half is untouched.
`Corrector/MarkedStageFieldCovariance.phi_markedSimilarity` is the same covariance stated
directly along `markedSimilarity`, also with no hypotheses.

## Position relative to the keystone

The only place the nested projection bound `hproj` occurs is the satisfiability corollary
`exists_strictMono_markedPatchEnergyCauchy`, where it is a **named open input**; the working
theorem takes the rate `hgeom` directly.  Nothing here routes around, or silently assumes, the
label-level bijection `σ : ℕ ≃ ℕ` that `MarkedNestedProjectionBound` bottoms out in — the
string `σ` does not occur in this file — and `Corrector/MarkedStagePythagoras`, whose `hfin` is
a genuinely open input, is not in this module's import closure.

This file proves no main theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.StageDifferenceWeakMaximal

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly

/-! ### Two `ℝ≥0∞` computations -/

/-- `C/p · p² = C·p` for a finite nonzero `p`.  This is the exact cancellation that makes the
weak-`L¹` bound at the level `2^{-2j}` meet the geometric rate `2^{-4j}`. -/
theorem div_mul_sq_cancel {C p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    C / p * (p * p) = C * p := by
  rw [div_eq_mul_inv, show C * p⁻¹ * (p * p) = C * (p⁻¹ * p) * p by ring,
    ENNReal.inv_mul_cancel hp0 hptop, mul_one]

/-- The manuscript's `4 · (2⁻¹)² = 1`, the ratio condition of the gap induction. -/
theorem four_mul_inv_two_sq_le_one : (4 : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ 2) ≤ 1 := by
  have h2 : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  refine le_of_eq ?_
  calc (4 : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ 2)
      = ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) := by
        rw [sq, h4]; ring
    _ = 1 := by rw [h2, one_mul]

/-! ### The maximal function of a stage difference -/

/-- `M(ρ(φ_a − φ_b))`: the manuscript's maximal function of the specific-energy density of the
difference of the stage-`a` and stage-`b` block interpolants, at a marked environment.  This is
`SmallBlockResidualProducer.residualBallMaximal` read at two concrete interpolants instead of at
the interpolant and the limit. -/
noncomputable def markedStageDifferenceMaximal (a b : ℕ) (ω : MarkedEnvironment) : ℝ≥0∞ :=
  SmallBlockResidualProducer.residualBallMaximal (decode ω.1)
    (phi (decode ω.1) ω.2 a) (phi (decode ω.1) ω.2 b)

/-- A bound on the maximal function is a bound on every ball integral of the stage-difference
density. -/
theorem setLIntegral_stageDifference_le (a b : ℕ) (ω : MarkedEnvironment) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z in Metric.closedBall (0 : Plane) s,
        rootedSpecificEnergyDensity (decode ω.1)
          (fun v => phi (decode ω.1) ω.2 a v - phi (decode ω.1) ω.2 b v) z ∂volume)
      ≤ ENNReal.ofReal (s ^ 2) * markedStageDifferenceMaximal a b ω :=
  SmallBlockResidualProducer.setLIntegral_le_of_residualBallMaximal_le (decode ω.1)
    (phi (decode ω.1) ω.2 a) (phi (decode ω.1) ω.2 b) le_rfl hs

/-- **OPEN INPUT (`s:eq:maximal` for the stage differences).**  With a single finite constant
`C`, valid at every pair of stages and every level,

`P[M(ρ(φ_a − φ_b)) > λ] ≤ (C/λ) · ‖g_a − g_b‖_*²`.

This is the manuscript's weak-`L¹` maximal inequality applied to the specific-energy density of
`φ_a − φ_b`.  The project proves the same display for marked densities with the absolute
constant `512` (`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le`); see the module
docstring for what instantiating it at this density still requires. -/
def MarkedStageDifferenceWeakMaximal (ν : Measure Env) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (a b : ℕ) (lam : ℝ≥0∞), 0 < lam →
    (ν.prod gridLaw) {ω : MarkedEnvironment | lam < markedStageDifferenceMaximal a b ω}
      ≤ C / lam * SpecificEnergyConvergence.markedStageDefect ν a b

/-! ### Borel–Cantelli with a general constant -/

/-- **`s:eq:BC` with an unspecified finite constant.**  This is
`Corrector/SpecificEnergyLocalControl.ae_eventually_le_geometric` with the constant `512`
replaced by an arbitrary `C ≠ ∞`; the geometric series `∑_j C · 2^{-2j}` is still finite, which
is all the first Borel–Cantelli lemma needs. -/
theorem ae_eventually_le_geometric_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (M : ℕ → Ω → ℝ≥0∞)
    (htail : ∀ j : ℕ, μ {ω | ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) < M j ω}
      ≤ C * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j)) :
    ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, M j ω ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) := by
  have hq : ((2 : ℝ≥0∞)⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) (by norm_num)
  have hpow : ∀ j : ℕ, C * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) = C * (((2 : ℝ≥0∞)⁻¹) ^ 2) ^ j :=
    fun j => by rw [pow_mul]
  have hgeom : (∑' j : ℕ, C * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j)) ≠ ∞ := by
    rw [tsum_congr hpow]
    exact SpecificEnergyLocalControl.tsum_const_mul_pow_ne_top hC hq
  have hsum : (∑' j : ℕ, μ {ω | ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) < M j ω}) ≠ ∞ :=
    ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum htail)
  simpa only [Set.mem_setOf_eq, not_lt] using MeasureTheory.ae_eventually_notMem hsum

/-! ### The tail bound along the geometric subsequence -/

/-- **The exact cancellation.**  At the level `λ = 2^{-2j}` the weak-`L¹` bound and the
geometric rate `2^{-4j}` of the subsequence combine into the summable `C · 2^{-2j}`.  The
constant `C` is untouched: nothing below needs it to depend on `j`. -/
theorem tail_le_of_weakMaximal {ν : Measure Env} {C : ℝ≥0∞}
    (hbound : ∀ (a b : ℕ) (lam : ℝ≥0∞), 0 < lam →
      (ν.prod gridLaw) {ω : MarkedEnvironment | lam < markedStageDifferenceMaximal a b ω}
        ≤ C / lam * SpecificEnergyConvergence.markedStageDefect ν a b)
    {ms : ℕ → ℕ} (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (j : ℕ) :
    (ν.prod gridLaw) {ω : MarkedEnvironment |
        ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) < markedStageDifferenceMaximal (ms j) (ms (j + 1)) ω}
      ≤ C * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) := by
  have hq0 : ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) ≠ 0 := pow_ne_zero _ (by simp)
  have hqtop : ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) ≠ ∞ := ENNReal.pow_ne_top (by simp)
  have hqpos : 0 < ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) := lt_of_le_of_ne zero_le (Ne.symm hq0)
  have hdef : SpecificEnergyConvergence.markedStageDefect ν (ms j) (ms (j + 1))
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) := by
    have h := hgeom j (ms (j + 1)) (hms (Nat.lt_add_one j)).le
    rwa [show 4 * j = 2 * j + 2 * j by ring, pow_add] at h
  refine le_trans (hbound (ms j) (ms (j + 1)) _ hqpos) ?_
  calc C / ((2 : ℝ≥0∞)⁻¹) ^ (2 * j)
          * SpecificEnergyConvergence.markedStageDefect ν (ms j) (ms (j + 1))
      ≤ C / ((2 : ℝ≥0∞)⁻¹) ^ (2 * j)
          * (((2 : ℝ≥0∞)⁻¹) ^ (2 * j) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j)) := by gcongr
    _ = C * ((2 : ℝ≥0∞)⁻¹) ^ (2 * j) := div_mul_sq_cancel hq0 hqtop

/-! ### The algebraic gap induction -/

section PatchInduction

variable {W : Type*} (G : ReflectedWalk.ConductanceGraph W)

/-- The vector energy of the zero field vanishes. -/
theorem vectorEnergy_self_sub (f : W → Plane) :
    vectorEnergy G (fun v => f v - f v) = 0 := by
  rw [MarkedPatchEnergyConvergence.vectorEnergy_eq_tsum_patchEdgeEnergy]
  refine ENNReal.tsum_eq_zero.2 fun p => ?_
  simp [MarkedPatchEnergyConvergence.patchEdgeEnergy]

/-- **Geometric increments give a uniform Cauchy bound at every gap.**  If the successive
increments obey `E(a_i − a_{i+1}) ≤ B r^i` from the index `N` on, and the ratio satisfies
`4r ≤ 1`, then `E(a_j − a_{j+d}) ≤ 4 B r^j` for every gap `d`.

The proof is the quadratic triangle inequality `vectorEnergy_sub_le` iterated on the gap; the
constant `4` is forced by `λ ≥ 2 + 2λr` at `r = 1/4`.  No energy is assumed finite. -/
theorem vectorEnergy_sub_le_of_geometric (a : ℕ → W → Plane) (B r : ℝ≥0∞) (hr : 4 * r ≤ 1)
    (N : ℕ)
    (h : ∀ i : ℕ, N ≤ i → vectorEnergy G (fun v => a i v - a (i + 1) v) ≤ B * r ^ i) :
    ∀ (d j : ℕ), N ≤ j →
      vectorEnergy G (fun v => a j v - a (j + d) v) ≤ 4 * (B * r ^ j) := by
  intro d
  induction d with
  | zero =>
      intro j _
      simp only [Nat.add_zero]
      rw [vectorEnergy_self_sub G (a j)]
      exact zero_le
  | succ d ih =>
      intro j hj
      have hstep : vectorEnergy G (fun v => a j v - a (j + (d + 1)) v)
          ≤ 2 * vectorEnergy G (fun v => a j v - a (j + 1) v)
            + 2 * vectorEnergy G (fun v => a (j + 1) v - a (j + (d + 1)) v) :=
        MarkedPatchEnergyConvergence.vectorEnergy_sub_le G (a j) (a (j + (d + 1))) (a (j + 1))
      have h2 : vectorEnergy G (fun v => a (j + 1) v - a (j + (d + 1)) v)
          ≤ 4 * (B * r ^ (j + 1)) := by
        rw [show j + (d + 1) = (j + 1) + d by omega]
        exact ih (j + 1) (hj.trans (Nat.le_succ j))
      have hkey : 2 * (4 * (B * r ^ (j + 1))) ≤ 2 * (B * r ^ j) := by
        have hrw : 2 * (4 * (B * r ^ (j + 1))) = 2 * (B * r ^ j) * (4 * r) := by
          rw [pow_succ]; ring
        rw [hrw]
        calc 2 * (B * r ^ j) * (4 * r) ≤ 2 * (B * r ^ j) * 1 := by gcongr
          _ = 2 * (B * r ^ j) := mul_one _
      refine hstep.trans ?_
      calc 2 * vectorEnergy G (fun v => a j v - a (j + 1) v)
              + 2 * vectorEnergy G (fun v => a (j + 1) v - a (j + (d + 1)) v)
          ≤ 2 * (B * r ^ j) + 2 * (4 * (B * r ^ (j + 1))) := by
            gcongr
            exact h j hj
        _ ≤ 2 * (B * r ^ j) + 2 * (B * r ^ j) := by gcongr
        _ = 4 * (B * r ^ j) := by ring

end PatchInduction

/-! ### The pathwise step -/

/-- **The Cauchy property on one bounded patch, at one configuration.**  The maximal function
enters only through the sequence of numbers `Mf` bounding every ball integral of the successive
increments; `s:eq:localcontrol` converts those into patch energies, and the gap induction turns
the geometric decay into the Cauchy property.

No measure and no good event occur: this is a statement about one `IndexedCells`. -/
theorem hasCauchyPatchEnergy_of_geometric_ballMaximal
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (u : ℕ → V → Plane) {A : Set Plane} {R DR : ℝ}
    (hAR : A ⊆ Metric.closedBall (0 : Plane) R) (hpos : 0 < R + DR)
    (hD : ∀ v ∈ hittingVertices F (Metric.closedBall (0 : Plane) R),
      Metric.diam (F.cell v : Set Plane) ≤ DR)
    (Mf : ℕ → ℝ≥0∞) (N : ℕ)
    (hMf : ∀ (i : ℕ) (s : ℝ), 0 < s →
      (∫⁻ z in Metric.closedBall (0 : Plane) s,
          rootedSpecificEnergyDensity F (fun v => u i v - u (i + 1) v) z ∂volume)
        ≤ ENNReal.ofReal (s ^ 2) * Mf i)
    (hNbd : ∀ i : ℕ, N ≤ i → Mf i ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i)) :
    MarkedPatchEnergyConvergence.HasCauchyPatchEnergy
      (restrictGraph F.graph {v | Hits F A v})
      (fun j (v : ↥{v | Hits F A v}) => u j v.val) := by
  have hr1 : (((2 : ℝ≥0∞)⁻¹) ^ 2) < 1 :=
    pow_lt_one₀ zero_le (ENNReal.inv_lt_one.2 ENNReal.one_lt_two) (by norm_num)
  have hKtop : ENNReal.ofReal ((R + DR) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hsub : {v | Hits F A v} ⊆ hittingVertices F (Metric.closedBall (0 : Plane) R) :=
    fun _ hv => mem_hittingVertices_of_hits_subset F hAR hv
  have hstep : ∀ i : ℕ, N ≤ i →
      vectorEnergy (restrictGraph F.graph {v | Hits F A v})
          (fun v => u i v.val - u (i + 1) v.val)
        ≤ ENNReal.ofReal ((R + DR) ^ 2) * (((2 : ℝ≥0∞)⁻¹) ^ 2) ^ i := by
    intro i hi
    have hmono := PatchCentroidTraceFiniteEnergy.vectorEnergy_restrictGraph_mono F.graph hsub
      (fun v : ↥(hittingVertices F (Metric.closedBall (0 : Plane) R)) =>
        u i v.val - u (i + 1) v.val)
    have hball := SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal
      F hF (fun v => u i v - u (i + 1) v) hpos hD (hMf i)
    calc vectorEnergy (restrictGraph F.graph {v | Hits F A v})
            (fun v => u i v.val - u (i + 1) v.val)
        ≤ vectorEnergy (restrictGraph F.graph
              (hittingVertices F (Metric.closedBall (0 : Plane) R)))
            (fun v => u i v.val - u (i + 1) v.val) := hmono
      _ ≤ ENNReal.ofReal ((R + DR) ^ 2) * Mf i := hball
      _ ≤ ENNReal.ofReal ((R + DR) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
          gcongr
          exact hNbd i hi
      _ = ENNReal.ofReal ((R + DR) ^ 2) * (((2 : ℝ≥0∞)⁻¹) ^ 2) ^ i := by rw [pow_mul]
  have hind := vectorEnergy_sub_le_of_geometric
    (restrictGraph F.graph {v | Hits F A v})
    (fun j (v : ↥{v | Hits F A v}) => u j v.val)
    (ENNReal.ofReal ((R + DR) ^ 2)) (((2 : ℝ≥0∞)⁻¹) ^ 2) four_mul_inv_two_sq_le_one N hstep
  intro ε hε
  have hlim : Tendsto
      (fun n : ℕ => 4 * (ENNReal.ofReal ((R + DR) ^ 2) * (((2 : ℝ≥0∞)⁻¹) ^ 2) ^ n))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (((2 : ℝ≥0∞)⁻¹) ^ 2) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((R + DR) ^ 2)) h0 (Or.inr hKtop)
    simp only [mul_zero] at h1
    have h2 := ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h1 (Or.inr (by simp))
    simpa using h2
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max N N1, fun j hj k hk => ?_⟩
  have hjN : N ≤ j := le_trans (le_max_left N N1) hj
  have hkN : N ≤ k := le_trans (le_max_left N N1) hk
  have hjN1 : N1 ≤ j := le_trans (le_max_right N N1) hj
  have hkN1 : N1 ≤ k := le_trans (le_max_right N N1) hk
  rcases le_total j k with hjk | hjk
  · have hb := hind (k - j) j hjN
    rw [show j + (k - j) = k by omega] at hb
    exact hb.trans (hN1 j hjN1).le
  · have hb := hind (j - k) k hkN
    rw [show k + (j - k) = j by omega] at hb
    refine le_trans (le_of_eq ?_) (hb.trans (hN1 k hkN1).le)
    exact MarkedPatchEnergyConvergence.vectorEnergy_sub_comm _
      (fun v : ↥{v | Hits F A v} => u j v.val) (fun v : ↥{v | Hits F A v} => u k v.val)

/-! ### `MarkedPatchEnergyCauchy` -/

/-- **`s:prop:limit`(d) at the approximant level, from the maximal inequality.**  The weak-`L¹`
bound for the stage differences, the geometric subsequence and `s:eq:localcontrol` give, almost
surely and on every bounded spatial patch, the Cauchy property of the patch energies of the
differences of the concrete block interpolants.

The environment hypotheses are only `s:eq:MTP` and the finite (FE) moment: they enter through
`HarmonicCoordinateAssembly.ae_marked_geometry`, which supplies `D_R < ∞` at every radius. -/
theorem markedPatchEnergyCauchy_of_stageDifferenceWeakMaximal
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : MarkedStageDifferenceWeakMaximal ν) :
    MarkedPatchEnergyConvergence.MarkedPatchEnergyCauchy ν ms := by
  obtain ⟨C, hC, hbound⟩ := hmax
  have hBC := ae_eventually_le_geometric_const (ν.prod gridLaw) hC
    (fun j (ω : MarkedEnvironment) => markedStageDifferenceMaximal (ms j) (ms (j + 1)) ω)
    (tail_le_of_weakMaximal hbound hms hgeom)
  have hgeo := ae_marked_geometry ν hν hFE.ne (spatialMaximalBound_of_massTransport ν hν hFE)
  filter_upwards [hBC, hgeo] with ω hev hgood
  intro A hA
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨R0, hR0⟩ := hA.subset_closedBall (0 : Plane)
  have hRpos : (0 : ℝ) < max R0 1 := lt_of_lt_of_le one_pos (le_max_right R0 1)
  have hAR : A ⊆ Metric.closedBall (0 : Plane) (max R0 1) :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left R0 1))
  have hDfin : Spatial.maxDiamHittingBall (decode ω.1) (max R0 1) < ∞ := hgood.1 _ hRpos.le
  have hDR0 : (0 : ℝ) ≤ (Spatial.maxDiamHittingBall (decode ω.1) (max R0 1)).toReal :=
    ENNReal.toReal_nonneg
  have hD : ∀ v ∈ hittingVertices (decode ω.1) (Metric.closedBall (0 : Plane) (max R0 1)),
      Metric.diam ((decode ω.1).cell v : Set Plane)
        ≤ (Spatial.maxDiamHittingBall (decode ω.1) (max R0 1)).toReal := by
    intro v hv
    have hle : ENNReal.ofReal (Metric.diam ((decode ω.1).cell v : Set Plane))
        ≤ Spatial.maxDiamHittingBall (decode ω.1) (max R0 1) :=
      le_iSup (f := fun w : {w // Hits (decode ω.1)
          (Metric.closedBall (0 : Plane) (max R0 1)) w} =>
        ENNReal.ofReal (Metric.diam ((decode ω.1).cell w.1 : Set Plane))) ⟨v, hv⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hDfin.ne).1 hle
  exact hasCauchyPatchEnergy_of_geometric_ballMaximal (decode ω.1) (decode_geometry ω.1)
    (fun j => phi (decode ω.1) ω.2 (ms j)) hAR (by linarith) hD
    (fun i => markedStageDifferenceMaximal (ms i) (ms (i + 1)) ω) N
    (fun i s hs => setLIntegral_stageDifference_le (ms i) (ms (i + 1)) ω hs) hN

/-! ### `hpatch` -/

/-- **`hpatch` from the stage-difference maximal inequality.**  Composed with
`Corrector/MarkedPatchEnergyConvergence.markedPatchConvergence_of_patchEnergyCauchy`, which
needs `hconv` as well.  This is an implication: `hgeom`, `hmax` and `hconv` are all open. -/
theorem markedPatchConvergence_of_stageDifferenceWeakMaximal
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : MarkedStageDifferenceWeakMaximal ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    MarkedPatchConvergence ν ms :=
  MarkedPatchEnergyConvergence.markedPatchConvergence_of_patchEnergyCauchy ν hν hFE ms hconv
    (markedPatchEnergyCauchy_of_stageDifferenceWeakMaximal ν hν hFE ms hms hgeom hmax)

/-! ### Satisfiability of the geometric hypothesis -/

end ReflectedGMS.StageDifferenceWeakMaximal
