/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SpecificEnergyConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedPatchEnergyConvergence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedDensityMeasurabilityProducer

/-!
# `hspec`: finite stage energies and the identification of `e_∞` (`s:eq:limitnorm`)

`HarmonicCoordinateAssembly.MarkedSpecificEnergyConvergence ν ms` (the assembly input `hspec`)
asks for

* **(a)** `∫⁻ ρ(φ_m) d(ν ⊗ gridLaw) < ∞` for every stage `m`, and
* **(b)** `∫⁻ ρ(φ_m − Φ) d(ν ⊗ gridLaw) → 0` along the **full** sequence `m`, where
  `Φ = markedPotential ms` is the marked limit along `ms`.

This module proves both from the manuscript's nested energy projections `s:prop:projection`,
following the manuscript's proof of `s:prop:limit` / `s:eq:limitnorm` (tex:550–570):

* `s:lem:e0` (checked, `Corrector/BaseSpecificEnergy`) bounds `e_0 ≤ 2 M_π < ∞`; the stage `0`
  interpolant *is* the centroid embedding everywhere (`DyadicApproximation.phi_zero`), and the
  marked stage-`0` energy is at most the environment-law base energy
  (`markedStageEnergy_zero_le_baseSpecificEnergy`, Tonelli's inequality `lintegral_prod_le`);
* `s:eq:pyth0` gives `e_m ≤ e_0`, which is clause (a) (`lintegral_stage_lt_top`);
* `s:eq:pythmn` gives `e_m ↓ e_∞` and `‖g_m − g_n‖_*² ≤ e_m − e_n`; a deterministic
  subsequence with `‖g_{m_j} − g_n‖_*² ≤ 2^{-4j}` for all `n ≥ m_j` is extracted
  (`exists_strictMono_geometric_markedStageDefect`, the manuscript's choice of `m_j`);
* **the identification of `e_∞`** (`tendsto_lintegral_markedSpecificGradientError`): along any
  strictly increasing `ms` on which the marked difference approximants converge almost surely
  (the assembly input `hconv`), Fatou gives
  `‖g_m − g‖_*² ≤ liminf_j ‖g_m − g_{m_j}‖_*² ≤ e_m − e_∞ → 0`.
  The pointwise half of Fatou is deterministic
  (`rootedSpecificEnergyDensity_le_liminf`: the rooted density is a series over the finitely
  many neighbours of the root cell, and each term converges because the increments of `φ_{m_j}`
  converge to those of `Φ`, `MarkedPatchEnergyConvergence.tendsto_phi_difference`); the
  integral half is `MeasureTheory.lintegral_liminf_le'`, fed by the measurability of the
  difference densities from the assembly input `hmeas`
  (`aemeasurable_rootedSpecificEnergyDensity_stageDifference`).

## The one named input

`MarkedNestedProjectionBound ν` is the inequality half `e_n + ‖g_m − g_n‖_*² ≤ e_m` (`m ≤ n`) of
the manuscript's `s:eq:pyth0`/`s:eq:pythmn` (tex:500–528) on the marked law, and
`MarkedNestedProjection ν` is the manuscript identity itself; the latter implies the former
(`markedNestedProjectionBound_of_nestedProjection`).  Stage `m = 0` is `s:eq:pyth0`.  Only the
inequality is consumed here.

**Satisfiability at `decode e` data.**  Both sides are expected *rooted densities* on the
marked law (no total energy over the infinite vertex set occurs), every value is allowed to be
`∞`, and off the full-measure event `SublinearEvent` the choice in `phi` is invisible to the
integrals.  Under `s:eq:MTP` and (FE) the manuscript proves the identity (hence the bound), with
`e_0 ≤ 2M_π < ∞` from `s:lem:e0`; no summability over cells is assumed.

**Producer route, and what is missing (survey of the checked corpus).**
* deterministic blockwise Pythagoras/orthogonality for the actual `CentroidTraceMinimizer`:
  `NestedEnergyProjections.blockPythagoras_nested`,
  `NestedProjectionProducers.tsum_vectorGradProd_nested_eq_zero` — checked;
* signed coefficient bookkeeping on the owner block of the origin (`hsum`/`hzero`):
  `PairingOwnershipInstance.summable_indicator_ownedByOriginBlock`,
  `PairingOwnershipInstance.tsum_indicator_ownedByOriginBlock_eq_zero` — checked;
* vanishing expected pairing from the two single-kernel transports:
  `PairingOwnershipInstance.integral_rootedPairingDensity_eq_zero_of_active` — checked,
  but with **every-`ω`** hypotheses (`hsel`, `hmin`, `hmE`, `hcoeff` measurable *everywhere*)
  that the concrete `phi` meets only on `SublinearEvent`; a gated restatement is needed;
* the transport identity on `Env × Grid` from `s:eq:MTP`:
  `MarkedMassTransportProducer.markedMassTransport_of_massTransport` — checked, for kernels
  that are `MarkedSimilarityCovariant`, i.e. covariant along the **specific** joint action
  `markedSimilarity s u hs = (similarityTargetEnv, dilate s hs ∘ translate u)`;
* expected Pythagoras from a vanishing pairing:
  `SpecificEnergyPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integral_pairing_eq_zero`
  — checked.
The genuinely missing atomic input is the **similarity covariance of `phi` along
`markedSimilarity`** on `SublinearEvent` (label bijection plus
`φ'_m(σ v) − φ'_m(σ w) = s • (φ_m(v) − φ_m(w))` for the grid `dilate s hs (translate u D)`).
`HarmonicCoordinateAssembly.ApproximantGradientCovariant` does **not** supply it: its grid action
is existentially quantified, while `MarkedSimilarityCovariant` needs the named action.  That
covariance is the `hcov` packet's object; measurability (`hmeas`) is already an assembly input.

**This file proves no main theorem.**  Its final statements are implications whose inputs
(`MarkedNestedProjectionBound`, `hmeas`, `hconv`) are open.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.SpecificEnergyConvergence

open Code StatementIngredients EnvironmentLaws RootDensities
open DyadicApproximation HarmonicLawIngredients HarmonicMainStatement
open HarmonicCoordinateAssembly MarkedLimitingCoordinateMeasurability

/-! ### The numerical skeleton of `s:prop:projection` and `s:eq:limitnorm`

`e m` is the stage energy and `d m n` the defect `‖g_m − g_n‖_*²`, both in `ℝ≥0∞`.  Only the
inequality `e n + d m n ≤ e m` (`m ≤ n`) and finiteness of `e` are used. -/

section Numerical

variable {e : ℕ → ℝ≥0∞} {d : ℕ → ℕ → ℝ≥0∞}

/-- `e_m` is nonincreasing. -/
theorem antitone_of_nestedBound (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m) : Antitone e :=
  fun m n hmn => le_of_add_le_left (hle m n hmn)

/-- `‖g_m − g_n‖_*² ≤ e_m − e_n`. -/
theorem defect_le_sub_of_nestedBound (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m)
    (hfin : ∀ n : ℕ, e n ≠ ∞) {m n : ℕ} (hmn : m ≤ n) : d m n ≤ e m - e n :=
  ENNReal.le_sub_of_add_le_left (hfin n) (hle m n hmn)

/-- `‖g_m − g_n‖_*² ≤ e_m − e_∞`, with `e_∞ = ⨅ e`. -/
theorem defect_le_sub_iInf_of_nestedBound (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m)
    (hfin : ∀ n : ℕ, e n ≠ ∞) {m n : ℕ} (hmn : m ≤ n) : d m n ≤ e m - ⨅ k, e k :=
  (defect_le_sub_of_nestedBound hle hfin hmn).trans (tsub_le_tsub_left (iInf_le e n) (e m))

/-- The limit energy `e_∞ = ⨅ e` is finite. -/
theorem iInf_ne_top_of_nestedBound (hfin : ∀ n : ℕ, e n ≠ ∞) : (⨅ k, e k) ≠ ∞ :=
  ne_top_of_le_ne_top (hfin 0) (iInf_le e 0)

/-- **`e_m ↓ e_∞`**, in the form `e_m − e_∞ → 0`. -/
theorem tendsto_sub_iInf_of_nestedBound (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m)
    (hfin : ∀ n : ℕ, e n ≠ ∞) :
    Tendsto (fun m => e m - ⨅ k, e k) atTop (𝓝 0) := by
  have hanti := antitone_of_nestedBound hle
  have hconst : Tendsto (fun _ : ℕ => ⨅ k, e k) atTop (𝓝 (⨅ k, e k)) := tendsto_const_nhds
  have h := ENNReal.Tendsto.sub (tendsto_atTop_iInf hanti) hconst
    (Or.inl (iInf_ne_top_of_nestedBound hfin))
  rwa [tsub_self] at h

/-- **The manuscript's choice of the deterministic subsequence.**  For any positive rates
`r j` there is a strictly increasing `ms` with `‖g_{ms j} − g_n‖_*² ≤ r j` for every
`n ≥ ms j`. -/
theorem exists_strictMono_defect_le (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m)
    (hfin : ∀ n : ℕ, e n ≠ ∞) {r : ℕ → ℝ≥0∞} (hr : ∀ j : ℕ, r j ≠ 0) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ j n : ℕ, ms j ≤ n → d (ms j) n ≤ r j := by
  have hanti := antitone_of_nestedBound hle
  have hinf := iInf_ne_top_of_nestedBound hfin
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ k ≥ N, e k ≤ (⨅ i, e i) + r j := by
    intro j
    obtain ⟨N, hN⟩ := iInf_lt_iff.1 (ENNReal.lt_add_right hinf (hr j))
    exact ⟨N, fun k hk => (hanti hk).trans hN.le⟩
  obtain ⟨ms, hms, hms'⟩ := Filter.extraction_forall_of_eventually' hN
  refine ⟨ms, hms, fun j n hn => ?_⟩
  refine (defect_le_sub_of_nestedBound hle hfin hn).trans ?_
  rw [tsub_le_iff_right]
  calc e (ms j) ≤ (⨅ i, e i) + r j := hms' j
    _ ≤ e n + r j := add_le_add (iInf_le e n) le_rfl
    _ = r j + e n := add_comm _ _

/-- **The Fatou-limit step of `s:eq:limitnorm`.**  If `F m ≤ liminf_j ‖g_m − g_{ms j}‖_*²` for
every `m`, then `F m ≤ e_m − e_∞`, and therefore `F m → 0` along the full sequence. -/
theorem tendsto_zero_of_le_liminf_defect (hle : ∀ m n : ℕ, m ≤ n → e n + d m n ≤ e m)
    (hfin : ∀ n : ℕ, e n ≠ ∞) {ms : ℕ → ℕ} (hms : StrictMono ms) {F : ℕ → ℝ≥0∞}
    (hF : ∀ m : ℕ, F m ≤ liminf (fun j => d m (ms j)) atTop) :
    Tendsto F atTop (𝓝 0) := by
  have hbound : ∀ m : ℕ, F m ≤ e m - ⨅ k, e k := by
    intro m
    refine (hF m).trans (liminf_le_of_frequently_le' ?_)
    refine Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop m] with j hj
    exact defect_le_sub_iInf_of_nestedBound hle hfin (hj.trans hms.le_apply)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_sub_iInf_of_nestedBound hle hfin) (fun m => zero_le) hbound

end Numerical

/-! ### Fatou for the rooted specific-energy density: the deterministic half

The rooted density at a vertex is a series over the neighbours of that vertex.  If the
increments of a sequence of fields converge to the increments of a limit field, every term of
the series converges, and the series of the limit is at most the `liminf` of the series. -/

section Pathwise

variable {V : Type*} [Countable V]

/-- **Fatou at one vertex.** -/
theorem specificEnergyDensity_le_liminf (F : IndexedCells V) (hF : Geometry F) (v : V)
    {u : ℕ → V → Plane} {U : V → Plane}
    (hptw : ∀ w : V, Tendsto (fun n => u n w - u n v) atTop (𝓝 (U w - U v))) :
    specificEnergyDensity F U v ≤ liminf (fun n => specificEnergyDensity F (u n) v) atTop := by
  have hA : (2 * ENNReal.ofReal (StatementIngredients.cellArea F v)) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (ENNReal.ofReal_pos.2 (StatementIngredients.cellArea_pos F hF v)).ne'
  have hAinv : (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 hA
  have hsum : ∀ Φ : V → Plane, specificEnergyDensity F Φ v
      = ∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2) *
          (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ := by
    intro Φ
    unfold specificEnergyDensity
    rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  have hterm : ∀ w : V, Tendsto
      (fun n => ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖u n w - u n v‖ ^ 2) *
        (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹) atTop
      (𝓝 (ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖U w - U v‖ ^ 2) *
        (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹)) := by
    intro w
    have h1 : Tendsto (fun n => ‖u n w - u n v‖ ^ 2) atTop (𝓝 (‖U w - U v‖ ^ 2)) :=
      (hptw w).norm.pow 2
    have h2 : Tendsto (fun n => ENNReal.ofReal (‖u n w - u n v‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖U w - U v‖ ^ 2))) := ENNReal.tendsto_ofReal h1
    have h3 : Tendsto
        (fun n => ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖u n w - u n v‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖U w - U v‖ ^ 2))) :=
      ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
    exact ENNReal.Tendsto.mul_const h3 (Or.inr hAinv)
  have hfun : (fun n => specificEnergyDensity F (u n) v)
      = fun n => ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖u n w - u n v‖ ^ 2) *
            (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ :=
    funext fun n => hsum (u n)
  rw [hsum U, hfun]
  exact MarkedPatchEnergyConvergence.tsum_le_liminf_tsum_of_tendsto hterm

/-- **Fatou for the boundary-masked rooted density.** -/
theorem rootedSpecificEnergyDensity_le_liminf (F : IndexedCells V) (hF : Geometry F) (z : Plane)
    {u : ℕ → V → Plane} {U : V → Plane}
    (hptw : ∀ v w : V, Tendsto (fun n => u n w - u n v) atTop (𝓝 (U w - U v))) :
    rootedSpecificEnergyDensity F U z
      ≤ liminf (fun n => rootedSpecificEnergyDensity F (u n) z) atTop := by
  unfold rootedSpecificEnergyDensity
  cases hroot : rootAt F z with
  | none =>
      show (0 : ℝ≥0∞) ≤ _
      exact zero_le
  | some v =>
      show specificEnergyDensity F U v
        ≤ liminf (fun n => specificEnergyDensity F (u n) v) atTop
      exact specificEnergyDensity_le_liminf F hF v (hptw v)

end Pathwise

/-! ### The marked stage energies and the named input -/

/-- **The specific energy `e_m = ‖g_m‖_*²` of stage `m`** on the marked law. -/
noncomputable def markedStageEnergy (ν : Measure Env) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω : MarkedEnvironment,
    rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0 ∂ν.prod gridLaw

/-- **The specific energy `‖g_m − g_n‖_*²` of the difference of two stages** on the marked
law. -/
noncomputable def markedStageDefect (ν : Measure Env) (m n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω : MarkedEnvironment, rootedSpecificEnergyDensity (decode ω.1)
    (fun v => phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 n v) 0 ∂ν.prod gridLaw

/-- **The manuscript's nested energy projections** (`s:prop:projection`, `s:eq:pyth0` at
`m = 0` and `s:eq:pythmn`), on the marked law: `e_m = e_n + ‖g_m − g_n‖_*²` for `m ≤ n`.
Not consumed directly; see `MarkedNestedProjectionBound`. -/
def MarkedNestedProjection (ν : Measure Env) : Prop :=
  ∀ m n : ℕ, m ≤ n → markedStageEnergy ν m = markedStageEnergy ν n + markedStageDefect ν m n

/-- **OPEN INPUT (`s:prop:projection`, inequality half).**  For `m ≤ n`,
`e_n + ‖g_m − g_n‖_*² ≤ e_m` on the marked law; at `m = 0` this is the inequality half of
`s:eq:pyth0`.  See the module docstring for its satisfiability at `decode e` data and for the
checked producer route (the missing atom is the covariance of `phi` along
`MarkedMassTransportProducer.markedSimilarity`). -/
def MarkedNestedProjectionBound (ν : Measure Env) : Prop :=
  ∀ m n : ℕ, m ≤ n → markedStageEnergy ν n + markedStageDefect ν m n ≤ markedStageEnergy ν m

/-- The manuscript identity implies the consumed inequality. -/
theorem markedNestedProjectionBound_of_nestedProjection {ν : Measure Env}
    (h : MarkedNestedProjection ν) : MarkedNestedProjectionBound ν :=
  fun m n hmn => (h m n hmn).ge

/-! ### Milestone 1: clause (a), every stage has finite specific energy -/

/-- **The marked stage-`0` energy is at most the base specific energy `e_0` of
`s:lem:e0`.**  The stage-`0` interpolant is the centroid embedding at every marked
environment, the integrand depends on the environment only, and the grid law has mass one. -/
theorem markedStageEnergy_zero_le_baseSpecificEnergy (ν : Measure Env) :
    markedStageEnergy ν 0 ≤ BaseSpecificEnergy.baseSpecificEnergy ν := by
  have h1 : markedStageEnergy ν 0 = ∫⁻ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1) (cellCentroid (decode ω.1)) 0 ∂ν.prod gridLaw := by
    unfold markedStageEnergy
    refine lintegral_congr fun ω => ?_
    rw [phi_zero]
  have h2 : (∫⁻ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1) (cellCentroid (decode ω.1)) 0 ∂ν.prod gridLaw)
      ≤ ∫⁻ e : Env, ∫⁻ _D : Grid,
          rootedSpecificEnergyDensity (decode e) (cellCentroid (decode e)) 0 ∂gridLaw ∂ν :=
    lintegral_prod_le (fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (cellCentroid (decode ω.1)) 0)
  have h3 : (∫⁻ e : Env, ∫⁻ _D : Grid,
      rootedSpecificEnergyDensity (decode e) (cellCentroid (decode e)) 0 ∂gridLaw ∂ν)
      = BaseSpecificEnergy.baseSpecificEnergy ν := by
    unfold BaseSpecificEnergy.baseSpecificEnergy
    refine lintegral_congr fun e => ?_
    rw [lintegral_const, measure_univ, mul_one]
  rw [h1, ← h3]
  exact h2

/-- **Milestone 1 (clause (a) of `hspec`).**  Every stage has finite expected specific energy:
`e_m ≤ e_0 ≤ 2 M_π < ∞` by `s:eq:pyth0` and `s:lem:e0`. -/
theorem markedStageEnergy_lt_top (ν : Measure Env) (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (hproj : MarkedNestedProjectionBound ν) (m : ℕ) :
    markedStageEnergy ν m < ∞ := by
  have hle : markedStageEnergy ν m ≤ markedStageEnergy ν 0 :=
    le_of_add_le_left (hproj 0 m (Nat.zero_le m))
  obtain ⟨hb, hM⟩ :=
    BaseSpecificEnergy.baseSpecificEnergy_le_two_mul_diamSqPiMoment_lt_top ν hν hFE.ne
  exact lt_of_le_of_lt
    (hle.trans ((markedStageEnergy_zero_le_baseSpecificEnergy ν).trans hb)) hM

/-- Clause (a) of `MarkedSpecificEnergyConvergence`, verbatim. -/
theorem lintegral_stage_lt_top (ν : Measure Env) (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (hproj : MarkedNestedProjectionBound ν) (m : ℕ) :
    (∫⁻ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0 ∂ν.prod gridLaw) < ∞ :=
  markedStageEnergy_lt_top ν hν hFE hproj m

/-! ### Milestone 2: the deterministic subsequence with geometric increments -/

/-- The geometric rate `2^{-4j}` never vanishes. -/
theorem geometricRate_ne_zero (j : ℕ) : ((2 : ℝ≥0∞)⁻¹) ^ (4 * j) ≠ 0 :=
  pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)

/-- **Milestone 2.**  The manuscript's deterministic subsequence: `ms` is strictly increasing
and `‖g_{ms j} − g_n‖_*² ≤ 2^{-4j}` for every `n ≥ ms j`; in particular
`‖g_{ms (j+1)} − g_{ms j}‖_*² ≤ 2^{-4j}`. -/
theorem exists_strictMono_geometric_markedStageDefect (ν : Measure Env) (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (hproj : MarkedNestedProjectionBound ν) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∀ j n : ℕ, ms j ≤ n → markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j) :=
  exists_strictMono_defect_le (e := markedStageEnergy ν) (d := markedStageDefect ν) hproj
    (fun n => (markedStageEnergy_lt_top ν hν hFE hproj n).ne) geometricRate_ne_zero

/-! ### Milestone 3: clause (b), the identification of `e_∞` -/

/-- Measurability of the rooted density of a difference of two stages, from `hmeas`. -/
theorem aemeasurable_rootedSpecificEnergyDensity_stageDifference (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (a b : ℕ) :
    AEMeasurable (fun ω : MarkedEnvironment => rootedSpecificEnergyDensity (decode ω.1)
      (fun v => phi (decode ω.1) ω.2 a v - phi (decode ω.1) ω.2 b v) 0) (ν.prod gridLaw) := by
  refine (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : MarkedEnvironment → Env)) measurable_fst
    (Ψ := fun ω n => gatedApproximant a ω n - gatedApproximant b ω n)
    (fun n => (hmeas a n).sub (hmeas b n))).aemeasurable.congr ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE.ne)] with ω hG
  have hEq : (fun v : Vertex ω.1.val => gatedApproximant a ω v.val - gatedApproximant b ω v.val)
      = fun v : Vertex ω.1.val => phi (decode ω.1) ω.2 a v - phi (decode ω.1) ω.2 b v := by
    funext v
    rw [MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := a) hG v,
      MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant (m := b) hG v]
  show rootedSpecificEnergyDensity (decode ω.1)
      (fun v : Vertex ω.1.val => gatedApproximant a ω v.val - gatedApproximant b ω v.val) 0
    = rootedSpecificEnergyDensity (decode ω.1)
        (fun v => phi (decode ω.1) ω.2 a v - phi (decode ω.1) ω.2 b v) 0
  rw [hEq]

/-- On the good event, along a subsequence at which the marked difference approximants
converge, the increments of `φ_m − φ_{ms j}` converge to those of `φ_m − Φ`. -/
theorem tendsto_stage_sub_increment (ms : ℕ → ℕ) (m : ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (hgood : ω ∈ LimitGood (differenceApproximant ms))
    (v w : Vertex ω.1.val) :
    Tendsto (fun j => (phi (decode ω.1) ω.2 m w - phi (decode ω.1) ω.2 (ms j) w)
        - (phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 (ms j) v)) atTop
      (𝓝 ((phi (decode ω.1) ω.2 m w - markedPotential ms ω w)
        - (phi (decode ω.1) ω.2 m v - markedPotential ms ω v))) := by
  have h := MarkedPatchEnergyConvergence.tendsto_phi_difference ms hG hgood v w
  have h1 : Tendsto (fun j => (phi (decode ω.1) ω.2 m w - phi (decode ω.1) ω.2 m v)
      - (phi (decode ω.1) ω.2 (ms j) w - phi (decode ω.1) ω.2 (ms j) v)) atTop
      (𝓝 ((phi (decode ω.1) ω.2 m w - phi (decode ω.1) ω.2 m v)
        - (markedPotential ms ω w - markedPotential ms ω v))) :=
    tendsto_const_nhds.sub h
  have heq : (phi (decode ω.1) ω.2 m w - phi (decode ω.1) ω.2 m v)
        - (markedPotential ms ω w - markedPotential ms ω v)
      = (phi (decode ω.1) ω.2 m w - markedPotential ms ω w)
        - (phi (decode ω.1) ω.2 m v - markedPotential ms ω v) := by abel
  rw [heq] at h1
  refine h1.congr fun j => ?_
  abel

/-- **Fatou for the gradient error**:
`E ρ(φ_m − Φ) ≤ liminf_j E ρ(φ_m − φ_{ms j})`. -/
theorem lintegral_markedSpecificGradientError_le_liminf (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (ms : ℕ → ℕ) (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    (∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
      ≤ liminf (fun j => markedStageDefect ν m (ms j)) atTop := by
  have hpt : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, markedSpecificGradientError ms m ω
      ≤ liminf (fun j => rootedSpecificEnergyDensity (decode ω.1)
          (fun v => phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 (ms j) v) 0) atTop := by
    filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
      (ae_mem_sublinearEvent ν hν hFE.ne), hconv] with ω hG hgood
    show rootedSpecificEnergyDensity (decode ω.1)
        (fun v => phi (decode ω.1) ω.2 m v - markedPotential ms ω v) 0 ≤ _
    exact rootedSpecificEnergyDensity_le_liminf (decode ω.1) (decode_geometry ω.1) 0
      (u := fun j v => phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 (ms j) v)
      (U := fun v => phi (decode ω.1) ω.2 m v - markedPotential ms ω v)
      (fun v w => tendsto_stage_sub_increment ms m hG hgood v w)
  calc (∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
      ≤ ∫⁻ ω : MarkedEnvironment, liminf (fun j => rootedSpecificEnergyDensity (decode ω.1)
          (fun v => phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 (ms j) v) 0) atTop
            ∂ν.prod gridLaw := lintegral_mono_ae hpt
    _ ≤ liminf (fun j => ∫⁻ ω : MarkedEnvironment, rootedSpecificEnergyDensity (decode ω.1)
          (fun v => phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 (ms j) v) 0
            ∂ν.prod gridLaw) atTop :=
        lintegral_liminf_le' fun j =>
          aemeasurable_rootedSpecificEnergyDensity_stageDifference ν hν hFE hmeas m (ms j)
    _ = liminf (fun j => markedStageDefect ν m (ms j)) atTop := rfl

/-- **Milestone 3 (clause (b) of `hspec`, `s:eq:limitnorm`).**  Along any strictly increasing
`ms` on which the marked difference approximants converge almost surely,
`E ρ(φ_m − Φ) ≤ e_m − e_∞`, so the expected specific gradient error tends to zero along the
**full** sequence `m`. -/
theorem tendsto_lintegral_markedSpecificGradientError (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : MarkedNestedProjectionBound ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hconv : MarkedDifferencesConverge ν ms) :
    Tendsto (fun m => ∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
      atTop (𝓝 0) :=
  tendsto_zero_of_le_liminf_defect (e := markedStageEnergy ν) (d := markedStageDefect ν) hproj
    (fun n => (markedStageEnergy_lt_top ν hν hFE hproj n).ne) hms
    (lintegral_markedSpecificGradientError_le_liminf ν hν hFE hmeas ms hconv)

/-- **The quantitative form**: `E ρ(φ_m − Φ) ≤ e_m − e_∞`. -/
theorem lintegral_markedSpecificGradientError_le_sub_iInf (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : MarkedNestedProjectionBound ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    (∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
      ≤ markedStageEnergy ν m - ⨅ k, markedStageEnergy ν k := by
  have hfin : ∀ n : ℕ, markedStageEnergy ν n ≠ ∞ := fun n =>
    (markedStageEnergy_lt_top ν hν hFE hproj n).ne
  refine (lintegral_markedSpecificGradientError_le_liminf ν hν hFE hmeas ms hconv m).trans
    (liminf_le_of_frequently_le' ?_)
  refine Eventually.frequently ?_
  filter_upwards [eventually_ge_atTop m] with j hj
  exact defect_le_sub_iInf_of_nestedBound (e := markedStageEnergy ν) (d := markedStageDefect ν)
    hproj hfin (hj.trans hms.le_apply)

/-- **`hspec` from the nested projections and `hconv`.**  This is an implication: its inputs
`hmeas`, `hproj` and `hconv` are open. -/
theorem markedSpecificEnergyConvergence_of_nestedProjection (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : MarkedNestedProjectionBound ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hconv : MarkedDifferencesConverge ν ms) :
    MarkedSpecificEnergyConvergence ν ms :=
  ⟨fun m => lintegral_stage_lt_top ν hν hFE hproj m,
    tendsto_lintegral_markedSpecificGradientError ν hν hFE hmeas hproj ms hms hconv⟩

end ReflectedGMS.SpecificEnergyConvergence
