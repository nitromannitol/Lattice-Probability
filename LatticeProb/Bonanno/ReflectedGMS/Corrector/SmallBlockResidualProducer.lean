/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SmallBlockResidualProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedCentroidSublinearityProducer

/-!
# `s:eq:smallresidual` from the maximal inequality for the residual density

`Corrector/MarkedCentroidSublinearityProducer.markedCentroidSublinearity_of_smallBlockResidual`
discharges the centroid half `hsub` of the harmonic-coordinate assembly from two open
inputs: `MarkedGeometricMassQuadratic` (`s:eq:Wbound`, quadratic form) and
`MarkedSmallBlockResidual` (`s:eq:smallresidual`).  This module removes the second one,
replacing it by the manuscript's own weak-`L¹` maximal inequality `s:eq:maximal` **for the
residual density** `ρ(φ_m − Φ)`.

## What `s:eq:smallresidual` asks for

`CentroidSublinearityFromResidual.SmallBlockResidual F D Φ` asks, for every `ε > 0`, for a
nonzero stage `n`, an actual `n`-block interpolant `f`, and a constant `M < ε` with

  `∫_{B̄_s} ρ(Φ − f) ≤ s² M`  for **every** `s > 0`.

The quantifier over *all* radii is essential — `uniformlySublinearCorrector_of_smallBlockResidual`
consumes the bound at every radius beyond a threshold that itself depends on `ε` — so
convergence of the residual patch energies on *bounded* sets
(`HarmonicCoordinateAssembly.MarkedPatchConvergence`) does **not** suffice, and no argument
below pretends otherwise.  What the display says is exactly that the manuscript's maximal
function

  `M(ρ) = sup_{s>0} s⁻² ∫_{B̄_s} ρ`

of the residual density is smaller than `ε` at some stage.  That is `residualBallMaximal`
below, and `setLIntegral_le_of_residualBallMaximal_le` is the (trivial) translation.

## The route, and what stays open

1. `markedSmallBlockResidual_of_maximalVanishes` — the a.s. statement "some stage makes the
   residual maximal function arbitrarily small" gives `MarkedSmallBlockResidual`, because the
   concrete `phi` *is* a block interpolant at every stage almost surely
   (`HarmonicCoordinateAssembly.ae_blockInterpolation_clause`, which since
   `spatialMaximalBound_of_massTransport` needs only `s:eq:MTP` and the finite (FE) moment).
   Nothing else is used: no covariance, no measurability, no convergence input.
2. `markedResidualMaximalVanishes_of_small` — that a.s. statement follows from convergence
   **in probability** of the residual maximal functions to `0`, by the first Borel–Cantelli
   lemma along a stage sequence chosen once and for all (not depending on the environment).
3. `markedResidualMaximalSmall_of_weakMaximal` — convergence in probability follows from the
   manuscript's weak-`L¹` maximal bound `s:eq:maximal` applied to the residual density,
   together with `HarmonicCoordinateAssembly.MarkedSpecificEnergyConvergence`, which is
   **already an input of the assembly** (`hspec`): `E[ρ(φ_m − Φ)] → 0` and
   `P[M(ρ(φ_m − Φ)) > λ] ≤ C E[ρ(φ_m − Φ)]/λ` give `M → 0` in probability at every `λ`.

So the residue is exactly `MarkedResidualWeakMaximal`: the project's own
`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le` and its paper-correct form
`Spatial/SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity` prove this bound with
the explicit constant `C = 512` for **marked densities** `ρ_ω(z) = F(ω − z)`, and
`Spatial/SpatialMaximalForFiniteEnergy` instantiates it at the rooted (FE) density from
`s:eq:MTP` and the finite (FE) moment alone.  Instantiating it at the *residual* density needs
two further identifications that no module in the project currently provides, and which are
**not** asserted here:

* translation covariance of the residual field `φ_m − Φ`, i.e. that
  `ρ^{decode e}(φ_m − Φ)(z)` is the value at the re-rooted configuration of a single
  functional.  The limit half is available exactly and everywhere
  (`HarmonicCoordinateAssembly.unmarkedDifferenceField_similarity`, from `hcov` and `hmeas`),
  but `ApproximantGradientCovariant` transports `phi` along an *existentially quantified*
  measure-preserving grid action, not along the grid translation `translate z` that
  re-rooting uses;
* joint measurability of `(e, z) ↦ ρ^{decode e}(φ_m − Φ)(z)` over the environment
  sigma-field, the `measurable_density` field of
  `Spatial/SpatialMaximalInequality.EnvironmentGrid` — a strengthening in the space variable
  of the third clause of `HarmonicCoordinateAssembly.MarkedDensityMeasurability`.

Both are instances of the standing trap that `DyadicApproximation.phi` is a `Classical.choose`
and is canonical only on `HarmonicCoordinateAssembly.SublinearEvent`.

The constant in `MarkedResidualWeakMaximal` is existentially quantified and only required to
be finite, so the hypothesis is weaker than the `C = 512` the project's inequality supplies.

The final statements are implications with open hypotheses; they do not prove the
harmonic-coordinate theorem.  `MarkedGeometricMassQuadratic` (`s:eq:Wbound`, quadratic form)
is untouched and remains open: it is *not* the finite-radius summability
`PatchCentroidTraceFiniteEnergy.SpatialDiameterCellBounds` discharged by
`Spatial/SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.SmallBlockResidualProducer

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly CentroidSublinearityFromResidual
open MarkedCentroidSublinearityProducer

variable {V : Type*}

/-! ### The maximal function of a residual density -/

/-- The normalised ball average `r⁻² ∫_{B̄_r} ρ(Φ − f)` of the specific-energy density of a
residual. -/
noncomputable def residualBallAverage (F : IndexedCells V) (Φ f : V → Plane) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (r ^ 2))⁻¹ *
    ∫⁻ z in Metric.closedBall (0 : Plane) r,
      rootedSpecificEnergyDensity F (fun v => Φ v - f v) z ∂volume

/-- The manuscript's maximal function `M(ρ) = sup_{r>0} r⁻² ∫_{B̄_r} ρ` of the residual
specific-energy density.  This is the same shape as
`Spatial/SpatialMaximalInequality.ballMaximal`, read directly on the environment rather than
through a marked functional. -/
noncomputable def residualBallMaximal (F : IndexedCells V) (Φ f : V → Plane) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ _ : 0 < r, residualBallAverage F Φ f r

theorem residualBallAverage_le_residualBallMaximal (F : IndexedCells V) (Φ f : V → Plane)
    {r : ℝ} (hr : 0 < r) :
    residualBallAverage F Φ f r ≤ residualBallMaximal F Φ f :=
  le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) => residualBallAverage F Φ f r) r hr

/-- **The translation between `s:eq:smallresidual` and the maximal function.**  A bound on the
maximal function is a bound on every ball integral. -/
theorem setLIntegral_le_of_residualBallMaximal_le (F : IndexedCells V) (Φ f : V → Plane)
    {M : ℝ≥0∞} (hM : residualBallMaximal F Φ f ≤ M) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z in Metric.closedBall (0 : Plane) s,
        rootedSpecificEnergyDensity F (fun v => Φ v - f v) z ∂volume)
      ≤ ENNReal.ofReal (s ^ 2) * M := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hne : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hs2
  have htop : ENNReal.ofReal (s ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hle : residualBallAverage F Φ f s ≤ M :=
    le_trans (residualBallAverage_le_residualBallMaximal F Φ f hs) hM
  calc (∫⁻ z in Metric.closedBall (0 : Plane) s,
          rootedSpecificEnergyDensity F (fun v => Φ v - f v) z ∂volume)
      = ENNReal.ofReal (s ^ 2) * residualBallAverage F Φ f s := by
        rw [residualBallAverage, ← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul]
    _ ≤ ENNReal.ofReal (s ^ 2) * M := by gcongr

/-! ### The marked residual maximal function -/

/-- `M(ρ(Φ − φ_m))` for the marked construction: the maximal function of the specific-energy
density of the residual between the marked limit and the concrete stage-`m` block
interpolant. -/
noncomputable def markedResidualMaximal (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment) : ℝ≥0∞ :=
  residualBallMaximal (decode ω.1) (markedPotential ms ω) (phi (decode ω.1) ω.2 m)

/-- The almost-sure form of `s:eq:residualchoice`: almost surely some nonzero stage makes the
residual maximal function arbitrarily small. -/
def MarkedResidualMaximalVanishes (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ m : ℕ, m ≠ 0 ∧ markedResidualMaximal ms m ω < ε

/-- Convergence in probability of the residual maximal functions to zero. -/
def MarkedResidualMaximalSmall (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ lam : ℝ≥0∞, 0 < lam →
    Tendsto
      (fun m : ℕ =>
        (ν.prod gridLaw) {ω : MarkedEnvironment | lam < markedResidualMaximal ms m ω})
      atTop (𝓝 0)

/-- **OPEN INPUT (`s:eq:maximal` for the residual density).**  The manuscript's weak-`L¹`
maximal inequality, applied to the specific-energy density of the residual `φ_m − Φ`: with a
single finite constant `C`, valid at every stage and every level,

`P[M(ρ(φ_m − Φ)) > λ] ≤ (C/λ) · E[ρ(φ_m − Φ)]`.

The project proves exactly this display for marked densities with `C = 512`
(`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le`,
`Spatial/SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity`) and instantiates it
at the rooted (FE) density from `s:eq:MTP` and the finite (FE) moment
(`Spatial/SpatialMaximalForFiniteEnergy.ae_ballMaximal_rootFE_lt_top`).  Instantiating it here
requires translation covariance and joint measurability of the residual density; see the
module docstring.  The constant is existential, so this is weaker than fixing `C = 512`. -/
def MarkedResidualWeakMaximal (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (m : ℕ) (lam : ℝ≥0∞), 0 < lam →
    (ν.prod gridLaw) {ω : MarkedEnvironment | lam < markedResidualMaximal ms m ω}
      ≤ C / lam *
        ∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw

/-! ### `s:eq:smallresidual` from the maximal function -/

/-- **`MarkedSmallBlockResidual` from the a.s. vanishing of the residual maximal function.**
The block-interpolant half costs nothing: the concrete `phi` is an actual block interpolant at
every stage almost surely, from `s:eq:MTP` and the finite (FE) moment alone. -/
theorem markedSmallBlockResidual_of_maximalVanishes (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hvan : MarkedResidualMaximalVanishes ν ms) :
    MarkedSmallBlockResidual ν ms := by
  have hblock := ae_blockInterpolation_clause ν hν hFE.ne
    (spatialMaximalBound_of_massTransport ν hν hFE)
  have key : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      SmallBlockResidual (decode ω.1) ω.2 (markedPotential ms ω) := by
    filter_upwards [hblock, hvan] with ω hb hr
    intro ε hε
    obtain ⟨m, hm0, hm⟩ := hr ε hε
    refine ⟨m, hm0, phi (decode ω.1) ω.2 m, (hb.2 m).1, markedResidualMaximal ms m ω, hm,
      fun s hs => ?_⟩
    exact setLIntegral_le_of_residualBallMaximal_le (decode ω.1) (markedPotential ms ω)
      (phi (decode ω.1) ω.2 m) le_rfl hs
  exact key

/-- **From convergence in probability to the almost-sure statement**, by the first
Borel–Cantelli lemma along a stage sequence chosen independently of the environment. -/
theorem markedResidualMaximalVanishes_of_small (ν : Measure Env) (ms : ℕ → ℕ)
    (h : MarkedResidualMaximalSmall ν ms) : MarkedResidualMaximalVanishes ν ms := by
  have hhalf : ((2 : ℝ≥0∞))⁻¹ ≠ 0 := by simp
  have hone : ((2 : ℝ≥0∞))⁻¹ < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have hpos : ∀ k : ℕ, (0 : ℝ≥0∞) < ((2 : ℝ≥0∞))⁻¹ ^ k := fun k =>
    lt_of_le_of_ne zero_le (Ne.symm (pow_ne_zero k hhalf))
  have hchoice : ∀ k : ℕ, ∃ m : ℕ, m ≠ 0 ∧
      (ν.prod gridLaw) {ω : MarkedEnvironment |
          ((2 : ℝ≥0∞))⁻¹ ^ k < markedResidualMaximal ms m ω} ≤ ((2 : ℝ≥0∞))⁻¹ ^ k := by
    intro k
    have hev : ∀ᶠ m : ℕ in atTop,
        (ν.prod gridLaw) {ω : MarkedEnvironment |
            ((2 : ℝ≥0∞))⁻¹ ^ k < markedResidualMaximal ms m ω} < ((2 : ℝ≥0∞))⁻¹ ^ k :=
      (h _ (hpos k)).eventually (gt_mem_nhds (hpos k))
    obtain ⟨m, hm1, hm2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    exact ⟨m, by omega, hm1.le⟩
  choose mk hmk0 hmk using hchoice
  have hgeo : (∑' k : ℕ, ((2 : ℝ≥0∞))⁻¹ ^ k) ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    simp only [ne_eq, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
    exact hone
  have hsum : (∑' k : ℕ, (ν.prod gridLaw) {ω : MarkedEnvironment |
      ((2 : ℝ≥0∞))⁻¹ ^ k < markedResidualMaximal ms (mk k) ω}) ≠ ∞ :=
    ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum hmk)
  have hlim : Tendsto (fun k : ℕ => ((2 : ℝ≥0∞))⁻¹ ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hone
  have key : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ m : ℕ, m ≠ 0 ∧ markedResidualMaximal ms m ω < ε := by
    filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with ω hω ε hε
    obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually (gt_mem_nhds hε)).and hω).exists
    have hk2' : ¬ ((2 : ℝ≥0∞))⁻¹ ^ k < markedResidualMaximal ms (mk k) ω := hk2
    exact ⟨mk k, hmk0 k, lt_of_le_of_lt (not_lt.1 hk2') hk1⟩
  exact key

/-- **Convergence in probability from `s:eq:maximal` and `s:eq:limitnorm`.**  The mean residual
specific energies tend to zero (`MarkedSpecificEnergyConvergence`, already an input of the
assembly), so the weak-`L¹` maximal bound makes the residual maximal functions tend to zero in
probability. -/
theorem markedResidualMaximalSmall_of_weakMaximal (ν : Measure Env) (ms : ℕ → ℕ)
    (hmax : MarkedResidualWeakMaximal ν ms) (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedResidualMaximalSmall ν ms := by
  obtain ⟨C, hC, hbound⟩ := hmax
  intro lam hlam
  have hdiv : C / lam ≠ ∞ := (ENNReal.div_lt_top hC hlam.ne').ne
  have hlim : Tendsto
      (fun m : ℕ => C / lam *
        ∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := C / lam) hspec.2 (Or.inr hdiv)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun m => hbound m lam hlam)

/-- **`s:eq:smallresidual` from `s:eq:maximal` for the residual density.** -/
theorem markedSmallBlockResidual_of_weakMaximal (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmax : MarkedResidualWeakMaximal ν ms) (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedSmallBlockResidual ν ms :=
  markedSmallBlockResidual_of_maximalVanishes ν hν hFE ms
    (markedResidualMaximalVanishes_of_small ν ms
      (markedResidualMaximalSmall_of_weakMaximal ν ms hmax hspec))

/-! ### `hsub` gone: the assembly with the residual replaced by the maximal inequality -/

/-- **`MarkedCentroidSublinearity` (`hsub`) discharged from the maximal inequality.**  The
centroid half of `s:eq:sublinear` for the marked limit, from full-rectangle minimality, the
weak-`L¹` maximal bound for the residual density, `s:eq:limitnorm`, the quadratic geometric
mass bound, and the manuscript's own environment hypotheses. -/
theorem markedCentroidSublinearity_of_weakMaximal (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hharm : MarkedHarmonicity ν ms)
    (hmass : MarkedGeometricMassQuadratic ν) (hmax : MarkedResidualWeakMaximal ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedCentroidSublinearity ν ms :=
  markedCentroidSublinearity_of_smallBlockResidual ν hν hFE.ne ms hharm hmass
    (markedSmallBlockResidual_of_weakMaximal ν hν hFE ms hmax hspec)

end ReflectedGMS.SmallBlockResidualProducer
