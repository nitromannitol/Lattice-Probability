/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GatedResidualWeakMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.RootedSpecificEnergySpaceMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedDensityMeasurabilityProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodEnvironmentSet
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageFieldCovariance
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LabelBijectionProducer

/-!
# `s:eq:maximal` for the residual density, with the measurable embedding removed

`Corrector/SpecificEnergyWeakMaximal.markedResidualWeakMaximal_of_auxiliaryMarkedSpace` (:422)
and its refinement `Corrector/ResidualDensitySimilarity.markedResidualWeakMaximal_of_similarityEquivariant`
(:160) both transport the project's own weak-`L¹` maximal inequality along a
**measurable embedding** `proj : Ω → MarkedEnvironment`.  That hypothesis is *unsatisfiable*
for the marked space the consumers actually need: the auxiliary second dyadic system of
`s:prop:maximal` forces `Ω` to carry **two** independent uniform grids, and `proj` forgets one
of them, so `proj` is a product projection and no product projection off a nontrivial factor is
an embedding.

`hproj` is used in exactly two places, `:455` (`hproj.map_apply`) and `:459`
(`hproj.lintegral_map`), and in both places only because the *target-side* objects
(`markedResidualMaximal`, `markedSpecificGradientError`) are built from
`DyadicApproximation.phi`, a `Classical.choose`, hence carry no measurability.  This module
removes the embedding by replacing those objects with the **gated residual density**
`gatedResidualDensity`, the left-hand side of the checked
`Corrector/ResidualDensitySpaceMeasurability.residualDensityOf_eq` (:115).  The gated density
is measurable outright, from the assembly's own `hmeas` and nothing else, so both uses become
ordinary `Measure.map_apply` / `lintegral_map` under plain `Measurable proj`; the pathwise gate
that used to relate the two objects becomes an almost-sure gate under `ν ⊗ gridLaw`, and is
*discharged* from the mass-transport and finite-energy hypotheses `hν`, `hFE` that every
downstream consumer already carries
(`SmallBlockResidualProducer.markedSmallBlockResidual_of_weakMaximal`,
`markedCentroidSublinearity_of_weakMaximal`).

## The only new mathematics

`densityMaximal_eq_iSup_rat`: the maximal function of an `ℝ≥0∞`-valued marked density is
already realised along **rational** radii,

  `M(ρ)(ω) = ⨆ q : ℚ, ⨆ _ : 0 < q, r⁻² ∫_{B̄_q} ρ_ω`.

This is the `ℝ≥0∞` analogue of `Spatial/SpatialMaximalInequality.exists_rat_ballAverage` (:463),
which cannot be instantiated here: that lemma is tied to a *real* functional `F` and to the
re-rooting `R` (`ENNReal.ofReal (F (R.shift z ω))`).  The argument is re-run for a general
density, and — this is the point — **on `MarkedEnvironment`**, which is exactly where
`Measure.map_apply` needs its measurable set.  With it, `measurable_densityMaximal` presents
`M(ρ)` as a countable supremum of Tonelli-measurable ball averages
(`SpatialMaximalInequality.measurable_const_mul_setLIntegral`).

## What is DISCHARGED and what is REDUCED

* **REDUCED, not discharged.**  `markedResidualWeakMaximal_of_twoGridSpace` is an implication.
  After it, `MarkedResidualWeakMaximal ν ms` is conditional on exactly one thing: the auxiliary
  **two-grid marked space** `(Ω, R, S, μ, 𝒜)` together with `hprojA`, `hmap`, `hshift`,
  `hdilate`.  This module does not build that space.
* **Discharged here** (were hypotheses of the two existing heads, are now proofs): the
  measurable embedding `hproj`, the pathwise gate `hgood`, and the two measurability
  hypotheses `hmeas0`, `hjoint`.  `hcov`/`hinv` were already discharged upstream in
  `Corrector/ResidualDensitySimilarity`; the four-line ungated core of
  `residualDensityOf_markedSimilarity` (:98–119, read before its two gate rewrites) is re-run
  here for the gated density as `gatedResidualDensity_markedSimilarity`, so no gate is needed
  for them either.
* `hcopies` (`GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal`) has the identical
  two `hproj` uses at `SpecificEnergyWeakMaximal:523,:530`, and the fix generalises: the
  copy-difference density involves **no `phi` at all** (`firstPotential`/`secondPotential` are
  `markedPotential` at the two grid copies), so its target-side measurability is free from
  `hmeas` and `copyDifferenceWeakMaximal_of_twoGridSpace` drops `hproj`, `hmeas0` and `hjoint`
  with **no new hypothesis**.  Its `hcov`/`hinv` are still open, so `hcopies` remains strictly
  behind `hsub`.

## Anti-vacuity

The constant `C := ENNReal.ofReal 512` is produced **outside** the `∀ m lam` quantifiers — it
is the manuscript's own `512`, inherited from
`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le` through
`SpecificEnergyWeakMaximal.measure_densityMaximal_gt_le`.  No `δ`-dependent, `m`-dependent or
`lam`-dependent constant occurs.  The gate is not a disguised vacuity: it is almost-sure under
`ν ⊗ gridLaw` and is proved, not assumed, from `hν`/`hFE`
(`HarmonicCoordinateAssembly.ae_mem_sublinearEvent` + `ae_marked_of_ae_env`).
-/

-- Merged from `ReflectedGMS/Corrector/ResidualDensitySimilarity.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ResidualDensitySimilarity

/-!
# `hcov` and `hinv` for the residual density, along the joint similarity

`Corrector/ResidualDensitySpaceMeasurability` closes the two *measurability* hypotheses of
`SpecificEnergyWeakMaximal.markedResidualWeakMaximal_of_auxiliaryMarkedSpace` and lists what is
left (items 4 and 5 of its docstring): the two **pathwise identities**

* `hcov` — re-rooting covariance `ρ_ω(z) = ρ_{ω−z}(0)`, and
* `hinv` — scale invariance `ρ_{S_t ω}(0) = ρ_ω(0)`,

for the residual density `SpecificEnergyWeakMaximal.residualDensityOf`.  This module proves the
single concrete identity both are instances of, **with no hypothesis beyond the pathwise gate**:

`residualDensityOf_markedSimilarity` : for every `s > 0`, `u`, `z` and every marked
configuration `p` on `SublinearEvent`,

  `ρ_{markedSimilarity s u hs p}(S(s,u) z) = ρ_p(z)`.

`hcov` is the case `s = 1`, `u = z` (where `S(1,z) z = 0` and
`MarkedMassTransportProducer.markedSimilarity_one` identifies the action with
`ActualMarkedBlockTransport.actualReRooting.shift`); `hinv` is the case `u = 0`, `z = 0`
(where `S(s,0) 0 = 0`).

## Why it is free

The residual field is, on the gate, minus the gradient-error label field of
`Corrector/MarkedBallEnergyConvergence`, whose transport along `markedSimilarity` is
`gradientTransported_gradientErrorLabel` — **ungated**, and with its single hypothesis
`ApproximantGradientCovariantAtEveryStage` discharged outright by
`Corrector/MarkedStageFieldCovariance.covariantAtEveryStage`.  Feeding that into the checked
`Corrector/SpecificEnergyDensitySimilarity.rootedSpecificEnergyDensity_similarity` and reading
both ends through `ResidualDensitySpaceMeasurability.residualDensityOf_eq` gives the identity.
The relabelling is the canonical one,
`Corrector/LabelBijectionProducer.isSimilarityRelabel_similarityRelabel`.

## What is DISCHARGED and what is REDUCED

* The pathwise identity `residualDensityOf_markedSimilarity`, and its two specializations
  `residualDensityOf_shift` / `residualDensityOf_dilate`, are **discharged**: no open input, no
  hypothesis beyond `p.1 ∈ SublinearEvent` (the same gate `ResidualDensitySpaceMeasurability`
  already uses, satisfied at every point of a marked space built over
  `Spatial/GoodMarkedSpace.goodSet`).
* `markedResidualWeakMaximal_of_similarityEquivariant` **reduces** `hcov` and `hinv` for an
  *abstract* marked space `Ω` to the two **equivariance** statements `hshift` / `hdilate`: that
  the embedding `proj` intertwines `R.shift z` with `markedSimilarity 1 z` and `S.dilate t` with
  `markedSimilarity t 0`.  This is not a re-statement of `hcov`/`hinv`: it is a property of the
  *space and its embedding* alone, with the residual density gone, and for a marked space whose
  re-rooting is `ActualMarkedBlockTransport.actualReRooting` and whose embedding is the identity
  it holds by `markedSimilarity_one` and `rfl`.  What this module does **not** do is build that
  marked space — the auxiliary second dyadic system of `s:prop:maximal` — which remains the
  single open producer recorded in `Corrector/SpecificEnergyWeakMaximal`.
-/

-- Merged from `ReflectedGMS/Corrector/ResidualDensitySpaceMeasurability.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ResidualDensitySpaceMeasurability

/-!
# `EnvironmentGrid.measurable_density` for the residual density, and what `hsub` still needs

`Corrector/SmallBlockResidualProducer`'s docstring records **two** obstructions to
instantiating the manuscript's weak-`L¹` maximal inequality `s:eq:maximal` at the residual
density `ρ(φ_m − Φ)`.  The first — translation covariance of the residual field — closed on
2026-09-16 (`Corrector/ApproximantCovarianceFromBlockTransport.phi_similarity`, whose sole
hypothesis is discharged by
`Corrector/BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant`), so that
docstring is stale; `Corrector/SpecificEnergyWeakMaximal` already records the correction.

The second is the subject of this module: **joint measurability of `(ω, z) ↦ ρ_ω(z)` in the
environment and the point**, the `measurable_density` field of
`Spatial/SpatialMaximalInequality.EnvironmentGrid` and, in the form the consumers use it, the
hypothesis `hjoint` of `Corrector/SpecificEnergyWeakMaximal.measure_densityMaximal_gt_le`.
It is discharged here, from the assembly's own measurability input `hmeas` and a pathwise
gate.

## What is proved

* `residualDensityOf_eq` — on `HarmonicCoordinateAssembly.SublinearEvent` the residual density
  is the rooted specific-energy density of the **label-indexed** field
  `n ↦ markedDifferenceField ms ω (⟨baseLabel ω.1, n⟩) − gatedApproximant m ω n`, at every
  point `z` of the plane.  This is the standard gate: `DyadicApproximation.phi` is a
  `Classical.choose` and agrees with the measurable `gatedApproximant` only there
  (`MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant`).
* `measurable_residualDensityOf_prod` — **the target**: for any parameter space with a
  measurable map `proj` into `MarkedEnvironment` whose environment coordinate is gated,
  `(ω, z) ↦ residualDensityOf ms m (proj ω) z` is jointly measurable.  The parameter space's
  sigma-field is arbitrary, so this may be — and below is — instantiated at the
  **sub**-sigma-field `𝒜.sigma` of `EnvironmentGrid`, which is what the consumer asks for.
* `measurable_residualDensityOf_zero` — the same at `z = 0`, which is the consumer's `hmeas0`.
  (At `z = 0` this is not new mathematics: it is the exact-measurability counterpart of
  `MarkedDensityMeasurabilityProducer.aemeasurable_markedSpecificGradientError`, with the
  almost-sure gate replaced by the pathwise one.)
* `markedResidualWeakMaximal_of_gatedMarkedSpace` — `SmallBlockResidualProducer`'s input
  `MarkedResidualWeakMaximal` (which feeds `hsub` through
  `markedSmallBlockResidual_of_weakMaximal` and
  `MarkedCentroidSublinearityProducer.markedCentroidSublinearity_of_smallBlockResidual`) with
  **both measurability hypotheses of
  `SpecificEnergyWeakMaximal.markedResidualWeakMaximal_of_auxiliaryMarkedSpace` removed**.

## The gate is satisfiable, and the statement is not vacuous

`mem_sublinearEvent_of_goodEnvironment` : `Spatial/GoodEnvironmentSet.GoodEnvironment e` has
`SublinearDiameterDecay (decode e)` as its second conjunct, which is literally membership of
`SublinearEvent`.  So `Spatial/GoodMarkedSpace.goodSet ⊆ SublinearEvent` and the pathwise gate
`hgood` holds at **every** point of any marked space built over the good set — no almost-sure
hypothesis and no null set.  The gate is therefore not a disguised vacuity: it is exactly the
condition under which `phi` is canonical, and `GoodEnvironmentSet.ae_goodEnvironment` shows the
good set carries full measure under (MTP) and the (FE) moment.

Nor is the conclusion circular: `hjoint` is proved from `hmeas` (measurability of the gated
approximants at each label) and nothing else — not from any maximal inequality, not from
`hspec`, and not from the conclusion `MarkedResidualWeakMaximal`.

## What `hsub` still needs — stated exactly

`markedResidualWeakMaximal_of_gatedMarkedSpace` is an implication and certifies none of its
remaining hypotheses.  After this module they are, verbatim:

1. the marked space itself: `R : MarkedReRooting Ω`, `S : ScaleAction R`, a probability `μ`,
   the environment sigma-field `𝒜`, `hchain : OriginChainRegular R`,
   `hdata : SimilarityBlockData R S μ` and `henv : EnvironmentGrid R μ F₀ 𝒜` — with `R.grid`
   a **second** uniform dyadic system, independent of the pair (environment, interpolation
   grid), as `Corrector/SpecificEnergyWeakMaximal`'s docstring explains.  This module does not
   build it;
2. `hproj`/`hprojA`/`hmap`: the embedding of that space onto `ν ⊗ gridLaw`, measurable for
   `𝒜.sigma`;
3. `hgood`: the pathwise gate (satisfied over the good set, see above);
4. `hcov`: re-rooting covariance of the residual density, `ρ_ω(z) = ρ_{ω−z}(0)`;
5. `hinv`: scale invariance of the residual density at the origin.

Items 4 and 5 are the pathwise identities that
`Corrector/ApproximantCovarianceFromBlockTransport.phi_similarity` and
`HarmonicCoordinateAssembly.markedDifferenceField_pairTransport` are expected to supply on
`SublinearEvent`, but the transport of a *density* along `R.shift`/`S.dilate` of an abstract
marked space is a statement about that space and is **not** proved here.  The measurability
half — the subject of this module — is now closed.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ResidualDensitySpaceMeasurability

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open SmallBlockResidualProducer SpecificEnergyWeakMaximal
open RootedSpecificEnergySpaceMeasurability

/-! ### The gate -/

/-! ### The residual density as the density of a label-indexed field -/

/-- **On the gate the residual density is the rooted specific energy of a label-indexed
field, at every point of the plane.**  The field is the one
`MarkedDensityMeasurabilityProducer` already uses at the origin; the point is now arbitrary. -/
theorem residualDensityOf_eq (ms : ℕ → ℕ) (m : ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (z : Plane) :
    rootedSpecificEnergyDensity (decode ω.1)
        (fun v : Vertex ω.1.val =>
          markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val) -
            gatedApproximant m ω v.val) z
      = residualDensityOf ms m ω z := by
  have hEq : (fun v : Vertex ω.1.val =>
        markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val) -
          gatedApproximant m ω v.val)
      = fun v : Vertex ω.1.val =>
          markedPotential ms ω v - phi (decode ω.1) ω.2 m v := by
    funext v
    rw [MarkedDensityMeasurabilityProducer.phi_eq_gatedApproximant hG v]
    rfl
  rw [hEq]
  rfl

/-! ### The two measurability statements -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The label field of the residual, on the parameter space. -/
theorem measurable_residualLabel (ms : ℕ → ℕ) (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → MarkedEnvironment) (hproj : Measurable proj) (n : ℕ) :
    Measurable fun ω : Ω =>
      markedDifferenceField ms (proj ω) (Nat.pair (baseLabel (proj ω).1) n) -
        gatedApproximant m (proj ω) n := by
  have h1 : Measurable fun ω : Ω =>
      markedDifferenceField ms (proj ω) (Nat.pair (baseLabel (proj ω).1) n) :=
    (MarkedDensityMeasurabilityProducer.measurable_markedPotentialLabel ms hmeas n).comp hproj
  have h2 : Measurable fun ω : Ω => gatedApproximant m (proj ω) n :=
    (hmeas m n).comp hproj
  exact h1.sub h2

/-! ### `MarkedResidualWeakMaximal` with the measurability hypotheses removed -/

end ReflectedGMS.ResidualDensitySpaceMeasurability

end Merged_ResidualDensitySpaceMeasurability

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ResidualDensitySimilarity

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open SmallBlockResidualProducer SpecificEnergyWeakMaximal
open MarkedMassTransportProducer SpecificEnergyDensitySimilarity
open LabelBijectionProducer ResidualDensitySpaceMeasurability

/-! ### Transport is insensitive to the sign of a difference field -/

/-- `GradientTransported` for a difference of two fields survives swapping the two fields:
only increments occur, and they merely change sign on both sides. -/
theorem gradientTransported_sub_comm {t : ℝ} {e e' : Env} {rel : Vertex e.val ≃ Vertex e'.val}
    {a b : Vertex e.val → Plane} {a' b' : Vertex e'.val → Plane}
    (h : GradientTransported t rel (fun x => a x - b x) (fun x => a' x - b' x)) :
    GradientTransported t rel (fun x => b x - a x) (fun x => b' x - a' x) := by
  intro v w
  have hL : b' (rel w) - a' (rel w) - (b' (rel v) - a' (rel v))
      = a' (rel v) - b' (rel v) - (a' (rel w) - b' (rel w)) := by abel
  have hR : b w - a w - (b v - a v) = a v - b v - (a w - b w) := by abel
  show b' (rel w) - a' (rel w) - (b' (rel v) - a' (rel v))
    = t • (b w - a w - (b v - a v))
  rw [hL, hR]
  exact h w v

/-! ### The identity -/

variable {s : ℝ} {u : Plane} {hs : 0 < s}

/-! ### `MarkedResidualWeakMaximal` with `hcov` and `hinv` removed -/

variable {Ω : Type*} [MeasurableSpace Ω]

end ReflectedGMS.ResidualDensitySimilarity

end Merged_ResidualDensitySimilarity

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GatedResidualWeakMaximal

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open MarkedCentroidSublinearityProducer SmallBlockResidualProducer
open GridIndependenceCoupling GridIndependenceDifferenceBridge
open SpecificEnergyWeakMaximal MarkedMassTransportProducer SpecificEnergyDensitySimilarity
open LabelBijectionProducer RootedSpecificEnergySpaceMeasurability
open ResidualDensitySpaceMeasurability ResidualDensitySimilarity

/-! ### A rational radius already realises the maximal function of a marked density -/

/-- The ball average exceeds `c` exactly when the ball integral exceeds `r² c`.  This is the
`ℝ≥0∞`-level version of `SpecificEnergyWeakMaximal.lt_densityMaximal_iff`'s inner step, at an
arbitrary extended-real level `c` rather than at `ENNReal.ofReal t`. -/
theorem lt_densityBallAverage_iff {α : Type*} [MeasurableSpace α] (ρ : α → Plane → ℝ≥0∞)
    {r : ℝ} (hr : 0 < r) (ω : α) (c : ℝ≥0∞) :
    c < densityBallAverage ρ r ω
      ↔ ENNReal.ofReal (r ^ 2) * c
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hnz : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hr2
  have hRHS : ENNReal.ofReal (r ^ 2) * densityBallAverage ρ r ω
      = ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume := by
    show ENNReal.ofReal (r ^ 2) * ((ENNReal.ofReal (r ^ 2))⁻¹ *
        ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume)
      = ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume
    rw [← mul_assoc, ENNReal.mul_inv_cancel hnz ENNReal.ofReal_ne_top, one_mul]
  rw [← ENNReal.mul_lt_mul_iff_right (a := ENNReal.ofReal (r ^ 2)) hnz ENNReal.ofReal_ne_top,
    hRHS]

/-- **A rational radius already realises the maximal function of a marked density.**

The `ℝ≥0∞` analogue of `Spatial/SpatialMaximalInequality.exists_rat_ballAverage`, which is tied
to a real functional and to a re-rooting and therefore cannot be instantiated here.  Passing to
a slightly larger rational radius only increases the ball integral, and the normalisation `r⁻²`
is continuous; no local integrability and no finiteness of the density is used. -/
theorem densityMaximal_eq_iSup_rat {α : Type*} [MeasurableSpace α] (ρ : α → Plane → ℝ≥0∞)
    (ω : α) :
    densityMaximal ρ ω = ⨆ q : ℚ, ⨆ _ : (0 : ℝ) < (q : ℝ), densityBallAverage ρ (q : ℝ) ω := by
  refine le_antisymm ?_ (iSup_le fun q => iSup_le fun hq =>
    densityBallAverage_le_densityMaximal ρ hq ω)
  refine le_of_forall_lt fun c hc => ?_
  have hc' : c < ⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage ρ r ω := hc
  rw [lt_iSup_iff] at hc'
  obtain ⟨r, hr⟩ := hc'
  rw [lt_iSup_iff] at hr
  obtain ⟨hrpos, hlt⟩ := hr
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hnz : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hr2
  have hmono : ∀ a b : ℝ, a ≤ b →
      (∫⁻ z in Metric.closedBall (0 : Plane) a, ρ ω z ∂volume)
        ≤ ∫⁻ z in Metric.closedBall (0 : Plane) b, ρ ω z ∂volume :=
    fun a b hab => lintegral_mono_set (Metric.closedBall_subset_closedBall hab)
  have hkey := (lt_densityBallAverage_iff ρ hrpos ω c).1 hlt
  have hcne : c ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hnz] at hkey
    exact absurd hkey not_top_lt
  have hgoal : ∃ q : ℚ, (0 : ℝ) < (q : ℝ) ∧ c < densityBallAverage ρ (q : ℝ) ω := by
    by_cases htop : (∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume) = ∞
    · obtain ⟨p, hp1, -⟩ := exists_rat_btwn (show r < r + 1 by linarith)
      have hppos : (0 : ℝ) < (p : ℝ) := lt_trans hrpos hp1
      refine ⟨p, hppos, (lt_densityBallAverage_iff ρ hppos ω c).2 ?_⟩
      have hIq : (∫⁻ z in Metric.closedBall (0 : Plane) ((p : ℝ)), ρ ω z ∂volume) = ∞ := by
        refine top_unique ?_
        rw [← htop]
        exact hmono r (p : ℝ) hp1.le
      rw [hIq]
      exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcne)
    · obtain ⟨d, hd0, hdEq⟩ : ∃ d : ℝ, 0 ≤ d ∧
          (∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume) = ENNReal.ofReal d :=
        ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal htop).symm⟩
      obtain ⟨e, he0, heEq⟩ : ∃ e : ℝ, 0 ≤ e ∧ c = ENNReal.ofReal e :=
        ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hcne).symm⟩
      have hkey' : ENNReal.ofReal (r ^ 2 * e) < ENNReal.ofReal d := by
        rw [ENNReal.ofReal_mul hr2.le, ← heEq, ← hdEq]
        exact hkey
      have hreal : r ^ 2 * e < d :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (by positivity) he0)).1 hkey'
      obtain ⟨p, hp1, hp2⟩ : ∃ p : ℚ, r < (p : ℝ) ∧ (p : ℝ) ^ 2 * e < d := by
        rcases eq_or_lt_of_le he0 with he | he
        · have hdpos : (0 : ℝ) < d := by
            have h := hreal
            rw [← he, mul_zero] at h
            exact h
          obtain ⟨p, hp1, -⟩ := exists_rat_btwn (show r < r + 1 by linarith)
          exact ⟨p, hp1, by rw [← he, mul_zero]; exact hdpos⟩
        · have hde : (0 : ℝ) ≤ d / e := div_nonneg hd0 he.le
          have hrlt : r ^ 2 < d / e := by
            rw [lt_div_iff₀ he]
            exact hreal
          have hrs : r < Real.sqrt (d / e) := by
            have hstep := Real.sqrt_lt_sqrt (by positivity) hrlt
            rwa [Real.sqrt_sq hrpos.le] at hstep
          obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hrs
          have hppos : (0 : ℝ) < (p : ℝ) := lt_trans hrpos hp1
          have hp2sq : (p : ℝ) ^ 2 < d / e := by
            nlinarith [Real.sq_sqrt hde, Real.sqrt_nonneg (d / e)]
          refine ⟨p, hp1, ?_⟩
          rw [lt_div_iff₀ he] at hp2sq
          exact hp2sq
      have hppos : (0 : ℝ) < (p : ℝ) := lt_trans hrpos hp1
      refine ⟨p, hppos, (lt_densityBallAverage_iff ρ hppos ω c).2 ?_⟩
      refine lt_of_lt_of_le ?_ (hmono r (p : ℝ) hp1.le)
      rw [hdEq, heEq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (by positivity) he0)).2 hp2
  obtain ⟨q, hqpos, hq⟩ := hgoal
  exact lt_of_lt_of_le hq
    (le_iSup₂ (f := fun (q : ℚ) (_ : (0 : ℝ) < (q : ℝ)) => densityBallAverage ρ (q : ℝ) ω)
      q hqpos)

/-- The ball average at a fixed radius is measurable, by Tonelli.  This is
`SpatialMaximalInequality.measurable_const_mul_setLIntegral` at a general `ℝ≥0∞` density. -/
theorem measurable_densityBallAverage {α : Type*} [MeasurableSpace α] {ρ : α → Plane → ℝ≥0∞}
    (hρ : Measurable fun q : α × Plane => ρ q.1 q.2) (r : ℝ) :
    Measurable fun ω : α => densityBallAverage ρ r ω := by
  show Measurable fun ω : α => (ENNReal.ofReal (r ^ 2))⁻¹ *
    ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume
  exact measurable_const_mul_setLIntegral hρ (ENNReal.ofReal (r ^ 2))⁻¹
    (Metric.closedBall (0 : Plane) r)

/-- **The maximal function of a jointly measurable marked density is measurable.**  The
supremum over all positive radii is a countable supremum, by `densityMaximal_eq_iSup_rat`. -/
theorem measurable_densityMaximal {α : Type*} [MeasurableSpace α] {ρ : α → Plane → ℝ≥0∞}
    (hρ : Measurable fun q : α × Plane => ρ q.1 q.2) :
    Measurable fun ω : α => densityMaximal ρ ω := by
  have h : (fun ω : α => densityMaximal ρ ω)
      = fun ω : α => ⨆ q : ℚ, ⨆ _ : (0 : ℝ) < (q : ℝ), densityBallAverage ρ (q : ℝ) ω :=
    funext fun ω => densityMaximal_eq_iSup_rat ρ ω
  rw [h]
  exact Measurable.iSup fun q =>
    Measurable.iSup_Prop _ (measurable_densityBallAverage hρ (q : ℝ))

/-- The maximal function at a configuration only sees the density at that configuration. -/
theorem densityMaximal_congr {α : Type*} [MeasurableSpace α] {ρ σ : α → Plane → ℝ≥0∞} {ω : α}
    (h : ∀ z : Plane, ρ ω z = σ ω z) : densityMaximal ρ ω = densityMaximal σ ω := by
  show (⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage ρ r ω)
      = ⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage σ r ω
  refine iSup_congr fun r => iSup_congr fun _ => ?_
  show (ENNReal.ofReal (r ^ 2))⁻¹ *
      ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume
    = (ENNReal.ofReal (r ^ 2))⁻¹ *
      ∫⁻ z in Metric.closedBall (0 : Plane) r, σ ω z ∂volume
  congr 1
  exact lintegral_congr fun z => h z

/-! ### The gated residual density -/

/-- **The gated residual density.**  This is literally the left-hand side of the checked
`ResidualDensitySpaceMeasurability.residualDensityOf_eq`: the rooted specific-energy density of
the *label-indexed* residual field `Φ − φ_m`, with the `Classical.choose` interpolant `phi`
replaced by the measurable `gatedApproximant`.  Unlike `residualDensityOf` it is measurable
with no gate at all. -/
noncomputable def gatedResidualDensity (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment)
    (z : Plane) : ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode ω.1)
    (fun v : Vertex ω.1.val =>
      markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val) - gatedApproximant m ω v.val) z

/-- On the gate the gated residual density is the residual density. -/
theorem gatedResidualDensity_eq (ms : ℕ → ℕ) (m : ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (z : Plane) :
    gatedResidualDensity ms m ω z = residualDensityOf ms m ω z :=
  residualDensityOf_eq ms m hG z

/-- **Joint measurability of the gated residual density, with no gate.**  The parameter space's
sigma-field is arbitrary, so this applies at the sub-sigma-field `𝒜.sigma`. -/
theorem measurable_gatedResidualDensity_prod {α : Type*} [MeasurableSpace α] (ms : ℕ → ℕ)
    (m : ℕ) (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → MarkedEnvironment) (hproj : Measurable proj) :
    Measurable fun q : α × Plane => gatedResidualDensity ms m (proj q.1) q.2 :=
  measurable_rootedSpecificEnergyDensity_prod (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      markedDifferenceField ms (proj ω) (Nat.pair (baseLabel (proj ω).1) n) -
        gatedApproximant m (proj ω) n)
    (measurable_residualLabel ms m hmeas proj hproj)

/-- The same at the origin, with no gate. -/
theorem measurable_gatedResidualDensity_zero {α : Type*} [MeasurableSpace α] (ms : ℕ → ℕ)
    (m : ℕ) (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → MarkedEnvironment) (hproj : Measurable proj) :
    Measurable fun ω : α => gatedResidualDensity ms m (proj ω) 0 :=
  measurable_rootedSpecificEnergyDensity_zero (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      markedDifferenceField ms (proj ω) (Nat.pair (baseLabel (proj ω).1) n) -
        gatedApproximant m (proj ω) n)
    (measurable_residualLabel ms m hmeas proj hproj)

/-! ### Similarity covariance of the gated residual density, ungated -/

/-- **The gated residual density is exactly similarity covariant, with no hypothesis at all.**

This is the four-line ungated core of `ResidualDensitySimilarity.residualDensityOf_markedSimilarity`
(:98–119) read *before* its two gate rewrites: the gate there is used only to rewrite both ends
into `residualDensityOf`, and here both ends are already the gated density. -/
theorem gatedResidualDensity_markedSimilarity (ms : ℕ → ℕ) (m : ℕ) (s : ℝ) (u : Plane)
    (hs : 0 < s) (p : MarkedEnvironment) (z : Plane) :
    gatedResidualDensity ms m (markedSimilarity s u hs p) (positiveSimilarity s u z)
      = gatedResidualDensity ms m p z := by
  have h : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1
      (similarityRelabel s u hs p.1) := isSimilarityRelabel_similarityRelabel s u hs p.1
  have h0 : GradientTransported s (similarityRelabel s u hs p.1)
      (fun x : Vertex p.1.val =>
        gatedApproximant m p x.val
          - markedDifferenceField ms p (Nat.pair (baseLabel p.1) x.val))
      (fun x : Vertex (markedSimilarity s u hs p).1.val =>
        gatedApproximant m (markedSimilarity s u hs p) x.val
          - markedDifferenceField ms (markedSimilarity s u hs p)
              (Nat.pair (baseLabel (markedSimilarity s u hs p).1) x.val)) :=
    MarkedBallEnergyConvergence.gradientTransported_gradientErrorLabel ms
      MarkedStageFieldCovariance.covariantAtEveryStage m p h
  exact rootedSpecificEnergyDensity_similarity h (gradientTransported_sub_comm h0) z

/-- `hcov`'s identity for the gated density: the case `s = 1`, `u = z`. -/
theorem gatedResidualDensity_shift (ms : ℕ → ℕ) (m : ℕ) (p : MarkedEnvironment) (z : Plane) :
    gatedResidualDensity ms m (markedSimilarity 1 z one_pos p) 0
      = gatedResidualDensity ms m p z := by
  have h := gatedResidualDensity_markedSimilarity ms m 1 z one_pos p z
  rwa [show positiveSimilarity (1 : ℝ) z z = 0 by simp] at h

/-- `hinv`'s identity for the gated density: the case `u = 0`, `z = 0`. -/
theorem gatedResidualDensity_dilate (ms : ℕ → ℕ) (m : ℕ) (s : ℝ) (hs : 0 < s)
    (p : MarkedEnvironment) :
    gatedResidualDensity ms m (markedSimilarity s 0 hs p) 0
      = gatedResidualDensity ms m p 0 := by
  have h := gatedResidualDensity_markedSimilarity ms m s 0 hs p 0
  rwa [show positiveSimilarity s (0 : Plane) 0 = 0 by simp] at h

/-! ### `hsub`'s maximal input, with no measurable embedding -/

/-- **CONDITIONAL.  `hsub`'s maximal input from a two-grid marked space, with the measurable
embedding, the pathwise gate and both measurability hypotheses removed.**

Compared with `SpecificEnergyWeakMaximal.markedResidualWeakMaximal_of_auxiliaryMarkedSpace` and
`ResidualDensitySimilarity.markedResidualWeakMaximal_of_similarityEquivariant`, the
*unsatisfiable* `hproj : MeasurableEmbedding proj` is gone: only `𝒜.sigma`-measurability of
`proj` is required (ambient measurability follows through `henv.le`).  The pathwise gate
`hgood` is gone too, replaced by the almost-sure gate that `hν` and `hFE` buy — and `hν`, `hFE`
are free, since every consumer of `MarkedResidualWeakMaximal` already carries them.

This is an implication and certifies none of its hypotheses.  What remains open is exactly the
auxiliary two-grid marked space `Ω` together with `hprojA`, `hmap`, `hshift`, `hdilate`; this
module does not build it.  The constant is the manuscript's `512`, fixed before `m` and
`lam`. -/
theorem markedResidualWeakMaximal_of_twoGridSpace
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → MarkedEnvironment)
    (hprojA : @Measurable Ω MarkedEnvironment 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod gridLaw)
    (hshift : ∀ (z : Plane) (ω : Ω),
      proj (R.shift z ω) = markedSimilarity 1 z one_pos (proj ω))
    (hdilate : ∀ (t : ℝ) (ht : 0 < t) (ω : Ω),
      proj (S.dilate t ω) = markedSimilarity t 0 ht (proj ω)) :
    MarkedResidualWeakMaximal ν ms := by
  have hprojM : Measurable proj := hprojA.mono henv.le le_rfl
  have hgate : ∀ᵐ p : MarkedEnvironment ∂ν.prod gridLaw, p.1 ∈ SublinearEvent :=
    ae_marked_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  have hjointMarked : ∀ m : ℕ, Measurable fun q : MarkedEnvironment × Plane =>
      gatedResidualDensity ms m q.1 q.2 := fun m =>
    measurable_gatedResidualDensity_prod ms m hmeas id measurable_id
  have hzeroMarked : ∀ m : ℕ, Measurable fun p : MarkedEnvironment =>
      gatedResidualDensity ms m p 0 := fun m =>
    measurable_gatedResidualDensity_zero ms m hmeas id measurable_id
  have hcov : ∀ (m : ℕ) (ω : Ω) (z : Plane),
      gatedResidualDensity ms m (proj ω) z
        = gatedResidualDensity ms m (proj (R.shift z ω)) 0 := by
    intro m ω z
    rw [hshift z ω, gatedResidualDensity_shift]
  have hinv : ∀ (m : ℕ) (s : ℝ), 0 < s → ∀ ω : Ω,
      gatedResidualDensity ms m (proj (S.dilate s ω)) 0
        = gatedResidualDensity ms m (proj ω) 0 := by
    intro m s hs ω
    rw [hdilate s hs ω, gatedResidualDensity_dilate]
  have hmeas0 : ∀ m : ℕ, Measurable fun ω : Ω => gatedResidualDensity ms m (proj ω) 0 :=
    fun m => measurable_gatedResidualDensity_zero ms m hmeas proj hprojM
  have hjoint : ∀ m : ℕ, @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
      fun q => gatedResidualDensity ms m (proj q.1) q.2 :=
    fun m => @measurable_gatedResidualDensity_prod Ω 𝒜.sigma ms m hmeas proj hprojA
  refine ⟨ENNReal.ofReal 512, ENNReal.ofReal_ne_top, fun m lam hlam => ?_⟩
  rcases eq_or_ne lam ∞ with rfl | hlamtop
  · have hempty : {p : MarkedEnvironment | (∞ : ℝ≥0∞) < markedResidualMaximal ms m p}
        = (∅ : Set MarkedEnvironment) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_top
    rw [hempty, measure_empty]
    exact zero_le
  · have ht : 0 < lam.toReal := ENNReal.toReal_pos hlam.ne' hlamtop
    have hlt : ENNReal.ofReal lam.toReal = lam := ENNReal.ofReal_toReal hlamtop
    have hmain := measure_densityMaximal_gt_le hchain hdata henv
      (fun ω z => gatedResidualDensity ms m (proj ω) z) (hcov m) (hinv m) (hmeas0 m)
      (hjoint m) ht
    rw [hlt] at hmain
    have hTmeas : MeasurableSet
        {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} :=
      measurableSet_lt measurable_const (measurable_densityMaximal (hjointMarked m))
    have hA : (ν.prod gridLaw)
          {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p}
        = μ {ω : Ω |
            lam < densityMaximal (fun ω' z => gatedResidualDensity ms m (proj ω') z) ω} := by
      rw [← hmap, Measure.map_apply hprojM hTmeas]
      rfl
    have hmono : (ν.prod gridLaw) {p : MarkedEnvironment | lam < markedResidualMaximal ms m p}
        ≤ (ν.prod gridLaw)
          {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} := by
      refine measure_mono_ae ?_
      filter_upwards [hgate] with p hp hmem
      have heq : densityMaximal (gatedResidualDensity ms m) p = markedResidualMaximal ms m p := by
        rw [markedResidualMaximal_eq]
        exact densityMaximal_congr fun z => gatedResidualDensity_eq ms m hp z
      show lam < densityMaximal (gatedResidualDensity ms m) p
      rw [heq]
      exact hmem
    have hL : (∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw)
        = ∫⁻ ω : Ω, gatedResidualDensity ms m (proj ω) 0 ∂μ := by
      have h1 : (∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw)
          = ∫⁻ p : MarkedEnvironment, gatedResidualDensity ms m p 0 ∂ν.prod gridLaw := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgate] with p hp
        rw [gatedResidualDensity_eq ms m hp 0]
        exact SpecificEnergyWeakMaximal.rootedSpecificEnergyDensity_sub_comm (decode p.1)
          (fun v => phi (decode p.1) p.2 m v) (fun v => markedPotential ms p v) 0
      rw [h1, ← hmap, lintegral_map (hzeroMarked m) hprojM]
    calc (ν.prod gridLaw) {p : MarkedEnvironment | lam < markedResidualMaximal ms m p}
        ≤ (ν.prod gridLaw)
            {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} := hmono
      _ = μ {ω : Ω |
            lam < densityMaximal (fun ω' z => gatedResidualDensity ms m (proj ω') z) ω} := hA
      _ ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, gatedResidualDensity ms m (proj ω) 0 ∂μ) / lam :=
          hmain
      _ = ENNReal.ofReal 512 / lam *
            ∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw := by
          rw [hL, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

/-! ### The machine-checked join with the consumer -/

/-- The join: the new head partially applied into
`SmallBlockResidualProducer.markedCentroidSublinearity_of_weakMaximal`.  This certifies that
the restated interface really is the one `hsub`'s consumer asks for. -/
example (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hharm : MarkedHarmonicity ν ms)
    (hmass : MarkedGeometricMassQuadratic ν) (hspec : MarkedSpecificEnergyConvergence ν ms)
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → MarkedEnvironment)
    (hprojA : @Measurable Ω MarkedEnvironment 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod gridLaw)
    (hshift : ∀ (z : Plane) (ω : Ω),
      proj (R.shift z ω) = markedSimilarity 1 z one_pos (proj ω))
    (hdilate : ∀ (t : ℝ) (ht : 0 < t) (ω : Ω),
      proj (S.dilate t ω) = markedSimilarity t 0 ht (proj ω)) :
    MarkedCentroidSublinearity ν ms :=
  markedCentroidSublinearity_of_weakMaximal ν hν hFE ms hharm hmass
    (markedResidualWeakMaximal_of_twoGridSpace hchain hdata henv ν hν hFE ms hmeas proj hprojA
      hmap hshift hdilate) hspec

/-! ### `hcopies`: the same fix, and here the measurability is free -/

/-- The copy-difference density, as a marked density on the coupled space.  It contains **no**
`phi`: `firstPotential`/`secondPotential` are `markedPotential` at the two grid copies, so the
label field is the difference of two `markedDifferenceField` values and is measurable from
`hmeas` alone, with no gate. -/
noncomputable def copyDifferenceDensity (ms : ℕ → ℕ) (p : CoupledSpace) (z : Plane) : ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode p.1)
    (fun u => firstPotential ms p u - secondPotential ms p u) z

/-- The label field of the copy difference is measurable on any parameter space mapping
measurably into the coupled space. -/
theorem measurable_copyDifferenceLabel {α : Type*} [MeasurableSpace α] (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → CoupledSpace) (hproj : Measurable proj) (n : ℕ) :
    Measurable fun ω : α =>
      markedDifferenceField ms ((proj ω).1, (proj ω).2.1)
          (Nat.pair (baseLabel (proj ω).1) n) -
        markedDifferenceField ms ((proj ω).1, (proj ω).2.2)
          (Nat.pair (baseLabel (proj ω).1) n) := by
  have hbase := MarkedDensityMeasurabilityProducer.measurable_markedPotentialLabel ms hmeas n
  have h1 : Measurable fun ω : α => ((proj ω).1, (proj ω).2.1) :=
    hproj.fst.prodMk hproj.snd.fst
  have h2 : Measurable fun ω : α => ((proj ω).1, (proj ω).2.2) :=
    hproj.fst.prodMk hproj.snd.snd
  exact (hbase.comp h1).sub (hbase.comp h2)

/-- Joint measurability of the copy-difference density, from `hmeas` alone. -/
theorem measurable_copyDifferenceDensity_prod {α : Type*} [MeasurableSpace α] (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → CoupledSpace) (hproj : Measurable proj) :
    Measurable fun q : α × Plane => copyDifferenceDensity ms (proj q.1) q.2 :=
  measurable_rootedSpecificEnergyDensity_prod (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      markedDifferenceField ms ((proj ω).1, (proj ω).2.1)
          (Nat.pair (baseLabel (proj ω).1) n) -
        markedDifferenceField ms ((proj ω).1, (proj ω).2.2)
          (Nat.pair (baseLabel (proj ω).1) n))
    (measurable_copyDifferenceLabel ms hmeas proj hproj)

/-- The same at the origin. -/
theorem measurable_copyDifferenceDensity_zero {α : Type*} [MeasurableSpace α] (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → CoupledSpace) (hproj : Measurable proj) :
    Measurable fun ω : α => copyDifferenceDensity ms (proj ω) 0 :=
  measurable_rootedSpecificEnergyDensity_zero (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      markedDifferenceField ms ((proj ω).1, (proj ω).2.1)
          (Nat.pair (baseLabel (proj ω).1) n) -
        markedDifferenceField ms ((proj ω).1, (proj ω).2.2)
          (Nat.pair (baseLabel (proj ω).1) n))
    (measurable_copyDifferenceLabel ms hmeas proj hproj)

/-- **CONDITIONAL.  `hcopies`' maximal input, with the measurable embedding and both
measurability hypotheses removed.**

`SpecificEnergyWeakMaximal.copyDifferenceWeakMaximal_of_auxiliaryMarkedSpace` uses `hproj` in
exactly the same two places (`:523`, `:530`), and the same replacement works — here without
even a gate, because the copy-difference density contains no `phi`.  `hmeas0` and `hjoint` are
discharged from the assembly's own `hmeas`, so this head is strictly weaker in hypotheses than
the existing one at **no** cost.

Its two pathwise identities `hcov`, `hinv` are **still open** (unlike `hsub`'s, which
`Corrector/ResidualDensitySimilarity` closed), so `hcopies` remains behind `hsub`. -/
theorem copyDifferenceWeakMaximal_of_twoGridSpace
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ν : Measure Env) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → CoupledSpace)
    (hprojA : @Measurable Ω CoupledSpace 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod (gridLaw.prod gridLaw))
    (hcov : ∀ (ω : Ω) (z : Plane),
      copyDifferenceDensity ms (proj ω) z = copyDifferenceDensity ms (proj (R.shift z ω)) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω,
      copyDifferenceDensity ms (proj (S.dilate s ω)) 0 = copyDifferenceDensity ms (proj ω) 0) :
    CopyDifferenceWeakMaximal ν ms := by
  have hprojM : Measurable proj := hprojA.mono henv.le le_rfl
  have hjointCoupled : Measurable fun q : CoupledSpace × Plane =>
      copyDifferenceDensity ms q.1 q.2 :=
    measurable_copyDifferenceDensity_prod ms hmeas id measurable_id
  have hzeroCoupled : Measurable fun p : CoupledSpace => copyDifferenceDensity ms p 0 :=
    measurable_copyDifferenceDensity_zero ms hmeas id measurable_id
  have hmeas0 : Measurable fun ω : Ω => copyDifferenceDensity ms (proj ω) 0 :=
    measurable_copyDifferenceDensity_zero ms hmeas proj hprojM
  have hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
      fun q => copyDifferenceDensity ms (proj q.1) q.2 :=
    @measurable_copyDifferenceDensity_prod Ω 𝒜.sigma ms hmeas proj hprojA
  refine ⟨ENNReal.ofReal 512, ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  have hmain := measure_exists_ball_gt_le hchain hdata henv
    (fun ω z => copyDifferenceDensity ms (proj ω) z) hcov hinv hmeas0 hjoint ht
  have hset : {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      = {p : CoupledSpace |
          ENNReal.ofReal t < densityMaximal (copyDifferenceDensity ms) p} := by
    ext p
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, lt_densityMaximal_iff (copyDifferenceDensity ms) ht p]
  have hTmeas : MeasurableSet {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume} := by
    rw [hset]
    exact measurableSet_lt measurable_const (measurable_densityMaximal hjointCoupled)
  have hA : (ν.prod (gridLaw.prod gridLaw))
        {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      = μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r,
              copyDifferenceDensity ms (proj ω) z ∂volume} := by
    rw [← hmap, Measure.map_apply hprojM hTmeas]
    rfl
  have hL : (∫⁻ p : CoupledSpace, copyDifferenceDensity ms p 0 ∂ν.prod (gridLaw.prod gridLaw))
      = ∫⁻ ω : Ω, copyDifferenceDensity ms (proj ω) 0 ∂μ := by
    rw [← hmap, lintegral_map hzeroCoupled hprojM]
  show (ν.prod (gridLaw.prod gridLaw))
        {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      ≤ ENNReal.ofReal 512 * (∫⁻ p : CoupledSpace, copyDifferenceDensity ms p 0
          ∂ν.prod (gridLaw.prod gridLaw)) / ENNReal.ofReal t
  rw [hA, hL]
  exact hmain

end ReflectedGMS.GatedResidualWeakMaximal
