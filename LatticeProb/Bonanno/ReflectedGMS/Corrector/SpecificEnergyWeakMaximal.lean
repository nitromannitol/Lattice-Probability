/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SpecificEnergyWeakMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SimilarityBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SmallBlockResidualProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridIndependenceDifferenceBridge

/-!
# The weak-`L¹` maximal inequality for a specific-energy density (`s:eq:maximal`)

Four of the eight open named inputs of the checked harmonic-coordinate reduction
(`Corrector/NeighborhoodConvergenceFromSpecificEnergy.harmonicCoordinateConclusions_of_eight_inputs`)
are consumed through a weak-`L¹` maximal inequality for a **rooted specific-energy density**:

* `Corrector/SmallBlockResidualProducer.MarkedResidualWeakMaximal` → `hsub`;
* `Corrector/GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal` → `hcopies`;
* `Corrector/MarkedDifferenceSubsequence.MarkedDifferenceIncrementsSummable` → `hconv`;
* `Corrector/MarkedPatchEnergyConvergence.MarkedPatchEnergyCauchy` → `hpatch`.

This module supplies the **one statement** that serves the first two of those four, proves it
from the project's checked `s:prop:maximal` with **no new open input of its own**, and records
precisely which clause of the remaining two defeats the common shape.

## The one statement

`measure_densityMaximal_gt_le` is, verbatim, the manuscript's `s:eq:maximal` for an arbitrary
`ℝ≥0∞`-valued **marked density** `ρ_ω(z)` on a marked configuration space:

  `μ[ M(ρ) > t ] ≤ 512 · E[ρ_·(0)] / t`,   `M(ρ)(ω) = sup_{r>0} r⁻² ∫_{B̄_r} ρ_ω(z) dz`.

Its hypotheses on `ρ` are exactly three pathwise identities plus measurability:

* `hcov` — **re-rooting covariance**, `ρ_ω(z) = ρ_{ω−z}(0)`.  This is the manuscript's
  "`ρ_ω(z) = F(ω − z)` for a functional `F` of the marked configuration";
* `hinv` — **scale invariance** of the value at the origin, the restriction `s:eq:MTP` actually
  tests (`Spatial/SimilarityBlockAveraging`);
* `hmeas0`, `hjoint` — measurability of `ω ↦ ρ_ω(0)` and joint measurability of `(ω, z) ↦ ρ_ω(z)`
  for the unmarked-environment sigma-field of `SpatialMaximalInequality.EnvironmentGrid`.

**No finiteness of `ρ_ω(0)` is assumed.**  That matters: the analogous statement for the *real*
functional `F = ρ_·(0)` used by `Spatial/SpatialMaximalInequality` silently requires
`ρ_ω(0) ≠ ∞` at every configuration, which is automatic for the (FE) density
(`RootDensities.rootedFiniteEnergyDensity_ne_top`, a consequence of `Geometry`) but is **false in
general** for the specific energy of a field.  The proof here removes that hypothesis by
truncating at level `N`, applying the checked
`SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity` to the bounded real functional
`(ρ_·(0) ∧ N).toReal`, and passing to the limit through continuity from below of `μ` on the
increasing (not necessarily measurable) sets `{M(ρ ∧ N) > t}` (`Monotone.measure_iUnion`).
Nothing is weakened: the constant is the manuscript's `512` and the conclusion is the manuscript's.

## What is discharged and what is not

`markedResidualWeakMaximal_of_auxiliaryMarkedSpace` and
`copyDifferenceWeakMaximal_of_auxiliaryMarkedSpace` deliver `hsub`'s and `hcopies`' maximal
inputs verbatim, from the one statement above transported along a measurable embedding
`proj : Ω → Env × Grid` (resp. `Ω → Env × Grid × Grid`) whose pushforward is the consumer's own
law.  **These are implications and they are CONDITIONAL**: they do not certify their hypotheses
and they do not prove the harmonic-coordinate theorem.

The single remaining atom is the marked space `Ω` itself.  It cannot be `Spatial/GoodMarkedSpace`'s
`goodMarked`, and the reason is structural rather than technical: on `goodSet × Grid` the *one*
`Grid` coordinate is simultaneously the manuscript's interpolation grid `𝔻` — the residual
density `ρ(φ_m − Φ)` is a function of it — and the auxiliary independent dyadic system `𝔻'` that
`s:prop:maximal` conditions on.  `GoodMarkedSpace.envSigma` is the environment-only sigma-field,
so `EnvironmentGrid.measurable_density` is not merely unproved for the residual density, it is
**false** there.  What is needed is the same good marked space carrying **two** independent
uniform dyadic systems, with `R.grid` the second one and `𝒜` the sigma-field of (environment,
interpolation grid); every field of `SimilarityBlockData` except the transport identity is
immediate from the existing proofs, and the transport identity is
`Corrector/MarkedMassTransportProducer.markedMassTransport_of_massTransport` carried along the
extra grid factor.  That is the precise open producer, and it is shared by `hsub` and `hcopies`.

Correction to the docstring of `Corrector/SmallBlockResidualProducer`, which predates the closure
of `hcov` on 2026-09-16: the first of the two obstructions it records — translation covariance of
the residual field — is **no longer open**.
`Corrector/ApproximantCovarianceFromBlockTransport.phi_similarity`, fed by the now-proved
`Corrector/BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant`, transports `phi`
along the *explicit* grid action `gridSimilarity s hs u` rather than an existentially quantified
one, and `HarmonicCoordinateAssembly.markedDifferenceField_pairTransport` composed with
`differenceApproximant_pairTransport` transports the limit `markedPotential` along the same
explicit action, pathwise on `SublinearEvent` and with **no** use of `hmeas`.  Since
`Spatial/GoodMarkedSpace.goodSet ⊆ HarmonicCoordinateAssembly.SublinearEvent` (the second
conjunct of `GoodEnvironmentSet.GoodEnvironment` is literally `SublinearDiameterDecay`), that
covariance holds at every point of the good marked space.

## `hconv` and `hpatch` are NOT served by this shape

Stated explicitly, as the scope demanded.

* `MarkedDifferenceIncrementsSummable` asks for almost-sure **absolute summability of
  `‖φ_{m_{j+1}}(H_b) − φ_{m_j}(H_b) − (…)(H_a)‖`** — a pointwise vertex-value quantity at one
  fixed pair of labels, and a *rate*.  Every consequence of a weak-type maximal inequality is an
  integrated energy density and carries no rate: the inequality gives convergence in probability,
  and Borel–Cantelli then gives a subsequence, not summability at a prescribed subsequence.
  Passing from an energy to a vertex value additionally needs a discrete Poincaré inequality
  (`Corrector/DiscreteBallPoincare`, or `BouRabeeGwynne/Section3ColumnEstimate`).  Two separate
  gaps, neither of which this shape closes.
* `MarkedPatchEnergyCauchy` asks for the **vector Dirichlet energy on a patch**,
  `∑'_{(v,w) ∈ W × W} c_{vw}‖Δ(φ_j − φ_k)‖²/2`, not a ball integral of the density.  The two are
  comparable — the ball integral of `ρ` over `B̄_r` dominates half the energy of the cells
  contained in `B̄_r`, and the cells hitting a bounded set lie in a ball by
  `Spatial/SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds` — but the comparison
  restricts the inner sum to `W`, so it is a genuine extra lemma and not an instance of this
  statement.  It is, however, the shortest route to `hpatch` once the auxiliary-grid space exists.

`hspec` is owned elsewhere and is neither used nor produced here.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS.SpecificEnergyWeakMaximal

open Code StatementIngredients RootDensities DyadicApproximation
open HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open SmallBlockResidualProducer GridIndependenceCoupling GridIndependenceDifferenceBridge

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The maximal function of a marked density -/

/-- The normalised ball average `r⁻² ∫_{B̄_r} ρ_ω(z) dz` of a marked density. -/
noncomputable def densityBallAverage (ρ : Ω → Plane → ℝ≥0∞) (r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  (ENNReal.ofReal (r ^ 2))⁻¹ *
    ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume

/-- The manuscript's maximal function `M(ρ) = sup_{r>0} r⁻² ∫_{B̄_r} ρ` of a marked density. -/
noncomputable def densityMaximal (ρ : Ω → Plane → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage ρ r ω

theorem densityBallAverage_le_densityMaximal (ρ : Ω → Plane → ℝ≥0∞) {r : ℝ} (hr : 0 < r)
    (ω : Ω) : densityBallAverage ρ r ω ≤ densityMaximal ρ ω :=
  le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) => densityBallAverage ρ r ω) r hr

/-- The maximal function is monotone in the density. -/
theorem densityMaximal_mono {ρ σ : Ω → Plane → ℝ≥0∞} (h : ∀ (ω : Ω) (z : Plane), ρ ω z ≤ σ ω z)
    (ω : Ω) : densityMaximal ρ ω ≤ densityMaximal σ ω := by
  show (⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage ρ r ω)
      ≤ ⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage σ r ω
  refine iSup_mono fun r => iSup_mono fun _ => ?_
  show (ENNReal.ofReal (r ^ 2))⁻¹ *
      ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume
    ≤ (ENNReal.ofReal (r ^ 2))⁻¹ *
      ∫⁻ z in Metric.closedBall (0 : Plane) r, σ ω z ∂volume
  exact mul_le_mul' le_rfl (lintegral_mono fun z => h ω z)

/-- **A bound on the maximal function is a bound on every ball integral, and conversely.**
This is the translation between the two shapes in which the consumers state `s:eq:maximal`. -/
theorem lt_densityMaximal_iff (ρ : Ω → Plane → ℝ≥0∞) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    ENNReal.ofReal t < densityMaximal ρ ω
      ↔ ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume := by
  have haux : ∀ r : ℝ, 0 < r →
      (ENNReal.ofReal t < densityBallAverage ρ r ω
        ↔ ENNReal.ofReal (t * r ^ 2)
            < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume) := by
    intro r hr
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
      hRHS, ENNReal.ofReal_mul ht.le,
      mul_comm (ENNReal.ofReal (r ^ 2)) (ENNReal.ofReal t)]
  constructor
  · intro h
    have h' : ENNReal.ofReal t < ⨆ r : ℝ, ⨆ _ : 0 < r, densityBallAverage ρ r ω := h
    rw [lt_iSup_iff] at h'
    obtain ⟨r, hr⟩ := h'
    rw [lt_iSup_iff] at hr
    obtain ⟨hrpos, hlt⟩ := hr
    exact ⟨r, hrpos, (haux r hrpos).1 hlt⟩
  · rintro ⟨r, hrpos, hlt⟩
    exact lt_of_lt_of_le ((haux r hrpos).2 hlt) (densityBallAverage_le_densityMaximal ρ hrpos ω)

/-! ### Truncation -/

/-- The truncation of the value of a marked density at the origin, as a **bounded real**
functional of the marked configuration.  This is the object the checked `s:prop:maximal`
accepts; the truncation is what removes the (false in general) hypothesis `ρ_ω(0) ≠ ∞`. -/
noncomputable def truncatedRoot (ρ : Ω → Plane → ℝ≥0∞) (N : ℕ) (ω : Ω) : ℝ :=
  (min (ρ ω 0) (N : ℝ≥0∞)).toReal

/-- Truncation exhausts an extended nonnegative real. -/
theorem iSup_min_natCast (x : ℝ≥0∞) : ⨆ N : ℕ, min x (N : ℝ≥0∞) = x := by
  refine le_antisymm (iSup_le fun N => min_le_left _ _) (le_of_forall_lt fun b hb => ?_)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
  exact lt_of_lt_of_le (lt_min hb hN) (le_iSup (fun N : ℕ => min x (N : ℝ≥0∞)) N)

/-! ### `s:eq:maximal` for a marked density -/

/-- **The one producer: the manuscript's weak-`L¹` maximal inequality `s:eq:maximal` for an
arbitrary marked density.**

`ρ_ω(z)` is any `ℝ≥0∞`-valued density which is re-rooting covariant (`hcov`), scale invariant at
the origin (`hinv`), and measurable (`hmeas0`, `hjoint`).  Then

  `μ[ M(ρ) > t ] ≤ 512 · E[ρ_·(0)] / t`.

No finiteness of `ρ_ω(0)` is assumed anywhere, and the constant is the manuscript's.  The proof
is the checked `SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity` applied to the
bounded real functional `truncatedRoot ρ N`, followed by continuity of `μ` from below along the
increasing family of super-level sets of the truncated maximal functions. -/
theorem measure_densityMaximal_gt_le
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ρ : Ω → Plane → ℝ≥0∞)
    (hcov : ∀ (ω : Ω) (z : Plane), ρ ω z = ρ (R.shift z ω) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω, ρ (S.dilate s ω) 0 = ρ ω 0)
    (hmeas0 : Measurable fun ω : Ω => ρ ω 0)
    (hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _ fun p => ρ p.1 p.2)
    {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
  classical
  -- measurability of the density in the space variable alone
  have hz : ∀ w : Ω, Measurable fun z : Plane => ρ w z := by
    intro w
    have hmk : @Measurable Plane (Ω × Plane) _
        (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) fun z : Plane => (w, z) :=
      Measurable.prodMk measurable_const measurable_id
    have h : Measurable ((fun p : Ω × Plane => ρ p.1 p.2) ∘ fun z : Plane => (w, z)) :=
      hjoint.comp hmk
    simpa only [Function.comp_def] using h
  -- the truncated inequality
  have key : ∀ N : ℕ,
      μ {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω}
        ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
    intro N
    have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
    have hmeasN : Measurable (truncatedRoot ρ N) :=
      (hmeas0.min measurable_const).ennreal_toReal
    have h0N : ∀ w : Ω, 0 ≤ truncatedRoot ρ N w := fun _ => ENNReal.toReal_nonneg
    have hlintN : (∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ) ≤ (N : ℝ≥0∞) := by
      calc (∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ)
          ≤ ∫⁻ _ : Ω, (N : ℝ≥0∞) ∂μ := lintegral_mono fun w => min_le_right _ _
        _ = (N : ℝ≥0∞) := by rw [lintegral_const, measure_univ, mul_one]
    have hintN : Integrable (truncatedRoot ρ N) μ :=
      integrable_toReal_of_lintegral_ne_top (hmeas0.min measurable_const).aemeasurable
        (ne_top_of_le_ne_top hNtop hlintN)
    have hinvN : S.InvariantFun (truncatedRoot ρ N) := by
      intro s hs w
      show (min (ρ (S.dilate s w) 0) (N : ℝ≥0∞)).toReal = (min (ρ w 0) (N : ℝ≥0∞)).toReal
      rw [hinv s hs w]
    have hdensN : @Measurable (Ω × Plane) ℝ
        (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
        fun p => truncatedRoot ρ N (R.shift p.2 p.1) := by
      have heq : (fun p : Ω × Plane => truncatedRoot ρ N (R.shift p.2 p.1))
          = fun p : Ω × Plane => (min (ρ p.1 p.2) (N : ℝ≥0∞)).toReal := by
        funext p
        show (min (ρ (R.shift p.2 p.1) 0) (N : ℝ≥0∞)).toReal
          = (min (ρ p.1 p.2) (N : ℝ≥0∞)).toReal
        rw [← hcov p.1 p.2]
      rw [heq]
      exact (hjoint.min measurable_const).ennreal_toReal
    have henvN : EnvironmentGrid R μ (truncatedRoot ρ N) 𝒜 :=
      { le := henv.le
        measurable_grid := henv.measurable_grid
        measurable_density := hdensN
        indep := henv.indep
        law := henv.law }
    have hbound := measure_ballMaximal_gt_le_similarity hchain hdata henvN hmeasN h0N hintN
      hinvN ht
    -- the truncated ball maximal function is the maximal function of the truncated density
    have hballeq : ∀ w : Ω, ballMaximal R (truncatedRoot ρ N) w
        = densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w := by
      intro w
      show (⨆ r : ℝ, ⨆ _ : 0 < r, ballAverage R (truncatedRoot ρ N) r w)
          = ⨆ r : ℝ, ⨆ _ : 0 < r,
              densityBallAverage (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) r w
      refine iSup_congr fun r => iSup_congr fun _ => ?_
      show (ENNReal.ofReal (r ^ 2))⁻¹ *
          ∫⁻ z in Metric.closedBall (0 : Plane) r,
            ENNReal.ofReal (truncatedRoot ρ N (R.shift z w)) ∂volume
        = (ENNReal.ofReal (r ^ 2))⁻¹ *
          ∫⁻ z in Metric.closedBall (0 : Plane) r, min (ρ w z) (N : ℝ≥0∞) ∂volume
      congr 1
      refine lintegral_congr fun z => ?_
      show ENNReal.ofReal (min (ρ (R.shift z w) 0) (N : ℝ≥0∞)).toReal = min (ρ w z) (N : ℝ≥0∞)
      rw [← hcov w z]
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hNtop (min_le_right _ _))
    have hset : {w : Ω | ENNReal.ofReal t < ballMaximal R (truncatedRoot ρ N) w}
        = {w : Ω |
            ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w} := by
      ext w
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hballeq w]
    rw [hset] at hbound
    refine le_trans hbound ?_
    have hI : ENNReal.ofReal (∫ w, truncatedRoot ρ N w ∂μ)
        = ∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hintN (Filter.Eventually.of_forall h0N)]
      refine lintegral_congr fun w => ?_
      show ENNReal.ofReal (min (ρ w 0) (N : ℝ≥0∞)).toReal = min (ρ w 0) (N : ℝ≥0∞)
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hNtop (min_le_right _ _))
    rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 512), hI,
      div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' (mul_le_mul' le_rfl (lintegral_mono fun w => min_le_left _ _)) le_rfl
  -- the super-level sets of the truncated maximal functions increase to the untruncated one
  have hincl : {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ⊆ ⋃ N : ℕ, {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} := by
    intro w hw
    have hlt : ENNReal.ofReal t < densityMaximal ρ w := hw
    obtain ⟨r, hrpos, hlt2⟩ := (lt_densityMaximal_iff ρ ht w).1 hlt
    have hmonoFun : Monotone fun (N : ℕ) (z : Plane) => min (ρ w z) (N : ℝ≥0∞) := by
      intro N M hNM z
      exact min_le_min le_rfl (by exact_mod_cast hNM)
    have hsupint : (∫⁻ z in Metric.closedBall (0 : Plane) r, ρ w z ∂volume)
        = ⨆ N : ℕ, ∫⁻ z in Metric.closedBall (0 : Plane) r,
            min (ρ w z) (N : ℝ≥0∞) ∂volume := by
      rw [← lintegral_iSup (fun N => (hz w).min measurable_const) hmonoFun]
      exact lintegral_congr fun z => (iSup_min_natCast (ρ w z)).symm
    rw [hsupint, lt_iSup_iff] at hlt2
    obtain ⟨N, hN⟩ := hlt2
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    show ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w
    exact (lt_densityMaximal_iff (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) ht w).2
      ⟨r, hrpos, hN⟩
  have hmonoSet : Monotone fun N : ℕ => {ω : Ω |
      ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} := by
    intro N M hNM w hw
    have hw' : ENNReal.ofReal t
        < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w := hw
    show ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (M : ℝ≥0∞)) w
    refine lt_of_lt_of_le hw' ?_
    exact densityMaximal_mono
      (fun w' z => min_le_min le_rfl (by exact_mod_cast hNM)) w
  calc μ {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ≤ μ (⋃ N : ℕ, {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω}) :=
        measure_mono hincl
    _ = ⨆ N : ℕ, μ {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} :=
        hmonoSet.measure_iUnion
    _ ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := iSup_le key

/-- **The same statement in the consumers' ball-integral shape**: this is verbatim the shape of
`GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal` and, after the trivial conversion
of the level from a real to an `ℝ≥0∞`, of `SmallBlockResidualProducer.MarkedResidualWeakMaximal`. -/
theorem measure_exists_ball_gt_le
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ρ : Ω → Plane → ℝ≥0∞)
    (hcov : ∀ (ω : Ω) (z : Plane), ρ ω z = ρ (R.shift z ω) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω, ρ (S.dilate s ω) 0 = ρ ω 0)
    (hmeas0 : Measurable fun ω : Ω => ρ ω 0)
    (hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _ fun p => ρ p.1 p.2)
    {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume}
      ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
  have hset : {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume}
      = {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, lt_densityMaximal_iff ρ ht ω]
  rw [hset]
  exact measure_densityMaximal_gt_le hchain hdata henv ρ hcov hinv hmeas0 hjoint ht

/-! ### The specific-energy density of a difference is symmetric -/

/-- The specific-energy density only sees increments, so it is unchanged by exchanging the two
fields of a difference. -/
theorem specificEnergyDensity_sub_comm {V : Type*} (F : IndexedCells V) (a b : V → Plane)
    (v : V) :
    specificEnergyDensity F (fun u => a u - b u) v
      = specificEnergyDensity F (fun u => b u - a u) v := by
  have hnorm : ∀ w : V, ‖(a w - b w) - (a v - b v)‖ = ‖(b w - a w) - (b v - a v)‖ := by
    intro w
    rw [show (b w - a w) - (b v - a v) = -((a w - b w) - (a v - b v)) by abel, norm_neg]
  unfold RootDensities.specificEnergyDensity
  simp only [hnorm]

/-- The rooted form of `specificEnergyDensity_sub_comm`. -/
theorem rootedSpecificEnergyDensity_sub_comm {V : Type*} (F : IndexedCells V) (a b : V → Plane)
    (z : Plane) :
    rootedSpecificEnergyDensity F (fun u => a u - b u) z
      = rootedSpecificEnergyDensity F (fun u => b u - a u) z := by
  show (rootAt F z).elim 0 (specificEnergyDensity F fun u => a u - b u)
    = (rootAt F z).elim 0 (specificEnergyDensity F fun u => b u - a u)
  cases rootAt F z with
  | none => rfl
  | some v => exact specificEnergyDensity_sub_comm F a b v

/-! ### `hsub`: `MarkedResidualWeakMaximal` from the one producer -/

/-- The residual density `ρ(Φ − φ_m)` of a marked environment, as a marked density. -/
noncomputable def residualDensityOf (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment) (z : Plane) :
    ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode ω.1)
    (fun v => markedPotential ms ω v - phi (decode ω.1) ω.2 m v) z

theorem markedResidualMaximal_eq (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment) :
    markedResidualMaximal ms m ω = densityMaximal (residualDensityOf ms m) ω := rfl

/-! ### `hcopies`: `CopyDifferenceWeakMaximal` from the one producer -/

end ReflectedGMS.SpecificEnergyWeakMaximal
