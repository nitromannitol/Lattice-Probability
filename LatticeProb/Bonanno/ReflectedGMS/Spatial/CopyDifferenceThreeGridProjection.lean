/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.CopyDifferenceThreeGridProjection at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CopyDifferenceThreeGridSpace
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceDensitySimilarity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceOriginEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedWeakMaximalOn

/-!
# The weld: `hcopies`' maximal input from the three-grid space

`Spatial/CopyDifferenceThreeGridSpace` builds `TriSpace = ((goodSet × Grid) × Grid) × Grid`
together with its `OriginChainRegularOn`, `SimilarityBlockDataOn`, `InvariantDomain` and
`EnvironmentGrid` — the first two read, as the singular-set manuscript's §3.1 requires, on the
invariant domain `coveredTri` of configurations whose origin lies in a cell — and
`Corrector/CopyDifferenceDensitySimilarity` proves the two pathwise identities `hcov`, `hinv` for
the copy-difference density.  This module supplies the consumer projection

```
couplProj ω = (environment, 𝔻₁, 𝔻₂) : CoupledSpace = Env × Grid × Grid
```

— the two **interpolation** grids, as opposed to `triProj`, which reads the auxiliary grid `𝔻'` —
and feeds everything to `Corrector/GatedWeakMaximalOn.copyDifferenceWeakMaximal_of_twoGridSpaceOn`.

## What is DISCHARGED and what is REDUCED

* **DISCHARGED.**  Every marked-space hypothesis of the consumer head — `hdom`, `hchain`,
  `hdata`, `henv`, `hprojA`, `hmap`, and now also `hcov` and `hinv` — is a *proof* here, from the
  manuscript's own `s:eq:MTP` and finite (FE) moment.  In particular there is no
  `MeasurableEmbedding` (which is false for any projection off a product) and no pathwise gate
  (the copy-difference field contains no `phi`).
* **REDUCED.**  `copyDifferenceWeakMaximal_threeGrid` reduces
  `GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal` to `hmeas` alone, the assembly's own
  measurability of the gated interpolant — the same residue as `hsub`, `hpatch` and `hconv`.
* Composing with `Corrector/CopyDifferenceOriginEnergy.differenceFieldGridIndependent_of_originEnergy`,
  `differenceFieldGridIndependent_of_originEnergy_threeGrid` reduces **`hcopies` itself to the
  single input `hzero`**, the manuscript's cross orthogonality in its integrability-free
  `ℝ≥0∞` form.  By
  `Corrector/CopyDifferenceInputReduction.integral_rootedPairing_diff_self_eq` that is the
  irreducible content of `hcopies`, so no further count reduction is possible along this route.

## Why the third grid is genuinely needed

`R.grid` cannot be collapsed onto either interpolation copy: `hprojA` makes both grid components
of `couplProj` `𝒜.sigma`-measurable, `henv.indep` makes `R.grid` independent of `𝒜.sigma`, and
`henv.law` forces `μ.map R.grid` to be a `UniformGridLaw`, not a Dirac.

## Anti-vacuity

`TriSpace` is inhabited at the actual data (`CopyDifferenceThreeGridSpace.nonempty_triSpace`,
re-exported by the `example` at the end), the constant in `CopyDifferenceWeakMaximal` is the
project's absolute `512`, produced outside the `∀ t` quantifier by the consumer head, and the
three-grid law is a probability measure.  The gate is not an unsatisfiable hypothesis hiding the
old falsity: `CopyDifferenceThreeGridSpace.invariantDomain_coveredTri` proves `coveredTri`
measurable, **conull for the three-grid law**, invariant under the dilation action and left by
only a Lebesgue-null set of re-rootings.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceThreeGridSpace

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open GoodMarkedScaleAction SimilarityBlockAveraging SpatialMaximalConsumerForm
open DyadicApproximation DyadicGridTranslation DyadicGridLaw UniformGridDilationInvariance
open SpatialMaximalForFiniteEnergy MarkedMassTransportProducer
open HarmonicCoordinateAssembly HarmonicMainStatement HarmonicLawIngredients
open RootDensities GridIndependenceCoupling GridIndependenceDifferenceBridge
open GatedResidualWeakMaximal CopyDifferenceDensitySimilarity
open AuxiliaryGridMarkedSpace GatedWeakMaximalOn

/-! ### The consumer projection -/

/-- The two-grid space mapped into the coupled space: environment and the **two interpolation**
grids.  The auxiliary grid of the two-grid space is `a.2`, which here plays the role of the second
interpolation copy `𝔻₂`; the maximal inequality's own dyadic system is the outer grid of
`TriSpace`. -/
def auxToCoupled (a : AuxSpace) : CoupledSpace := ((a.1.1 : Env), a.1.2, a.2)

theorem measurable_auxToCoupled : Measurable auxToCoupled :=
  ((measurable_fst.comp measurable_fst).subtype_coe).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- **The consumer's projection**: the environment together with the two *interpolation* grids.
This is **not** `triProj`, which reads the auxiliary grid `𝔻'`. -/
def couplProj (ω : TriSpace) : CoupledSpace := auxToCoupled ω.1

/-- **`hprojA`.**  `couplProj` is measurable for the environment sigma-field, because it factors
through the first projection and `triEnvSigma.sigma` is exactly that comap.  This is the payoff of
the `AuxSpace × Grid` ordering. -/
theorem measurable_envSigma_couplProj :
    @Measurable TriSpace CoupledSpace triEnvSigma.sigma _ couplProj := by
  have h2 : @Measurable TriSpace AuxSpace triEnvSigma.sigma _ Prod.fst :=
    (@measurable_iff_comap_le _ _ triEnvSigma.sigma _ Prod.fst).2 le_rfl
  exact measurable_auxToCoupled.comp h2

/-! ### The law -/

variable (ν : Measure Env)

/-- **`hmap`.**  The interpolation-grid marginal of the three-grid law is `ν ⊗ (𝔻 ⊗ 𝔻)`: the
auxiliary grid is integrated out, the good set has full measure, and the remaining triple product
is reassociated. -/
theorem map_couplProj_triLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (triLaw ν).map couplProj = ν.prod (gridLaw.prod gridLaw) := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have := isProbabilityMeasure_auxLaw ν hgood
  have hcomp : couplProj = auxToCoupled ∘ (Prod.fst : TriSpace → AuxSpace) := rfl
  have hfst : (triLaw ν).map (Prod.fst : TriSpace → AuxSpace) = auxLaw ν := by
    show ((auxLaw ν).prod gridMeasure).map Prod.fst = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [hcomp, ← Measure.map_map measurable_auxToCoupled measurable_fst, hfst]
  have hstep : auxToCoupled
      = (MeasurableEquiv.prodAssoc : (Env × Grid) × Grid ≃ᵐ Env × Grid × Grid)
        ∘ (Prod.map incl (id : Grid → Grid)) := rfl
  rw [hstep, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (measurable_incl.prodMap measurable_id)]
  show (((goodLaw (G := goodSet) ν).prod gridMeasure).map (Prod.map incl id)).map
      MeasurableEquiv.prodAssoc = _
  rw [← Measure.map_prod_map _ _ measurable_incl measurable_id, Measure.map_id,
    map_incl_goodLaw ν hgood]
  exact Measure.prodAssoc_prod

/-! ### The two pathwise identities, welded -/

/-- **`hcov`'s weld.**  Re-rooting the three-grid configuration is the unit-scale joint similarity
on both interpolation copies simultaneously. -/
theorem couplProj_shift (z : Plane) (ω : TriSpace) :
    couplProj (triReRooting.shift z ω) = coupledSimilarity 1 z one_pos (couplProj ω) := by
  rw [coupledSimilarity_one]
  rfl

/-- **`hinv`'s weld.**  Dilating the three-grid configuration is the origin-centred joint
similarity on both interpolation copies; the only non-definitional step is `translate 0 D = D`. -/
theorem couplProj_dilate (t : ℝ) (ht : 0 < t) (ω : TriSpace) :
    couplProj (triScale.dilate t ω) = coupledSimilarity t 0 ht (couplProj ω) := by
  show couplProj (triDilate t ω) = _
  rw [triDilate_of_pos ht, auxDilate_of_pos ht, goodDilate_of_pos ht]
  show (similarityTargetEnv t 0 ht (ω.1.1.1 : Env), dilate t ht ω.1.1.2, dilate t ht ω.1.2)
    = (similarityTargetEnv t 0 ht (ω.1.1.1 : Env), dilate t ht (translate 0 ω.1.1.2),
        dilate t ht (translate 0 ω.1.2))
  simp only [translate_zero]

/-! ### `hcopies`' maximal input -/

/-- **`hcopies`' maximal input, produced — not assumed — from the auxiliary three-grid marked
space.**

`Corrector/GatedWeakMaximalOn.copyDifferenceWeakMaximal_of_twoGridSpaceOn` is the embedding-free
consumer head on the manuscript's invariant domain; every one of its hypotheses — the marked-space
data `hdom`, `hchain`, `hdata`, `henv`, the projection conditions `hprojA`, `hmap`, and the two
pathwise identities `hcov`, `hinv` — is discharged here.  What remains on the right of the arrow
is `hmeas`, the
assembly's own measurability of the gated interpolant, which has nothing to do with the auxiliary
dyadic system.

So this is a **DISCHARGE** of the marked-space producer for `hcopies`, and a **REDUCTION** of
`CopyDifferenceWeakMaximal` to `hmeas` alone (beyond the manuscript's own `s:eq:MTP` and finite
(FE) moment) — the same residue as `hsub`, `hpatch` and `hconv`. -/
theorem copyDifferenceWeakMaximal_threeGrid [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    CopyDifferenceWeakMaximal ν ms := by
  have hgood : ∀ᵐ e ∂ν, e ∈ goodSet := ae_mem_goodSet ν hν hFE.ne
  have := isProbabilityMeasure_triLaw ν hgood
  refine copyDifferenceWeakMaximal_of_twoGridSpaceOn (invariantDomain_coveredTri ν hν hgood)
    originChainRegularOn_tri (similarityBlockDataOn_tri ν hν hgood)
    (environmentGrid_tri ν hgood) ν ms hmeas
    couplProj measurable_envSigma_couplProj (map_couplProj_triLaw ν hgood) ?_ ?_
  · intro ω z
    rw [couplProj_shift z ω]
    exact (copyDifferenceDensity_shift ms (couplProj ω) z).symm
  · intro s hs ω
    rw [couplProj_dilate s hs ω]
    exact copyDifferenceDensity_dilate ms s hs (couplProj ω)

/-- **`hcopies` from the single input `hzero`.**

`Corrector/CopyDifferenceOriginEnergy.differenceFieldGridIndependent_of_originEnergy` reduced
`hcopies` to the pair `(hzero, hmax)`; the second member is now a theorem, so `hcopies` costs
exactly one statement beyond the manuscript's own hypotheses and the assembly's `hmeas`:

  `hzero : E[ ρ_{Φ¹ − Φ²}(0) ] = 0`,

the expected rooted specific-energy density at the origin of the difference of the two grid-copy
potentials.  By `Corrector/CopyDifferenceInputReduction.integral_rootedPairing_diff_self_eq` and
the pointwise nonnegativity of the self-pairing, `hzero` *is* the manuscript's cross
orthogonality; it is the irreducible content of `hcopies` and no further bookkeeping removes
it. -/
theorem differenceFieldGridIndependent_of_originEnergy_threeGrid [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hzero : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (fun u => firstPotential ms p u - secondPotential ms p u) 0
          ∂ν.prod (gridLaw.prod gridLaw)) = 0) :
    DifferenceFieldGridIndependent ν ms :=
  CopyDifferenceOriginEnergy.differenceFieldGridIndependent_of_originEnergy ν ms hzero
    (copyDifferenceWeakMaximal_threeGrid ν hν hFE ms hmeas)

/-! ### Anti-vacuity -/

/-- The three-grid law is a probability measure under the manuscript's own hypotheses. -/
example (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) : IsProbabilityMeasure (triLaw ν) :=
  isProbabilityMeasure_triLaw ν (ae_mem_goodSet ν hν hFE.ne)

end ReflectedGMS.CopyDifferenceThreeGridSpace
