/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.AuxiliaryGridMarkedSpaceProjection at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AuxiliaryGridMarkedSpace
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedResidualWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageDifferenceWeakMaximalProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedWeakMaximalOn

/-!
# The consumer projection off the auxiliary two-grid marked space

`Spatial/AuxiliaryGridMarkedSpace` builds the two-grid space `AuxSpace = (goodSet × Grid) × Grid`
together with its `OriginChainRegularOn`, `SimilarityBlockDataOn`, `InvariantDomain` and
`EnvironmentGrid` — the first two read, as the singular-set manuscript's §3.1 requires, on the
invariant domain `coveredAux` of configurations whose origin lies in a cell.  The
corrector-lane consumers (`Corrector/ResidualDensitySimilarity`,
`Corrector/SpecificEnergyWeakMaximal`) additionally need a projection

```
markedProj ω = (environment, INTERPOLATION grid) : MarkedEnvironment
```

— the *inner* grid, as opposed to `proj`, which reads the auxiliary grid `𝔻'` — satisfying four
conditions.  All four are supplied here:

* `measurable_envSigma_markedProj` (`hprojA`) — `markedProj` is measurable for the environment
  sigma-field `auxEnvSigma.sigma = comap Prod.fst`.  This is the payoff of putting the auxiliary
  grid **outermost**: with the other association `markedProj` is not `𝒜`-measurable on the nose;
* `map_markedProj_auxLaw` (`hmap`) — the pushforward is `ν ⊗ gridLaw`;
* `markedProj_shift` (`hshift`) and `markedProj_dilate` (`hdilate`) — equivariance for the joint
  similarity action.

In addition `markedProj_mem_sublinearEvent` supplies the pathwise gate `hgood`, because the
second conjunct of `GoodEnvironmentSet.GoodEnvironment` is literally
`HarmonicCoordinateAssembly.SublinearEvent`.

`twoGridConsumerData` bundles all of it, so that a consumer stated over an abstract marked space
is a single application.

**What is deliberately not here.**  `MeasurableEmbedding markedProj` is *false* — a projection
off a product forgets the auxiliary grid — so the older consumer shapes
(`markedResidualWeakMaximal_of_similarityEquivariant`,
`markedResidualWeakMaximal_of_auxiliaryMarkedSpace`) cannot be fed by any two-grid space.  The
gated-density consumer shape, which asks only for `Measurable` and the four conditions above, is
what this data is for.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.AuxiliaryGridMarkedSpace

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open GoodMarkedScaleAction SimilarityBlockAveraging SpatialMaximalConsumerForm
open DyadicApproximation DyadicGridTranslation DyadicGridLaw UniformGridDilationInvariance
open SpatialMaximalForFiniteEnergy MarkedMassTransportProducer
open HarmonicCoordinateAssembly HarmonicMainStatement HarmonicLawIngredients
open SmallBlockResidualProducer SpecificEnergyWeakMaximal GatedResidualWeakMaximal
open GatedWeakMaximalOn

/-! ### The consumer projection -/

/-- **The consumer's projection**: the environment together with the *interpolation* grid, i.e.
the inner factor of `AuxSpace` mapped into the actual marked space `Env × Grid`.  This is **not**
`proj`, which reads the auxiliary grid `𝔻'`. -/
def markedProj (ω : AuxSpace) : MarkedEnvironment := incl ω.1

/-- **`hprojA`.**  `markedProj` is measurable for the environment sigma-field, because it factors
through the first projection and `auxEnvSigma.sigma` is exactly that comap.  This is the payoff of
the `(goodSet × Grid) × Grid` ordering. -/
theorem measurable_envSigma_markedProj :
    @Measurable AuxSpace MarkedEnvironment auxEnvSigma.sigma _ markedProj := by
  have h2 : @Measurable AuxSpace (goodSet × Grid) auxEnvSigma.sigma _ Prod.fst :=
    (@measurable_iff_comap_le _ _ auxEnvSigma.sigma _ Prod.fst).2 le_rfl
  exact measurable_incl.comp h2

/-! ### The law and the equivariance -/

variable (ν : Measure Env)

/-- **`hmap`.**  The interpolation-grid marginal of the two-grid law is the actual marked law
`ν ⊗ 𝔻`: the auxiliary grid is integrated out, and the good set has full measure. -/
theorem map_markedProj_auxLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (auxLaw ν).map markedProj = ν.prod gridLaw := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hcomp : markedProj = incl ∘ (Prod.fst : AuxSpace → goodSet × Grid) := rfl
  have hfst : (auxLaw ν).map (Prod.fst : AuxSpace → goodSet × Grid)
      = goodLaw (G := goodSet) ν := by
    show ((goodLaw (G := goodSet) ν).prod gridMeasure).map Prod.fst = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [hcomp, ← Measure.map_map measurable_incl measurable_fst, hfst, map_incl_goodLaw ν hgood]

/-- **`hshift`.**  Re-rooting the two-grid configuration is the unit-scale joint similarity on the
interpolation marked pair. -/
theorem markedProj_shift (z : Plane) (ω : AuxSpace) :
    markedProj (auxReRooting.shift z ω) = markedSimilarity 1 z one_pos (markedProj ω) := by
  rw [markedSimilarity_one]
  rfl

/-- **`hdilate`.**  Dilating the two-grid configuration is the origin-centred joint similarity on
the interpolation marked pair; the only non-definitional step is `translate 0 D = D`. -/
theorem markedProj_dilate (t : ℝ) (ht : 0 < t) (ω : AuxSpace) :
    markedProj (auxScale.dilate t ω) = markedSimilarity t 0 ht (markedProj ω) := by
  show markedProj (auxDilate t ω) = _
  rw [auxDilate_of_pos ht, goodDilate_of_pos ht]
  show (similarityTargetEnv t 0 ht (ω.1.1 : Env), dilate t ht ω.1.2)
    = (similarityTargetEnv t 0 ht (ω.1.1 : Env), dilate t ht (translate 0 ω.1.2))
  rw [translate_zero]

/-! ### The bundled consumer data -/

/-! ### The weld: `hsub`'s maximal input from the two-grid space -/

/-- **`hsub`'s maximal input, produced — not assumed — from the auxiliary two-grid marked
space.**

`Corrector/GatedWeakMaximalOn.markedResidualWeakMaximal_of_twoGridSpaceOn` is the embedding-free
consumer head on the manuscript's invariant domain; every one of its marked-space hypotheses,
including `hdom : InvariantDomain`, is discharged here by the two-grid space of
`Spatial/AuxiliaryGridMarkedSpace`.  What remains on the right of the arrow is
`hmeas`, the assembly's own measurability of the gated interpolant, which is an input of the
harmonic-coordinate assembly and has nothing to do with the auxiliary dyadic system.

So this is a **DISCHARGE** of the marked-space producer for `hsub`, and a **REDUCTION** of
`MarkedResidualWeakMaximal` to `hmeas` alone (beyond the manuscript's own `s:eq:MTP` and finite
(FE) moment). -/
theorem markedResidualWeakMaximal_auxTwoGrid [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    MarkedResidualWeakMaximal ν ms := by
  have hgood : ∀ᵐ e ∂ν, e ∈ goodSet := ae_mem_goodSet ν hν hFE.ne
  have := isProbabilityMeasure_auxLaw ν hgood
  exact markedResidualWeakMaximal_of_twoGridSpaceOn (invariantDomain_coveredAux ν hν hgood)
    originChainRegularOn_aux (similarityBlockDataOn_aux ν hν hgood)
    (environmentGrid_aux ν hgood) ν hν hFE ms hmeas
    markedProj measurable_envSigma_markedProj (map_markedProj_auxLaw ν hgood)
    markedProj_shift markedProj_dilate

/-- **`hpatch`/`hconv`'s maximal input, produced — not assumed — from the auxiliary two-grid
marked space.**

`Corrector/GatedWeakMaximalOn.markedStageDifferenceWeakMaximal_of_twoGridSpaceOn`
takes exactly the same marked-space data as the residual head, so the same instantiation serves.
As for `hsub`, this is a **DISCHARGE** of the marked-space producer and a **REDUCTION** of
`MarkedStageDifferenceWeakMaximal` to `hmeas` alone. -/
theorem markedStageDifferenceWeakMaximal_auxTwoGrid [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν := by
  have hgood : ∀ᵐ e ∂ν, e ∈ goodSet := ae_mem_goodSet ν hν hFE.ne
  have := isProbabilityMeasure_auxLaw ν hgood
  exact markedStageDifferenceWeakMaximal_of_twoGridSpaceOn
    (invariantDomain_coveredAux ν hν hgood) originChainRegularOn_aux
    (similarityBlockDataOn_aux ν hν hgood) (environmentGrid_aux ν hgood)
    ν hν hFE hmeas markedProj measurable_envSigma_markedProj (map_markedProj_auxLaw ν hgood)
    markedProj_shift markedProj_dilate

end ReflectedGMS.AuxiliaryGridMarkedSpace
