/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.AuxiliaryGridMarkedSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy

/-!
# The auxiliary two-grid marked space

The manuscript's `s:prop:maximal` is applied twice in the corrector lane: once with the
interpolation grid playing the role of the auxiliary dyadic system `𝔻'`, and once with a
*second, independent* dyadic system, because the residual/difference functionals are
themselves functions of the interpolation grid and the single grid of `goodSet × Grid`
cannot play both roles at once.

This module builds that two-grid space:

```
AuxSpace := (goodSet × Grid) × Grid
auxLaw ν := (goodLaw ν) ⊗ gridMeasure
```

with the **auxiliary grid outermost**, so that the first factor is *literally* the existing
good marked space `goodSet × Grid` of `Spatial/GoodMarkedSpace`.  The load-bearing map is

```
proj ω := (ω.1.1, ω.2)   -- (environment, AUXILIARY grid)
```

which intertwines `env`, `grid`, `shift`, and therefore `blockSetAt`, `blockSideAt` and
`originBlockIndex`, **definitionally**.  Consequently `OriginChainRegular` and four of the
five fields of `SimilarityBlockAveraging.SimilarityBlockData` transfer from the checked
one-grid statements by `rfl`, and the whole of `SpatialMaximalInequality.EnvironmentGrid`
is a short rectangle computation, exactly as in `GoodMarkedSpace.indep_goodMarked`.

The remaining field, the mark-averaged mass transport, is supplied in the second half of the
file (`lintegral_blockAverageLint_aux`): it is *derived* from the already-checked one-grid
identity `SpatialMaximalForFiniteEnergy.lintegral_blockAverageLint_eq` by averaging the test
function over the extra grid, so no second copy of the block kernel is needed.

Nothing here is assumed beyond the manuscript's own hypotheses: `MassTransport ν` and the
finite (FE) moment, through `GoodMarkedSpace.ae_mem_goodSet`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.AuxiliaryGridMarkedSpace

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open GoodMarkedScaleAction SimilarityBlockAveraging SpatialMaximalConsumerForm
open DyadicApproximation DyadicGridTranslation DyadicGridLaw UniformGridDilationInvariance
open SpatialMaximalForFiniteEnergy MarkedSimilarityActionLaws
open UniformGridTranslationInvariance

/-! ### The carrier and the projection -/

/-- **The auxiliary two-grid marked space.**  A point is `((e, 𝔻), 𝔻')` with `e` a good
environment, `𝔻` the interpolation grid and `𝔻'` the auxiliary independent dyadic system.
The auxiliary grid is the *outer* factor, so the inner factor is the good marked space. -/
abbrev AuxSpace : Type := (goodSet × Grid) × Grid

/-- The projection onto (environment, **auxiliary** grid).  This is the map along which all
the selected-block data transfers; it is definitionally compatible with `env`, `grid` and
`shift`. -/
def proj (ω : AuxSpace) : goodSet × Grid := (ω.1.1, ω.2)

/-! ### The marked re-rooting -/

/-- **The marked re-rooting of the two-grid space.**  The environment is read off the inner
factor, the dyadic system `𝔻'` is the *outer* grid, and re-rooting acts simultaneously on the
good marked configuration and on the auxiliary grid. -/
noncomputable def auxReRooting : MarkedReRooting AuxSpace where
  env ω := ω.1.1.1
  grid ω := ω.2
  shift w ω := (goodMarked.shift w ω.1, translate w ω.2)
  measurable_shift := by
    have h1 : Measurable fun p : AuxSpace × Plane => goodMarked.shift p.2 p.1.1 := by
      have hmap : Measurable fun p : AuxSpace × Plane => ((p.1.1 : goodSet × Grid), p.2) :=
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
      have h : Measurable ((fun r : (goodSet × Grid) × Plane => goodMarked.shift r.2 r.1) ∘
          fun p : AuxSpace × Plane => ((p.1.1 : goodSet × Grid), p.2)) :=
        goodMarked.measurable_shift.comp hmap
      simpa only [Function.comp_def] using h
    have h2 : Measurable fun p : AuxSpace × Plane => translate p.2 p.1.2 := by
      have hmap : Measurable fun p : AuxSpace × Plane => ((p.1.2 : Grid), p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have h : Measurable ((fun r : Grid × Plane => translate r.2 r.1) ∘
          fun p : AuxSpace × Plane => ((p.1.2 : Grid), p.2)) :=
        measurable_translate.comp hmap
      simpa only [Function.comp_def] using h
    exact h1.prodMk h2
  shift_zero ω := by
    apply Prod.ext
    · exact goodMarked.shift_zero ω.1
    · exact translate_zero ω.2
  shift_shift w z ω := by
    apply Prod.ext
    · exact goodMarked.shift_shift w z ω.1
    · exact translate_translate w z ω.2

@[simp] theorem auxReRooting_env (ω : AuxSpace) : auxReRooting.env ω = ω.1.1.1 := rfl

@[simp] theorem auxReRooting_grid (ω : AuxSpace) : auxReRooting.grid ω = ω.2 := rfl

/-! ### `proj` intertwines everything, definitionally -/

theorem blockSetAt_proj (m : ℝ) (ω : AuxSpace) :
    auxReRooting.blockSetAt m ω = goodMarked.blockSetAt m (proj ω) := rfl

theorem blockSideAt_proj (m : ℝ) (ω : AuxSpace) :
    auxReRooting.blockSideAt m ω = goodMarked.blockSideAt m (proj ω) := rfl

/-- Re-rooting the two-grid configuration re-roots its image in the good marked space: `proj`
intertwines the two shifts definitionally. -/
theorem proj_shift (z : Plane) (ω : AuxSpace) :
    proj (auxReRooting.shift z ω) = goodMarked.shift z (proj ω) := rfl

/-! ### Pulling the manuscript's invariant domain back along an intertwiner -/

/-- **The manuscript's invariant domain pulls back along any map intertwining the two actions.**

`SimilarityBlockAveraging.InvariantDomain` has four conditions, and all four are preserved by a
measurable `f` which intertwines the re-rootings and the dilations: measurability and dilation
invariance are pointwise, the Lebesgue-null set of bad re-rootings is the *same* set of offsets
downstairs, and conullity is the hypothesis `hae`.

Conullity is asked for directly rather than through `μ.map f = μ'`, because the two-grid and
three-grid laws reach it from `Measure.quasiMeasurePreserving_fst` without ever computing a
pushforward.  `μ'` enters only through the type of `hdom'`. -/
theorem invariantDomain_comap {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω}
    {R' : MarkedReRooting Ω'} {S' : ScaleAction R'} {μ' : Measure Ω'}
    {G' : Set Ω'} (hdom' : InvariantDomain R' S' μ' G')
    {f : Ω → Ω'} (hf : Measurable f) (hae : ∀ᵐ ω ∂μ, f ω ∈ G')
    (hshift : ∀ (z : Plane) (ω : Ω), f (R.shift z ω) = R'.shift z (f ω))
    (hdilate : ∀ s : ℝ, 0 < s → ∀ ω : Ω, f (S.dilate s ω) = S'.dilate s (f ω)) :
    InvariantDomain R S μ (f ⁻¹' G') where
  measurable := hf hdom'.measurable
  ae_mem := hae
  shift_ae ω := by
    have heq : {z : Plane | R.shift z ω ∉ f ⁻¹' G'} = {z : Plane | R'.shift z (f ω) ∉ G'} := by
      ext z
      show f (R.shift z ω) ∉ G' ↔ R'.shift z (f ω) ∉ G'
      rw [hshift z ω]
    rw [heq]
    exact hdom'.shift_ae (f ω)
  dilate_mem s hs ω := by
    show f (S.dilate s ω) ∈ G' ↔ f ω ∈ G'
    rw [hdilate s hs ω]
    exact hdom'.dilate_mem s hs (f ω)

/-! ### Origin-chain regularity, block equivariance and measurability -/

/-- The manuscript's invariant domain on the two-grid space: pulled back along `proj`, which
intertwines `env` and `grid` definitionally. -/
def coveredAux : Set AuxSpace := proj ⁻¹' coveredMarked

theorem measurable_proj : Measurable proj :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem measurableSet_coveredAux : MeasurableSet coveredAux :=
  measurable_proj measurableSet_coveredMarked

/-- **Origin-chain regularity on the two-grid space**, on the manuscript's invariant domain.
All three clauses are statements about `originBlockIndex`, which is computed from `env` and
`grid` alone. -/
theorem originChainRegularOn_aux : OriginChainRegularOn auxReRooting coveredAux where
  index_ne_top ω k := originChainRegularOn_goodMarked.index_ne_top (proj ω) k
  inverseRatio_tendsto ω k := originChainRegularOn_goodMarked.inverseRatio_tendsto (proj ω) k
  index_small ω hω m hm := originChainRegularOn_goodMarked.index_small (proj ω) hω m hm

/-- **Origin-chain regularity on the two-grid space**, given full covering.  Kept as the
no-regression form of `originChainRegularOn_aux`. -/
theorem originChainRegular_aux (hcov : CoveredOrigins) : OriginChainRegular auxReRooting where
  index_ne_top ω k := originChainRegularOn_goodMarked.index_ne_top (proj ω) k
  inverseRatio_tendsto ω k := originChainRegularOn_goodMarked.inverseRatio_tendsto (proj ω) k
  index_small ω m hm :=
    originChainRegularOn_goodMarked.index_small (proj ω)
      (hcov (proj ω).1.1 (proj ω).1.2) m hm

/-- **Re-rooting inside the selected block translates it**, transferred along `proj`, on the
invariant domain. -/
theorem blockEquivariantOn_aux (m : ℝ) (hm : 0 < m) :
    BlockEquivariantOn auxReRooting coveredAux m := by
  intro ω hω w hw
  exact blockEquivariantOn_goodMarked m hm (proj ω) hω w hw

/-- **Re-rooting inside the selected block translates it**, transferred along `proj`, given
full covering. -/
theorem blockEquivariant_aux (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    auxReRooting.BlockEquivariant m := by
  intro ω w hw
  exact blockEquivariant_goodMarked hcov m hm (proj ω) w hw

theorem measurable_env_aux : Measurable auxReRooting.env := by
  have h : Measurable fun ω : AuxSpace => ω.1.1 := measurable_fst.comp measurable_fst
  exact h.subtype_coe

theorem measurable_grid_aux : Measurable auxReRooting.grid := measurable_snd

/-- The selected block of the two-grid space has a measurable graph and a measurable side
length. -/
theorem measurableBlockGraph_aux (m : ℝ) :
    auxReRooting.MeasurableBlockGraph m ∧ Measurable (auxReRooting.blockSideAt m) :=
  MeasurableSelectedBlocks.measurableSelectedBlock_of_strictMono measurable_env_aux
    measurable_grid_aux fun ω => originChainRegularOn_aux.strictMono ω

/-! ### The dilation action -/

/-- Common scaling on the two-grid space: the good-space dilation on the inner factor and the
dyadic dilation on the auxiliary grid. -/
noncomputable def auxDilate (s : ℝ) (ω : AuxSpace) : AuxSpace :=
  if hs : 0 < s then (goodDilate s ω.1, dilate s hs ω.2) else ω

theorem auxDilate_of_pos {s : ℝ} (hs : 0 < s) (ω : AuxSpace) :
    auxDilate s ω = (goodDilate s ω.1, dilate s hs ω.2) := dif_pos hs

/-- **The dilation action on the two-grid space.** -/
noncomputable def auxScale : ScaleAction auxReRooting where
  dilate := auxDilate
  dilate_shift s hs w ω := by
    show auxDilate s (auxReRooting.shift w ω) = auxReRooting.shift (s • w) (auxDilate s ω)
    rw [auxDilate_of_pos hs (auxReRooting.shift w ω), auxDilate_of_pos hs ω]
    apply Prod.ext
    · exact goodScale.dilate_shift s hs w ω.1
    · exact dilate_translate s hs w ω.2

@[simp] theorem auxScale_dilate (s : ℝ) (ω : AuxSpace) :
    auxScale.dilate s ω = auxDilate s ω := rfl

theorem proj_dilate {s : ℝ} (hs : 0 < s) (ω : AuxSpace) :
    proj (auxScale.dilate s ω) = goodScale.dilate s (proj ω) := by
  show proj (auxDilate s ω) = goodDilate s (proj ω)
  rw [auxDilate_of_pos hs ω, goodDilate_of_pos hs (proj ω), goodDilate_of_pos hs ω.1]
  rfl

/-- **The selected block scales with the configuration**, transferred along `proj`, on the
manuscript's invariant domain. -/
theorem blockScaleCovariantOn_aux (m : ℝ) (hm : 0 < m) :
    auxScale.BlockScaleCovariantOn coveredAux m := by
  intro s hs ω hω
  have h := blockScaleCovariantOn_goodScale m hm s hs (proj ω) hω
  have hset : auxReRooting.blockSetAt m (auxScale.dilate s ω)
      = goodMarked.blockSetAt m (goodScale.dilate s (proj ω)) := by
    rw [← proj_dilate hs ω]
    exact blockSetAt_proj m (auxScale.dilate s ω)
  have hside : auxReRooting.blockSideAt m (auxScale.dilate s ω)
      = goodMarked.blockSideAt m (goodScale.dilate s (proj ω)) := by
    rw [← proj_dilate hs ω]
    exact blockSideAt_proj m (auxScale.dilate s ω)
  refine ⟨?_, ?_⟩
  · rw [hset]; exact h.1
  · rw [hside]; exact h.2

/-- **The selected block scales with the configuration**, transferred along `proj`, given full
covering.  Kept as the no-regression form of `blockScaleCovariantOn_aux`. -/
theorem blockScaleCovariant_aux (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    auxScale.BlockScaleCovariant m :=
  fun s hs ω =>
    blockScaleCovariantOn_aux m hm s hs ω (hcov (proj ω).1.1 (proj ω).1.2)

/-! ### The two-grid law, independence, and the uniform dyadic law of `𝔻'` -/

variable (ν : Measure Env)

/-- **The two-grid law**: the good marked law coupled independently with a second copy of the
uniform dyadic law. -/
noncomputable def auxLaw : Measure AuxSpace := (goodLaw (G := goodSet) ν).prod gridMeasure

theorem isProbabilityMeasure_auxLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    IsProbabilityMeasure (auxLaw ν) := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The unmarked-environment sigma-field of the two-grid space: the events determined by the
inner (good marked) factor.  It carries the environment *and* the interpolation grid, and is
independent of the auxiliary grid `𝔻'`. -/
def auxEnvSigma : EnvSigma AuxSpace :=
  ⟨MeasurableSpace.comap (Prod.fst : AuxSpace → goodSet × Grid) inferInstance⟩

/-- **The auxiliary grid is independent of the environment sigma-field**: in this ordering both
preimages are honest rectangles and the two-grid law is a product. -/
theorem indep_aux [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    ProbabilityTheory.Indep auxEnvSigma.sigma
      (MeasurableSpace.comap auxReRooting.grid inferInstance) (auxLaw ν) := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  rw [ProbabilityTheory.Indep_iff]
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hAB : ((Prod.fst : AuxSpace → goodSet × Grid) ⁻¹' A') ∩ (auxReRooting.grid ⁻¹' B')
      = A' ×ˢ B' := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, auxReRooting_grid]
  have hA2 : ((Prod.fst : AuxSpace → goodSet × Grid) ⁻¹' A')
      = A' ×ˢ (Set.univ : Set Grid) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hB2 : (auxReRooting.grid ⁻¹' B')
      = (Set.univ : Set (goodSet × Grid)) ×ˢ B' := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, auxReRooting_grid]
  rw [hAB, hA2, hB2]
  simp only [auxLaw, Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- The auxiliary grid marginal of the two-grid law is the uniform dyadic law. -/
theorem map_grid_auxLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (auxLaw ν).map auxReRooting.grid = gridMeasure := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  ext s hs
  rw [Measure.map_apply measurable_grid_aux hs]
  have hpre : (auxReRooting.grid ⁻¹' s) = (Set.univ : Set (goodSet × Grid)) ×ˢ s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, auxReRooting_grid]
  rw [hpre]
  simp only [auxLaw, Measure.prod_prod, measure_univ, one_mul]

/-- **The independent uniform dyadic system on the two-grid space.**  The density slot is
filled with the zero functional: the sole consumer
(`Corrector/SpecificEnergyWeakMaximal.measure_densityMaximal_gt_le`) rebuilds the record with
its own truncated density and never uses the incoming `measurable_density`. -/
theorem environmentGrid_aux [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    EnvironmentGrid auxReRooting (auxLaw ν) (fun _ : AuxSpace => (0 : ℝ)) auxEnvSigma where
  le := (measurable_iff_comap_le).1 (measurable_fst : Measurable (Prod.fst : AuxSpace → _))
  measurable_grid := measurable_grid_aux
  measurable_density := measurable_const
  indep := indep_aux ν hgood
  law := by
    rw [map_grid_auxLaw ν hgood]
    exact DyadicCylinderLaw.uniformGridLaw_gridMeasure

/-! ### The mark average and the two-grid transport identity

The remaining field of `SimilarityBlockData` is the mark-averaged mass transport.  It is
*derived* from the checked one-grid identity
`SpatialMaximalForFiniteEnergy.lintegral_blockAverageLint_eq` by averaging the test function
over the extra (interpolation) grid: no second copy of the block kernel is built. -/

/-- The test function averaged over the extra grid: `V(e, 𝔻') = ∫ U((e, 𝔻), 𝔻') d𝔻`.  Note
that the block data of `((e, 𝔻), 𝔻')` depends on `(e, 𝔻')` only, which is what makes the
averaging commute with the block average. -/
noncomputable def markAverage (U : AuxSpace → ℝ≥0∞) (q : goodSet × Grid) : ℝ≥0∞ :=
  ∫⁻ D : Grid, U ((q.1, D), q.2) ∂gridMeasure

theorem measurable_markAverage {U : AuxSpace → ℝ≥0∞} (hU : Measurable U) :
    Measurable (markAverage U) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmap : Measurable fun p : (goodSet × Grid) × Grid =>
      ((((p.1.1, p.2) : goodSet × Grid), p.1.2) : AuxSpace) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have h : Measurable (U ∘ fun p : (goodSet × Grid) × Grid =>
      ((((p.1.1, p.2) : goodSet × Grid), p.1.2) : AuxSpace)) := hU.comp hmap
  have h' : Measurable fun p : (goodSet × Grid) × Grid => U ((p.1.1, p.2), p.1.2) := by
    simpa only [Function.comp_def] using h
  show Measurable fun q : goodSet × Grid => ∫⁻ D : Grid, U ((q.1, D), q.2) ∂gridMeasure
  exact h'.lintegral_prod_right'

/-- Dilating the two-grid point `((e, 𝔻), 𝔻')` dilates the environment and `𝔻'` exactly as the
good-space dilation does, and dilates `𝔻` separately. -/
theorem auxDilate_apply {s : ℝ} (hs : 0 < s) (q : goodSet × Grid) (D : Grid) :
    auxScale.dilate s ((q.1, D), q.2)
      = (((goodScale.dilate s q).1, dilate s hs D), (goodScale.dilate s q).2) := by
  simp only [auxScale_dilate, auxDilate_of_pos hs, goodScale_dilate, goodDilate_of_pos hs]

/-- **The mark average of a scale-invariant function is scale invariant.**  The extra grid is
dilated away using the dilation invariance of the uniform dyadic law. -/
theorem invariantFun_markAverage {U : AuxSpace → ℝ≥0∞} (hU : Measurable U)
    (hUinv : auxScale.InvariantFun U) : goodScale.InvariantFun (markAverage U) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  intro s hs q
  have hG : Measurable fun D : Grid =>
      U (((goodScale.dilate s q).1, D), (goodScale.dilate s q).2) := by
    have hmap : Measurable fun D : Grid =>
        (((((goodScale.dilate s q).1, D) : goodSet × Grid),
          (goodScale.dilate s q).2) : AuxSpace) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have h : Measurable (U ∘ fun D : Grid =>
        (((((goodScale.dilate s q).1, D) : goodSet × Grid),
          (goodScale.dilate s q).2) : AuxSpace)) := hU.comp hmap
    simpa only [Function.comp_def] using h
  have hpt : ∀ D : Grid, U ((q.1, D), q.2)
      = U (((goodScale.dilate s q).1, dilate s hs D), (goodScale.dilate s q).2) := by
    intro D
    rw [← hUinv s hs ((q.1, D), q.2), auxDilate_apply hs q D]
  have hstep : markAverage U q
      = ∫⁻ D : Grid, U (((goodScale.dilate s q).1, dilate s hs D), (goodScale.dilate s q).2)
          ∂gridMeasure := lintegral_congr hpt
  rw [hstep, ← lintegral_map hG (measurable_dilate s hs), map_dilate_gridMeasure hs]
  rfl

/-- Re-rooting the two-grid point commutes with the mark average: the extra grid is translated
away using the translation invariance of the uniform dyadic law. -/
theorem lintegral_shift_markAverage {U : AuxSpace → ℝ≥0∞} (hU : Measurable U)
    (q : goodSet × Grid) (z : Plane) :
    (∫⁻ D : Grid, U (auxReRooting.shift z ((q.1, D), q.2)) ∂gridMeasure)
      = markAverage U (goodMarked.shift z q) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hG : Measurable fun D : Grid =>
      U (((goodMarked.shift z q).1, D), (goodMarked.shift z q).2) := by
    have hmap : Measurable fun D : Grid =>
        (((((goodMarked.shift z q).1, D) : goodSet × Grid),
          (goodMarked.shift z q).2) : AuxSpace) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have h : Measurable (U ∘ fun D : Grid =>
        (((((goodMarked.shift z q).1, D) : goodSet × Grid),
          (goodMarked.shift z q).2) : AuxSpace)) := hU.comp hmap
    simpa only [Function.comp_def] using h
  have hpt : ∀ D : Grid, auxReRooting.shift z ((q.1, D), q.2)
      = (((goodMarked.shift z q).1, translate z D), (goodMarked.shift z q).2) := fun _ => rfl
  calc (∫⁻ D : Grid, U (auxReRooting.shift z ((q.1, D), q.2)) ∂gridMeasure)
      = ∫⁻ D : Grid, U (((goodMarked.shift z q).1, translate z D),
          (goodMarked.shift z q).2) ∂gridMeasure :=
        lintegral_congr fun D => congrArg U (hpt D)
    _ = ∫⁻ D : Grid, U (((goodMarked.shift z q).1, D), (goodMarked.shift z q).2)
          ∂gridMeasure := by
        rw [← lintegral_map hG (measurable_translate_left z),
          UniformGridTranslationInvariance.map_translate_gridMeasure z]
    _ = markAverage U (goodMarked.shift z q) := rfl

/-- **The mark average commutes with the block average.**  Both the block `S_m(0)` and its side
length are read off `(e, 𝔻')` alone, so the constant and the domain of the inner integral do not
depend on the averaged variable; the identity is then Tonelli plus the translation invariance of
the mark law. -/
theorem lintegral_blockAverageLint_markAverage (m : ℝ) {U : AuxSpace → ℝ≥0∞}
    (hU : Measurable U) (q : goodSet × Grid) :
    (∫⁻ D : Grid, auxReRooting.blockAverageLint m U ((q.1, D), q.2) ∂gridMeasure)
      = goodMarked.blockAverageLint m (markAverage U) q := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have h0 : ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2) ≠ 0 := by
    have hpos : (0 : ℝ) < goodMarked.blockSideAt m q ^ 2 := by
      have := goodMarked.blockSideAt_pos m q
      positivity
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hpos
  have hc : (ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hjoint : Measurable fun p : Grid × Plane =>
      U (auxReRooting.shift p.2 ((q.1, p.1), q.2)) := by
    have hmap : Measurable fun p : Grid × Plane =>
        (((((q.1, p.1) : goodSet × Grid), q.2) : AuxSpace), p.2) :=
      ((measurable_const.prodMk measurable_fst).prodMk measurable_const).prodMk measurable_snd
    have h : Measurable ((fun r : AuxSpace × Plane => auxReRooting.shift r.2 r.1) ∘
        fun p : Grid × Plane =>
          (((((q.1, p.1) : goodSet × Grid), q.2) : AuxSpace), p.2)) :=
      auxReRooting.measurable_shift.comp hmap
    have h' : Measurable fun p : Grid × Plane =>
        auxReRooting.shift p.2 (((q.1, p.1), q.2) : AuxSpace) := by
      simpa only [Function.comp_def] using h
    have h'' : Measurable (U ∘ fun p : Grid × Plane =>
        auxReRooting.shift p.2 (((q.1, p.1), q.2) : AuxSpace)) := hU.comp h'
    simpa only [Function.comp_def] using h''
  calc (∫⁻ D : Grid, auxReRooting.blockAverageLint m U ((q.1, D), q.2) ∂gridMeasure)
      = ∫⁻ D : Grid, (ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2))⁻¹ *
          (∫⁻ z in goodMarked.blockSetAt m q,
            U (auxReRooting.shift z ((q.1, D), q.2)) ∂volume) ∂gridMeasure :=
        lintegral_congr fun _ => rfl
    _ = (ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2))⁻¹ *
          ∫⁻ D : Grid, (∫⁻ z in goodMarked.blockSetAt m q,
            U (auxReRooting.shift z ((q.1, D), q.2)) ∂volume) ∂gridMeasure :=
        lintegral_const_mul' _ _ hc
    _ = (ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2))⁻¹ *
          ∫⁻ z in goodMarked.blockSetAt m q, (∫⁻ D : Grid,
            U (auxReRooting.shift z ((q.1, D), q.2)) ∂gridMeasure) ∂volume := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ = (ENNReal.ofReal (goodMarked.blockSideAt m q ^ 2))⁻¹ *
          ∫⁻ z in goodMarked.blockSetAt m q,
            markAverage U (goodMarked.shift z q) ∂volume := by
        congr 1
        exact lintegral_congr fun z => lintegral_shift_markAverage hU q z
    _ = goodMarked.blockAverageLint m (markAverage U) q := rfl

/-- Integration against the two-grid law is integration of the mark average against the good
marked law. -/
theorem lintegral_auxLaw_eq [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet)
    {f : AuxSpace → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f ω ∂(auxLaw ν)) = ∫⁻ q, markAverage f q ∂(goodLaw (G := goodSet) ν) := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hL : (∫⁻ ω, f ω ∂(auxLaw ν))
      = ∫⁻ e : goodSet, ∫⁻ D : Grid, ∫⁻ D' : Grid, f ((e, D), D') ∂gridMeasure
          ∂gridMeasure ∂(ν.comap (Subtype.val : goodSet → Env)) := by
    show (∫⁻ ω, f ω ∂(((ν.comap (Subtype.val : goodSet → Env)).prod gridMeasure).prod
        gridMeasure)) = _
    rw [lintegral_prod _ hf.aemeasurable,
      lintegral_prod _ (hf.lintegral_prod_right').aemeasurable]
  have hR : (∫⁻ q, markAverage f q ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ e : goodSet, ∫⁻ D' : Grid, ∫⁻ D : Grid, f ((e, D), D') ∂gridMeasure
          ∂gridMeasure ∂(ν.comap (Subtype.val : goodSet → Env)) := by
    show (∫⁻ q, markAverage f q
        ∂((ν.comap (Subtype.val : goodSet → Env)).prod gridMeasure)) = _
    rw [lintegral_prod _ (measurable_markAverage hf).aemeasurable]
    rfl
  rw [hL, hR]
  refine lintegral_congr fun e => ?_
  have hswap : Measurable fun p : Grid × Grid => f ((e, p.1), p.2) := by
    have hmap : Measurable fun p : Grid × Grid => ((((e, p.1) : goodSet × Grid), p.2) : AuxSpace) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have h : Measurable (f ∘ fun p : Grid × Grid =>
        ((((e, p.1) : goodSet × Grid), p.2) : AuxSpace)) := hf.comp hmap
    simpa only [Function.comp_def] using h
  exact lintegral_lintegral_swap hswap.aemeasurable

/-- **The mark-averaged transport identity on the two-grid space**, derived from the checked
one-grid identity by averaging the test function over the extra grid.  The only probabilistic
input is `s:eq:MTP` for `ν`, exactly as in the one-grid case. -/
theorem lintegral_blockAverageLint_aux [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) {m : ℝ} (hm : 0 < m)
    {U : AuxSpace → ℝ≥0∞} (hU : Measurable U) (hUinv : auxScale.InvariantFun U) :
    (∫⁻ ω, auxReRooting.blockAverageLint m U ω ∂(auxLaw ν)) = ∫⁻ ω, U ω ∂(auxLaw ν) := by
  have hmeasA : Measurable (auxReRooting.blockAverageLint m U) :=
    MarkedReRooting.measurable_blockAverageLint (measurableBlockGraph_aux m).1
      (measurableBlockGraph_aux m).2 hU
  calc (∫⁻ ω, auxReRooting.blockAverageLint m U ω ∂(auxLaw ν))
      = ∫⁻ q, markAverage (auxReRooting.blockAverageLint m U) q
          ∂(goodLaw (G := goodSet) ν) := lintegral_auxLaw_eq ν hgood hmeasA
    _ = ∫⁻ q, goodMarked.blockAverageLint m (markAverage U) q
          ∂(goodLaw (G := goodSet) ν) :=
        lintegral_congr fun q => lintegral_blockAverageLint_markAverage m hU q
    _ = ∫⁻ q, markAverage U q ∂(goodLaw (G := goodSet) ν) :=
        lintegral_blockAverageLint_eq ν hν hgood hm (measurable_markAverage hU)
          (invariantFun_markAverage hU hUinv)
    _ = ∫⁻ ω, U ω ∂(auxLaw ν) := (lintegral_auxLaw_eq ν hgood hU).symm

/-! ### The invariant domain and the selected-block data -/

/-- **The manuscript's invariant domain on the two-grid space.**  All four conditions of
`SimilarityBlockAveraging.InvariantDomain` are inherited from the one-grid domain
`GoodMarkedScaleAction.invariantDomain_coveredMarked` through `proj`, which intertwines the
re-rooting and the dilation.

`coveredAux` is *measurable* (`measurableSet_coveredAux`), *conull* — this is the manuscript's
Lemma 2.4, `ReflectedGMS.ae_zero_notMem_uncoveredSet`, transported to the two-grid law, and it
needs `s:eq:MTP` — *left by only a Lebesgue-null set of re-rootings* (the `H¹`-null uncovered set
of the environment itself), and *invariant under the dilation action* (dilations fix the origin).
So it is not an empty or degenerate gate: it carries full measure. -/
theorem invariantDomain_coveredAux [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    InvariantDomain auxReRooting auxScale (auxLaw ν) coveredAux := by
  have hprob := isProbabilityMeasure_goodLaw ν hgood
  have hgrid : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hae : ∀ᵐ ω ∂(auxLaw ν), proj ω ∈ coveredMarked :=
    (Measure.quasiMeasurePreserving_fst (μ := goodLaw (G := goodSet) ν)
      (ν := gridMeasure)).tendsto_ae.eventually (ae_mem_coveredMarked ν hν hgood)
  exact invariantDomain_comap (invariantDomain_coveredMarked ν hν hgood) measurable_proj hae
    proj_shift fun s hs ω => proj_dilate hs ω

/-- **The manuscript's selected-block data on the auxiliary two-grid marked space**, from
`s:eq:MTP` and the good set, read on the invariant domain `coveredAux`.  Four fields transfer
definitionally from the one-grid space; the transport identity is
`lintegral_blockAverageLint_aux` and is **not** gated — it tests every measurable scale-invariant
kernel and never looks at the origin chain. -/
theorem similarityBlockDataOn_aux [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    SimilarityBlockDataOn auxReRooting auxScale (auxLaw ν) coveredAux where
  equivariant m hm := blockEquivariantOn_aux m hm
  measurableGraph m _ := (measurableBlockGraph_aux m).1
  measurableSide m _ := (measurableBlockGraph_aux m).2
  scaleCovariant m hm := blockScaleCovariantOn_aux m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_aux ν hν hgood hm hU hUinv

/-- **No regression**: where every good environment has a covered origin — the earlier
manuscript's covering clause `⋃ v, cell v = univ` — the two-grid datum is the ungated
`SimilarityBlockData`, exactly as before the covering clause was weakened. -/
theorem similarityBlockData_aux [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) (hcov : CoveredOrigins) :
    SimilarityBlockData auxReRooting auxScale (auxLaw ν) where
  equivariant m hm := blockEquivariant_aux hcov m hm
  measurableGraph m _ := (measurableBlockGraph_aux m).1
  measurableSide m _ := (measurableBlockGraph_aux m).2
  scaleCovariant m hm := blockScaleCovariant_aux hcov m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_aux ν hν hgood hm hU hUinv

/-! ### Anti-vacuity: the space is inhabited at the actual data -/

end ReflectedGMS.AuxiliaryGridMarkedSpace
