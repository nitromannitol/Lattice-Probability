/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.CopyDifferenceThreeGridSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AuxiliaryGridMarkedSpace

/-!
# The auxiliary **three**-grid marked space

`Spatial/AuxiliaryGridMarkedSpace` builds the two-grid space
`AuxSpace = (goodSet × Grid) × Grid`, whose inner grid is the interpolation grid and whose
**outer** grid is the independent auxiliary dyadic system `𝔻'` of `s:prop:maximal`.  That space
serves `hsub`, `hpatch` and `hconv`, whose consumer projections land in
`MarkedEnvironment = Env × Grid`.

`hcopies` needs one grid more.  Its consumer projection lands in
`GridIndependenceCoupling.CoupledSpace = Env × Grid × Grid` and
`GatedResidualWeakMaximal.copyDifferenceWeakMaximal_of_twoGridSpace` demands
`μ.map proj = ν ⊗ (𝔻 ⊗ 𝔻)`, i.e. **two** independent interpolation grids; and the re-rooting
grid `R.grid` cannot be either of them, because `hprojA` makes both of `proj`'s grid components
`𝒜.sigma`-measurable while `henv.indep` makes `R.grid` independent of `𝒜.sigma` and `henv.law`
forces `μ.map R.grid` to be a `UniformGridLaw`, not a Dirac.  So a genuine third coordinate is
required.

## It is one extra instantiation, not new mathematics

The two-grid construction is uniform in the mark factor, so this file is that construction run
once more with the base space `goodSet × Grid` replaced by `AuxSpace`:

```
TriSpace := AuxSpace × Grid = ((goodSet × Grid) × Grid) × Grid
triLaw ν := (auxLaw ν) ⊗ gridMeasure
```

with the **new auxiliary grid outermost**.  Reading the three grids of a point
`ω = (((e, 𝔻₁), 𝔻₂), 𝔻')`:

* `ω.1.1.2 = 𝔻₁` — the **first** interpolation grid copy;
* `ω.1.2 = 𝔻₂` — the **second** interpolation grid copy;
* `ω.2 = 𝔻'` — the auxiliary dyadic system of the maximal inequality, i.e. `triReRooting.grid`.

Because `triProj ω = (ω.1.1.1, ω.2)` intertwines `env`, `grid` and `shift` *definitionally* with
`GoodMarkedSpace.goodMarked`, `OriginChainRegular`, block equivariance, the measurable block
graph and block scale covariance all transfer by `rfl` from the checked one-grid statements,
exactly as in the two-grid file.

The mass-transport field costs no kernel algebra either: the test function is averaged over the
extra grid `𝔻₂` (`markAverage3`) and the identity is reduced to the already-checked two-grid
`AuxiliaryGridMarkedSpace.lintegral_blockAverageLint_aux` by Tonelli plus the translation and
dilation invariance of the uniform dyadic law.

Nothing here is assumed beyond the manuscript's own hypotheses: `MassTransport ν` and the finite
(FE) moment, through `GoodMarkedSpace.ae_mem_goodSet`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceThreeGridSpace

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open GoodMarkedScaleAction SimilarityBlockAveraging SpatialMaximalConsumerForm
open DyadicApproximation DyadicGridTranslation DyadicGridLaw UniformGridDilationInvariance
open SpatialMaximalForFiniteEnergy MarkedSimilarityActionLaws
open UniformGridTranslationInvariance AuxiliaryGridMarkedSpace

/-! ### The carrier and the projection -/

/-- **The auxiliary three-grid marked space.**  A point is `(((e, 𝔻₁), 𝔻₂), 𝔻')` with `e` a good
environment, `𝔻₁` and `𝔻₂` the two independent interpolation grid copies and `𝔻'` the auxiliary
dyadic system of the maximal inequality.  The auxiliary grid is the *outermost* factor, so the
inner factor is literally the two-grid space of `Spatial/AuxiliaryGridMarkedSpace`. -/
abbrev TriSpace : Type := AuxSpace × Grid

/-- The projection onto (environment, **auxiliary** grid).  All selected-block data transfers
along it; it is definitionally compatible with `env`, `grid` and `shift`. -/
def triProj (ω : TriSpace) : goodSet × Grid := (ω.1.1.1, ω.2)

/-! ### The marked re-rooting -/

/-- **The marked re-rooting of the three-grid space.**  The environment is read off the innermost
factor, the dyadic system `𝔻'` is the outermost grid, and re-rooting acts simultaneously on the
two-grid configuration and on the auxiliary grid. -/
noncomputable def triReRooting : MarkedReRooting TriSpace where
  env ω := ω.1.1.1.1
  grid ω := ω.2
  shift w ω := (auxReRooting.shift w ω.1, translate w ω.2)
  measurable_shift := by
    have h1 : Measurable fun p : TriSpace × Plane => auxReRooting.shift p.2 p.1.1 := by
      have hmap : Measurable fun p : TriSpace × Plane => ((p.1.1 : AuxSpace), p.2) :=
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
      have h : Measurable ((fun r : AuxSpace × Plane => auxReRooting.shift r.2 r.1) ∘
          fun p : TriSpace × Plane => ((p.1.1 : AuxSpace), p.2)) :=
        auxReRooting.measurable_shift.comp hmap
      simpa only [Function.comp_def] using h
    have h2 : Measurable fun p : TriSpace × Plane => translate p.2 p.1.2 := by
      have hmap : Measurable fun p : TriSpace × Plane => ((p.1.2 : Grid), p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have h : Measurable ((fun r : Grid × Plane => translate r.2 r.1) ∘
          fun p : TriSpace × Plane => ((p.1.2 : Grid), p.2)) :=
        measurable_translate.comp hmap
      simpa only [Function.comp_def] using h
    exact h1.prodMk h2
  shift_zero ω := by
    apply Prod.ext
    · exact auxReRooting.shift_zero ω.1
    · exact translate_zero ω.2
  shift_shift w z ω := by
    apply Prod.ext
    · exact auxReRooting.shift_shift w z ω.1
    · exact translate_translate w z ω.2

@[simp] theorem triReRooting_env (ω : TriSpace) : triReRooting.env ω = ω.1.1.1.1 := rfl

@[simp] theorem triReRooting_grid (ω : TriSpace) : triReRooting.grid ω = ω.2 := rfl

/-! ### `triProj` intertwines everything, definitionally -/

theorem blockSetAt_triProj (m : ℝ) (ω : TriSpace) :
    triReRooting.blockSetAt m ω = goodMarked.blockSetAt m (triProj ω) := rfl

theorem blockSideAt_triProj (m : ℝ) (ω : TriSpace) :
    triReRooting.blockSideAt m ω = goodMarked.blockSideAt m (triProj ω) := rfl

/-- Re-rooting the three-grid configuration re-roots its image in the good marked space:
`triProj` intertwines the two shifts definitionally. -/
theorem triProj_shift (z : Plane) (ω : TriSpace) :
    triProj (triReRooting.shift z ω) = goodMarked.shift z (triProj ω) := rfl

/-! ### Origin-chain regularity, block equivariance and measurability -/

/-- The manuscript's invariant domain on the three-grid space, pulled back along `triProj`. -/
def coveredTri : Set TriSpace := triProj ⁻¹' coveredMarked

theorem measurable_triProj : Measurable triProj :=
  (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd

theorem measurableSet_coveredTri : MeasurableSet coveredTri :=
  measurable_triProj measurableSet_coveredMarked

/-- **Origin-chain regularity on the three-grid space**, on the manuscript's invariant domain.
All three clauses are statements about `originBlockIndex`, which is computed from `env` and
`grid` alone. -/
theorem originChainRegularOn_tri : OriginChainRegularOn triReRooting coveredTri where
  index_ne_top ω k := originChainRegularOn_goodMarked.index_ne_top (triProj ω) k
  inverseRatio_tendsto ω k := originChainRegularOn_goodMarked.inverseRatio_tendsto (triProj ω) k
  index_small ω hω m hm := originChainRegularOn_goodMarked.index_small (triProj ω) hω m hm

/-- **Origin-chain regularity on the three-grid space**, given full covering.  Kept as the
no-regression form of `originChainRegularOn_tri`. -/
theorem originChainRegular_tri (hcov : CoveredOrigins) : OriginChainRegular triReRooting where
  index_ne_top ω k := originChainRegularOn_goodMarked.index_ne_top (triProj ω) k
  inverseRatio_tendsto ω k := originChainRegularOn_goodMarked.inverseRatio_tendsto (triProj ω) k
  index_small ω m hm :=
    originChainRegularOn_goodMarked.index_small (triProj ω)
      (hcov (triProj ω).1.1 (triProj ω).1.2) m hm

/-- **Re-rooting inside the selected block translates it**, transferred along `triProj`, on the
invariant domain. -/
theorem blockEquivariantOn_tri (m : ℝ) (hm : 0 < m) :
    BlockEquivariantOn triReRooting coveredTri m := by
  intro ω hω w hw
  exact blockEquivariantOn_goodMarked m hm (triProj ω) hω w hw

/-- **Re-rooting inside the selected block translates it**, transferred along `triProj`, given
full covering. -/
theorem blockEquivariant_tri (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    triReRooting.BlockEquivariant m := by
  intro ω w hw
  exact blockEquivariant_goodMarked hcov m hm (triProj ω) w hw

theorem measurable_env_tri : Measurable triReRooting.env := by
  have h : Measurable fun ω : TriSpace => ω.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  exact h.subtype_coe

theorem measurable_grid_tri : Measurable triReRooting.grid := measurable_snd

/-- The selected block of the three-grid space has a measurable graph and a measurable side
length. -/
theorem measurableBlockGraph_tri (m : ℝ) :
    triReRooting.MeasurableBlockGraph m ∧ Measurable (triReRooting.blockSideAt m) :=
  MeasurableSelectedBlocks.measurableSelectedBlock_of_strictMono measurable_env_tri
    measurable_grid_tri fun ω => originChainRegularOn_tri.strictMono ω

/-! ### The dilation action -/

/-- Common scaling on the three-grid space: the two-grid dilation on the inner factor and the
dyadic dilation on the auxiliary grid. -/
noncomputable def triDilate (s : ℝ) (ω : TriSpace) : TriSpace :=
  if hs : 0 < s then (auxDilate s ω.1, dilate s hs ω.2) else ω

theorem triDilate_of_pos {s : ℝ} (hs : 0 < s) (ω : TriSpace) :
    triDilate s ω = (auxDilate s ω.1, dilate s hs ω.2) := dif_pos hs

/-- **The dilation action on the three-grid space.** -/
noncomputable def triScale : ScaleAction triReRooting where
  dilate := triDilate
  dilate_shift s hs w ω := by
    show triDilate s (triReRooting.shift w ω) = triReRooting.shift (s • w) (triDilate s ω)
    rw [triDilate_of_pos hs (triReRooting.shift w ω), triDilate_of_pos hs ω]
    apply Prod.ext
    · exact auxScale.dilate_shift s hs w ω.1
    · exact dilate_translate s hs w ω.2

@[simp] theorem triScale_dilate (s : ℝ) (ω : TriSpace) :
    triScale.dilate s ω = triDilate s ω := rfl

theorem triProj_dilate {s : ℝ} (hs : 0 < s) (ω : TriSpace) :
    triProj (triScale.dilate s ω) = goodScale.dilate s (triProj ω) := by
  show triProj (triDilate s ω) = goodDilate s (triProj ω)
  rw [triDilate_of_pos hs ω, goodDilate_of_pos hs (triProj ω), auxDilate_of_pos hs ω.1,
    goodDilate_of_pos hs ω.1.1]
  rfl

/-- **The selected block scales with the configuration**, transferred along `triProj`, on the
manuscript's invariant domain. -/
theorem blockScaleCovariantOn_tri (m : ℝ) (hm : 0 < m) :
    triScale.BlockScaleCovariantOn coveredTri m := by
  intro s hs ω hω
  have h := blockScaleCovariantOn_goodScale m hm s hs (triProj ω) hω
  have hset : triReRooting.blockSetAt m (triScale.dilate s ω)
      = goodMarked.blockSetAt m (goodScale.dilate s (triProj ω)) := by
    rw [← triProj_dilate hs ω]
    exact blockSetAt_triProj m (triScale.dilate s ω)
  have hside : triReRooting.blockSideAt m (triScale.dilate s ω)
      = goodMarked.blockSideAt m (goodScale.dilate s (triProj ω)) := by
    rw [← triProj_dilate hs ω]
    exact blockSideAt_triProj m (triScale.dilate s ω)
  refine ⟨?_, ?_⟩
  · rw [hset]; exact h.1
  · rw [hside]; exact h.2

/-- **The selected block scales with the configuration**, transferred along `triProj`, given full
covering.  Kept as the no-regression form of `blockScaleCovariantOn_tri`. -/
theorem blockScaleCovariant_tri (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    triScale.BlockScaleCovariant m :=
  fun s hs ω =>
    blockScaleCovariantOn_tri m hm s hs ω (hcov (triProj ω).1.1 (triProj ω).1.2)

/-! ### The three-grid law, independence, and the uniform dyadic law of `𝔻'` -/

variable (ν : Measure Env)

/-- **The three-grid law**: the two-grid law coupled independently with a third copy of the
uniform dyadic law. -/
noncomputable def triLaw : Measure TriSpace := (auxLaw ν).prod gridMeasure

theorem isProbabilityMeasure_triLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    IsProbabilityMeasure (triLaw ν) := by
  have := isProbabilityMeasure_auxLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The unmarked-environment sigma-field of the three-grid space: the events determined by the
inner (two-grid) factor.  It carries the environment *and both* interpolation grids, and is
independent of the auxiliary grid `𝔻'`. -/
def triEnvSigma : EnvSigma TriSpace :=
  ⟨MeasurableSpace.comap (Prod.fst : TriSpace → AuxSpace) inferInstance⟩

/-- **The auxiliary grid is independent of the environment sigma-field**: in this ordering both
preimages are honest rectangles and the three-grid law is a product. -/
theorem indep_tri [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    ProbabilityTheory.Indep triEnvSigma.sigma
      (MeasurableSpace.comap triReRooting.grid inferInstance) (triLaw ν) := by
  have := isProbabilityMeasure_auxLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  rw [ProbabilityTheory.Indep_iff]
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hAB : ((Prod.fst : TriSpace → AuxSpace) ⁻¹' A') ∩ (triReRooting.grid ⁻¹' B')
      = A' ×ˢ B' := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, triReRooting_grid]
  have hA2 : ((Prod.fst : TriSpace → AuxSpace) ⁻¹' A')
      = A' ×ˢ (Set.univ : Set Grid) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hB2 : (triReRooting.grid ⁻¹' B')
      = (Set.univ : Set AuxSpace) ×ˢ B' := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, triReRooting_grid]
  rw [hAB, hA2, hB2]
  simp only [triLaw, Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- The auxiliary grid marginal of the three-grid law is the uniform dyadic law. -/
theorem map_grid_triLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (triLaw ν).map triReRooting.grid = gridMeasure := by
  have := isProbabilityMeasure_auxLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  ext s hs
  rw [Measure.map_apply measurable_grid_tri hs]
  have hpre : (triReRooting.grid ⁻¹' s) = (Set.univ : Set AuxSpace) ×ˢ s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, triReRooting_grid]
  rw [hpre]
  simp only [triLaw, Measure.prod_prod, measure_univ, one_mul]

/-- **The independent uniform dyadic system on the three-grid space.**  The density slot is
filled with the zero functional, exactly as in the two-grid case: the consumer rebuilds the
record with its own truncated density and never uses the incoming `measurable_density`. -/
theorem environmentGrid_tri [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    EnvironmentGrid triReRooting (triLaw ν) (fun _ : TriSpace => (0 : ℝ)) triEnvSigma where
  le := (measurable_iff_comap_le).1 (measurable_fst : Measurable (Prod.fst : TriSpace → _))
  measurable_grid := measurable_grid_tri
  measurable_density := measurable_const
  indep := indep_tri ν hgood
  law := by
    rw [map_grid_triLaw ν hgood]
    exact DyadicCylinderLaw.uniformGridLaw_gridMeasure

/-! ### The mark average and the three-grid transport identity

The remaining field of `SimilarityBlockData` is the mark-averaged mass transport.  It is
*derived* from the checked two-grid identity
`AuxiliaryGridMarkedSpace.lintegral_blockAverageLint_aux` by averaging the test function over the
second interpolation grid `𝔻₂`: no second copy of the block kernel is built. -/

/-- The test function averaged over the extra grid: `V(r) = ∫ U((r.1, 𝔻₂), r.2) d𝔻₂`.  The block
data of `((r.1, 𝔻₂), r.2)` depends on `(e, 𝔻')` only, which is what makes the averaging commute
with the block average. -/
noncomputable def markAverage3 (U : TriSpace → ℝ≥0∞) (r : AuxSpace) : ℝ≥0∞ :=
  ∫⁻ D : Grid, U ((r.1, D), r.2) ∂gridMeasure

theorem measurable_markAverage3 {U : TriSpace → ℝ≥0∞} (hU : Measurable U) :
    Measurable (markAverage3 U) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmap : Measurable fun p : AuxSpace × Grid =>
      ((((p.1.1, p.2) : AuxSpace), p.1.2) : TriSpace) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have h : Measurable (U ∘ fun p : AuxSpace × Grid =>
      ((((p.1.1, p.2) : AuxSpace), p.1.2) : TriSpace)) := hU.comp hmap
  have h' : Measurable fun p : AuxSpace × Grid => U ((p.1.1, p.2), p.1.2) := by
    simpa only [Function.comp_def] using h
  show Measurable fun r : AuxSpace => ∫⁻ D : Grid, U ((r.1, D), r.2) ∂gridMeasure
  exact h'.lintegral_prod_right'

/-- Dilating the three-grid point `((r.1, 𝔻₂), r.2)` dilates the two-grid configuration exactly
as the two-grid dilation does, and dilates `𝔻₂` separately. -/
theorem triDilate_apply {s : ℝ} (hs : 0 < s) (r : AuxSpace) (D : Grid) :
    triScale.dilate s ((r.1, D), r.2)
      = (((auxScale.dilate s r).1, dilate s hs D), (auxScale.dilate s r).2) := by
  simp only [triScale_dilate, triDilate_of_pos hs, auxScale_dilate, auxDilate_of_pos hs]

/-- **The mark average of a scale-invariant function is scale invariant.**  The extra grid is
dilated away using the dilation invariance of the uniform dyadic law. -/
theorem invariantFun_markAverage3 {U : TriSpace → ℝ≥0∞} (hU : Measurable U)
    (hUinv : triScale.InvariantFun U) : auxScale.InvariantFun (markAverage3 U) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  intro s hs r
  have hG : Measurable fun D : Grid =>
      U (((auxScale.dilate s r).1, D), (auxScale.dilate s r).2) := by
    have hmap : Measurable fun D : Grid =>
        (((((auxScale.dilate s r).1, D) : AuxSpace),
          (auxScale.dilate s r).2) : TriSpace) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have h : Measurable (U ∘ fun D : Grid =>
        (((((auxScale.dilate s r).1, D) : AuxSpace),
          (auxScale.dilate s r).2) : TriSpace)) := hU.comp hmap
    simpa only [Function.comp_def] using h
  have hpt : ∀ D : Grid, U ((r.1, D), r.2)
      = U (((auxScale.dilate s r).1, dilate s hs D), (auxScale.dilate s r).2) := by
    intro D
    rw [← hUinv s hs ((r.1, D), r.2), triDilate_apply hs r D]
  have hstep : markAverage3 U r
      = ∫⁻ D : Grid, U (((auxScale.dilate s r).1, dilate s hs D), (auxScale.dilate s r).2)
          ∂gridMeasure := lintegral_congr hpt
  rw [hstep, ← lintegral_map hG (measurable_dilate s hs), map_dilate_gridMeasure hs]
  rfl

/-- Re-rooting the three-grid point commutes with the mark average: the extra grid is translated
away using the translation invariance of the uniform dyadic law. -/
theorem lintegral_shift_markAverage3 {U : TriSpace → ℝ≥0∞} (hU : Measurable U)
    (r : AuxSpace) (z : Plane) :
    (∫⁻ D : Grid, U (triReRooting.shift z ((r.1, D), r.2)) ∂gridMeasure)
      = markAverage3 U (auxReRooting.shift z r) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hG : Measurable fun D : Grid =>
      U (((auxReRooting.shift z r).1, D), (auxReRooting.shift z r).2) := by
    have hmap : Measurable fun D : Grid =>
        (((((auxReRooting.shift z r).1, D) : AuxSpace),
          (auxReRooting.shift z r).2) : TriSpace) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have h : Measurable (U ∘ fun D : Grid =>
        (((((auxReRooting.shift z r).1, D) : AuxSpace),
          (auxReRooting.shift z r).2) : TriSpace)) := hU.comp hmap
    simpa only [Function.comp_def] using h
  have hpt : ∀ D : Grid, triReRooting.shift z ((r.1, D), r.2)
      = (((auxReRooting.shift z r).1, translate z D), (auxReRooting.shift z r).2) := fun _ => rfl
  calc (∫⁻ D : Grid, U (triReRooting.shift z ((r.1, D), r.2)) ∂gridMeasure)
      = ∫⁻ D : Grid, U (((auxReRooting.shift z r).1, translate z D),
          (auxReRooting.shift z r).2) ∂gridMeasure :=
        lintegral_congr fun D => congrArg U (hpt D)
    _ = ∫⁻ D : Grid, U (((auxReRooting.shift z r).1, D), (auxReRooting.shift z r).2)
          ∂gridMeasure := by
        rw [← lintegral_map hG (measurable_translate_left z),
          UniformGridTranslationInvariance.map_translate_gridMeasure z]
    _ = markAverage3 U (auxReRooting.shift z r) := rfl

/-- **The mark average commutes with the block average.**  Both the block `S_m(0)` and its side
length are read off `(e, 𝔻')` alone, so the constant and the domain of the inner integral do not
depend on the averaged variable; the identity is then Tonelli plus the translation invariance of
the mark law. -/
theorem lintegral_blockAverageLint_markAverage3 (m : ℝ) {U : TriSpace → ℝ≥0∞}
    (hU : Measurable U) (r : AuxSpace) :
    (∫⁻ D : Grid, triReRooting.blockAverageLint m U ((r.1, D), r.2) ∂gridMeasure)
      = auxReRooting.blockAverageLint m (markAverage3 U) r := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have h0 : ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2) ≠ 0 := by
    have hpos : (0 : ℝ) < auxReRooting.blockSideAt m r ^ 2 := by
      have := auxReRooting.blockSideAt_pos m r
      positivity
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hpos
  have hc : (ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hjoint : Measurable fun p : Grid × Plane =>
      U (triReRooting.shift p.2 ((r.1, p.1), r.2)) := by
    have hmap : Measurable fun p : Grid × Plane =>
        (((((r.1, p.1) : AuxSpace), r.2) : TriSpace), p.2) :=
      ((measurable_const.prodMk measurable_fst).prodMk measurable_const).prodMk measurable_snd
    have h : Measurable ((fun q : TriSpace × Plane => triReRooting.shift q.2 q.1) ∘
        fun p : Grid × Plane =>
          (((((r.1, p.1) : AuxSpace), r.2) : TriSpace), p.2)) :=
      triReRooting.measurable_shift.comp hmap
    have h' : Measurable fun p : Grid × Plane =>
        triReRooting.shift p.2 (((r.1, p.1), r.2) : TriSpace) := by
      simpa only [Function.comp_def] using h
    have h'' : Measurable (U ∘ fun p : Grid × Plane =>
        triReRooting.shift p.2 (((r.1, p.1), r.2) : TriSpace)) := hU.comp h'
    simpa only [Function.comp_def] using h''
  calc (∫⁻ D : Grid, triReRooting.blockAverageLint m U ((r.1, D), r.2) ∂gridMeasure)
      = ∫⁻ D : Grid, (ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2))⁻¹ *
          (∫⁻ z in auxReRooting.blockSetAt m r,
            U (triReRooting.shift z ((r.1, D), r.2)) ∂volume) ∂gridMeasure :=
        lintegral_congr fun _ => rfl
    _ = (ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2))⁻¹ *
          ∫⁻ D : Grid, (∫⁻ z in auxReRooting.blockSetAt m r,
            U (triReRooting.shift z ((r.1, D), r.2)) ∂volume) ∂gridMeasure :=
        lintegral_const_mul' _ _ hc
    _ = (ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2))⁻¹ *
          ∫⁻ z in auxReRooting.blockSetAt m r, (∫⁻ D : Grid,
            U (triReRooting.shift z ((r.1, D), r.2)) ∂gridMeasure) ∂volume := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ = (ENNReal.ofReal (auxReRooting.blockSideAt m r ^ 2))⁻¹ *
          ∫⁻ z in auxReRooting.blockSetAt m r,
            markAverage3 U (auxReRooting.shift z r) ∂volume := by
        congr 1
        exact lintegral_congr fun z => lintegral_shift_markAverage3 hU r z
    _ = auxReRooting.blockAverageLint m (markAverage3 U) r := rfl

/-- Integration against the three-grid law is integration of the mark average against the
two-grid law. -/
theorem lintegral_triLaw_eq [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet)
    {f : TriSpace → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f ω ∂(triLaw ν)) = ∫⁻ r, markAverage3 f r ∂(auxLaw ν) := by
  have := isProbabilityMeasure_goodLaw ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hL : (∫⁻ ω, f ω ∂(triLaw ν))
      = ∫⁻ q : goodSet × Grid, ∫⁻ D : Grid, ∫⁻ D' : Grid, f ((q, D), D') ∂gridMeasure
          ∂gridMeasure ∂(goodLaw (G := goodSet) ν) := by
    show (∫⁻ ω, f ω ∂(((goodLaw (G := goodSet) ν).prod gridMeasure).prod gridMeasure)) = _
    rw [lintegral_prod _ hf.aemeasurable,
      lintegral_prod _ (hf.lintegral_prod_right').aemeasurable]
  have hR : (∫⁻ r, markAverage3 f r ∂(auxLaw ν))
      = ∫⁻ q : goodSet × Grid, ∫⁻ D' : Grid, ∫⁻ D : Grid, f ((q, D), D') ∂gridMeasure
          ∂gridMeasure ∂(goodLaw (G := goodSet) ν) := by
    show (∫⁻ r, markAverage3 f r
        ∂((goodLaw (G := goodSet) ν).prod gridMeasure)) = _
    rw [lintegral_prod _ (measurable_markAverage3 hf).aemeasurable]
    rfl
  rw [hL, hR]
  refine lintegral_congr fun q => ?_
  have hswap : Measurable fun p : Grid × Grid => f ((q, p.1), p.2) := by
    have hmap : Measurable fun p : Grid × Grid => ((((q, p.1) : AuxSpace), p.2) : TriSpace) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have h : Measurable (f ∘ fun p : Grid × Grid =>
        ((((q, p.1) : AuxSpace), p.2) : TriSpace)) := hf.comp hmap
    simpa only [Function.comp_def] using h
  exact lintegral_lintegral_swap hswap.aemeasurable

/-- **The mark-averaged transport identity on the three-grid space**, derived from the checked
two-grid identity by averaging the test function over the second interpolation grid.  The only
probabilistic input is `s:eq:MTP` for `ν`, exactly as in the one- and two-grid cases. -/
theorem lintegral_blockAverageLint_tri [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) {m : ℝ} (hm : 0 < m)
    {U : TriSpace → ℝ≥0∞} (hU : Measurable U) (hUinv : triScale.InvariantFun U) :
    (∫⁻ ω, triReRooting.blockAverageLint m U ω ∂(triLaw ν)) = ∫⁻ ω, U ω ∂(triLaw ν) := by
  have hmeasA : Measurable (triReRooting.blockAverageLint m U) :=
    MarkedReRooting.measurable_blockAverageLint (measurableBlockGraph_tri m).1
      (measurableBlockGraph_tri m).2 hU
  calc (∫⁻ ω, triReRooting.blockAverageLint m U ω ∂(triLaw ν))
      = ∫⁻ r, markAverage3 (triReRooting.blockAverageLint m U) r ∂(auxLaw ν) :=
        lintegral_triLaw_eq ν hgood hmeasA
    _ = ∫⁻ r, auxReRooting.blockAverageLint m (markAverage3 U) r ∂(auxLaw ν) :=
        lintegral_congr fun r => lintegral_blockAverageLint_markAverage3 m hU r
    _ = ∫⁻ r, markAverage3 U r ∂(auxLaw ν) :=
        lintegral_blockAverageLint_aux ν hν hgood hm (measurable_markAverage3 hU)
          (invariantFun_markAverage3 hU hUinv)
    _ = ∫⁻ ω, U ω ∂(triLaw ν) := (lintegral_triLaw_eq ν hgood hU).symm

/-! ### The invariant domain and the selected-block data -/

/-- **The manuscript's invariant domain on the three-grid space.**  Inherited from the one-grid
domain through `triProj`, which intertwines the re-rooting and the dilation, exactly as
`AuxiliaryGridMarkedSpace.invariantDomain_coveredAux` does for the two-grid space.  `coveredTri`
is measurable, conull (Lemma 2.4 under `s:eq:MTP`), left by only a Lebesgue-null set of
re-rootings, and invariant under the dilation action. -/
theorem invariantDomain_coveredTri [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    InvariantDomain triReRooting triScale (triLaw ν) coveredTri := by
  have := isProbabilityMeasure_auxLaw ν hgood
  have hgrid : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hae : ∀ᵐ ω ∂(triLaw ν), triProj ω ∈ coveredMarked :=
    (Measure.quasiMeasurePreserving_fst (μ := auxLaw ν)
      (ν := gridMeasure)).tendsto_ae.eventually (invariantDomain_coveredAux ν hν hgood).ae_mem
  exact invariantDomain_comap (invariantDomain_coveredMarked ν hν hgood) measurable_triProj hae
    triProj_shift fun s hs ω => triProj_dilate hs ω

/-- **The manuscript's selected-block data on the auxiliary three-grid marked space**, from
`s:eq:MTP` and the good set, read on the invariant domain `coveredTri`.  Four fields transfer
definitionally from the one-grid space; the transport identity is
`lintegral_blockAverageLint_tri` and is **not** gated. -/
theorem similarityBlockDataOn_tri [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    SimilarityBlockDataOn triReRooting triScale (triLaw ν) coveredTri where
  equivariant m hm := blockEquivariantOn_tri m hm
  measurableGraph m _ := (measurableBlockGraph_tri m).1
  measurableSide m _ := (measurableBlockGraph_tri m).2
  scaleCovariant m hm := blockScaleCovariantOn_tri m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_tri ν hν hgood hm hU hUinv

/-- **No regression**: where every good environment has a covered origin — the earlier
manuscript's covering clause `⋃ v, cell v = univ` — the three-grid datum is the ungated
`SimilarityBlockData`. -/
theorem similarityBlockData_tri [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) (hcov : CoveredOrigins) :
    SimilarityBlockData triReRooting triScale (triLaw ν) where
  equivariant m hm := blockEquivariant_tri hcov m hm
  measurableGraph m _ := (measurableBlockGraph_tri m).1
  measurableSide m _ := (measurableBlockGraph_tri m).2
  scaleCovariant m hm := blockScaleCovariant_tri hcov m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_tri ν hν hgood hm hU hUinv

/-! ### Anti-vacuity: the space is inhabited at the actual data -/

end ReflectedGMS.CopyDifferenceThreeGridSpace
