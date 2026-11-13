/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.GoodMarkedSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalConsumerForm
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SimilarityBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodEnvironmentSet
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MeasurableSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CoveredOrigin
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicCylinderLaw

/-!
# The good marked space: origin-chain regularity, block data and the independent grid

This module instantiates the abstract inputs of the spatial maximal inequality on the
**good marked space** `goodSet × Grid`, where `goodSet` is the set of environments with finite
large-cell diameter at every radius and sublinear large-cell decay
(`GoodEnvironmentSet.GoodEnvironment`, almost sure under `MassTransport ν` and the (FE) moment
by `s:lem:largecells`).

Everything here is unconditional.  For the marked re-rooting `goodMarked` and the law
`goodLaw ν = (ν|_{goodSet}) ⊗ gridMeasure`:

* `coveredMarked` — the manuscript's **measurable invariant domain**: the configurations whose
  origin lies in a cell.  Since the covering clause of `Geometry` was weakened to
  `μH[1] (uncoveredSet F) = 0`, a prescribed point need no longer be covered, and the manuscript
  correspondingly defines the block partition only where it is defined.  The domain is
  measurable (`measurableSet_coveredMarked`), conull (`ae_mem_coveredMarked`, the manuscript's
  Lemma 2.4) and left by only a Lebesgue-null set of re-rootings
  (`volume_shift_notMem_coveredMarked`, the manuscript's *"hence Lebesgue-almost every point of
  the plane"*);
* `originChainRegularOn_goodMarked` — the manuscript's regularity of the origin dyadic chain on
  that domain, with **no hypothesis**.  The everywhere form
  `originChainRegular_goodMarked` is kept, but it carries the hypothesis `CoveredOrigins`, which
  is full covering in disguise (`coveredOrigin_translateEnv`) and is not available under the
  weakened clause; the two agree when the uncovered set is empty;
* `blockEquivariantOn_goodMarked` — re-rooting inside the selected origin block translates it
  (the translation half of "the partitions commute with similarities"), on the domain and with
  no hypothesis; `blockEquivariant_goodMarked` is its `CoveredOrigins` form;
* `measurableBlockGraph_goodMarked` — the selected block is jointly measurable and its side
  length is measurable; **this needs no covering hypothesis at all**, only strict monotonicity
  of `κ` along the origin chain;
* `environmentGrid_goodMarked` — the independent uniform dyadic system `𝔻'`: the grid
  coordinate is independent of the environment sigma-field and carries the uniform dyadic law,
  and the rooted (FE) density is an environment observable (from
  `RootedFiniteEnergyDensityMeasurable`);
* `measurable_rootFE_goodMarked`, `integrable_rootFE_goodLaw` — the (FE) functional is a
  nonnegative integrable observable of the good marked law, from the manuscript's (FE) moment.

The dilation action and the scale-invariant transport identity (the remaining fields of
`SimilarityBlockAveraging.SimilarityBlockData`) are supplied elsewhere.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GoodMarkedSpace

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open SpatialMaximalConsumerForm ActualSpatialDensityBridge ActualMarkedBlockTransport
open GoodEnvironmentSet DyadicApproximation DyadicGridTranslation DyadicGridLaw
open RootedFiniteEnergyDensityMeasurable

/-! ### The good set and the good marked re-rooting -/

/-- The good environments, as a set. -/
def goodSet : Set Env := {e | GoodEnvironment e}

theorem measurableSet_goodSet : MeasurableSet goodSet := measurableSet_goodEnvironment

theorem goodSet_translateEnv (w : Plane) (e : Env) (he : e ∈ goodSet) :
    translateEnv w e ∈ goodSet :=
  goodEnvironment_translateEnv w he

theorem ae_mem_goodSet (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, e ∈ goodSet :=
  ae_goodEnvironment ν hν hFE

/-- The good marked re-rooting: `SpatialMaximalConsumerForm.goodReRooting` on the good set. -/
noncomputable def goodMarked : MarkedReRooting (goodSet × Grid) :=
  goodReRooting goodSet goodSet_translateEnv

@[simp] theorem goodMarked_env (ω : goodSet × Grid) : goodMarked.env ω = ω.1.1 := rfl

@[simp] theorem goodMarked_grid (ω : goodSet × Grid) : goodMarked.grid ω = ω.2 := rfl

theorem envReRooting_goodMarked : EnvReRooting goodMarked :=
  envReRooting_goodReRooting goodSet_translateEnv

theorem measurable_env_goodMarked : Measurable goodMarked.env :=
  measurable_subtype_coe.comp measurable_fst

theorem measurable_grid_goodMarked : Measurable goodMarked.grid := measurable_snd

/-! ### Origin-chain regularity, pathwise on the good space -/

/-- **Every good environment has its origin in a cell.**

This is an explicit hypothesis, and under the weakened covering clause of `Geometry`
(`μH[1] (uncoveredSet F) = 0` in place of `⋃ v, cell v = Set.univ`) it cannot be discharged —
neither here nor by strengthening `goodSet`.  The reason is structural rather than technical:

* `goodMarked` is `SpatialMaximalConsumerForm.goodReRooting`, whose shift is defined for **every**
  `w : Plane`, so its carrier `goodSet` must satisfy `goodSet_translateEnv`: it is closed under
  every translation of the environment.
* `uncoveredSet (decode (translateEnv w e))` is the translate of `uncoveredSet (decode e)`
  (`Spatial.envCoveredSet_of_isSimilarity` at `IsSimilarity 1 w`), so `CoveredOrigins` holding at
  every translate of a good environment says that **every** point of that environment is covered,
  i.e. `uncoveredSet (decode e) = ∅`.  `coveredOrigin_translateEnv` records this closure.
* `ReflectedGMS.ae_zero_notMem_uncoveredSet` (`Spatial/CoveredOrigin.lean`) — the manuscript's
  Lemma 2.4 — gives only
  `∀ᵐ e ∂ν, (0 : Plane) ∉ uncoveredSet (decode e)`, a statement **at the origin**; and
  `∀ᵐ e ∂ν, uncoveredSet (decode e) = ∅` is precisely what the singular-set manuscript declines
  to assume.  Nor can the condition be folded into `goodSet`: it would have to be simultaneously
  translation closed, measurable and `ν`-conull, and full covering is neither of the last two.

So under the weakened covering clause `OriginChainRegular goodMarked` is **false** (see
`GoodEnvironmentSet.exists_blockIndex_originIndex_le` for an explicit configuration in `goodSet`
whose origin chain has `κ` bounded below), and the manuscript does not claim it: it defines the
selected block `S_m(z)` only at covered `z` and sets the construction to zero elsewhere.  The
corresponding Lean repair is to weaken the `index_small` field of
`SpatialMaximalInequality.OriginChainRegular` from "at every `ω`" to "at almost every shift",
which is available — for `ν`-a.e. environment the uncovered set is Lebesgue-null
(`volume_uncoveredSet`), so Lebesgue-a.e. shift has a covered origin — but which is a change to a
structure this module only consumes. -/
def CoveredOrigins : Prop := ∀ e : Env, e ∈ goodSet → (0 : Plane) ∉ uncoveredSet (decode e)

/-- **`CoveredOrigins` is a full-covering hypothesis in disguise.**  `goodSet` is closed under
every translation of the environment (`goodSet_translateEnv`), so `CoveredOrigins` applies at every
translate of every good environment; and translating an environment translates its uncovered set
(`Spatial.envCoveredSet_of_isSimilarity` at `IsSimilarity 1 w`), so this says that no point of a
good environment is uncovered.

This is the machine-checked half of the argument in `CoveredOrigins`' docstring for why the
hypothesis cannot be discharged from the manuscript's Lemma 2.4, which is a statement about the
origin only. -/
theorem coveredOrigin_translateEnv (h : CoveredOrigins) (e : Env) (he : e ∈ goodSet) (w : Plane) :
    (0 : Plane) ∉ uncoveredSet (decode (translateEnv w e)) :=
  h (translateEnv w e) (goodSet_translateEnv w e he)

/-- **The origin dyadic chain is regular at every point of the good space**, given that every
good environment has its origin in a cell.  The three clauses are the checked pathwise results of
`GoodEnvironmentSet`, applied to the good environment carried by the point; only the third needs
`hcov`, the first two surviving the weakened covering clause unaided because
`NonmacroscopicSelectedBlocks.maxCellDiameter_pos` needs a covered point merely somewhere in the
square and the covered points are dense.  See `CoveredOrigins` for why `hcov` is not removable,
and `originChainRegularOn_goodMarked` for the manuscript's own hypothesis-free form. -/
theorem originChainRegular_goodMarked (hcov : CoveredOrigins) :
    OriginChainRegular goodMarked where
  index_ne_top ω k :=
    blockIndex_originIndex_ne_top (decode ω.1.1) (decode_geometry _) ω.2 k
  inverseRatio_tendsto ω k :=
    tendsto_inverseRatio_ancestor_originIndex (decode ω.1.1) ω.2 ω.1.2.2 k
  index_small ω m hm :=
    exists_blockIndex_originIndex_le (decode ω.1.1) (decode_geometry _) ω.2 m hm
      (hcov ω.1.1 ω.1.2)

/-! ### The manuscript's invariant domain: the configurations with a covered origin -/

/-- **The manuscript's invariant domain on the good marked space**: the configurations whose
origin lies in a cell.

This is the set `CoveredOrigins` asks to be everything.  It is not everything, and cannot be
arranged to be (see `CoveredOrigins`), but it is measurable, conull, invariant under the
dilation action, and — this is the manuscript's *"and hence Lebesgue-almost every point of the
plane"* — left by only a Lebesgue-null set of re-rootings, namely the `H¹`-null uncovered set
of the environment itself.  Those are exactly the four conditions of
`SimilarityBlockAveraging.InvariantDomain`. -/
def coveredMarked : Set (goodSet × Grid) :=
  {ω | (0 : Plane) ∉ uncoveredSet (decode ω.1.1)}

/-- The uncovered set of an environment is the complement of its covered set; `decode e` is
indexed by `Vertex e.val`, which is the index `Spatial.envCoveredSet` unions over. -/
theorem uncoveredSet_decode (e : Env) :
    uncoveredSet (decode e) = (Spatial.envCoveredSet e)ᶜ := rfl

theorem mem_coveredMarked_iff (ω : goodSet × Grid) :
    ω ∈ coveredMarked ↔ (0 : Plane) ∈ Spatial.envCoveredSet (ω.1.1 : Env) := by
  show (0 : Plane) ∉ uncoveredSet (decode (ω.1.1 : Env))
    ↔ (0 : Plane) ∈ Spatial.envCoveredSet (ω.1.1 : Env)
  rw [uncoveredSet_decode]
  simp

theorem measurableSet_coveredMarked : MeasurableSet coveredMarked := by
  have hmap : Measurable fun ω : goodSet × Grid => ((ω.1.1 : Env), (0 : Plane)) :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_const)
  have h := hmap Spatial.measurableSet_envCoveredProd
  have heq : (fun ω : goodSet × Grid => ((ω.1.1 : Env), (0 : Plane))) ⁻¹'
      {p : Env × Plane | p.2 ∈ Spatial.envCoveredSet p.1} = coveredMarked := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact (mem_coveredMarked_iff ω).symm
  rwa [heq] at h

/-- Translating the environment translates its covered set: the origin of `ω - w` is covered
exactly when `w` is covered in `ω`. -/
theorem zero_mem_envCoveredSet_translateEnv_iff (e : Env) (w : Plane) :
    (0 : Plane) ∈ Spatial.envCoveredSet (translateEnv w e)
      ↔ w ∈ Spatial.envCoveredSet e := by
  rw [Spatial.envCoveredSet_of_isSimilarity 1 w one_pos e (translateEnv w e)
    (isSimilarity_translateEnv w e)]
  constructor
  · rintro ⟨x, hx, hx0⟩
    have hxw : x = w := by
      have h1 : (1 : ℝ) • (x - w) = (0 : Plane) := hx0
      rw [one_smul, sub_eq_zero] at h1
      exact h1
    exact hxw ▸ hx
  · intro hw
    exact ⟨w, hw, by simp [positiveSimilarity]⟩

/-- **Re-rooting at `w` moves the origin to `w`**: the re-rootings that leave the invariant
domain are exactly the uncovered points of the environment, an `H¹`-null — hence Lebesgue-null —
set.  This is the manuscript's *"and hence Lebesgue-almost every point of the plane"*. -/
theorem shift_notMem_coveredMarked_iff (ω : goodSet × Grid) (w : Plane) :
    goodMarked.shift w ω ∉ coveredMarked ↔ w ∈ uncoveredSet (decode (ω.1.1 : Env)) := by
  have hshift : ((goodMarked.shift w ω).1.1 : Env) = translateEnv w (ω.1.1 : Env) := rfl
  rw [← not_iff_not, not_not, mem_coveredMarked_iff, hshift,
    zero_mem_envCoveredSet_translateEnv_iff, uncoveredSet_decode]
  simp

/-- The re-rootings leaving the invariant domain form a Lebesgue-null set of offsets. -/
theorem volume_shift_notMem_coveredMarked (ω : goodSet × Grid) :
    volume {z : Plane | goodMarked.shift z ω ∉ coveredMarked} = 0 := by
  have heq : {z : Plane | goodMarked.shift z ω ∉ coveredMarked}
      = uncoveredSet (decode (ω.1.1 : Env)) := by
    ext z
    exact shift_notMem_coveredMarked_iff ω z
  rw [heq]
  exact volume_uncoveredSet (decode_geometry _)

/-- The subtype measure of the good set is a probability measure when the good set has full
measure. -/
theorem isProbabilityMeasure_comap_goodSet (ν : Measure Env) [IsProbabilityMeasure ν]
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    IsProbabilityMeasure (ν.comap (Subtype.val : goodSet → Env)) := by
  refine ⟨?_⟩
  rw [comap_subtype_coe_apply measurableSet_goodSet, Set.image_univ, Subtype.range_coe,
    ← Measure.restrict_apply_univ, Measure.restrict_eq_self_of_ae_mem hgood, measure_univ]

/-- **The invariant domain is conull.**  This is the manuscript's Lemma 2.4
(`ReflectedGMS.ae_zero_notMem_uncoveredSet`), transported to the good marked law: the origin lies
in a cell for `ν`-almost every environment, hence for `goodLaw ν`-almost every configuration. -/
theorem ae_mem_coveredMarked (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    ∀ᵐ ω : goodSet × Grid ∂(goodLaw (G := goodSet) ν), ω ∈ coveredMarked := by
  have hprob := isProbabilityMeasure_comap_goodSet ν hgood
  have hgrid : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hsub : ∀ᵐ x : goodSet ∂(ν.comap (Subtype.val : goodSet → Env)),
      (0 : Plane) ∉ uncoveredSet (decode (x : Env)) := by
    refine ae_of_ae_map (f := (Subtype.val : goodSet → Env))
      (p := fun e : Env => (0 : Plane) ∉ uncoveredSet (decode e))
      measurable_subtype_coe.aemeasurable ?_
    rw [map_comap_subtype_coe measurableSet_goodSet ν]
    exact ae_restrict_of_ae (ReflectedGMS.ae_zero_notMem_uncoveredSet ν hν)
  exact (Measure.quasiMeasurePreserving_fst
    (μ := ν.comap (Subtype.val : goodSet → Env)) (ν := gridMeasure)).tendsto_ae.eventually hsub

/-- **The origin dyadic chain is regular on the manuscript's invariant domain**, with no
hypothesis at all.  This replaces `originChainRegular_goodMarked`, whose `hcov` is a full-covering
hypothesis in disguise (`coveredOrigin_translateEnv`) and is not available under the singular-set
covering clause.  The first two clauses are unchanged — they hold at every configuration, because
`NonmacroscopicSelectedBlocks.maxCellDiameter_pos` needs a covered point merely *somewhere* in the
square and the covered points are dense — and only the third is read on the domain. -/
theorem originChainRegularOn_goodMarked : OriginChainRegularOn goodMarked coveredMarked where
  index_ne_top ω k :=
    blockIndex_originIndex_ne_top (decode ω.1.1) (decode_geometry _) ω.2 k
  inverseRatio_tendsto ω k :=
    tendsto_inverseRatio_ancestor_originIndex (decode ω.1.1) ω.2 ω.1.2.2 k
  index_small ω hω m hm :=
    exists_blockIndex_originIndex_le (decode ω.1.1) (decode_geometry _) ω.2 m hm hω

/-! ### Block equivariance and measurability -/

/-- **Re-rooting inside the selected origin block translates it**, at every point of the
manuscript's invariant domain, and with no hypothesis.

Nothing is asked at the re-rooted configuration `ω - w`, whose origin may well be uncovered: the
selected origin square at `ω` is *transported* to `ω - w` by
`originSelected_translateEnv`, and `blockLevel_eq` then pins it down there from strict
monotonicity of `κ`, which holds at every configuration. -/
theorem blockEquivariantOn_goodMarked (m : ℝ) (hm : 0 < m) :
    BlockEquivariantOn goodMarked coveredMarked m := by
  rintro ⟨⟨e, he⟩, D⟩ hω w hw
  have hchain := originChainRegularOn_goodMarked
  have hw' : w ∈ halfOpenSquare D (originIndex (blockLevel (decode e) D m)) := hw
  have hsel : OriginSelected (decode e) D m (blockLevel (decode e) D m) :=
    originSelected_blockLevel (hchain.exists_originSelected' hω hm)
  have hsel' : OriginSelected (decode (translateEnv w e)) (translate w D) m
      (blockLevel (decode e) D m) :=
    (originSelected_translateEnv m e D w le_rfl hw').2 hsel
  have hlevel : blockLevel (decode (translateEnv w e)) (translate w D) m
      = blockLevel (decode e) D m :=
    blockLevel_eq (hchain.strictMono (goodMarked.shift w (⟨e, he⟩, D))) hsel'
  refine ⟨?_, ?_⟩
  · show halfOpenSquare (translate w D)
        (originIndex (blockLevel (decode (translateEnv w e)) (translate w D) m))
      = (fun y : Plane => w + y) ⁻¹'
        halfOpenSquare D (originIndex (blockLevel (decode e) D m))
    rw [hlevel]
    exact halfOpenSquare_translate D w le_rfl hw'
  · show side (translate w D) (blockLevel (decode (translateEnv w e)) (translate w D) m)
      = side D (blockLevel (decode e) D m)
    rw [side_translate, hlevel]

/-- **Re-rooting inside the selected origin block translates it**, at every point of the
good space, given full covering.  Kept as the no-regression form of
`blockEquivariantOn_goodMarked`; under the earlier manuscript's covering clause `hcov` holds and
the two coincide (`blockEquivariant_of_blockEquivariantOn`). -/
theorem blockEquivariant_goodMarked (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    goodMarked.BlockEquivariant m :=
  fun ω w hw => blockEquivariantOn_goodMarked m hm ω (hcov ω.1.1 ω.1.2) w hw

/-- The selected block has a measurable graph and a measurable side length.  **No covering
hypothesis**: only strict monotonicity of `κ` along the origin chain is used, and that holds at
every configuration of the good space. -/
theorem measurableBlockGraph_goodMarked (m : ℝ) :
    goodMarked.MeasurableBlockGraph m ∧ Measurable (goodMarked.blockSideAt m) :=
  MeasurableSelectedBlocks.measurableSelectedBlock_of_strictMono measurable_env_goodMarked
    measurable_grid_goodMarked fun ω => originChainRegularOn_goodMarked.strictMono ω

/-! ### The (FE) functional on the good space -/

/-- The re-rooted (FE) functional is the rooted (FE) density of the environment. -/
theorem rootFE_goodMarked_shift (ω : goodSet × Grid) (z : Plane) :
    rootFE goodMarked (goodMarked.shift z ω)
      = (RootDensities.rootedFiniteEnergyDensity (decode ω.1.1) z).toReal := by
  have h := ofReal_rootFE_shift envReRooting_goodMarked ω z
  show rootFE goodMarked (goodMarked.shift z ω)
    = (RootDensities.rootedFiniteEnergyDensity (decode (goodMarked.env ω)) z).toReal
  rw [← h, ENNReal.toReal_ofReal (rootFE_nonneg _ _)]

theorem measurable_rootFE_goodMarked : Measurable (rootFE goodMarked) :=
  (measurable_rootedFiniteEnergyDensity_zero.comp measurable_env_goodMarked).ennreal_toReal

/-- The (FE) functional is scale invariant: the rooted (FE) density at the origin is unchanged
by the canonical similarity about the origin. -/
theorem rootFE_similarityTargetEnv_zero (s : ℝ) (hs : 0 < s) (e : Env) :
    RootDensities.rootedFiniteEnergyDensity (decode (similarityTargetEnv s 0 hs e)) 0
      = RootDensities.rootedFiniteEnergyDensity (decode e) 0 := by
  have h := rootedFiniteEnergyDensity_similarity hs (isSimilarity_similarityTargetEnv s 0 hs e) 0
  have hzero : positiveSimilarity s 0 (0 : Plane) = 0 := by
    simp [positiveSimilarity]
  rwa [hzero] at h

/-! ### The good marked law -/

variable (ν : Measure Env)

theorem isProbabilityMeasure_goodLaw [IsProbabilityMeasure ν]
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) : IsProbabilityMeasure (goodLaw (G := goodSet) ν) := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The environment sigma-field of the good marked space: the events determined by the
good-environment coordinate. -/
def envSigma : EnvSigma (goodSet × Grid) :=
  ⟨MeasurableSpace.comap (fun ω : goodSet × Grid => ω.1) inferInstance⟩

set_option maxHeartbeats 1000000 in
/-- The rooted (FE) density is an environment observable: jointly measurable in the
good-environment coordinate and the point. -/
theorem measurable_density_goodMarked :
    @Measurable ((goodSet × Grid) × Plane) ℝ
      (@Prod.instMeasurableSpace (goodSet × Grid) Plane envSigma.sigma _) _
      fun p => rootFE goodMarked (goodMarked.shift p.2 p.1) := by
  have hfun : (fun p : (goodSet × Grid) × Plane => rootFE goodMarked (goodMarked.shift p.2 p.1))
      = fun p => (RootDensities.rootedFiniteEnergyDensity (decode p.1.1.1) p.2).toReal :=
    funext fun p => rootFE_goodMarked_shift p.1 p.2
  rw [hfun]
  have h1 : @Measurable ((goodSet × Grid) × Plane) (goodSet × Grid)
      (@Prod.instMeasurableSpace (goodSet × Grid) Plane envSigma.sigma _) envSigma.sigma
      Prod.fst := @measurable_fst _ _ envSigma.sigma _
  have h2 : @Measurable (goodSet × Grid) goodSet envSigma.sigma _ Prod.fst :=
    (@measurable_iff_comap_le _ _ envSigma.sigma _ Prod.fst).2 le_rfl
  have h3 : @Measurable ((goodSet × Grid) × Plane) Env
      (@Prod.instMeasurableSpace (goodSet × Grid) Plane envSigma.sigma _) _
      fun p => (p.1.1.1 : Env) := by
    have h := (measurable_subtype_coe.comp h2).comp h1
    simpa only [Function.comp_def] using h
  have h4 : @Measurable ((goodSet × Grid) × Plane) Plane
      (@Prod.instMeasurableSpace (goodSet × Grid) Plane envSigma.sigma _) _ Prod.snd :=
    @measurable_snd _ _ envSigma.sigma _
  have hπ : @Measurable ((goodSet × Grid) × Plane) (Env × Plane)
      (@Prod.instMeasurableSpace (goodSet × Grid) Plane envSigma.sigma _) _
      fun p => ((p.1.1.1 : Env), p.2) := h3.prodMk h4
  have h := (measurable_rootedFiniteEnergyDensity.ennreal_toReal).comp hπ
  simpa only [Function.comp_def] using h

/-- The grid coordinate is independent of the environment sigma-field under the good marked
law: it is a product law. -/
theorem indep_goodMarked [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    ProbabilityTheory.Indep envSigma.sigma
      (MeasurableSpace.comap goodMarked.grid inferInstance) (goodLaw (G := goodSet) ν) := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  rw [ProbabilityTheory.Indep_iff]
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hAB : ((fun ω : goodSet × Grid => ω.1) ⁻¹' A') ∩ (goodMarked.grid ⁻¹' B')
      = A' ×ˢ B' := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, goodMarked_grid]
  have hA2 : ((fun ω : goodSet × Grid => ω.1) ⁻¹' A') = A' ×ˢ (Set.univ : Set Grid) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have hB2 : (goodMarked.grid ⁻¹' B') = (Set.univ : Set goodSet) ×ˢ B' := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, goodMarked_grid]
  rw [hAB, hA2, hB2]
  simp only [goodLaw, Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- The grid marginal of the good marked law is the uniform dyadic law. -/
theorem map_grid_goodLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (goodLaw (G := goodSet) ν).map goodMarked.grid = gridMeasure := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  ext s hs
  rw [Measure.map_apply measurable_grid_goodMarked hs]
  have hpre : (goodMarked.grid ⁻¹' s) = (Set.univ : Set goodSet) ×ˢ s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, goodMarked_grid]
  rw [hpre]
  simp only [goodLaw, Measure.prod_prod, measure_univ, one_mul]

/-- **The independent uniform dyadic system on the good marked space.** -/
theorem environmentGrid_goodMarked [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    EnvironmentGrid goodMarked (goodLaw (G := goodSet) ν) (rootFE goodMarked) envSigma where
  le := (@measurable_iff_comap_le _ _ _ _ (fun ω : goodSet × Grid => ω.1)).1 measurable_fst
  measurable_grid := measurable_grid_goodMarked
  measurable_density := measurable_density_goodMarked
  indep := indep_goodMarked ν hgood
  law := by
    rw [map_grid_goodLaw ν hgood]
    exact DyadicCylinderLaw.uniformGridLaw_gridMeasure

/-! ### Integrability of the (FE) functional -/

/-- The (FE) moment on the good marked law is bounded by the (FE) moment on `ν`. -/
theorem lintegral_rootedFiniteEnergyDensity_goodLaw_le [IsProbabilityMeasure ν]
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (∫⁻ ω : goodSet × Grid, RootDensities.rootedFiniteEnergyDensity (decode ω.1.1) 0
        ∂(goodLaw (G := goodSet) ν))
      ≤ ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hg : Measurable fun e : Env => RootDensities.rootedFiniteEnergyDensity (decode e) 0 :=
    measurable_rootedFiniteEnergyDensity_zero
  have hmeas : Measurable fun ω : goodSet × Grid =>
      RootDensities.rootedFiniteEnergyDensity (decode ω.1.1) 0 :=
    hg.comp measurable_env_goodMarked
  have hprod : (∫⁻ ω : goodSet × Grid, RootDensities.rootedFiniteEnergyDensity (decode ω.1.1) 0
        ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ x : goodSet, RootDensities.rootedFiniteEnergyDensity (decode x.1) 0
          ∂(ν.comap (Subtype.val : goodSet → Env)) := by
    rw [goodLaw, lintegral_prod _ hmeas.aemeasurable]
    refine lintegral_congr fun x => ?_
    show (∫⁻ _ : Grid, RootDensities.rootedFiniteEnergyDensity (decode x.1) 0 ∂gridMeasure)
      = RootDensities.rootedFiniteEnergyDensity (decode x.1) 0
    rw [lintegral_const, measure_univ, mul_one]
  have hmap : (∫⁻ x : goodSet, RootDensities.rootedFiniteEnergyDensity (decode x.1) 0
        ∂(ν.comap (Subtype.val : goodSet → Env)))
      = ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0
          ∂(ν.restrict goodSet) := by
    rw [← map_comap_subtype_coe measurableSet_goodSet ν]
    exact (lintegral_map hg measurable_subtype_coe).symm
  rw [hprod, hmap]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- **The (FE) functional is integrable on the good marked space**, from the manuscript's (FE)
moment. -/
theorem integrable_rootFE_goodLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    Integrable (rootFE goodMarked) (goodLaw (G := goodSet) ν) :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_rootedFiniteEnergyDensity_zero.comp measurable_env_goodMarked).aemeasurable
    (ne_top_of_le_ne_top hFE (lintegral_rootedFiniteEnergyDensity_goodLaw_le ν hgood))

end ReflectedGMS.GoodMarkedSpace
