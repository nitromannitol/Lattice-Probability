/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.GoodMarkedScaleAction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedSpace
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedSimilarityActionLaws
import LatticeProb.Bonanno.ReflectedGMS.Spatial.DilatedSelectedBlocks

/-!
# The dilation action on the good marked space and the scale covariance of the blocks

The manuscript's `𝒢_m` and its marked transport both refer to *common scaling* of the
configuration and the marks.  This module supplies that action on the good marked space
`goodSet × Grid` of `Spatial/GoodMarkedSpace`:

* `goodDilate s` — the canonical similarity about the origin at scale `s` on the environment
  (`EnvironmentLaws.similarityTargetEnv s 0`) together with the checked grid dilation
  `UniformGridDilationInvariance.dilate s`; the good set is stable under it
  (`GoodEnvironmentSet.goodEnvironment_similarityTargetEnv`), and in fact under the inverse
  similarity too (`mem_goodSet_of_similarityTargetEnv_mem`);
* `goodScale : SimilarityBlockAveraging.ScaleAction goodMarked` — the compatibility
  `s • (ω − w) = (s • ω) − s • w` is the pair of checked composition laws
  `MarkedSimilarityActionLaws.similarityTargetEnv_zero_translateEnv_eq_translateEnv` and
  `MarkedSimilarityActionLaws.dilate_translate`;
* `blockScaleCovariant_goodScale` — the selected origin block scales with the configuration,
  from `DilatedSelectedBlocks.blockSet_dilate` / `blockSide_dilate`, with existence and
  uniqueness of the selected square supplied by the origin-chain regularity of the good space;
* `invariantFun_rootFE` — the (FE) functional is scale invariant, which is the manuscript's
  hypothesis "scale-invariant `F`" in `s:prop:maximal`;
* `neg_mem_blockSetAt_shift_iff_of_equivariant`, `blockSideAt_shift_of_mem` — the partition
  identity `0 ∈ S_m(w) ↔ w ∈ S_m(0)` and the constancy of the side, for any block-equivariant
  marked re-rooting; these are what the incoming integral of the block transport needs.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GoodMarkedScaleAction

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open SpatialMaximalConsumerForm
open SimilarityBlockAveraging MarkedSimilarityActionLaws DilatedSelectedBlocks
open DyadicApproximation DyadicGridTranslation UniformGridDilationInvariance

/-! ### The good set under the inverse similarity -/

/-- The canonical similarity at scale `1` about the origin is the identity. -/
theorem similarityTargetEnv_one_zero (e : Env) : similarityTargetEnv 1 0 one_pos e = e :=
  (eq_similarityTargetEnv_of_isSimilarity (isSimilarity_refl e)).symm

/-- If the image of an environment under a canonical similarity is good, so is the
environment: apply the inverse similarity. -/
theorem mem_goodSet_of_similarityTargetEnv_mem {s : ℝ} (hs : 0 < s) (u : Plane) {e : Env}
    (h : similarityTargetEnv s u hs e ∈ goodSet) : e ∈ goodSet := by
  have hinv : 0 < s⁻¹ := inv_pos.2 hs
  have h2 : GoodEnvironment
      (similarityTargetEnv s⁻¹ (-(s • u)) hinv (similarityTargetEnv s u hs e)) :=
    goodEnvironment_similarityTargetEnv s⁻¹ (-(s • u)) hinv h
  rw [similarityTargetEnv_similarityTargetEnv,
    similarityTargetEnv_congr _ one_pos (inv_mul_cancel₀ hs.ne')
      (by rw [smul_neg, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_neg_cancel]) e,
    similarityTargetEnv_one_zero] at h2
  exact h2

/-! ### The dilation action -/

/-- Common scaling of a good marked configuration by `s > 0`: the canonical similarity about
the origin on the environment and the dyadic dilation on the grid.  (For `s ≤ 0` the map is
the identity; only positive scales are ever used.) -/
noncomputable def goodDilate (s : ℝ) (ω : goodSet × Grid) : goodSet × Grid :=
  if hs : 0 < s then
    (⟨similarityTargetEnv s 0 hs ω.1.1, goodEnvironment_similarityTargetEnv s 0 hs ω.1.2⟩,
      dilate s hs ω.2)
  else ω

theorem goodDilate_of_pos {s : ℝ} (hs : 0 < s) (ω : goodSet × Grid) :
    goodDilate s ω
      = (⟨similarityTargetEnv s 0 hs ω.1.1, goodEnvironment_similarityTargetEnv s 0 hs ω.1.2⟩,
          dilate s hs ω.2) :=
  dif_pos hs

/-- **The dilation action on the good marked space.**  Compatibility with re-rooting is the
pair of checked composition laws for the canonical similarity and for the grid. -/
noncomputable def goodScale : ScaleAction goodMarked where
  dilate := goodDilate
  dilate_shift s hs w ω := by
    rw [goodDilate_of_pos hs, goodDilate_of_pos hs]
    apply Prod.ext
    · apply Subtype.ext
      show similarityTargetEnv s 0 hs (translateEnv w ω.1.1)
        = translateEnv (s • w) (similarityTargetEnv s 0 hs ω.1.1)
      exact similarityTargetEnv_zero_translateEnv_eq_translateEnv s hs w ω.1.1
    · show dilate s hs (translate w ω.2) = translate (s • w) (dilate s hs ω.2)
      exact dilate_translate s hs w ω.2

@[simp] theorem goodScale_dilate (s : ℝ) (ω : goodSet × Grid) :
    goodScale.dilate s ω = goodDilate s ω := rfl

/-! ### Scale covariance of the selected block -/

/-- **The selected origin block scales with the configuration** at every point of the
manuscript's invariant domain: `S_m(0)(s • ω) = s • S_m(0)(ω)` and
`ℓ(S_m(0)(s • ω)) = s ℓ(S_m(0)(ω))`.

The restriction to the domain is **not** a technicality: off it the statement is false.
`DilatedSelectedBlocks.blockLevel_dilate` shifts the selected level by `levelShift s D`, and the
junk level of a chain with no selected square — which is what an uncovered origin produces — is
the same integer on both sides, so it cannot absorb that shift. -/
theorem blockScaleCovariantOn_goodScale (m : ℝ) (hm : 0 < m) :
    goodScale.BlockScaleCovariantOn coveredMarked m := by
  intro s hs ω hω
  obtain ⟨⟨e, he⟩, D⟩ := ω
  have hchain := originChainRegularOn_goodMarked
  have hdil : goodScale.dilate s (⟨e, he⟩, D)
      = (⟨similarityTargetEnv s 0 hs e, goodEnvironment_similarityTargetEnv s 0 hs he⟩,
          dilate s hs D) :=
    goodDilate_of_pos hs _
  have hex : ∃ l : ℤ, OriginSelected (decode e) D m l :=
    hchain.exists_originSelected' hω hm
  have hmono := hchain.strictMono (goodScale.dilate s (⟨e, he⟩, D))
  rw [hdil] at hmono
  have huniq : ∀ l l' : ℤ,
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l →
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l' → l = l' :=
    fun _ _ hl hl' => originSelected_unique hmono hl hl'
  rw [hdil]
  exact ⟨blockSet_dilate hs e D m hex huniq, blockSide_dilate hs e D m hex huniq⟩

/-- **The selected origin block scales with the configuration** at every point of the good
space, given full covering.  Kept as the no-regression form of
`blockScaleCovariantOn_goodScale`. -/
theorem blockScaleCovariant_goodScale (hcov : CoveredOrigins) (m : ℝ) (hm : 0 < m) :
    goodScale.BlockScaleCovariant m :=
  fun s hs ω => blockScaleCovariantOn_goodScale m hm s hs ω (hcov ω.1.1 ω.1.2)

/-! ### The invariant domain of the good marked space -/

/-- Dilating about the origin fixes the origin, so it does not move the covered-origin
condition. -/
theorem zero_mem_envCoveredSet_similarityTargetEnv_iff {s : ℝ} (hs : 0 < s) (e : Env) :
    (0 : Plane) ∈ Spatial.envCoveredSet (similarityTargetEnv s 0 hs e)
      ↔ (0 : Plane) ∈ Spatial.envCoveredSet e := by
  rw [Spatial.envCoveredSet_of_isSimilarity s 0 hs e (similarityTargetEnv s 0 hs e)
    (isSimilarity_similarityTargetEnv s 0 hs e)]
  constructor
  · rintro ⟨x, hx, hx0⟩
    have hxz : x = 0 := by
      have h1 : s • (x - (0 : Plane)) = (0 : Plane) := hx0
      rw [sub_zero, smul_eq_zero] at h1
      exact h1.resolve_left hs.ne'
    exact hxz ▸ hx
  · intro h0
    exact ⟨0, h0, by simp [positiveSimilarity]⟩

/-- **The manuscript's invariant domain, on the good marked space.**  All four conditions of
`SimilarityBlockAveraging.InvariantDomain` hold with no covering hypothesis: measurability and
conullity come from `GoodMarkedSpace`, the shift condition is the `H¹`-nullity of the uncovered
set (the manuscript's *"hence Lebesgue-almost every point of the plane"*), and dilation
invariance holds because the dilations are about the origin. -/
theorem invariantDomain_coveredMarked (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    InvariantDomain goodMarked goodScale (goodLaw (G := goodSet) ν) coveredMarked where
  measurable := measurableSet_coveredMarked
  ae_mem := ae_mem_coveredMarked ν hν hgood
  shift_ae := volume_shift_notMem_coveredMarked
  dilate_mem s hs ω := by
    rw [show goodScale.dilate s ω = goodDilate s ω from rfl, goodDilate_of_pos hs]
    rw [mem_coveredMarked_iff, mem_coveredMarked_iff]
    exact zero_mem_envCoveredSet_similarityTargetEnv_iff hs _

/-! ### Scale invariance of the (FE) functional -/

/-- **The (FE) functional is scale invariant**: the manuscript's hypothesis on `F` in
`s:prop:maximal`, proved for the rooted (FE) density. -/
theorem invariantFun_rootFE : goodScale.InvariantFun (rootFE goodMarked) := by
  intro s hs ω
  show (RootDensities.rootedFiniteEnergyDensity (decode (goodDilate s ω).1.1) 0).toReal
    = (RootDensities.rootedFiniteEnergyDensity (decode ω.1.1) 0).toReal
  rw [goodDilate_of_pos hs]
  exact congrArg ENNReal.toReal (rootFE_similarityTargetEnv_zero s hs ω.1.1)

/-! ### The partition identity for a block-equivariant re-rooting -/

section Equivariant

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

/-- **`0 ∈ S_m(w) ↔ w ∈ S_m(0)`**: the selected blocks partition the plane.  For any
block-equivariant marked re-rooting. -/
theorem neg_mem_blockSetAt_shift_iff_of_equivariant (hequi : R.BlockEquivariant m) (ω : Ω)
    (z : Plane) : (-z) ∈ R.blockSetAt m (R.shift z ω) ↔ z ∈ R.blockSetAt m ω := by
  constructor
  · intro h
    obtain ⟨hset, -⟩ := hequi (R.shift z ω) (-z) h
    rw [R.shift_shift, add_neg_cancel, R.shift_zero] at hset
    rw [hset]
    show -z + z ∈ R.blockSetAt m (R.shift z ω)
    rw [neg_add_cancel]
    exact R.zero_mem_blockSetAt m _
  · intro h
    obtain ⟨hset, -⟩ := hequi ω z h
    rw [hset]
    show z + -z ∈ R.blockSetAt m ω
    rw [add_neg_cancel]
    exact R.zero_mem_blockSetAt m ω

/-- Inside the selected origin block the re-rooted block has the same side length. -/
theorem blockSideAt_shift_of_mem (hequi : R.BlockEquivariant m) {ω : Ω} {z : Plane}
    (hz : z ∈ R.blockSetAt m ω) : R.blockSideAt m (R.shift z ω) = R.blockSideAt m ω :=
  (hequi ω z hz).2

end Equivariant

end ReflectedGMS.GoodMarkedScaleAction
