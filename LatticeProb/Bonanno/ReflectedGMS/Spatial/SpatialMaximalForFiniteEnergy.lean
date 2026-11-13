/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedScaleAction
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureSpatialDiameterBounds
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActualUniformSublinearity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.QuenchedFormulation

/-!
# `s:prop:maximal` for the rooted (FE) density, from `s:eq:MTP` and the (FE) moment

This module closes the spatial maximal inequality for the actual environment law.  Its main
theorem is the consumers' hypothesis `hMax`, now a **theorem**:

`ae_exists_ballBound_rootedFiniteEnergyDensity (ν) [IsProbabilityMeasure ν]
  (hν : MassTransport ν) (hFE : ∫⁻ ρ_FE(𝓗_e)(0) dν ≠ ∞) :
  ∀ᵐ e ∂ν, ∃ M ≠ ∞, ∀ r > 0, ∫_{B̄_r} ρ_FE(𝓗_e) ≤ r² M`,

i.e. the third clause of manuscript Proposition `s:prop:maximal` for the (FE) functional, with
**no hypothesis beyond the manuscript's own** `s:eq:MTP` and finite (FE) moment.  The
consumers are then discharged verbatim at the end of the file: `s:eq:Wbound`
(`ae_spatialDiameterCellBounds`), the block interpolant and `s:lem:smallblocks` for the
concrete interpolant (rows `n = 1`, `n = 16`), the hypotheses of `r:prop:log`, and the
recurrence-lane quenched wrapper.

## The last producer: the marked block transport from `s:eq:MTP`

`Spatial/GoodMarkedSpace` and `Spatial/GoodMarkedScaleAction` supply every field of
`SimilarityBlockAveraging.SimilarityBlockDataOn … coveredMarked` except the transport identity
`E[A_m U] = E[U]` for scale-invariant `U`.  That identity is the manuscript's application of
marked mass transport to

`T(ω, w, z) = 1_{z ∈ S_m(w)} ℓ(S_m(w))⁻² U(ω − z)`,

*"for an arbitrary nonnegative scale-invariant `U`"*.  Here:

* `goodBlockKernel m U` is that kernel on the good marked space (`S_m(w)` is the selected
  origin block of the configuration re-rooted at `w`, translated back);
* `blockKernel m U` is its extension by zero to the actual marked space `Env × Grid`, along
  the measurable embedding of the good cylinder;
* `markedSimilarityCovariant_blockKernel` is `s:eq:Tcov` for it — degree `−2` under the full
  similarity group — from the scale covariance of the blocks, the compatibility of the two
  actions and the scale invariance of `U` (`goodBlockKernel_dilate_shift`); off the good set
  both sides vanish because the good set is stable under similarities in both directions;
* `Corrector/MarkedMassTransportProducer.markedMassTransport_of_massTransport` then yields the
  transport identity on `ν ⊗ gridMeasure` from `MassTransport ν` alone, and
  `lintegral_prod_eq_lintegral_goodLaw` moves it to the good marked law;
* the outgoing integral at the origin is the block average `A_m U` and the incoming integral
  is `U` (the partition identity `0 ∈ S_m(z) ↔ z ∈ S_m(0)` and `volume S_m(0) = ℓ²`):
  `lintegral_blockAverageLint_eq`.

Nothing is assumed: every input is checked upstream, and the manuscript's argument is followed
step by step.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SpatialMaximalForFiniteEnergy

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport GoodEnvironmentSet GoodMarkedSpace
open GoodMarkedScaleAction SimilarityBlockAveraging MarkedSimilarityActionLaws
open SpatialMaximalConsumerForm DyadicApproximation DyadicGridTranslation DyadicGridLaw
open UniformGridDilationInvariance MarkedMassTransportProducer

/-! ### The inclusion of the good marked space -/

/-- The inclusion of the good marked space into the actual marked space `Env × Grid`. -/
def incl : goodSet × Grid → Env × Grid := Prod.map (Subtype.val : goodSet → Env) id

theorem measurable_incl : Measurable incl := measurable_subtype_coe.prodMap measurable_id

variable (ν : Measure Env)

/-- The good marked law pushed forward along the inclusion is the actual marked law
`ν ⊗ gridMeasure`, because the good set has full measure. -/
theorem map_incl_goodLaw [IsProbabilityMeasure ν] (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    (goodLaw (G := goodSet) ν).map incl = ν.prod gridMeasure := by
  have := isProbabilityMeasure_comap_goodSet ν hgood
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  show ((ν.comap (Subtype.val : goodSet → Env)).prod gridMeasure).map
      (Prod.map (Subtype.val : goodSet → Env) id) = ν.prod gridMeasure
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id,
    map_comap_subtype_coe measurableSet_goodSet ν, Measure.restrict_eq_self_of_ae_mem hgood]

/-- Integrals against the actual marked law are integrals against the good marked law. -/
theorem lintegral_prod_eq_lintegral_goodLaw [IsProbabilityMeasure ν]
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) {f : Env × Grid → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂(ν.prod gridMeasure)) = ∫⁻ ω, f (incl ω) ∂(goodLaw (G := goodSet) ν) := by
  rw [← map_incl_goodLaw ν hgood, lintegral_map hf measurable_incl]

/-- The joint similarity of the actual marked space, read on the good space: dilation after
re-rooting. -/
theorem markedSimilarity_incl (s : ℝ) (u : Plane) (hs : 0 < s) (ω : goodSet × Grid) :
    markedSimilarity s u hs (incl ω) = incl (goodDilate s (goodMarked.shift u ω)) := by
  rw [goodDilate_of_pos hs]
  show (similarityTargetEnv s u hs ω.1.1, dilate s hs (translate u ω.2))
    = (similarityTargetEnv s 0 hs (translateEnv u ω.1.1), dilate s hs (translate u ω.2))
  rw [similarityTargetEnv_zero_translateEnv s hs u ω.1.1]

/-! ### The manuscript's invariant domain, inside the kernel

Under the singular-set manuscript's covering clause the selected origin block is undefined at an
uncovered origin, so `GoodMarkedScaleAction.blockScaleCovariantOn_goodScale` and
`GoodMarkedSpace.blockEquivariantOn_goodMarked` hold only on `GoodMarkedSpace.coveredMarked`.
But `MassTransport` tests kernels that are similarity covariant **pointwise**, so the block
transport must stay *exactly* covariant.

The repair is to build the domain into the kernel's support: the transport is required to
re-root at a **covered** source point, i.e. `goodMarked.shift w ω ∈ coveredMarked`.  That
condition is itself exactly similarity covariant (`goodDilate_mem_coveredMarked_iff` together
with the compatibility `hshift` of the two actions), so the kernel remains exactly covariant of
degree `−2`; off it both sides of `s:eq:Tcov` vanish.  The two boundary integrals then survive:
the outgoing one at `w = 0` is unchanged on the domain, and the incoming one loses only the
uncovered `z`, a Lebesgue-null set of offsets (`volume_shift_notMem_coveredMarked`, the
manuscript's *"hence Lebesgue-almost every point of the plane"*).

**No regression**: when every origin is covered the added condition is vacuous
(`coveredMarked_eq_univ`) and every statement below is literally the old one; the ungated
`similarityBlockData_goodMarked` is kept and reproved from the gated data. -/

/-- Dilating about the origin fixes the origin, so it does not move the covered-origin
condition.  This is the `dilate_mem` field of
`GoodMarkedScaleAction.invariantDomain_coveredMarked` without the measure that structure is
packaged with; this file needs it before any law is in sight. -/
theorem goodDilate_mem_coveredMarked_iff {s : ℝ} (hs : 0 < s) (ω : goodSet × Grid) :
    goodDilate s ω ∈ coveredMarked ↔ ω ∈ coveredMarked := by
  rw [goodDilate_of_pos hs, mem_coveredMarked_iff, mem_coveredMarked_iff]
  exact zero_mem_envCoveredSet_similarityTargetEnv_iff hs _

/-- **No regression**: where every good environment has a covered origin — the earlier
manuscript's covering clause — the invariant domain is everything. -/
theorem coveredMarked_eq_univ (hcov : CoveredOrigins) :
    (coveredMarked : Set (goodSet × Grid)) = Set.univ := by
  ext ω
  exact iff_of_true (hcov ω.1.1 ω.1.2) (Set.mem_univ ω)

section Equivariant

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ} {G : Set Ω}

/-- **`0 ∈ S_m(w) ↔ w ∈ S_m(0)`** on an invariant domain: the gated form of
`GoodMarkedScaleAction.neg_mem_blockSetAt_shift_iff_of_equivariant`.  Both re-rootings have to
lie in the domain, one for each direction. -/
theorem neg_mem_blockSetAt_shift_iff_of_equivariantOn (hequi : BlockEquivariantOn R G m)
    {ω : Ω} (hω : ω ∈ G) {z : Plane} (hzω : R.shift z ω ∈ G) :
    (-z) ∈ R.blockSetAt m (R.shift z ω) ↔ z ∈ R.blockSetAt m ω := by
  constructor
  · intro h
    obtain ⟨hset, -⟩ := hequi (R.shift z ω) hzω (-z) h
    rw [R.shift_shift, add_neg_cancel, R.shift_zero] at hset
    rw [hset]
    show -z + z ∈ R.blockSetAt m (R.shift z ω)
    rw [neg_add_cancel]
    exact R.zero_mem_blockSetAt m _
  · intro h
    obtain ⟨hset, -⟩ := hequi ω hω z h
    rw [hset]
    show z + -z ∈ R.blockSetAt m ω
    rw [add_neg_cancel]
    exact R.zero_mem_blockSetAt m ω

/-- Inside the selected origin block the re-rooted block has the same side length: the gated
form of `GoodMarkedScaleAction.blockSideAt_shift_of_mem`. -/
theorem blockSideAt_shift_of_memOn (hequi : BlockEquivariantOn R G m) {ω : Ω} (hω : ω ∈ G)
    {z : Plane} (hz : z ∈ R.blockSetAt m ω) :
    R.blockSideAt m (R.shift z ω) = R.blockSideAt m ω :=
  (hequi ω hω z hz).2

end Equivariant

/-! ### The manuscript block transport -/

section Kernel

variable (m : ℝ) (U : goodSet × Grid → ℝ≥0∞)

/-- The re-rooting at the source point lands in the manuscript's invariant domain: the source
point of the transport is required to be a **covered** point of the environment.  Written as a
condition on the re-rooted configuration so that the checked `GoodMarkedSpace` lemmas apply to
it directly; by `GoodMarkedSpace.shift_notMem_coveredMarked_iff` it says exactly
`q.2.1 ∈ Spatial.envCoveredSet q.1.1.1`. -/
def coveredSource : Set ((goodSet × Grid) × Plane × Plane) :=
  {q | goodMarked.shift q.2.1 q.1 ∈ coveredMarked}

/-- The support of the block transport: the source point is covered, and `z ∈ S_m(w)`, i.e.
`z − w` lies in the selected origin block of the configuration re-rooted at `w`. -/
def goodBlockSupport : Set ((goodSet × Grid) × Plane × Plane) :=
  coveredSource ∩
    ((fun q : (goodSet × Grid) × Plane × Plane => (goodMarked.shift q.2.1 q.1, q.2.2 - q.2.1)) ⁻¹'
      {p : (goodSet × Grid) × Plane | p.2 ∈ goodMarked.blockSetAt m p.1})

theorem mem_goodBlockSupport {q : (goodSet × Grid) × Plane × Plane} :
    q ∈ goodBlockSupport m
      ↔ goodMarked.shift q.2.1 q.1 ∈ coveredMarked ∧
        q.2.2 - q.2.1 ∈ goodMarked.blockSetAt m (goodMarked.shift q.2.1 q.1) := Iff.rfl

/-- The same at an explicit triple, so that the projections are already reduced. -/
theorem mem_goodBlockSupport_triple (ω : goodSet × Grid) (w z : Plane) :
    (ω, w, z) ∈ goodBlockSupport m
      ↔ goodMarked.shift w ω ∈ coveredMarked ∧
        z - w ∈ goodMarked.blockSetAt m (goodMarked.shift w ω) := Iff.rfl

/-- **No regression**: where every origin is covered the domain condition is vacuous and the
support is the old one. -/
theorem mem_goodBlockSupport_of_coveredOrigins (hcov : CoveredOrigins)
    {q : (goodSet × Grid) × Plane × Plane} :
    q ∈ goodBlockSupport m
      ↔ q.2.2 - q.2.1 ∈ goodMarked.blockSetAt m (goodMarked.shift q.2.1 q.1) := by
  rw [mem_goodBlockSupport]
  refine and_iff_right ?_
  rw [coveredMarked_eq_univ hcov]
  exact Set.mem_univ _

/-- The weight of the block transport: `ℓ(S_m(w))⁻² U(ω − z)`. -/
noncomputable def goodBlockWeight (q : (goodSet × Grid) × Plane × Plane) : ℝ≥0∞ :=
  (ENNReal.ofReal (goodMarked.blockSideAt m (goodMarked.shift q.2.1 q.1) ^ 2))⁻¹ *
    U (goodMarked.shift q.2.2 q.1)

/-- **The manuscript's marked block transport** on the good marked space:
`T(ω, w, z) = 1_{z ∈ S_m(w)} ℓ(S_m(w))⁻² U(ω − z)`. -/
noncomputable def goodBlockKernel : (goodSet × Grid) × Plane × Plane → ℝ≥0∞ :=
  (goodBlockSupport m).indicator (goodBlockWeight m U)

/-- Re-rooting at the source point is jointly measurable in the kernel arguments. -/
theorem measurable_shift_source :
    Measurable fun q : (goodSet × Grid) × Plane × Plane => goodMarked.shift q.2.1 q.1 := by
  have hpr : Measurable fun q : (goodSet × Grid) × Plane × Plane => (q.1, q.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h : Measurable ((fun p : (goodSet × Grid) × Plane => goodMarked.shift p.2 p.1) ∘
      fun q : (goodSet × Grid) × Plane × Plane => (q.1, q.2.1)) :=
    goodMarked.measurable_shift.comp hpr
  simpa only [Function.comp_def] using h

/-- Re-rooting at the target point is jointly measurable in the kernel arguments. -/
theorem measurable_shift_target :
    Measurable fun q : (goodSet × Grid) × Plane × Plane => goodMarked.shift q.2.2 q.1 := by
  have hpr : Measurable fun q : (goodSet × Grid) × Plane × Plane => (q.1, q.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have h : Measurable ((fun p : (goodSet × Grid) × Plane => goodMarked.shift p.2 p.1) ∘
      fun q : (goodSet × Grid) × Plane × Plane => (q.1, q.2.2)) :=
    goodMarked.measurable_shift.comp hpr
  simpa only [Function.comp_def] using h

theorem measurableSet_coveredSource : MeasurableSet coveredSource :=
  measurable_shift_source measurableSet_coveredMarked

theorem measurableSet_goodBlockSupport : MeasurableSet (goodBlockSupport m) := by
  have hgraph := (measurableBlockGraph_goodMarked m).1
  have hdiff : Measurable fun q : (goodSet × Grid) × Plane × Plane => q.2.2 - q.2.1 :=
    (measurable_snd.comp measurable_snd).sub (measurable_fst.comp measurable_snd)
  exact measurableSet_coveredSource.inter ((measurable_shift_source.prodMk hdiff) hgraph)

theorem measurable_goodBlockWeight (hU : Measurable U) : Measurable (goodBlockWeight m U) := by
  have hside := (measurableBlockGraph_goodMarked m).2
  have h1 : Measurable fun q : (goodSet × Grid) × Plane × Plane =>
      goodMarked.blockSideAt m (goodMarked.shift q.2.1 q.1) := by
    have h := hside.comp measurable_shift_source
    simpa only [Function.comp_def] using h
  have h2 : Measurable fun q : (goodSet × Grid) × Plane × Plane =>
      U (goodMarked.shift q.2.2 q.1) := by
    have h := hU.comp measurable_shift_target
    simpa only [Function.comp_def] using h
  exact ((h1.pow_const 2).ennreal_ofReal.inv).mul h2

theorem measurable_goodBlockKernel (hU : Measurable U) : Measurable (goodBlockKernel m U) :=
  (measurable_goodBlockWeight m U hU).indicator (measurableSet_goodBlockSupport m)

/-- The good cylinder: the points of `(Env × Grid) × Plane × Plane` whose environment is good. -/
def goodCylinder : Set ((Env × Grid) × Plane × Plane) := {x | x.1.1 ∈ goodSet}

theorem measurableSet_goodCylinder : MeasurableSet goodCylinder :=
  (measurable_fst.comp measurable_fst) measurableSet_goodSet

/-- The block transport read on the good cylinder. -/
noncomputable def cylinderKernel (y : goodCylinder) : ℝ≥0∞ :=
  goodBlockKernel m U ((⟨y.1.1.1, y.2⟩, y.1.1.2), y.1.2.1, y.1.2.2)

theorem measurable_cylinderKernel (hU : Measurable U) : Measurable (cylinderKernel m U) := by
  have hval : Measurable fun y : goodCylinder => (y.1 : (Env × Grid) × Plane × Plane) :=
    measurable_subtype_coe
  have he : Measurable fun y : goodCylinder => (y.1.1.1 : Env) := by
    have h := (measurable_fst.comp measurable_fst).comp hval
    simpa only [Function.comp_def] using h
  have hg : Measurable fun y : goodCylinder => (⟨y.1.1.1, y.2⟩ : goodSet) := he.subtype_mk
  have hD : Measurable fun y : goodCylinder => (y.1.1.2 : Grid) := by
    have h := (measurable_snd.comp measurable_fst).comp hval
    simpa only [Function.comp_def] using h
  have hz1 : Measurable fun y : goodCylinder => (y.1.2.1 : Plane) := by
    have h := (measurable_fst.comp measurable_snd).comp hval
    simpa only [Function.comp_def] using h
  have hz2 : Measurable fun y : goodCylinder => (y.1.2.2 : Plane) := by
    have h := (measurable_snd.comp measurable_snd).comp hval
    simpa only [Function.comp_def] using h
  have hmap : Measurable fun y : goodCylinder =>
      (((⟨y.1.1.1, y.2⟩ : goodSet), y.1.1.2), y.1.2.1, y.1.2.2) :=
    (hg.prodMk hD).prodMk (hz1.prodMk hz2)
  have h : Measurable (goodBlockKernel m U ∘ fun y : goodCylinder =>
      (((⟨y.1.1.1, y.2⟩ : goodSet), y.1.1.2), y.1.2.1, y.1.2.2)) :=
    (measurable_goodBlockKernel m U hU).comp hmap
  unfold cylinderKernel
  simpa only [Function.comp_def] using h

/-- **The block transport on the actual marked space**: the good-space kernel, extended by
zero off the good cylinder. -/
noncomputable def blockKernel : (Env × Grid) × Plane × Plane → ℝ≥0∞ :=
  Function.extend (Subtype.val : goodCylinder → (Env × Grid) × Plane × Plane)
    (cylinderKernel m U) fun _ => 0

theorem measurable_blockKernel (hU : Measurable U) : Measurable (blockKernel m U) :=
  (MeasurableEmbedding.subtype_coe measurableSet_goodCylinder).measurable_extend
    (measurable_cylinderKernel m U hU) measurable_const

theorem blockKernel_incl (ω : goodSet × Grid) (w z : Plane) :
    blockKernel m U (incl ω, w, z) = goodBlockKernel m U (ω, w, z) := by
  have hx : (incl ω, w, z) ∈ goodCylinder := ω.1.2
  exact Subtype.coe_injective.extend_apply (cylinderKernel m U) (fun _ => (0 : ℝ≥0∞))
    (⟨(incl ω, w, z), hx⟩ : goodCylinder)

theorem blockKernel_of_notMem {p : Env × Grid} (hp : p.1 ∉ goodSet) (w z : Plane) :
    blockKernel m U (p, w, z) = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨y, hy⟩
  have hmem := y.2
  rw [hy] at hmem
  exact hp hmem

/-! ### `s:eq:Tcov` for the block transport -/

/-- The good-space kernel has degree `−2` under the joint similarity `dilate ∘ shift`, for a
scale-invariant `U`: the block scales, so does its side, and `U` does not change.

The scale covariance is needed only **on the manuscript's invariant domain**, because the
kernel's support already asks the source re-rooting to lie there, and that condition is itself
exactly similarity covariant.  So `s:eq:Tcov` still holds at *every* configuration, which is
what `MassTransport` tests. -/
theorem goodBlockKernel_dilate_shift (hcov : goodScale.BlockScaleCovariantOn coveredMarked m)
    (hUinv : goodScale.InvariantFun U) {s : ℝ} (hs : 0 < s) (u w z : Plane)
    (ω : goodSet × Grid) :
    goodBlockKernel m U (goodDilate s (goodMarked.shift u ω),
        positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * goodBlockKernel m U (ω, w, z) := by
  have hsw : positiveSimilarity s u w = s • (w - u) := rfl
  have hsz : positiveSimilarity s u z = s • (z - u) := rfl
  have hshift : ∀ v : Plane,
      goodMarked.shift (s • (v - u)) (goodDilate s (goodMarked.shift u ω))
        = goodDilate s (goodMarked.shift v ω) := by
    intro v
    have huv : u + (v - u) = v := by abel
    rw [← goodScale_dilate, ← goodScale_dilate, ← goodScale.dilate_shift s hs (v - u),
      goodMarked.shift_shift, huv]
  have hcovered : goodMarked.shift (positiveSimilarity s u w)
        (goodDilate s (goodMarked.shift u ω)) ∈ coveredMarked
      ↔ goodMarked.shift w ω ∈ coveredMarked := by
    rw [hsw, hshift w]
    exact goodDilate_mem_coveredMarked_iff hs _
  by_cases hw : goodMarked.shift w ω ∈ coveredMarked
  · obtain ⟨hB, hL⟩ := hcov s hs (goodMarked.shift w ω) hw
    have hmem : (goodDilate s (goodMarked.shift u ω), positiveSimilarity s u w,
          positiveSimilarity s u z) ∈ goodBlockSupport m
        ↔ (ω, w, z) ∈ goodBlockSupport m := by
      rw [mem_goodBlockSupport_triple, mem_goodBlockSupport_triple]
      refine and_congr hcovered ?_
      rw [hsw, hsz, hshift w, ← goodScale_dilate, hB]
      show s⁻¹ • (s • (z - u) - s • (w - u)) ∈ goodMarked.blockSetAt m (goodMarked.shift w ω)
        ↔ z - w ∈ goodMarked.blockSetAt m (goodMarked.shift w ω)
      rw [← smul_sub, sub_sub_sub_cancel_right, inv_smul_smul₀ hs.ne']
    have hside : goodMarked.blockSideAt m
        (goodMarked.shift (positiveSimilarity s u w) (goodDilate s (goodMarked.shift u ω)))
        = s * goodMarked.blockSideAt m (goodMarked.shift w ω) := by
      rw [hsw, hshift w, ← goodScale_dilate, hL]
    have hUeq : U (goodMarked.shift (positiveSimilarity s u z)
        (goodDilate s (goodMarked.shift u ω))) = U (goodMarked.shift z ω) := by
      rw [hsz, hshift z, ← goodScale_dilate, hUinv s hs]
    have h0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.2 (pow_pos hs 2)
    unfold goodBlockKernel
    by_cases hz : (ω, w, z) ∈ goodBlockSupport m
    · rw [Set.indicator_of_mem (hmem.2 hz), Set.indicator_of_mem hz]
      unfold goodBlockWeight
      show (ENNReal.ofReal (goodMarked.blockSideAt m
          (goodMarked.shift (positiveSimilarity s u w)
            (goodDilate s (goodMarked.shift u ω))) ^ 2))⁻¹
          * U (goodMarked.shift (positiveSimilarity s u z) (goodDilate s (goodMarked.shift u ω)))
        = ENNReal.ofReal ((s ^ 2)⁻¹) *
          ((ENNReal.ofReal (goodMarked.blockSideAt m (goodMarked.shift w ω) ^ 2))⁻¹ *
            U (goodMarked.shift z ω))
      rw [hside, hUeq, mul_pow, ENNReal.ofReal_mul (sq_nonneg s),
        ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top),
        ENNReal.ofReal_inv_of_pos (pow_pos hs 2), mul_assoc]
    · rw [Set.indicator_of_notMem (fun h => hz (hmem.1 h)), Set.indicator_of_notMem hz, mul_zero]
  · -- off the invariant domain the source re-rooting is uncovered on both sides, so the
    -- transport vanishes and `s:eq:Tcov` is `0 = c * 0`.
    have hl : (goodDilate s (goodMarked.shift u ω), positiveSimilarity s u w,
        positiveSimilarity s u z) ∉ goodBlockSupport m := fun h =>
      hw (hcovered.1 ((mem_goodBlockSupport_triple m _ _ _).1 h).1)
    have hr : (ω, w, z) ∉ goodBlockSupport m := fun h =>
      hw ((mem_goodBlockSupport_triple m _ _ _).1 h).1
    unfold goodBlockKernel
    rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hr, mul_zero]

/-- **`s:eq:Tcov` for the block transport**, on the actual marked space. -/
theorem markedSimilarityCovariant_blockKernel
    (hcov : goodScale.BlockScaleCovariantOn coveredMarked m)
    (hUinv : goodScale.InvariantFun U) :
    MarkedSimilarityCovariant fun p w z => blockKernel m U (p, w, z) := by
  intro s u hs p w z
  by_cases hp : p.1 ∈ goodSet
  · show blockKernel m U (markedSimilarity s u hs (incl (⟨p.1, hp⟩, p.2)),
        positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * blockKernel m U (incl (⟨p.1, hp⟩, p.2), w, z)
    rw [markedSimilarity_incl, blockKernel_incl, blockKernel_incl]
    exact goodBlockKernel_dilate_shift m U hcov hUinv hs u w z _
  · have hp' : (markedSimilarity s u hs p).1 ∉ goodSet :=
      fun h => hp (mem_goodSet_of_similarityTargetEnv_mem hs u h)
    show blockKernel m U (markedSimilarity s u hs p, positiveSimilarity s u w,
        positiveSimilarity s u z) = ENNReal.ofReal ((s ^ 2)⁻¹) * blockKernel m U (p, w, z)
    rw [blockKernel_of_notMem m U hp', blockKernel_of_notMem m U hp, mul_zero]

end Kernel

/-! ### The transport identity for scale-invariant `U` -/

/-- The outgoing integral at the origin is the block average, **on the invariant domain**: the
source point is the origin, so the domain condition in the support is exactly `ω ∈
coveredMarked` and the identity is otherwise unchanged. -/
theorem lintegral_blockKernel_zero_left (m : ℝ) (U : goodSet × Grid → ℝ≥0∞) (hU : Measurable U)
    (ω : goodSet × Grid) (hω : ω ∈ coveredMarked) :
    (∫⁻ z : Plane, blockKernel m U (incl ω, 0, z) ∂volume) = goodMarked.blockAverageLint m U ω := by
  have hset := MarkedReRooting.measurableSet_blockSetAt (measurableBlockGraph_goodMarked m).1
  have hω0 : goodMarked.shift (0 : Plane) ω ∈ coveredMarked := by
    rw [goodMarked.shift_zero]; exact hω
  have hpt : ∀ z : Plane, blockKernel m U (incl ω, 0, z)
      = (goodMarked.blockSetAt m ω).indicator
          (fun y => (ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2))⁻¹ *
            U (goodMarked.shift y ω)) z := by
    intro z
    rw [blockKernel_incl]
    unfold goodBlockKernel
    by_cases hz : z ∈ goodMarked.blockSetAt m ω
    · have hz' : (ω, (0 : Plane), z) ∈ goodBlockSupport m := by
        rw [mem_goodBlockSupport_triple]
        refine ⟨hω0, ?_⟩
        rw [sub_zero, goodMarked.shift_zero]
        exact hz
      rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz]
      unfold goodBlockWeight
      show (ENNReal.ofReal (goodMarked.blockSideAt m (goodMarked.shift 0 ω) ^ 2))⁻¹ *
          U (goodMarked.shift z ω)
        = (ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2))⁻¹ * U (goodMarked.shift z ω)
      rw [goodMarked.shift_zero]
    · have hz' : (ω, (0 : Plane), z) ∉ goodBlockSupport m := by
        rw [mem_goodBlockSupport_triple]
        rintro ⟨-, h⟩
        rw [sub_zero, goodMarked.shift_zero] at h
        exact hz h
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  have hg : Measurable fun y : Plane => U (goodMarked.shift y ω) := by
    have h := hU.comp (goodMarked.measurable_shift.comp (measurable_prodMk_left (x := ω)))
    simpa only [Function.comp_def] using h
  simp_rw [hpt]
  rw [lintegral_indicator (hset ω), lintegral_const_mul _ hg]
  rfl

/-- The incoming integral at the origin is `U` itself, **on the invariant domain**: the selected
blocks partition the plane and `volume S_m(0) = ℓ(S_m(0))²`.

Here the source point is the integration variable `z`, so the domain condition in the support
excludes the uncovered offsets.  Those form a Lebesgue-null set
(`GoodMarkedSpace.volume_shift_notMem_coveredMarked`, the manuscript's *"hence Lebesgue-almost
every point of the plane"*), so the identity survives with an almost-everywhere comparison in
place of the pointwise one. -/
theorem lintegral_blockKernel_zero_right (m : ℝ) (hm : 0 < m) (U : goodSet × Grid → ℝ≥0∞)
    (ω : goodSet × Grid) (hω : ω ∈ coveredMarked) :
    (∫⁻ z : Plane, blockKernel m U (incl ω, z, 0) ∂volume) = U ω := by
  have hequi := blockEquivariantOn_goodMarked m hm
  have hset := MarkedReRooting.measurableSet_blockSetAt (measurableBlockGraph_goodMarked m).1
  have hae : ∀ᵐ z : Plane ∂volume, goodMarked.shift z ω ∈ coveredMarked :=
    MeasureTheory.ae_iff.2 (volume_shift_notMem_coveredMarked ω)
  have hpt : ∀ z : Plane, goodMarked.shift z ω ∈ coveredMarked →
      blockKernel m U (incl ω, z, 0)
      = (goodMarked.blockSetAt m ω).indicator
          (fun _ => (ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2))⁻¹ * U ω) z := by
    intro z hzc
    rw [blockKernel_incl]
    unfold goodBlockKernel
    by_cases hz : z ∈ goodMarked.blockSetAt m ω
    · have hz' : (ω, z, (0 : Plane)) ∈ goodBlockSupport m := by
        rw [mem_goodBlockSupport_triple]
        refine ⟨hzc, ?_⟩
        rw [zero_sub]
        exact (neg_mem_blockSetAt_shift_iff_of_equivariantOn hequi hω hzc).2 hz
      rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz]
      unfold goodBlockWeight
      show (ENNReal.ofReal (goodMarked.blockSideAt m (goodMarked.shift z ω) ^ 2))⁻¹ *
          U (goodMarked.shift 0 ω)
        = (ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2))⁻¹ * U ω
      rw [blockSideAt_shift_of_memOn hequi hω hz, goodMarked.shift_zero]
    · have hz' : (ω, z, (0 : Plane)) ∉ goodBlockSupport m := by
        rw [mem_goodBlockSupport_triple]
        rintro ⟨-, h⟩
        rw [zero_sub] at h
        exact hz ((neg_mem_blockSetAt_shift_iff_of_equivariantOn hequi hω hzc).1 h)
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  have hcongr : (∫⁻ z : Plane, blockKernel m U (incl ω, z, 0) ∂volume)
      = ∫⁻ z : Plane, (goodMarked.blockSetAt m ω).indicator
          (fun _ => (ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2))⁻¹ * U ω) z ∂volume :=
    lintegral_congr_ae (by filter_upwards [hae] with z hz using hpt z hz)
  rw [hcongr, lintegral_indicator_const (hset ω)]
  have hvol : volume (goodMarked.blockSetAt m ω)
      = ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2) := by
    show volume (halfOpenSquare ω.2 (originIndex (blockLevel (decode ω.1.1) ω.2 m)))
      = ENNReal.ofReal (side ω.2 (blockLevel (decode ω.1.1) ω.2 m) ^ 2)
    exact SpecificEnergyRedistribution.volume_halfOpenSquare ω.2 _
  have hpos : (0 : ℝ) < goodMarked.blockSideAt m ω ^ 2 := by
    have := goodMarked.blockSideAt_pos m ω
    positivity
  have h0 : ENNReal.ofReal (goodMarked.blockSideAt m ω ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hpos
  rw [hvol, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- **The mark-averaged transport identity `E[A_m U] = E[U]` for scale-invariant `U`**, from
`s:eq:MTP` alone: the manuscript's step in `s:lem:conditional`, on the good marked space. -/
theorem lintegral_blockAverageLint_eq [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) {m : ℝ} (hm : 0 < m)
    {U : goodSet × Grid → ℝ≥0∞} (hU : Measurable U) (hUinv : goodScale.InvariantFun U) :
    (∫⁻ ω, goodMarked.blockAverageLint m U ω ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ ω, U ω ∂(goodLaw (G := goodSet) ν) := by
  have hcov := blockScaleCovariantOn_goodScale m hm
  have hker := measurable_blockKernel m U hU
  have hT : Measurable fun x : (Env × Grid) × Plane × Plane =>
      blockKernel m U (x.1, x.2.1, x.2.2) := hker
  have hmtp := markedMassTransport_of_massTransport ν hν (fun p w z => blockKernel m U (p, w, z))
    hT (markedSimilarityCovariant_blockKernel m U hcov hUinv)
  have hout : Measurable fun p : Env × Grid => ∫⁻ z : Plane, blockKernel m U (p, 0, z) ∂volume := by
    have h : Measurable fun q : (Env × Grid) × Plane => blockKernel m U (q.1, 0, q.2) := by
      have h' := hker.comp ((measurable_fst (α := Env × Grid) (β := Plane)).prodMk
        ((measurable_const (a := (0 : Plane))).prodMk measurable_snd))
      simpa only [Function.comp_def] using h'
    exact h.lintegral_prod_right'
  have hin : Measurable fun p : Env × Grid => ∫⁻ z : Plane, blockKernel m U (p, z, 0) ∂volume := by
    have h : Measurable fun q : (Env × Grid) × Plane => blockKernel m U (q.1, q.2, 0) := by
      have h' := hker.comp ((measurable_fst (α := Env × Grid) (β := Plane)).prodMk
        (measurable_snd.prodMk (measurable_const (a := (0 : Plane)))))
      simpa only [Function.comp_def] using h'
    exact h.lintegral_prod_right'
  -- the two boundary identities hold on the conull invariant domain, so the two integrals
  -- against the good marked law are unchanged
  have hae : ∀ᵐ ω ∂(goodLaw (G := goodSet) ν), ω ∈ coveredMarked :=
    ae_mem_coveredMarked ν hν hgood
  have hleft : (∫⁻ ω, (∫⁻ z : Plane, blockKernel m U (incl ω, 0, z) ∂volume)
        ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ ω, goodMarked.blockAverageLint m U ω ∂(goodLaw (G := goodSet) ν) :=
    lintegral_congr_ae (by
      filter_upwards [hae] with ω hω using lintegral_blockKernel_zero_left m U hU ω hω)
  have hright : (∫⁻ ω, (∫⁻ z : Plane, blockKernel m U (incl ω, z, 0) ∂volume)
        ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ ω, U ω ∂(goodLaw (G := goodSet) ν) :=
    lintegral_congr_ae (by
      filter_upwards [hae] with ω hω using lintegral_blockKernel_zero_right m hm U ω hω)
  calc (∫⁻ ω, goodMarked.blockAverageLint m U ω ∂(goodLaw (G := goodSet) ν))
      = ∫⁻ ω, (∫⁻ z : Plane, blockKernel m U (incl ω, 0, z) ∂volume)
          ∂(goodLaw (G := goodSet) ν) := hleft.symm
    _ = ∫⁻ p, (∫⁻ z : Plane, blockKernel m U (p, 0, z) ∂volume) ∂(ν.prod gridMeasure) :=
        (lintegral_prod_eq_lintegral_goodLaw ν hgood hout).symm
    _ = ∫⁻ p, (∫⁻ z : Plane, blockKernel m U (p, z, 0) ∂volume) ∂(ν.prod gridMeasure) := hmtp
    _ = ∫⁻ ω, (∫⁻ z : Plane, blockKernel m U (incl ω, z, 0) ∂volume)
          ∂(goodLaw (G := goodSet) ν) := lintegral_prod_eq_lintegral_goodLaw ν hgood hin
    _ = ∫⁻ ω, U ω ∂(goodLaw (G := goodSet) ν) := hright

/-! ### The producer data and `s:prop:maximal` for the (FE) functional -/

/-- **The manuscript's selected-block data on the good marked space, from `s:eq:MTP`**, read on
the manuscript's invariant domain `coveredMarked`.  The transport field is **not** gated: it is
the full `∀ U` identity above, which is what makes this datum strong enough for every consumer
of `SimilarityBlockAveraging`. -/
theorem similarityBlockDataOn_goodMarked [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) :
    SimilarityBlockDataOn goodMarked goodScale (goodLaw (G := goodSet) ν) coveredMarked where
  equivariant m hm := blockEquivariantOn_goodMarked m hm
  measurableGraph m _ := (measurableBlockGraph_goodMarked m).1
  measurableSide m _ := (measurableBlockGraph_goodMarked m).2
  scaleCovariant m hm := blockScaleCovariantOn_goodScale m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_eq ν hν hgood hm hU hUinv

/-- **No regression**: where every good environment has a covered origin — the earlier
manuscript's covering clause `⋃ v, cell v = univ` — the datum is the ungated
`SimilarityBlockData`, exactly as before the covering clause was weakened. -/
theorem similarityBlockData_goodMarked [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hgood : ∀ᵐ e ∂ν, e ∈ goodSet) (hcovered : CoveredOrigins) :
    SimilarityBlockData goodMarked goodScale (goodLaw (G := goodSet) ν) where
  equivariant m hm := blockEquivariant_goodMarked hcovered m hm
  measurableGraph m _ := (measurableBlockGraph_goodMarked m).1
  measurableSide m _ := (measurableBlockGraph_goodMarked m).2
  scaleCovariant m hm := blockScaleCovariant_goodScale hcovered m hm
  transport m hm _ hU hUinv := lintegral_blockAverageLint_eq ν hν hgood hm hU hUinv

/-- **`M(ρ_FE) < ∞` almost surely on the good marked space**: the third clause of
`s:prop:maximal` for the (FE) functional, from `s:eq:MTP` and the (FE) moment. -/
theorem ae_ballMaximal_rootFE_lt_top [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ ω ∂(goodLaw (G := goodSet) ν), ballMaximal goodMarked (rootFE goodMarked) ω < ∞ := by
  have hgood := ae_mem_goodSet ν hν hFE
  have := isProbabilityMeasure_goodLaw ν hgood
  exact ballMaximal_lt_top_ae_similarityOn (invariantDomain_coveredMarked ν hν hgood)
    originChainRegularOn_goodMarked
    (similarityBlockDataOn_goodMarked ν hν hgood) (environmentGrid_goodMarked ν hgood)
    measurable_rootFE_goodMarked (rootFE_nonneg _) (integrable_rootFE_goodLaw ν hgood hFE)
    invariantFun_rootFE

/-- **Manuscript Proposition `s:prop:maximal` for the rooted (FE) density, in the consumers'
form.**  Under the manuscript's own hypotheses — `s:eq:MTP` and the finite (FE) moment —
almost every environment admits a finite random constant `M` with
`∫_{B̄_r} ρ_FE ≤ r² M` at every positive radius.  This is verbatim the hypothesis `hMax` of
`Spatial/AlmostSureSpatialDiameterBounds`, `Spatial/AlmostSureCutoffBounds` and
`Recurrence/QuenchedFormulation`. -/
theorem ae_exists_ballBound_rootedFiniteEnergyDensity [IsProbabilityMeasure ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M :=
  ae_exists_ballBound_of_good_ballMaximal ν measurableSet_goodSet (ae_mem_goodSet ν hν hFE)
    goodSet_translateEnv (ae_ballMaximal_rootFE_lt_top ν hν hFE)

/-! ### The consumers, discharged -/

/-- **`s:eq:Wbound`, finite-radius half, almost surely** (`s:cor:spatialbounds`). -/
theorem ae_spatialDiameterCellBounds [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, PatchCentroidTraceFiniteEnergy.SpatialDiameterCellBounds (decode e) :=
  AlmostSureSpatialDiameterBounds.ae_spatialDiameterCellBounds_of_ballBound ν hν hFE
    (ae_exists_ballBound_rootedFiniteEnergyDensity ν hν hFE)

/-- **The hypothesis tuple of Proposition `r:prop:log`, almost surely**, from the manuscript's
hypotheses alone. -/
theorem ae_exists_logCutoff_hypotheses [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∀ (z : Vertex e.val → Plane) (o : Vertex e.val),
      ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖z o‖ ≤ r₀ ∧
        (∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
          Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
          Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100) ∧
        (∀ R : ℝ, r₀ ≤ R →
          LogCutoff.localMassENN (decode e)
              {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
            ≤ ENNReal.ofReal (C * R ^ 2)) :=
  AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hν hFE
    (ae_exists_ballBound_rootedFiniteEnergyDensity ν hν hFE)

end ReflectedGMS.SpatialMaximalForFiniteEnergy
