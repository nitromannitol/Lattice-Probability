/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.SimilarityBlockAveraging at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalInequality

/-!
# The similarity-invariant block sigma-fields and the maximal inequality for scale-invariant `F`

Manuscript Lemma `s:lem:conditional` defines `𝒢_m` as the sigma-field of events *"whose
indicators are unchanged by common scaling and by translating a point of `S_m(0)°` to the
origin"*, and its proof applies marked mass transport to `T(ω, w, z) = 1_{z ∈ S_m(w)}
ℓ(S_m(w))⁻² U(ω − z)` *"for an arbitrary nonnegative scale-invariant `U`"*.  Both restrictions
are essential: `s:eq:MTP` tests only kernels of degree `−2` under the full similarity group
(`s:eq:Tcov`), and the block transport of a `U` that is not scale invariant has no degree.

`Spatial/MarkedBlockAveraging` and `Spatial/SpatialMaximalInequality` were written with the
translation-only sigma-field `blockSigma m` and a transport identity `MarkedBlockTransport`
demanded for *every* measurable `U`.  That transport is stronger than the manuscript's and is
not derivable from `s:eq:MTP`.  This module supplies the manuscript's own version:

* `ScaleAction R` — a dilation action `ω ↦ s • ω` compatible with re-rooting,
  `s • (ω − w) = (s • ω) − s • w`;
* `ScaleAction.similaritySigma S m` — the manuscript's `𝒢_m`: block-invariant **and**
  scale-invariant measurable events, a sub-sigma-field of `blockSigma m`
  (`similaritySigma_le_blockSigma`), decreasing in `m` (`similaritySigma_antitone`);
* `blockAverageLint_dilate` — the block average of a scale-invariant `U` is scale invariant
  when the selected block is scale covariant (`BlockScaleCovariant`): a change of variables in
  the plane, `volume (s • B) = s² volume B`;
* `SimilarityBlockData R S μ` — the producer data in the manuscript's form: block
  equivariance, measurability of the block, scale covariance of the block, and the transport
  identity `E[A_m U] = E[U]` **for scale-invariant `U` only**;
* `blockAverage_ae_eq_condExp_similarity` — `A_m F = E[F | 𝒢_m]` for scale-invariant `F`,
  from the generalized `MarkedBlockAveraging.blockAverage_ae_eq_condExp_of_sigma`;
* `measure_exists_originAverage_gt_le_similarity`, `measure_ballMaximal_gt_le_similarity`,
  `ballMaximal_lt_top_ae_similarity` — the three probabilistic conclusions of
  `s:prop:maximal` for a nonnegative integrable **scale-invariant** `F`, through the
  abstract `_of_condExp` / `_of_originBound` forms of `SpatialMaximalInequality`.

Nothing here constructs the action or discharges `SimilarityBlockData` on the actual marked
space; that is the producer's task, and the only probabilistic input it needs is
`EnvironmentLaws.MassTransport` through
`Corrector/MarkedMassTransportProducer.markedMassTransport_of_massTransport`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SimilarityBlockAveraging

open MarkedBlockAveraging SpatialMaximalInequality DyadicApproximation Code

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The dilation action -/

/-- A dilation action on a marked configuration space, compatible with the re-rooting
action: `s • (ω − w) = (s • ω) − s • w`.  Only the action law is required; measurability of
the dilations is never used, because they enter only through invariance of sets. -/
structure ScaleAction (R : MarkedReRooting Ω) where
  /-- The configuration scaled by `s`. -/
  dilate : ℝ → Ω → Ω
  /-- Compatibility with re-rooting. -/
  dilate_shift : ∀ (s : ℝ), 0 < s → ∀ (w : Plane) (ω : Ω),
    dilate s (R.shift w ω) = R.shift (s • w) (dilate s ω)

namespace ScaleAction

variable {R : MarkedReRooting Ω} (S : ScaleAction R)

/-- A set unchanged by every positive dilation. -/
def InvariantSet (A : Set Ω) : Prop :=
  ∀ (s : ℝ), 0 < s → ∀ ω : Ω, S.dilate s ω ∈ A ↔ ω ∈ A

/-- A function unchanged by every positive dilation: the manuscript's "scale invariant". -/
def InvariantFun {β : Type*} (U : Ω → β) : Prop :=
  ∀ (s : ℝ), 0 < s → ∀ ω : Ω, U (S.dilate s ω) = U ω

/-- The manuscript's sigma-field of events invariant under common scaling. -/
def scaleSigma : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ S.InvariantSet A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun s hs ω => not_congr (hA.2 s hs ω)⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun s hs ω => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2 s hs ω⟩

/-- **The manuscript's `𝒢_m`**: the measurable events unchanged by re-rooting inside the
selected origin block and by common scaling. -/
def similaritySigma (m : ℝ) : SubSigma Ω := ⟨R.blockSigma m ⊓ S.scaleSigma⟩

/-- Block covariance of the selected origin block under dilation: `S_m(0)(s • ω) = s • S_m(0)(ω)`
and `ℓ(S_m(0)(s • ω)) = s ℓ(S_m(0)(ω))`.  This is the manuscript's "the partitions commute
with similarities", the dilation half; the translation half is `BlockEquivariant`. -/
def BlockScaleCovariant (m : ℝ) : Prop :=
  ∀ (s : ℝ), 0 < s → ∀ ω : Ω,
    R.blockSetAt m (S.dilate s ω) = (fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω ∧
      R.blockSideAt m (S.dilate s ω) = s * R.blockSideAt m ω

variable {S}

theorem invariantFun_indicator {A : Set Ω} (hA : S.InvariantSet A) {U : Ω → ℝ≥0∞}
    (hU : S.InvariantFun U) : S.InvariantFun (A.indicator U) := by
  intro s hs ω
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((hA s hs ω).2 hω), hU s hs ω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun h => hω ((hA s hs ω).1 h)]

theorem invariantFun_ofReal {f : Ω → ℝ} (hf : S.InvariantFun f) :
    S.InvariantFun fun x => ENNReal.ofReal (f x) :=
  fun s hs ω => by simp only [hf s hs ω]

theorem similaritySigma_le_blockSigma (m : ℝ) :
    (S.similaritySigma m).sigma ≤ R.blockSigma m := inf_le_left

theorem similaritySigma_le (m : ℝ) : (S.similaritySigma m).sigma ≤ ‹MeasurableSpace Ω› :=
  le_trans inf_le_left (R.blockSigma_le m)

theorem measurableSet_similaritySigma_iff {m : ℝ} {A : Set Ω} :
    MeasurableSet[(S.similaritySigma m).sigma] A
      ↔ MeasurableSet[R.blockSigma m] A ∧ (MeasurableSet A ∧ S.InvariantSet A) :=
  MeasurableSpace.measurableSet_inf

/-- **The sigma-fields `𝒢_m` decrease with `m`.** -/
theorem similaritySigma_antitone (h : OriginChainRegular R) {m m' : ℝ} (hm : 0 < m)
    (hmm : m ≤ m') : (S.similaritySigma m').sigma ≤ (S.similaritySigma m).sigma :=
  inf_le_inf_right _ (blockSigma_antitone h hm hmm)

/-! ### Scale invariance of the block average -/

/-- The plane integral of a dilated function: `∫ g (s⁻¹ • z) dz = s² ∫ g`. -/
theorem lintegral_comp_inv_smul_plane {g : Plane → ℝ≥0∞} (hg : Measurable g) {s : ℝ}
    (hs : 0 < s) :
    (∫⁻ z : Plane, g (s⁻¹ • z) ∂volume) = ENNReal.ofReal (s ^ 2) * ∫⁻ z : Plane, g z ∂volume := by
  have hsmul : Measurable fun z : Plane => s⁻¹ • z := measurable_const_smul s⁻¹
  rw [← lintegral_map hg hsmul, Measure.map_addHaar_smul volume (inv_ne_zero hs.ne'),
    lintegral_smul_measure, finrank_euclideanSpace_fin]
  congr 2
  rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg s)]

/-- **The block average of a scale-invariant `U` is scale invariant** when the selected
block is scale covariant **at that configuration**: a change of variables moves the dilated
block back onto the original one, and the two factors `s²` cancel.

Only the scale covariance at `(s, ω)` is used, which is what the manuscript's gated
`BlockScaleCovariantOn` supplies — under the singular-set covering clause the selected block
is undefined at an uncovered origin, and `DilatedSelectedBlocks.blockLevel_dilate` shifts the
selected level by `levelShift s D`, so scale covariance genuinely fails there. -/
theorem blockAverageLint_dilate_at {m : ℝ}
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω)) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hUinv : S.InvariantFun U) {s : ℝ} (hs : 0 < s) (ω : Ω)
    (hB : R.blockSetAt m (S.dilate s ω) = (fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω)
    (hL : R.blockSideAt m (S.dilate s ω) = s * R.blockSideAt m ω) :
    R.blockAverageLint m U (S.dilate s ω) = R.blockAverageLint m U ω := by
  have hg : Measurable fun y : Plane => U (R.shift y ω) :=
    hU.comp (R.measurable_shift.comp measurable_prodMk_left)
  have hpt : ∀ z : Plane, U (R.shift z (S.dilate s ω)) = U (R.shift (s⁻¹ • z) ω) := by
    intro z
    have hz : s • (s⁻¹ • z) = z := smul_inv_smul₀ hs.ne' z
    rw [← hz, ← S.dilate_shift s hs, hUinv s hs, hz]
  have hpre : MeasurableSet ((fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω) :=
    (measurable_const_smul s⁻¹) (hset ω)
  have hint : (∫⁻ z in R.blockSetAt m (S.dilate s ω), U (R.shift z (S.dilate s ω)) ∂volume)
      = ENNReal.ofReal (s ^ 2) * ∫⁻ z in R.blockSetAt m ω, U (R.shift z ω) ∂volume := by
    rw [hB, ← lintegral_indicator hpre, ← lintegral_indicator (hset ω)]
    have hind : ∀ z : Plane,
        ((fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω).indicator
          (fun z => U (R.shift z (S.dilate s ω))) z
        = (R.blockSetAt m ω).indicator (fun y => U (R.shift y ω)) (s⁻¹ • z) := by
      intro z
      by_cases hz : s⁻¹ • z ∈ R.blockSetAt m ω
      · rw [Set.indicator_of_mem (show z ∈ (fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω
            from hz), Set.indicator_of_mem hz, hpt z]
      · rw [Set.indicator_of_notMem (show z ∉ (fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω
            from hz), Set.indicator_of_notMem hz]
    simp_rw [hind]
    exact lintegral_comp_inv_smul_plane (hg.indicator (hset ω)) hs
  have hs2 : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 (pow_pos hs 2)
  unfold MarkedReRooting.blockAverageLint
  rw [hint, hL, mul_pow, ENNReal.ofReal_mul (sq_nonneg s),
    ENNReal.mul_inv (Or.inl hs2) (Or.inl ENNReal.ofReal_ne_top), mul_assoc,
    ← mul_assoc (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹,
    mul_comm (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ (ENNReal.ofReal (s ^ 2)),
    mul_assoc, ← mul_assoc (ENNReal.ofReal (s ^ 2))⁻¹,
    ENNReal.inv_mul_cancel hs2 ENNReal.ofReal_ne_top, one_mul]

/-- **The block average of a scale-invariant `U` is scale invariant** when the selected
block is scale covariant. -/
theorem blockAverageLint_dilate {m : ℝ} (hcov : S.BlockScaleCovariant m)
    (hset : ∀ ω : Ω, MeasurableSet (R.blockSetAt m ω)) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hUinv : S.InvariantFun U) {s : ℝ} (hs : 0 < s) (ω : Ω) :
    R.blockAverageLint m U (S.dilate s ω) = R.blockAverageLint m U ω :=
  blockAverageLint_dilate_at hset hU hUinv hs ω (hcov s hs ω).1 (hcov s hs ω).2

/-- The block average of a scale-invariant `U` is measurable for the manuscript's `𝒢_m`. -/
theorem measurable_similaritySigma_blockAverageLint {m : ℝ} (hequi : R.BlockEquivariant m)
    (hgraph : R.MeasurableBlockGraph m) (hside : Measurable (R.blockSideAt m))
    (hcov : S.BlockScaleCovariant m) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hUinv : S.InvariantFun U) :
    Measurable[(S.similaritySigma m).sigma] (R.blockAverageLint m U) := by
  intro t ht
  refine MeasurableSpace.measurableSet_inf.2
    ⟨MarkedReRooting.measurable_blockSigma_blockAverageLint hequi hgraph hside hU ht, ?_⟩
  refine ⟨MarkedReRooting.measurable_blockAverageLint hgraph hside hU ht, fun s hs ω => ?_⟩
  simp only [Set.mem_preimage]
  rw [blockAverageLint_dilate hcov (MarkedReRooting.measurableSet_blockSetAt hgraph) hU hUinv
    hs ω]

end ScaleAction

/-! ### The producer data in the manuscript's form -/

/-- The selected-block data of `s:lem:conditional` in the manuscript's own form: block
equivariance, measurability of the block graph and side, scale covariance of the block, and
the mark-averaged mass-transport identity `E[A_m U] = E[U]` **for scale-invariant `U`
only** — the class `s:eq:MTP` actually tests. -/
structure SimilarityBlockData (R : MarkedReRooting Ω) (S : ScaleAction R) (μ : Measure Ω) :
    Prop where
  /-- Re-rooting inside the block translates the block. -/
  equivariant : ∀ m : ℝ, 0 < m → R.BlockEquivariant m
  /-- The selected block has a measurable graph. -/
  measurableGraph : ∀ m : ℝ, 0 < m → R.MeasurableBlockGraph m
  /-- The selected block side length is measurable. -/
  measurableSide : ∀ m : ℝ, 0 < m → Measurable (R.blockSideAt m)
  /-- Dilation scales the block. -/
  scaleCovariant : ∀ m : ℝ, 0 < m → S.BlockScaleCovariant m
  /-- The mark-averaged mass transport for scale-invariant test functions. -/
  transport : ∀ m : ℝ, 0 < m → ∀ U : Ω → ℝ≥0∞, Measurable U → S.InvariantFun U →
    (∫⁻ ω, R.blockAverageLint m U ω ∂μ) = ∫⁻ ω, U ω ∂μ

variable {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω}

/-- The transport identity tested on `𝒢_m`, for a scale-invariant `f`. -/
theorem blockTransportOn_similaritySigma (hdata : SimilarityBlockData R S μ) {m : ℝ}
    (hm : 0 < m) {f : Ω → ℝ} (hf : Measurable f) (hfinv : S.InvariantFun f) :
    R.BlockTransportOn m (S.similaritySigma m) μ fun x => ENNReal.ofReal (f x) := by
  intro A hA
  obtain ⟨_, hAmeas, hAinv⟩ := ScaleAction.measurableSet_similaritySigma_iff.1 hA
  exact hdata.transport m hm _ (hf.ennreal_ofReal.indicator hAmeas)
    (ScaleAction.invariantFun_indicator hAinv (ScaleAction.invariantFun_ofReal hfinv))

/-- **`s:lem:conditional` in the manuscript's form**: for a nonnegative integrable
scale-invariant `f`, the block average is the conditional expectation given `𝒢_m`. -/
theorem blockAverage_ae_eq_condExp_similarity [IsProbabilityMeasure μ]
    (hdata : SimilarityBlockData R S μ) {m : ℝ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (hint : Integrable f μ)
    (hfinv : S.InvariantFun f) :
    R.blockAverage m f =ᵐ[μ] μ[f|(S.similaritySigma m).sigma] := by
  refine MarkedReRooting.blockAverage_ae_eq_condExp_of_sigma (hdata.measurableGraph m hm)
    (hdata.measurableSide m hm) (ScaleAction.similaritySigma_le_blockSigma m) hf hf0 hint ?_
    (blockTransportOn_similaritySigma hdata hm hf hfinv)
  have hlint : Measurable[(S.similaritySigma m).sigma]
      (R.blockAverageLint m fun x => ENNReal.ofReal (f x)) :=
    ScaleAction.measurable_similaritySigma_blockAverageLint (hdata.equivariant m hm)
      (hdata.measurableGraph m hm) (hdata.measurableSide m hm) (hdata.scaleCovariant m hm)
      hf.ennreal_ofReal (ScaleAction.invariantFun_ofReal hfinv)
  rw [MarkedReRooting.blockAverage_eq_toReal_fun hf hf0]
  exact hlint.ennreal_toReal

/-! ### `s:prop:maximal` for scale-invariant `F` -/

/-- **`s:eq:dyadicmax` over the complete origin chain**, for scale-invariant `F`. -/
theorem measure_exists_originAverage_gt_le_similarity [IsProbabilityMeasure μ]
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) {t : ℝ} (ht : 0 < t) :
    μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
      ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t) := by
  refine measure_exists_originAverage_gt_le_of_condExp R hchain hF hF0 hFint
    (fun q : ℚ => (S.similaritySigma (param q)).sigma)
    (fun a b hab => ScaleAction.similaritySigma_antitone hchain (param_pos a) (param_mono hab))
    (fun q => ScaleAction.similaritySigma_le _)
    (fun q => blockAverage_ae_eq_condExp_similarity hdata (param_pos q) hF hF0 hFint hFinv)
    (fun q => ?_) ht
  exact ae_lt_top
    (MarkedReRooting.measurable_blockAverageLint (hdata.measurableGraph _ (param_pos q))
      (hdata.measurableSide _ (param_pos q)) hF.ennreal_ofReal)
    (MarkedReRooting.lintegral_blockAverageLint_ofReal_ne_top_of_on
      (blockTransportOn_similaritySigma hdata (param_pos q) hF hFinv) hF0 hFint)

/-- **`s:eq:maximal`** for scale-invariant `F`: `P[M(ρ) > λ] ≤ 512 E[F]/λ`. -/
theorem measure_ballMaximal_gt_le_similarity [IsProbabilityMeasure μ] {𝒜 : EnvSigma Ω}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    {F : Ω → ℝ} (henv : EnvironmentGrid R μ F 𝒜)
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | ENNReal.ofReal lam < ballMaximal R F ω}
      ≤ ENNReal.ofReal (512 * (∫ ω, F ω ∂μ) / lam) :=
  measure_ballMaximal_gt_le_of_originBound R henv
    (fun _ ht => measure_exists_originAverage_gt_le_similarity hchain hdata hF hF0 hFint hFinv ht)
    hlam

/-- **`M(ρ) < ∞` almost surely** for scale-invariant `F`: the third clause of
`s:prop:maximal`, from the manuscript's own producer data. -/
theorem ballMaximal_lt_top_ae_similarity [IsProbabilityMeasure μ] {𝒜 : EnvSigma Ω}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
    {F : Ω → ℝ} (henv : EnvironmentGrid R μ F 𝒜)
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) :
    ∀ᵐ ω ∂μ, ballMaximal R F ω < ∞ :=
  ballMaximal_lt_top_ae_of_originBound R henv
    (fun _ ht => measure_exists_originAverage_gt_le_similarity hchain hdata hF hF0 hFint hFinv ht)

/-! ### `s:prop:maximal` on the manuscript's invariant domain

Under the singular-set manuscript's covering clause `μH[1] (uncoveredSet F) = 0` the selected
origin block is undefined at an uncovered origin, and §3.1 says so: *"their closures cover every
point belonging to a cell, and hence Lebesgue-almost every point of the plane … no claim is
needed about an uncovered singular point … undefined constructions are set to zero off their
invariant domain"*.  Three of the inputs above are therefore false as stated at every
configuration and have to be read on that domain:

* `index_small` — gated as `SpatialMaximalInequality.OriginChainRegularOn`;
* `BlockEquivariant` — gated as `SpatialMaximalInequality.BlockEquivariantOn`;
* `BlockScaleCovariant` — gated as `BlockScaleCovariantOn`.  It is genuinely false off the
  domain and not merely unproved: `DilatedSelectedBlocks.blockLevel_dilate` shifts the selected
  level by `levelShift s D`, which the junk level of an unselected chain cannot do.

The transport identity is **not** gated: it is asked for every measurable scale-invariant test
function and never looks at the origin chain.  What the gated theory has to supply instead is
that the gated test sets can be replaced by exactly invariant ones, which is what the three
domain conditions of `InvariantDomain` are for. -/

/-- The manuscript's **measurable invariant domain** for the selected-block construction.

`ae_mem` is the domain being conull, `shift_ae` is "*hence* Lebesgue-almost every point of the
plane" — the re-rootings leaving the domain form a Lebesgue-null set of offsets, which for the
actual space is exactly the `H¹`-null uncovered set of the environment — and `dilate_mem` is the
domain being invariant under the dilation action, so that `A ∩ G` is exactly scale invariant
whenever `A` is scale invariant on the domain.

`invariantDomain_univ` shows the full domain qualifies, which is the situation under the earlier
manuscript's covering clause `⋃ v, cell v = univ`; there every result below is literally the
ungated one. -/
structure InvariantDomain (R : MarkedReRooting Ω) (S : ScaleAction R) (μ : Measure Ω)
    (G : Set Ω) : Prop where
  /-- The domain is measurable. -/
  measurable : MeasurableSet G
  /-- The domain is conull. -/
  ae_mem : ∀ᵐ ω ∂μ, ω ∈ G
  /-- Almost every re-rooting stays in the domain. -/
  shift_ae : ∀ ω : Ω, volume {z : Plane | R.shift z ω ∉ G} = 0
  /-- The domain is invariant under the dilation action. -/
  dilate_mem : ∀ s : ℝ, 0 < s → ∀ ω : Ω, (S.dilate s ω ∈ G ↔ ω ∈ G)

/-- **No regression**: the full domain is an invariant domain, so every gated statement below
specialises to its ungated counterpart. -/
theorem invariantDomain_univ (R : MarkedReRooting Ω) (S : ScaleAction R) (μ : Measure Ω) :
    InvariantDomain R S μ Set.univ where
  measurable := MeasurableSet.univ
  ae_mem := Filter.Eventually.of_forall fun _ => Set.mem_univ _
  shift_ae ω := by
    have h : {z : Plane | R.shift z ω ∉ Set.univ} = (∅ : Set Plane) := by
      ext z; simp
    rw [h]
    simp
  dilate_mem _ _ _ := Iff.rfl

namespace ScaleAction

/-- Scale covariance of the selected origin block **on an invariant domain**. -/
def BlockScaleCovariantOn (S : ScaleAction R) (G : Set Ω) (m : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ ω ∈ G,
    R.blockSetAt m (S.dilate s ω) = (fun z : Plane => s⁻¹ • z) ⁻¹' R.blockSetAt m ω ∧
      R.blockSideAt m (S.dilate s ω) = s * R.blockSideAt m ω

theorem blockScaleCovariantOn_of_blockScaleCovariant {S : ScaleAction R} {m : ℝ}
    (h : S.BlockScaleCovariant m) (G : Set Ω) : S.BlockScaleCovariantOn G m :=
  fun s hs ω _ => h s hs ω

theorem blockScaleCovariant_of_blockScaleCovariantOn {S : ScaleAction R} {m : ℝ}
    (h : S.BlockScaleCovariantOn Set.univ m) : S.BlockScaleCovariant m :=
  fun s hs ω => h s hs ω (Set.mem_univ ω)

/-- The sigma-field of events unchanged by common scaling **at the configurations of `G`**. -/
def scaleSigmaOn (S : ScaleAction R) (G : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ ∀ s : ℝ, 0 < s → ∀ ω ∈ G, (S.dilate s ω ∈ A ↔ ω ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun s hs ω hω => not_congr (hA.2 s hs ω hω)⟩
  measurableSet_iUnion f hf :=
    ⟨MeasurableSet.iUnion fun i => (hf i).1, fun s hs ω hω => by
      simp only [Set.mem_iUnion]
      exact exists_congr fun i => (hf i).2 s hs ω hω⟩

theorem scaleSigma_le_scaleSigmaOn (S : ScaleAction R) (G : Set Ω) :
    S.scaleSigma ≤ S.scaleSigmaOn G := fun _ hA => ⟨hA.1, fun s hs ω _ => hA.2 s hs ω⟩

theorem scaleSigmaOn_univ (S : ScaleAction R) : S.scaleSigmaOn Set.univ = S.scaleSigma :=
  le_antisymm (fun _ hA => ⟨hA.1, fun s hs ω => hA.2 s hs ω (Set.mem_univ ω)⟩)
    (scaleSigma_le_scaleSigmaOn S Set.univ)

/-- **The manuscript's `𝒢_m` on an invariant domain.** -/
def similaritySigmaOn (S : ScaleAction R) (G : Set Ω) (m : ℝ) : SubSigma Ω :=
  ⟨blockSigmaOn R G m ⊓ S.scaleSigmaOn G⟩

theorem similaritySigmaOn_le (S : ScaleAction R) (G : Set Ω) (m : ℝ) :
    (S.similaritySigmaOn G m).sigma ≤ ‹MeasurableSpace Ω› :=
  le_trans inf_le_left (blockSigmaOn_le R G m)

theorem similaritySigma_le_similaritySigmaOn (S : ScaleAction R) (G : Set Ω) (m : ℝ) :
    (S.similaritySigma m).sigma ≤ (S.similaritySigmaOn G m).sigma :=
  inf_le_inf (blockSigma_le_blockSigmaOn R G m) (scaleSigma_le_scaleSigmaOn S G)

/-- **No regression**: at the full domain the gated sigma-field is the manuscript's `𝒢_m`. -/
theorem similaritySigmaOn_univ (S : ScaleAction R) (m : ℝ) :
    (S.similaritySigmaOn Set.univ m).sigma = (S.similaritySigma m).sigma := by
  show blockSigmaOn R Set.univ m ⊓ S.scaleSigmaOn Set.univ = R.blockSigma m ⊓ S.scaleSigma
  rw [blockSigmaOn_univ, scaleSigmaOn_univ]

theorem measurableSet_similaritySigmaOn_iff {S : ScaleAction R} {G : Set Ω} {m : ℝ}
    {A : Set Ω} : MeasurableSet[(S.similaritySigmaOn G m).sigma] A
      ↔ MeasurableSet[blockSigmaOn R G m] A ∧ MeasurableSet[S.scaleSigmaOn G] A :=
  MeasurableSpace.measurableSet_inf

/-- **The sigma-fields `𝒢_m` decrease with `m`**, on the domain. -/
theorem similaritySigmaOn_antitone {S : ScaleAction R} {G : Set Ω}
    (h : OriginChainRegularOn R G) {m m' : ℝ} (hm : 0 < m) (hmm : m ≤ m') :
    (S.similaritySigmaOn G m').sigma ≤ (S.similaritySigmaOn G m).sigma :=
  inf_le_inf_right _ (blockSigmaOn_antitone h hm hmm)

/-- On a dilation-invariant domain, an event which is scale invariant **on the domain** becomes
exactly scale invariant after intersecting with the domain.  This is what lets the gated theory
test the *ungated* transport identity. -/
theorem invariantSet_inter_domain {S : ScaleAction R} {G : Set Ω} {μ : Measure Ω}
    (hdom : InvariantDomain R S μ G) {A : Set Ω}
    (hA : ∀ s : ℝ, 0 < s → ∀ ω ∈ G, (S.dilate s ω ∈ A ↔ ω ∈ A)) :
    S.InvariantSet (A ∩ G) := by
  intro s hs ω
  constructor
  · rintro ⟨hA1, hG1⟩
    have hωG : ω ∈ G := (hdom.dilate_mem s hs ω).1 hG1
    exact ⟨(hA s hs ω hωG).1 hA1, hωG⟩
  · rintro ⟨hA1, hG1⟩
    exact ⟨(hA s hs ω hG1).2 hA1, (hdom.dilate_mem s hs ω).2 hG1⟩

end ScaleAction

/-- Intersecting the test set with the domain does not change a block average: the re-rootings
leaving the domain form a Lebesgue-null set of offsets. -/
theorem blockAverageLint_indicator_inter_domain {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} {G : Set Ω} (hdom : InvariantDomain R S μ G) {m : ℝ} (A : Set Ω)
    (U : Ω → ℝ≥0∞) (ω : Ω) :
    R.blockAverageLint m ((A ∩ G).indicator U) ω
      = R.blockAverageLint m (A.indicator U) ω := by
  have hae : ∀ᵐ z : Plane ∂volume, R.shift z ω ∈ G := by
    rw [MeasureTheory.ae_iff]
    exact hdom.shift_ae ω
  unfold MarkedReRooting.blockAverageLint
  congr 1
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  by_cases hA : R.shift z ω ∈ A
  · rw [Set.indicator_of_mem (show R.shift z ω ∈ A ∩ G from ⟨hA, hz⟩),
      Set.indicator_of_mem hA]
  · rw [Set.indicator_of_notMem (fun h => hA h.1), Set.indicator_of_notMem hA]

/-- Intersecting the test set with the domain does not change its integral: the domain is
conull. -/
theorem lintegral_indicator_inter_domain {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} {G : Set Ω} (hdom : InvariantDomain R S μ G) (A : Set Ω) (U : Ω → ℝ≥0∞) :
    (∫⁻ ω, (A ∩ G).indicator U ω ∂μ) = ∫⁻ ω, A.indicator U ω ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hdom.ae_mem] with ω hω
  by_cases hA : ω ∈ A
  · rw [Set.indicator_of_mem (show ω ∈ A ∩ G from ⟨hA, hω⟩), Set.indicator_of_mem hA]
  · rw [Set.indicator_of_notMem (fun h => hA h.1), Set.indicator_of_notMem hA]

/-- The selected-block data of `s:lem:conditional` **on an invariant domain**: exactly
`SimilarityBlockData` with the three configuration-wise clauses read on the domain.  The
transport identity is unchanged — `s:eq:MTP` tests every scale-invariant kernel of degree `-2`
and knows nothing about the origin chain. -/
structure SimilarityBlockDataOn (R : MarkedReRooting Ω) (S : ScaleAction R) (μ : Measure Ω)
    (G : Set Ω) : Prop where
  /-- Re-rooting inside the block translates the block, on the domain. -/
  equivariant : ∀ m : ℝ, 0 < m → BlockEquivariantOn R G m
  /-- The selected block has a measurable graph. -/
  measurableGraph : ∀ m : ℝ, 0 < m → R.MeasurableBlockGraph m
  /-- The selected block side length is measurable. -/
  measurableSide : ∀ m : ℝ, 0 < m → Measurable (R.blockSideAt m)
  /-- Dilation scales the block, on the domain. -/
  scaleCovariant : ∀ m : ℝ, 0 < m → S.BlockScaleCovariantOn G m
  /-- The mark-averaged mass transport for scale-invariant test functions. -/
  transport : ∀ m : ℝ, 0 < m → ∀ U : Ω → ℝ≥0∞, Measurable U → S.InvariantFun U →
    (∫⁻ ω, R.blockAverageLint m U ω ∂μ) = ∫⁻ ω, U ω ∂μ

/-- **No regression**: the everywhere data is data on every domain. -/
theorem similarityBlockDataOn_of_similarityBlockData {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} (h : SimilarityBlockData R S μ) (G : Set Ω) :
    SimilarityBlockDataOn R S μ G where
  equivariant m hm := blockEquivariantOn_of_blockEquivariant (h.equivariant m hm) G
  measurableGraph := h.measurableGraph
  measurableSide := h.measurableSide
  scaleCovariant m hm := ScaleAction.blockScaleCovariantOn_of_blockScaleCovariant
    (h.scaleCovariant m hm) G
  transport := h.transport

/-- **No regression, converse**: data on the full domain is the everywhere data. -/
theorem similarityBlockData_of_similarityBlockDataOn {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} (h : SimilarityBlockDataOn R S μ Set.univ) : SimilarityBlockData R S μ where
  equivariant m hm := blockEquivariant_of_blockEquivariantOn (h.equivariant m hm)
  measurableGraph := h.measurableGraph
  measurableSide := h.measurableSide
  scaleCovariant m hm := ScaleAction.blockScaleCovariant_of_blockScaleCovariantOn
    (h.scaleCovariant m hm)
  transport := h.transport

/-- The block average of a scale-invariant `U` is measurable for the gated `𝒢_m`. -/
theorem measurable_similaritySigmaOn_blockAverageLint {R : MarkedReRooting Ω}
    {S : ScaleAction R} {G : Set Ω} {m : ℝ} (hequi : BlockEquivariantOn R G m)
    (hgraph : R.MeasurableBlockGraph m) (hside : Measurable (R.blockSideAt m))
    (hcov : S.BlockScaleCovariantOn G m) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hUinv : S.InvariantFun U) :
    Measurable[(S.similaritySigmaOn G m).sigma] (R.blockAverageLint m U) := by
  intro t ht
  refine MeasurableSpace.measurableSet_inf.2
    ⟨measurable_blockSigmaOn_blockAverageLint hequi hgraph hside hU ht, ?_⟩
  refine ⟨MarkedReRooting.measurable_blockAverageLint hgraph hside hU ht, fun s hs ω hω => ?_⟩
  simp only [Set.mem_preimage]
  rw [ScaleAction.blockAverageLint_dilate_at (MarkedReRooting.measurableSet_blockSetAt hgraph)
    hU hUinv hs ω (hcov s hs ω hω).1 (hcov s hs ω hω).2]

/-- The transport identity tested on the gated `𝒢_m`, for a scale-invariant `f`.  The gated test
set is replaced by its intersection with the domain, which is exactly scale invariant
(`ScaleAction.invariantSet_inter_domain`), so the **ungated** transport identity applies; the two
replacements are then undone by `blockAverageLint_indicator_inter_domain` (Lebesgue-almost every
re-rooting stays in the domain) and `lintegral_indicator_inter_domain` (the domain is conull). -/
theorem blockTransportOn_similaritySigmaOn {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hdata : SimilarityBlockDataOn R S μ G) {m : ℝ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Measurable f) (hfinv : S.InvariantFun f) :
    R.BlockTransportOn m (S.similaritySigmaOn G m) μ fun x => ENNReal.ofReal (f x) := by
  intro A hA
  obtain ⟨hAblock, hAscale⟩ := ScaleAction.measurableSet_similaritySigmaOn_iff.1 hA
  have hAmeas : MeasurableSet A := hAblock.1
  have hImeas : MeasurableSet (A ∩ G) := hAmeas.inter hdom.measurable
  have hIinv : S.InvariantSet (A ∩ G) :=
    ScaleAction.invariantSet_inter_domain hdom hAscale.2
  have htr := hdata.transport m hm ((A ∩ G).indicator fun x => ENNReal.ofReal (f x))
    (hf.ennreal_ofReal.indicator hImeas)
    (ScaleAction.invariantFun_indicator hIinv (ScaleAction.invariantFun_ofReal hfinv))
  calc (∫⁻ ω, R.blockAverageLint m (A.indicator fun x => ENNReal.ofReal (f x)) ω ∂μ)
      = ∫⁻ ω, R.blockAverageLint m ((A ∩ G).indicator fun x => ENNReal.ofReal (f x)) ω ∂μ :=
        lintegral_congr fun ω =>
          (blockAverageLint_indicator_inter_domain hdom A (fun x => ENNReal.ofReal (f x)) ω).symm
    _ = ∫⁻ ω, (A ∩ G).indicator (fun x => ENNReal.ofReal (f x)) ω ∂μ := htr
    _ = ∫⁻ ω, A.indicator (fun x => ENNReal.ofReal (f x)) ω ∂μ :=
        lintegral_indicator_inter_domain hdom A _

/-- **`s:lem:conditional` on the invariant domain**: for a nonnegative integrable
scale-invariant `f`, the block average is the conditional expectation given the gated `𝒢_m`. -/
theorem blockAverage_ae_eq_condExp_similarityOn {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hdata : SimilarityBlockDataOn R S μ G) {m : ℝ} (hm : 0 < m)
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (hint : Integrable f μ)
    (hfinv : S.InvariantFun f) :
    R.blockAverage m f =ᵐ[μ] μ[f|(S.similaritySigmaOn G m).sigma] := by
  refine MarkedReRooting.blockAverage_ae_eq_condExp_of_sigma_ae (hdata.measurableGraph m hm)
    (hdata.measurableSide m hm) (ScaleAction.similaritySigmaOn_le S G m) ?_ hf hf0 hint ?_
    (blockTransportOn_similaritySigmaOn hdom hdata hm hf hfinv)
  · intro A hA
    filter_upwards [hdom.ae_mem] with ω hω
    intro z hz
    exact (ScaleAction.measurableSet_similaritySigmaOn_iff.1 hA).1.2 ω hω z hz
  · have hlint : Measurable[(S.similaritySigmaOn G m).sigma]
        (R.blockAverageLint m fun x => ENNReal.ofReal (f x)) :=
      measurable_similaritySigmaOn_blockAverageLint (hdata.equivariant m hm)
        (hdata.measurableGraph m hm) (hdata.measurableSide m hm) (hdata.scaleCovariant m hm)
        hf.ennreal_ofReal (ScaleAction.invariantFun_ofReal hfinv)
    rw [MarkedReRooting.blockAverage_eq_toReal_fun hf hf0]
    exact hlint.ennreal_toReal

/-- **`s:eq:dyadicmax` over the complete origin chain**, for scale-invariant `F`, on the
manuscript's invariant domain. -/
theorem measure_exists_originAverage_gt_le_similarityOn {R : MarkedReRooting Ω}
    {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Set Ω}
    (hdom : InvariantDomain R S μ G) (hchain : OriginChainRegularOn R G)
    (hdata : SimilarityBlockDataOn R S μ G)
    {F : Ω → ℝ} (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) {t : ℝ} (ht : 0 < t) :
    μ {ω | ∃ k : ℤ, ENNReal.ofReal t < originAverage R F k ω}
      ≤ ENNReal.ofReal ((∫ ω, F ω ∂μ) / t) := by
  refine measure_exists_originAverage_gt_le_of_condExpOn R hchain hF hF0 hFint
    (fun q : ℚ => (S.similaritySigmaOn G (param q)).sigma)
    (fun a b hab => ScaleAction.similaritySigmaOn_antitone hchain (param_pos a) (param_mono hab))
    (fun q => ScaleAction.similaritySigmaOn_le _ _ _)
    (fun q => blockAverage_ae_eq_condExp_similarityOn hdom hdata (param_pos q) hF hF0 hFint hFinv)
    (fun q => ?_) ht
  exact ae_lt_top
    (MarkedReRooting.measurable_blockAverageLint (hdata.measurableGraph _ (param_pos q))
      (hdata.measurableSide _ (param_pos q)) hF.ennreal_ofReal)
    (MarkedReRooting.lintegral_blockAverageLint_ofReal_ne_top_of_on
      (blockTransportOn_similaritySigmaOn hdom hdata (param_pos q) hF hFinv) hF0 hFint)

/-- **`s:eq:maximal`** for scale-invariant `F`, on the manuscript's invariant domain:
`P[M(ρ) > λ] ≤ 512 E[F]/λ`. -/
theorem measure_ballMaximal_gt_le_similarityOn {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒜 : EnvSigma Ω} {G : Set Ω}
    (hdom : InvariantDomain R S μ G) (hchain : OriginChainRegularOn R G)
    (hdata : SimilarityBlockDataOn R S μ G)
    {F : Ω → ℝ} (henv : EnvironmentGrid R μ F 𝒜)
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) {lam : ℝ} (hlam : 0 < lam) :
    μ {ω | ENNReal.ofReal lam < ballMaximal R F ω}
      ≤ ENNReal.ofReal (512 * (∫ ω, F ω ∂μ) / lam) :=
  measure_ballMaximal_gt_le_of_originBound R henv
    (fun _ ht =>
      measure_exists_originAverage_gt_le_similarityOn hdom hchain hdata hF hF0 hFint hFinv ht)
    hlam

/-- **`M(ρ) < ∞` almost surely** for scale-invariant `F`, on the manuscript's invariant
domain. -/
theorem ballMaximal_lt_top_ae_similarityOn {R : MarkedReRooting Ω} {S : ScaleAction R}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒜 : EnvSigma Ω} {G : Set Ω}
    (hdom : InvariantDomain R S μ G) (hchain : OriginChainRegularOn R G)
    (hdata : SimilarityBlockDataOn R S μ G)
    {F : Ω → ℝ} (henv : EnvironmentGrid R μ F 𝒜)
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hFint : Integrable F μ)
    (hFinv : S.InvariantFun F) :
    ∀ᵐ ω ∂μ, ballMaximal R F ω < ∞ :=
  ballMaximal_lt_top_ae_of_originBound R henv
    (fun _ ht =>
      measure_exists_originAverage_gt_le_similarityOn hdom hchain hdata hF hF0 hFint hFinv ht)

end ReflectedGMS.SimilarityBlockAveraging
