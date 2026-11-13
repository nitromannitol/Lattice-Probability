/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.ActualSpatialDensityBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalInequality
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualMarkedBlockTransport

/-!
# The actual (FE) density is the marked density of the spatial maximal inequality

`Spatial/AlmostSureCutoffBounds.lean` reduces the manuscript's logarithmic cutoff hypotheses
for the actual reflected walk to one quantitative input: an almost surely finite random `M`
with

`∫_{B̄_r} ρ_FE ≤ r² M`  for every `r > 0`,  `ρ_FE(z) = (d²/a)(H_z) (π + π*)(H_z)`,

where `H_z = RootDensities.rootAt` is the boundary-masked root.  `Spatial/
SpatialMaximalInequality.lean` proves such a bound — `ballMaximal_lt_top_ae` — but for the
*marked* density `ρ_ω(z) = F(ω - z)` of an arbitrary nonnegative integrable functional `F`
of the marked configuration.  Neither module identifies the two densities.  This file makes
that identification and composes the two results.

## The identification

The marked functional is `rootFE R ω = ρ_FE(0)` read in the environment of `ω`: the
manuscript's (FE) integrand at the root cell of the configuration.  The density it generates
is `ρ_FE` itself, because re-rooting at `z` is the translation of the environment that takes
`z` to the origin.  The mathematical content is the *similarity covariance of the rooted (FE)
density*, proved here from the physical similarity relation
`EnvironmentLaws.IsSimilarity` and not assumed:

* `rootAt_similarity` — the boundary-masked root is covariant: the global boundary mask is
  carried to the global boundary mask (`mem_boundaryMask_similarity_iff`, from
  `Homeomorph.image_frontier` for the similarity homeomorphism) and interior membership is
  covariant (`Spatial.mem_interior_transformCell_iff`), so
  `H_{S z}(𝓗') = relabel (H_z(𝓗))`.
* `finiteEnergyDensity_relabel` — the (FE) *integrand* is scale invariant: diameters scale by
  `s` and areas by `s²`, so `d²/a` is unchanged (`ENNReal.mul_div_mul_left`), while the
  conductances are unchanged by a physical similarity, so `π` and `π*` are unchanged
  (`Equiv.tsum_eq` along the relabeling).
* `rootedFiniteEnergyDensity_similarity` — the two combined:
  `ρ_FE^{𝓗'}(S(s,u) z) = ρ_FE^{𝓗}(z)`.  Taking `s = 1`, `u = z` and evaluating at `z` gives
  `ofReal_rootFE_shift`: `ofReal (rootFE R (ω - z)) = ρ_FE^{𝓗(ω)}(z)`, the exact density of
  the maximal inequality.  `rootedFiniteEnergyDensity_ne_top` (from `cellArea_pos`) is what
  makes the `ℝ`-valued functional of the maximal inequality lose nothing.

## What is proved

* `ae_exists_ballBound_rootedFiniteEnergyDensity` — the input of
  `AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses`, for the actual rooted (FE)
  density, with `M = M(ρ_FE)(ω)` the manuscript's maximal function: **a random finite
  constant, valid at every radius**, not a deterministic uniform bound.
* `ae_exists_logCutoff_hypotheses_marked` — the full hypothesis tuple of manuscript
  Proposition `r:prop:log` on the marked space, with *no* remaining ball-bound hypothesis:
  the diameter clause comes from the checked large-cell decay pulled back along `R.env`
  (`ae_of_ae_map`), the quadratic local-mass clause from the maximal inequality through this
  identification.
* `envReRooting_actualReRooting`, `ae_exists_ballBound_actual`,
  `ae_exists_logCutoff_hypotheses_actual` — the same two statements on the *actual* marked
  configuration space `Env × Grid` of `Spatial/ActualMarkedBlockTransport.lean`, where the
  re-rooting property and the measurability of the environment observable are discharged
  (`ActualMarkedBlockTransport.isSimilarity_translateEnv`, `measurable_fst`) rather than
  assumed.

## The inputs that are *not* proved here

They are exactly the producer dependencies of the two modules composed, none of which is the
ball bound or any recurrence conclusion:

* `OriginChainRegular R`, `BlockData R μ`, `EnvironmentGrid R μ (rootFE R) 𝒜` — the
  selected-block regularity, the marked block transport and the independent uniform dyadic
  system of `SpatialMaximalInequality`;
* `Measurable (rootFE R)` and `Integrable (rootFE R) μ` — the manuscript's (FE) moment in
  Bochner form for the actual density.  Measurability of `e ↦ ρ_FE(decode e, 0)` on `Env` is
  not available in the repository and is *not* proved here;
* `EnvReRooting R` — that `R.shift z` really is the re-rooting `ω ↦ ω - z` of the
  environment.  This is a structural property of the action, stated through the existing
  physical similarity relation with `s = 1`, `u = z`; it is independent of every conclusion
  below, and on the actual space it is *proved*
  (`envReRooting_actualReRooting`), so it is a hypothesis only in the abstract statements;
* `MassTransport (μ.map R.env)` and the (FE) moment on `Env` — the environment-law inputs
  already required by `LargeCellDiameterDecay`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.ActualSpatialDensityBridge

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality DyadicApproximation

universe u

/-! ### Finiteness of the rooted (FE) density -/

section Finiteness

variable {V : Type u} [Countable V]

/-- The (FE) integrand of a single cell is finite: the cell area is positive
(`StatementIngredients.cellArea_pos`) and every factor is the `ofReal` of a real number. -/
theorem finiteEnergyDensity_ne_top (F : IndexedCells V) (hF : Geometry F) (v : V) :
    RootDensities.finiteEnergyDensity F v ≠ ∞ := by
  have harea : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ 0 := fun h =>
    absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (StatementIngredients.cellArea_pos F hF v))
  unfold RootDensities.finiteEnergyDensity
  exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top harea)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)

/-- The rooted (FE) density is finite everywhere: off the boundary mask it is a cell
integrand, on the mask it vanishes. -/
theorem rootedFiniteEnergyDensity_ne_top (F : IndexedCells V) (hF : Geometry F) (z : Plane) :
    RootDensities.rootedFiniteEnergyDensity F z ≠ ∞ := by
  cases hroot : RootDensities.rootAt F z with
  | none => simp [RootDensities.rootedFiniteEnergyDensity, hroot]
  | some v =>
      simpa [RootDensities.rootedFiniteEnergyDensity, hroot] using
        finiteEnergyDensity_ne_top F hF v

end Finiteness

/-! ### Similarity covariance of the rooted (FE) density -/

section Covariance

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-- The total conductance is unchanged by a physical similarity: the conductances themselves
are unchanged, and the relabeling is a bijection of the active vertices. -/
theorem pi_relabel (h : IsSimilarityRelabel s u hs e e' relabel) (v : Vertex e.val) :
    RootDensities.pi (decode e') (relabel v) = RootDensities.pi (decode e) v := by
  show (∑' w : Vertex e'.val, (decode e').graph.c (relabel v) w)
      = ∑' w : Vertex e.val, (decode e).graph.c v w
  rw [← Equiv.tsum_eq relabel fun w : Vertex e'.val => (decode e').graph.c (relabel v) w]
  exact tsum_congr fun w => h.2 v w

/-- The total reciprocal conductance is unchanged by a physical similarity. -/
theorem piStar_relabel (h : IsSimilarityRelabel s u hs e e' relabel) (v : Vertex e.val) :
    RootDensities.piStar (decode e') (relabel v) = RootDensities.piStar (decode e) v := by
  show (∑' w : Vertex e'.val, ((decode e').graph.c (relabel v) w)⁻¹)
      = ∑' w : Vertex e.val, ((decode e).graph.c v w)⁻¹
  rw [← Equiv.tsum_eq relabel fun w : Vertex e'.val => ((decode e').graph.c (relabel v) w)⁻¹]
  exact tsum_congr fun w => by rw [h.2 v w]

/-- Cell diameters scale by `s`. -/
theorem diam_cell_relabel (h : IsSimilarityRelabel s u hs e e' relabel) (v : Vertex e.val) :
    Metric.diam ((decode e').cell (relabel v) : Set Plane)
      = s * Metric.diam ((decode e).cell v : Set Plane) := by
  rw [h.1 v, coe_transformCell, Spatial.diam_image_positiveSimilarity s u hs]

/-- Cell areas scale by `s ^ 2`. -/
theorem cellArea_relabel (h : IsSimilarityRelabel s u hs e e' relabel) (v : Vertex e.val) :
    StatementIngredients.cellArea (decode e') (relabel v)
      = s ^ 2 * StatementIngredients.cellArea (decode e) v := by
  have hvol : volume ((decode e').cell (relabel v) : Set Plane)
      = ENNReal.ofReal (s ^ 2) * volume ((decode e).cell v : Set Plane) := by
    rw [h.1 v, coe_transformCell, Spatial.volume_image_positiveSimilarity]
  simp only [StatementIngredients.cellArea, hvol, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ s ^ 2)]

/-- **The (FE) integrand is similarity invariant.**  The ratio `d² / a` is scale invariant
because diameters scale by `s` and areas by `s²`, and `π`, `π*` are unchanged because a
physical similarity does not change conductances. -/
theorem finiteEnergyDensity_relabel (h : IsSimilarityRelabel s u hs e e' relabel)
    (v : Vertex e.val) :
    RootDensities.finiteEnergyDensity (decode e') (relabel v)
      = RootDensities.finiteEnergyDensity (decode e) v := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hc0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hs2
  have hdiam : ENNReal.ofReal (Metric.diam ((decode e').cell (relabel v) : Set Plane) ^ 2)
      = ENNReal.ofReal (s ^ 2) *
          ENNReal.ofReal (Metric.diam ((decode e).cell v : Set Plane) ^ 2) := by
    rw [diam_cell_relabel h v, mul_pow, ENNReal.ofReal_mul (by positivity)]
  have harea : ENNReal.ofReal (StatementIngredients.cellArea (decode e') (relabel v))
      = ENNReal.ofReal (s ^ 2) *
          ENNReal.ofReal (StatementIngredients.cellArea (decode e) v) := by
    rw [cellArea_relabel h v, ENNReal.ofReal_mul (by positivity)]
  unfold RootDensities.finiteEnergyDensity
  rw [hdiam, harea, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top,
    pi_relabel h v, piStar_relabel h v]

/-- Cell frontiers are covariant: the similarity is a homeomorphism of the plane. -/
theorem mem_frontier_transformCell_iff (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell)
    (z : Plane) :
    positiveSimilarity s u z ∈ frontier ((transformCell s u hs K : CompactCell) : Set Plane)
      ↔ z ∈ frontier (K : Set Plane) := by
  have himg : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarityHomeomorph s u hs '' (K : Set Plane) := rfl
  rw [himg, ← Homeomorph.image_frontier]
  exact Function.Injective.mem_set_image (positiveSimilarityHomeomorph s u hs).injective

/-- Cell membership is covariant: the similarity is injective. -/
theorem mem_transformCell_iff (s : ℝ) (u : Plane) (hs : 0 < s) (K : CompactCell)
    (z : Plane) :
    positiveSimilarity s u z ∈ ((transformCell s u hs K : CompactCell) : Set Plane)
      ↔ z ∈ (K : Set Plane) := by
  have himg : ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarityHomeomorph s u hs '' (K : Set Plane) := rfl
  rw [himg]
  exact Function.Injective.mem_set_image (positiveSimilarityHomeomorph s u hs).injective

/-- The uncovered set is covariant. -/
theorem mem_uncoveredSet_similarity_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (z : Plane) :
    positiveSimilarity s u z ∈ uncoveredSet (decode e') ↔ z ∈ uncoveredSet (decode e) := by
  have hiff : positiveSimilarity s u z ∈ (⋃ v', ((decode e').cell v' : Set Plane))
      ↔ z ∈ ⋃ v, ((decode e).cell v : Set Plane) := by
    constructor
    · intro hz
      obtain ⟨v', hv'⟩ := Set.mem_iUnion.mp hz
      obtain ⟨v, rfl⟩ := relabel.surjective v'
      rw [h.1 v] at hv'
      exact Set.mem_iUnion.mpr ⟨v, (mem_transformCell_iff s u hs _ z).1 hv'⟩
    · intro hz
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
      refine Set.mem_iUnion.mpr ⟨relabel v, ?_⟩
      rw [h.1 v]
      exact (mem_transformCell_iff s u hs _ z).2 hv
  simp only [uncoveredSet, Set.mem_compl_iff]
  exact not_congr hiff

/-- The global boundary mask is covariant.  Both parts transport: the frontier union because the
similarity is a homeomorphism, and the uncovered set because it is injective and surjective onto the
transformed cells. -/
theorem mem_boundaryMask_similarity_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (z : Plane) :
    positiveSimilarity s u z ∈ RootDensities.boundaryMask (decode e')
      ↔ z ∈ RootDensities.boundaryMask (decode e) := by
  show (positiveSimilarity s u z ∈
      (⋃ v', frontier ((decode e').cell v' : Set Plane)) ∪ uncoveredSet (decode e'))
    ↔ (z ∈ (⋃ v, frontier ((decode e).cell v : Set Plane)) ∪ uncoveredSet (decode e))
  constructor
  · rintro (hfr | hunc)
    · obtain ⟨v', hv'⟩ := Set.mem_iUnion.mp hfr
      obtain ⟨v, rfl⟩ := relabel.surjective v'
      rw [h.1 v] at hv'
      exact Or.inl (Set.mem_iUnion.mpr ⟨v, (mem_frontier_transformCell_iff s u hs _ z).1 hv'⟩)
    · exact Or.inr ((mem_uncoveredSet_similarity_iff h z).1 hunc)
  · rintro (hfr | hunc)
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hfr
      refine Or.inl (Set.mem_iUnion.mpr ⟨relabel v, ?_⟩)
      rw [h.1 v]
      exact (mem_frontier_transformCell_iff s u hs _ z).2 hv
    · exact Or.inr ((mem_uncoveredSet_similarity_iff h z).2 hunc)

/-- Interior root membership is covariant. -/
theorem isInteriorRoot_similarity_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (z : Plane) (v : Vertex e.val) :
    RootDensities.IsInteriorRoot (decode e') (positiveSimilarity s u z) (relabel v)
      ↔ RootDensities.IsInteriorRoot (decode e) z v := by
  unfold RootDensities.IsInteriorRoot
  rw [h.1 v]
  exact Spatial.mem_interior_transformCell_iff s u hs _ z

/-- **The boundary-masked root is covariant.**  Both branches of `rootAt` are preserved: the
mask is carried to the mask and the unique interior root is carried to the relabeled unique
interior root. -/
theorem rootAt_similarity (h : IsSimilarityRelabel s u hs e e' relabel) (z : Plane) :
    RootDensities.rootAt (decode e') (positiveSimilarity s u z)
      = (RootDensities.rootAt (decode e) z).map relabel := by
  cases hroot : RootDensities.rootAt (decode e) z with
  | none =>
      have hz : z ∈ RootDensities.boundaryMask (decode e) :=
        (RootDensities.rootAt_eq_none_iff (decode e) (decode_geometry e) z).1 hroot
      simpa using RootDensities.rootAt_eq_none_of_mem_boundaryMask (decode e')
        ((mem_boundaryMask_similarity_iff h z).2 hz)
  | some v =>
      obtain ⟨hz, hv⟩ :=
        (RootDensities.rootAt_eq_some_iff (decode e) (decode_geometry e) z v).1 hroot
      have hgoal : RootDensities.rootAt (decode e') (positiveSimilarity s u z)
          = some (relabel v) :=
        (RootDensities.rootAt_eq_some_iff (decode e') (decode_geometry e') _ _).2
          ⟨fun hmem => hz ((mem_boundaryMask_similarity_iff h z).1 hmem),
            (isInteriorRoot_similarity_iff h z v).2 hv⟩
      simpa using hgoal

/-- **Similarity covariance of the rooted (FE) density.**  The manuscript's (FE) density is a
scale-invariant rooted observable: `ρ_FE^{𝓗'}(S(s,u) z) = ρ_FE^{𝓗}(z)` for every physical
similarity `𝓗 → 𝓗'`. -/
theorem rootedFiniteEnergyDensity_similarity (hs : 0 < s) (hsim : IsSimilarity s u hs e e')
    (z : Plane) :
    RootDensities.rootedFiniteEnergyDensity (decode e') (positiveSimilarity s u z)
      = RootDensities.rootedFiniteEnergyDensity (decode e) z := by
  obtain ⟨relabel, h⟩ := hsim
  unfold RootDensities.rootedFiniteEnergyDensity
  rw [rootAt_similarity h z]
  cases hroot : RootDensities.rootAt (decode e) z with
  | none => simp
  | some v => simpa using finiteEnergyDensity_relabel h v

end Covariance

/-! ### The actual (FE) density as the marked density of the maximal inequality -/

section Marked

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The manuscript's (FE) integrand read at the root cell of a marked configuration.  This is
the functional `F` whose marked density `ρ_ω(z) = F(ω - z)` is the rooted (FE) density. -/
noncomputable def rootFE (R : MarkedReRooting Ω) (ω : Ω) : ℝ :=
  (RootDensities.rootedFiniteEnergyDensity (decode (R.env ω)) 0).toReal

theorem rootFE_nonneg (R : MarkedReRooting Ω) (ω : Ω) : 0 ≤ rootFE R ω :=
  ENNReal.toReal_nonneg

/-- **The re-rooting property of the marked action.**  `R.shift z` is the translation of the
environment that takes `z` to the origin, stated through the existing physical similarity
relation with `s = 1`, `u = z`.  This is a structural property of the action `ω ↦ ω - z`; it
mentions no ball average and no local mass. -/
def EnvReRooting (R : MarkedReRooting Ω) : Prop :=
  ∀ (ω : Ω) (z : Plane), IsSimilarity 1 z zero_lt_one (R.env ω) (R.env (R.shift z ω))

/-- **The density identification.**  The marked density generated by `rootFE R` is exactly the
rooted (FE) density of the environment of `ω`. -/
theorem ofReal_rootFE_shift {R : MarkedReRooting Ω} (hR : EnvReRooting R) (ω : Ω) (z : Plane) :
    ENNReal.ofReal (rootFE R (R.shift z ω))
      = RootDensities.rootedFiniteEnergyDensity (decode (R.env ω)) z := by
  have hzero : positiveSimilarity 1 z z = (0 : Plane) := by
    simp [positiveSimilarity]
  have hcov := rootedFiniteEnergyDensity_similarity zero_lt_one (hR ω z) z
  rw [hzero] at hcov
  simp only [rootFE, hcov]
  exact ENNReal.ofReal_toReal
    (rootedFiniteEnergyDensity_ne_top (decode (R.env ω)) (decode_geometry _) z)

/-- The ball integral of the marked density is below `r²` times the maximal function. -/
theorem setLIntegral_le_ballMaximal (R : MarkedReRooting Ω) (F : Ω → ℝ) (ω : Ω)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in Metric.closedBall (0 : Plane) r, ENNReal.ofReal (F (R.shift z ω)) ∂volume)
      ≤ ENNReal.ofReal (r ^ 2) * ballMaximal R F ω := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hnz : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.2 hr2
  have hid : (∫⁻ z in Metric.closedBall (0 : Plane) r,
        ENNReal.ofReal (F (R.shift z ω)) ∂volume)
      = ENNReal.ofReal (r ^ 2) * ballAverage R F r ω := by
    simp only [ballAverage]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hnz ENNReal.ofReal_ne_top, one_mul]
  rw [hid]
  exact mul_le_mul' le_rfl (ballAverage_le_ballMaximal R F hr ω)

end Marked

/-! ### The actual marked configuration space -/

section Actual

open ActualMarkedBlockTransport

end Actual

end ReflectedGMS.ActualSpatialDensityBridge
