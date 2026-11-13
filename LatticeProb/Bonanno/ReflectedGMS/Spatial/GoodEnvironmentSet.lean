/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.GoodEnvironmentSet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MeasurableSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualMarkedBlockTransport

/-!
# The good environment set

The spatial maximal inequality `s:prop:maximal` assumes the origin-chain
regularity `SpatialMaximalInequality.OriginChainRegular` for *every*
configuration of the marked space.  For an arbitrary code that is false: it holds
exactly on the environments whose large cells decay, which is an almost sure event
(`Spatial.ae_maxDiamHittingBall_finite_and_sublinear`).  This module isolates that
event and records the three properties the restriction of the marked space needs.

* `GoodEnvironment e`: `D_R < ∞` for every radius `R ≥ 0` together with the
  sublinear decay `NonmacroscopicSelectedBlocks.SublinearDiameterDecay`.
* `ae_goodEnvironment`: the event has full measure under mass transport and a
  finite (FE) moment.
* `measurableSet_goodEnvironment`: the event is measurable.  `R ↦ D_R` is monotone,
  so the real quantifiers reduce to countable ones (`finite_iff_nat`,
  `sublinearDiameterDecay_iff_rat`), and each `D_R` is a measurable function of the
  code (`measurable_maxDiamHittingBall`), being a countable slot supremum
  (`maxDiamHittingBall_eq_iSup_slotBallDiam`) in the style of
  `MeasurableSelectedBlocks.maxCellDiameter_eq_iSup_slotBoxDiam`.
* `goodEnvironment_of_isSimilarity`: the event is stable under every physical
  similarity, through the covariance bound `maxDiamHittingBall_le_of_isSimilarity`
  `D'_R ≤ s · D_{‖u‖ + R/s}`; in particular under `translateEnv` and
  `similarityTargetEnv`.
* The three pathwise origin-chain regularity clauses
  (`blockIndex_originIndex_ne_top`, `tendsto_inverseRatio_ancestor_originIndex`,
  `exists_blockIndex_originIndex_le`), stated for an arbitrary countable cell family
  with `Geometry` and the decay hypotheses, in the exact shapes of the fields of
  `OriginChainRegular`.  The third of these additionally needs **the origin to lie in a
  cell**: under the weakened covering clause of `Geometry` (`μH[1] (uncoveredSet F) = 0`
  rather than `⋃ v, cell v = univ`) it is false at an uncovered origin, see its docstring.
  The first two survive unaided, because `maxCellDiameter_pos` only needs a covered point
  somewhere in the square and the covered points are dense.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GoodEnvironmentSet

open StatementIngredients DyadicApproximation DiameterBlockIndex Code Spatial
open NonmacroscopicSelectedBlocks MarkedBlockAveraging EnvironmentLaws MeasurableSelectedBlocks
open ActualMarkedBlockTransport

variable {V : Type*}

/-! ### Monotonicity of `D_R` in the radius -/

theorem maxDiamHittingBall_mono (F : IndexedCells V) {R R' : ℝ} (h : R ≤ R') :
    maxDiamHittingBall F R ≤ maxDiamHittingBall F R' := by
  refine iSup_le fun v => ?_
  obtain ⟨x, hx1, hx2⟩ := v.2
  exact le_iSup (fun w : {w : V // Hits F (Metric.closedBall (0 : Plane) R') w} =>
    ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane)))
    ⟨v.1, ⟨x, hx1, Metric.closedBall_subset_closedBall h hx2⟩⟩

/-- Finiteness at every radius reduces to the natural radii. -/
theorem finite_iff_nat (F : IndexedCells V) :
    (∀ R : ℝ, 0 ≤ R → maxDiamHittingBall F R < ∞) ↔
      ∀ n : ℕ, maxDiamHittingBall F n < ∞ := by
  refine ⟨fun h n => h n (Nat.cast_nonneg n), fun h R _ => ?_⟩
  exact lt_of_le_of_lt (maxDiamHittingBall_mono F (Nat.le_ceil R)) (h ⌈R⌉₊)

/-- Sublinear decay reduces to rational slopes, natural thresholds and rational
radii. -/
theorem sublinearDiameterDecay_iff_rat (F : IndexedCells V) :
    SublinearDiameterDecay F ↔
      ∀ ε : {ε : ℚ // 0 < ε}, ∃ N : ℕ, ∀ q : {q : ℚ // (N : ℝ) ≤ q},
        maxDiamHittingBall F q.1 ≤ ENNReal.ofReal ((ε.1 : ℝ) * q.1) := by
  constructor
  · rintro h ⟨ε, hε⟩
    obtain ⟨R₀, -, hR₀⟩ := h (ε : ℝ) (by exact_mod_cast hε)
    exact ⟨⌈R₀⌉₊, fun q => hR₀ q.1 (le_trans (Nat.le_ceil R₀) q.2)⟩
  · intro h ε hε
    obtain ⟨ε', hε'0, hε'⟩ := exists_rat_btwn (half_pos hε)
    have hε'0' : (0 : ℚ) < ε' := by exact_mod_cast hε'0
    obtain ⟨N, hN⟩ := h ⟨ε', hε'0'⟩
    refine ⟨max (N : ℝ) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun R hR => ?_⟩
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) hR
    have hRN : (N : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    obtain ⟨q, hRq, hqR⟩ := exists_rat_btwn (lt_add_one R)
    have hq := hN ⟨q, le_trans hRN hRq.le⟩
    refine le_trans (maxDiamHittingBall_mono F hRq.le)
      (le_trans hq (ENNReal.ofReal_le_ofReal ?_))
    have h1 : (ε' : ℝ) * q ≤ ε / 2 * (R + 1) :=
      mul_le_mul hε'.le hqR.le (by linarith) (by linarith)
    nlinarith [mul_nonneg hε.le (sub_nonneg.2 hR1)]

/-! ### `D_R` as a countable slot supremum -/

/-- A nonempty compact cell meets `clB R` iff its distance from the origin is at
most `R`. -/
theorem cell_inter_closedBall_nonempty_iff (K : CompactCell) (R : ℝ) :
    ((K : Set Plane) ∩ Metric.closedBall (0 : Plane) R).Nonempty ↔
      Metric.infDist (0 : Plane) (K : Set Plane) ≤ R := by
  constructor
  · rintro ⟨x, hxK, hxB⟩
    exact le_trans (Metric.infDist_le_dist_of_mem hxK) (Metric.mem_closedBall'.mp hxB)
  · intro h
    obtain ⟨y, hyK, hy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty (0 : Plane)
    exact ⟨y, hyK, Metric.mem_closedBall'.mpr (by rw [← hy]; exact h)⟩

/-- Present code slots whose cell meets `clB R`. -/
def SlotMeetsBallSet (R : ℝ) : Set (Option CompactCell) :=
  {o | o.isSome ∧
    Metric.infDist (0 : Plane) ((o.getD referenceCell : CompactCell) : Set Plane) ≤ R}

theorem measurableSet_slotMeetsBallSet (R : ℝ) : MeasurableSet (SlotMeetsBallSet R) := by
  have hEq : SlotMeetsBallSet R
      = {o : Option CompactCell | o.isSome} ∩
        {o : Option CompactCell |
          Metric.infDist (0 : Plane) ((o.getD referenceCell : CompactCell) : Set Plane) ≤ R} :=
    Set.ext fun _ => Iff.rfl
  rw [hEq]
  exact measurableSet_slotIsSome.inter
    (measurableSet_le ((measurable_infDist_cell (0 : Plane)).comp measurable_slotCell)
      measurable_const)

/-- The cell diameter contributed by one code slot to `clB R`: zero for an absent
slot and for a cell missing the ball. -/
noncomputable def slotBallDiam (R : ℝ) (o : Option CompactCell) : ℝ≥0∞ :=
  (SlotMeetsBallSet R).indicator
    (fun o => ENNReal.ofReal (Metric.diam ((o.getD referenceCell : CompactCell) : Set Plane))) o

theorem measurable_slotBallDiam (R : ℝ) : Measurable (slotBallDiam R) :=
  ((measurable_cellDiam.comp measurable_slotCell).ennreal_ofReal).indicator
    (measurableSet_slotMeetsBallSet R)

/-- `D_R` of a coded environment is a supremum over the countably many code slots. -/
theorem maxDiamHittingBall_eq_iSup_slotBallDiam (e : Env) (R : ℝ) :
    maxDiamHittingBall (decode e) R = ⨆ n : ℕ, slotBallDiam R (e.val.1 n) := by
  refine le_antisymm (iSup_le fun v => ?_) (iSup_le fun n => ?_)
  · have hcell : ((e.val.1 v.1.val).getD referenceCell : CompactCell) = (decode e).cell v.1 :=
      getD_eq_get _ v.1.property
    have hmem : e.val.1 v.1.val ∈ SlotMeetsBallSet R :=
      ⟨v.1.property, by
        rw [hcell]
        exact (cell_inter_closedBall_nonempty_iff _ R).mp v.2⟩
    have hval : slotBallDiam R (e.val.1 v.1.val)
        = ENNReal.ofReal (Metric.diam ((decode e).cell v.1 : Set Plane)) := by
      unfold slotBallDiam
      rw [Set.indicator_of_mem hmem, hcell]
    rw [← hval]
    exact le_iSup (fun n : ℕ => slotBallDiam R (e.val.1 n)) v.1.val
  · by_cases hmem : e.val.1 n ∈ SlotMeetsBallSet R
    · have hsome := hmem.1
      have hcell : ((e.val.1 n).getD referenceCell : CompactCell)
          = (decode e).cell ⟨n, hsome⟩ := getD_eq_get _ hsome
      have hhits : Hits (decode e) (Metric.closedBall (0 : Plane) R) ⟨n, hsome⟩ := by
        have hle := hmem.2
        rw [hcell] at hle
        exact (cell_inter_closedBall_nonempty_iff _ R).mpr hle
      have hval : slotBallDiam R (e.val.1 n)
          = ENNReal.ofReal (Metric.diam ((decode e).cell ⟨n, hsome⟩ : Set Plane)) := by
        unfold slotBallDiam
        rw [Set.indicator_of_mem hmem, hcell]
      rw [hval]
      exact le_iSup
        (fun v : {v : Vertex e.val // Hits (decode e) (Metric.closedBall (0 : Plane) R) v} =>
          ENNReal.ofReal (Metric.diam ((decode e).cell v.1 : Set Plane))) ⟨⟨n, hsome⟩, hhits⟩
    · have hval : slotBallDiam R (e.val.1 n) = 0 := by
        unfold slotBallDiam
        rw [Set.indicator_of_notMem hmem]
      rw [hval]
      exact zero_le

/-- `D_R` is a measurable function of the coded environment. -/
theorem measurable_maxDiamHittingBall (R : ℝ) :
    Measurable fun e : Env => maxDiamHittingBall (decode e) R := by
  have hEq : (fun e : Env => maxDiamHittingBall (decode e) R)
      = fun e : Env => ⨆ n : ℕ, slotBallDiam R (e.val.1 n) :=
    funext fun e => maxDiamHittingBall_eq_iSup_slotBallDiam e R
  rw [hEq]
  exact Measurable.iSup fun n => (measurable_slotBallDiam R).comp
    ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion))

/-! ### The good environments -/

/-- The good environments: finite large-cell diameter at every radius and sublinear
decay. -/
def GoodEnvironment (e : Env) : Prop :=
  (∀ R : ℝ, 0 ≤ R → maxDiamHittingBall (decode e) R < ∞) ∧
    SublinearDiameterDecay (decode e)

/-- Almost every environment is good, from `s:lem:largecells`. -/
theorem ae_goodEnvironment (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, GoodEnvironment e := by
  filter_upwards [ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE] with e he
  exact ⟨he.1, he.2.1⟩

/-- The good set as a countable Boolean combination of level sets of `D_R`. -/
theorem setOf_goodEnvironment_eq :
    {e : Env | GoodEnvironment e}
      = (⋂ n : ℕ, {e : Env | maxDiamHittingBall (decode e) n < ∞}) ∩
        ⋂ ε : {ε : ℚ // 0 < ε}, ⋃ N : ℕ, ⋂ q : {q : ℚ // (N : ℝ) ≤ q},
          {e : Env | maxDiamHittingBall (decode e) q.1 ≤ ENNReal.ofReal ((ε.1 : ℝ) * q.1)} := by
  ext e
  simp only [GoodEnvironment, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_iUnion]
  exact and_congr (finite_iff_nat (decode e)) (sublinearDiameterDecay_iff_rat (decode e))

theorem measurableSet_goodEnvironment : MeasurableSet {e : Env | GoodEnvironment e} := by
  rw [setOf_goodEnvironment_eq]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => ?_)
    (MeasurableSet.iInter fun ε => MeasurableSet.iUnion fun N =>
      MeasurableSet.iInter fun q => ?_)
  · exact measurableSet_lt (measurable_maxDiamHittingBall (n : ℝ)) measurable_const
  · exact measurableSet_le (measurable_maxDiamHittingBall (q.1 : ℝ)) measurable_const

/-! ### Similarity covariance -/

/-- A point whose similarity image lies in `clB R` lies in `clB (‖u‖ + R/s)`. -/
theorem norm_le_of_positiveSimilarity_mem_closedBall {s : ℝ} (hs : 0 < s) (u x : Plane)
    {R : ℝ} (hx : positiveSimilarity s u x ∈ Metric.closedBall (0 : Plane) R) :
    ‖x‖ ≤ ‖u‖ + R / s := by
  have h1 : ‖positiveSimilarity s u x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have h2 : ‖positiveSimilarity s u x‖ = s * ‖x - u‖ := by
    rw [positiveSimilarity_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have h3 : ‖x - u‖ ≤ R / s := (le_div_iff₀' hs).2 (by rw [← h2]; exact h1)
  calc ‖x‖ = ‖x - u + u‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
    _ ≤ R / s + ‖u‖ := by linarith
    _ = ‖u‖ + R / s := add_comm _ _

/-- The covariance of `D_R`: a similarity image scales the large-cell diameter by
`s` and moves the ball to a ball of radius `‖u‖ + R/s`. -/
theorem maxDiamHittingBall_le_of_isSimilarity {s : ℝ} {u : Plane} (hs : 0 < s) {e e' : Env}
    (hsim : IsSimilarity s u hs e e') (R : ℝ) :
    maxDiamHittingBall (decode e') R
      ≤ ENNReal.ofReal s * maxDiamHittingBall (decode e) (‖u‖ + R / s) := by
  obtain ⟨relabel, hcell, -⟩ := hsim
  unfold maxDiamHittingBall
  rw [ENNReal.mul_iSup]
  refine iSup_le fun w => ?_
  have hw : (decode e').cell w.1
      = transformCell s u hs ((decode e).cell (relabel.symm w.1)) := by
    rw [← hcell, Equiv.apply_symm_apply]
  obtain ⟨y, hyK, hyB⟩ := w.2
  rw [hw, coe_transformCell] at hyK
  obtain ⟨x, hxK, rfl⟩ := hyK
  have hhits : Hits (decode e) (Metric.closedBall (0 : Plane) (‖u‖ + R / s)) (relabel.symm w.1) :=
    ⟨x, hxK, mem_closedBall_zero_iff.mpr
      (norm_le_of_positiveSimilarity_mem_closedBall hs u x hyB)⟩
  refine le_trans ?_ (le_iSup
    (fun z : {z : Vertex e.val //
        Hits (decode e) (Metric.closedBall (0 : Plane) (‖u‖ + R / s)) z} =>
      ENNReal.ofReal s * ENNReal.ofReal (Metric.diam ((decode e).cell z.1 : Set Plane)))
    ⟨relabel.symm w.1, hhits⟩)
  rw [hw, coe_transformCell, diam_image_positiveSimilarity s u hs, ENNReal.ofReal_mul hs.le]

/-- Good environments are stable under every physical similarity. -/
theorem goodEnvironment_of_isSimilarity {s : ℝ} {u : Plane} (hs : 0 < s) {e e' : Env}
    (hsim : IsSimilarity s u hs e e') (he : GoodEnvironment e) : GoodEnvironment e' := by
  obtain ⟨hfin, hsub⟩ := he
  refine ⟨fun R hR => ?_, fun ε hε => ?_⟩
  · refine lt_of_le_of_lt (maxDiamHittingBall_le_of_isSimilarity hs hsim R) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hfin _ (add_nonneg (norm_nonneg u) (div_nonneg hR hs.le)))
  · obtain ⟨R₀, hR₀, hR₀b⟩ := hsub (ε / 2) (half_pos hε)
    refine ⟨max (s * R₀) (s * ‖u‖), lt_of_lt_of_le (mul_pos hs hR₀) (le_max_left _ _),
      fun R hR => ?_⟩
    have hR1 : s * R₀ ≤ R := le_trans (le_max_left _ _) hR
    have hR2 : s * ‖u‖ ≤ R := le_trans (le_max_right _ _) hR
    have hs0 : s ≠ 0 := hs.ne'
    have hRs : s * (R / s) = R := by field_simp
    have hR₀le : R₀ ≤ ‖u‖ + R / s := by
      have : R₀ ≤ R / s := (le_div_iff₀' hs).2 hR1
      linarith [norm_nonneg u]
    refine le_trans (maxDiamHittingBall_le_of_isSimilarity hs hsim R) ?_
    refine le_trans (mul_le_mul' le_rfl (hR₀b _ hR₀le)) ?_
    rw [← ENNReal.ofReal_mul hs.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hε2 : (0 : ℝ) ≤ ε / 2 := by linarith
    calc s * (ε / 2 * (‖u‖ + R / s))
        = ε / 2 * (s * ‖u‖) + ε / 2 * (s * (R / s)) := by ring
      _ = ε / 2 * (s * ‖u‖) + ε / 2 * R := by rw [hRs]
      _ ≤ ε / 2 * R + ε / 2 * R := by linarith [mul_le_mul_of_nonneg_left hR2 hε2]
      _ = ε * R := by ring

theorem goodEnvironment_translateEnv (w : Plane) {e : Env} (he : GoodEnvironment e) :
    GoodEnvironment (translateEnv w e) :=
  goodEnvironment_of_isSimilarity one_pos (isSimilarity_translateEnv w e) he

theorem goodEnvironment_similarityTargetEnv (s : ℝ) (u : Plane) (hs : 0 < s) {e : Env}
    (he : GoodEnvironment e) : GoodEnvironment (similarityTargetEnv s u hs e) :=
  goodEnvironment_of_isSimilarity hs (isSimilarity_similarityTargetEnv s u hs e) he

/-! ### The pathwise origin-chain regularity clauses -/

/-- `κ` is finite at every origin square (the first field of `OriginChainRegular`). -/
theorem blockIndex_originIndex_ne_top [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (k : ℤ) : blockIndex F D (originIndex k) ≠ ∞ :=
  (blockIndex_lt_top F D _ (ancestorRatio_pos F D _ (maxCellDiameter_pos F hF D _))).ne

/-- Along any ancestor chain the inverse ratio exceeds every finite level. -/
theorem exists_ofReal_le_inverseRatio_ancestor (F : IndexedCells V) (D : Grid)
    (hsub : SublinearDiameterDecay F) (s : SquareIndex) {m : ℝ} (hm : 0 < m) :
    ∃ J : ℕ, ENNReal.ofReal m ≤ inverseRatio F D (ancestor D s J) := by
  have hδ : (0 : ℝ) < (3 * m)⁻¹ := by positivity
  obtain ⟨J, hJ⟩ := exists_ancestorRatio_ancestor_le F D s hsub hδ
  refine ⟨J, ?_⟩
  have h3δ : (3 : ℝ) * (3 * m)⁻¹ = m⁻¹ := by
    have hm0 : m ≠ 0 := hm.ne'
    field_simp
  rw [h3δ, ENNReal.ofReal_inv_of_pos hm] at hJ
  show ENNReal.ofReal m ≤ (ancestorRatio F D (ancestor D s J))⁻¹
  calc ENNReal.ofReal m = ((ENNReal.ofReal m)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ (ancestorRatio F D (ancestor D s J))⁻¹ := ENNReal.inv_le_inv.2 hJ

/-- The inverse ratios diverge along the origin chain (the second field of
`OriginChainRegular`). -/
theorem tendsto_inverseRatio_ancestor_originIndex (F : IndexedCells V) (D : Grid)
    (hsub : SublinearDiameterDecay F) (k : ℤ) :
    Filter.Tendsto (fun j : ℕ => inverseRatio F D (ancestor D (originIndex k) j))
      Filter.atTop (nhds ∞) := by
  refine ENNReal.tendsto_nhds_top fun n => ?_
  obtain ⟨J, hJ⟩ := exists_ofReal_le_inverseRatio_ancestor F D hsub (originIndex k)
    (m := (n : ℝ) + 1) (by positivity)
  have hlt : (n : ℝ≥0∞) < ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast n]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  exact Filter.eventually_atTop.2 ⟨J, fun j hj =>
    lt_of_lt_of_le hlt (le_trans hJ (inverseRatio_ancestor_mono F D (originIndex k) hj))⟩

/-- `κ` drops below every positive level at a fine enough origin square (the third
field of `OriginChainRegular`): the origin lies in every origin square, and a deep
square containing a point of a fixed cell has small `κ`.

The hypothesis `h0` — **the origin lies in a cell** — is not removable.  Since the covering
clause of `Geometry` was weakened from `⋃ v, cell v = univ` to `μH[1] (uncoveredSet F) = 0`,
a prescribed point need no longer lie in a cell, and the manuscript makes exactly this
restriction: *"Along a decreasing chain containing a point `z ∈ H` one has `D(S) ≥ d_H` and
hence `κ(S) ≤ 2 ℓ(S)/d_H → 0`. … No claim is needed about an uncovered singular point."*

Without `h0` the statement is false.  Unfolding the definitions it asks for
`⨆_{j ∈ ℤ} D(S_j)/ℓ(S_j) = ∞` along the origin chain, and the cells accumulating at an
uncovered origin may have diameters shrinking arbitrarily faster than the squares — tile the
annulus `2^{-n-1} ≤ ‖x‖_∞ ≤ 2^{-n}` by squares of side `2^{-n²}` and the rest of the plane by
unit squares.  That configuration satisfies every clause of `Geometry` (its uncovered set is
`{0}`, which is `H¹`-null) and has `D(S_j)/ℓ(S_j) ≤ C` for every `j`, so `κ` stays bounded
below along the origin chain.  Only `maxCellDiameter_pos`, which needs a covered point
*somewhere in the square* rather than *at the origin*, survives the weakening unaided. -/
theorem exists_blockIndex_originIndex_le [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (D : Grid) (m : ℝ) (hm : 0 < m) (h0 : (0 : Plane) ∉ uncoveredSet F) :
    ∃ k : ℤ, blockIndex F D (originIndex k) ≤ ENNReal.ofReal m := by
  obtain ⟨v, hv, hd⟩ := exists_mem_cell_diam_pos F hF (0 : Plane) h0
  obtain ⟨k, hk⟩ := exists_side_le D
    (t := m * Metric.diam (F.cell v : Set Plane) / 2) (by positivity)
  have hz : (0 : Plane) ∈ (square D (originIndex k)).carrier :=
    halfOpenSquare_subset D _ (zero_mem_halfOpenSquare_originIndex D k)
  refine ⟨k, le_trans (blockIndex_le_ofReal_of_mem F D _ hz hv hd)
    (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [originIndex_fst]
  have hdiv : side D k / Metric.diam (F.cell v : Set Plane) ≤ m / 2 :=
    (div_le_iff₀ hd).mpr (by linarith)
  linarith

end ReflectedGMS.GoodEnvironmentSet
