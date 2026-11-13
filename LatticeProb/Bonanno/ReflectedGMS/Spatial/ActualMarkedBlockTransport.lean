/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.ActualMarkedBlockTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicGridTranslation
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalSimilarityMeasurable

/-!
# The actual marked re-rooting and its block equivariance

`ReflectedGMS.Spatial.MarkedBlockAveraging` proves the manuscript lemma
"Conditional block averaging" (`s:lem:conditional`) for an abstract marked
configuration space from three explicit producer dependencies: the equivariance
`MarkedReRooting.BlockEquivariant`, the joint measurability
`MarkedReRooting.MeasurableBlockGraph`, and the measurability of the block side
length.  The last two are supplied for the actual environment–grid observables by
`ReflectedGMS.Spatial.MeasurableSelectedBlocks`.

This module builds the *actual* marked configuration space and discharges the
equivariance producer on it.  Nothing is assumed about the law here: the whole
statement is pathwise geometry plus the canonical similarity action.

* the marked configuration is an actual pair `Env × Grid`: the trace-measurable
  environment of `ReflectedGMS.Code` together with the independent uniform dyadic
  system `𝔻'` of the marks;
* re-rooting at `w` is the *existing* canonical similarity action at unit scale,
  `EnvironmentLaws.similarityTargetEnv 1 w`, on the environment and the *existing*
  `DyadicGridTranslation.translate w` on the grid.  `translateEnv_zero`,
  `translateEnv_translateEnv` and `measurable_translateEnv` make this an actual
  jointly measurable action, so `actualReRooting : MarkedReRooting (Env × Grid)`
  is a genuine instance of the consumer's data, not an abstraction;
* the geometric heart is `originCoord`, the position of a point inside the
  level-`k` origin square in units of the side length.  A point lies in the
  half-open level-`k` origin square exactly when every coordinate of `originCoord`
  lies in `[0,1)` (`mem_halfOpenSquare_originIndex_iff`), and the halving
  recursion `originCoord_succ` propagates this upwards along the origin chain
  (`mem_halfOpenSquare_originIndex_of_le`).  Consequently re-rooting at a point of
  the level-`k` origin square leaves the integer lattice reindexing of
  `DyadicGridTranslation.square_carrier_translate` trivial at every level `l ≥ k`;
* therefore the whole selection statistic is transported: the patch of a
  re-rooted square is the patch of the original square
  (`maxCellDiameter_translateEnv`, through the checked
  `hits_transformIndexedCells` and the isometry invariance of the diameter),
  hence `blockIndex_originIndex_translateEnv` and
  `originSelected_translateEnv` along the whole origin ancestor chain;
* `blockEquivariant_actualReRooting` is the producer itself, and
  `neg_mem_blockSetAt_shift_iff` is the partition statement `0 ∈ S_m(w) ↔ w ∈
  S_m(0)` that the mass-transport computation of `MarkedBlockTransport` needs for
  its incoming integral.

The only hypotheses are the manuscript's pathwise existence and uniqueness of the
selected origin square, in the same form already used by
`MeasurableSelectedBlocks`; `blockEquivariant_of_strictMono` derives uniqueness
from strict monotonicity of `κ` along the origin chain through the checked
`MarkedBlockAveraging.originSelected_unique`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ActualMarkedBlockTransport

open StatementIngredients DyadicApproximation DiameterBlockIndex Code
open MarkedBlockAveraging DyadicGridTranslation EnvironmentLaws CanonicalSimilarity

/-! ### Re-rooting an environment at unit scale -/

theorem positiveSimilarity_one (w z : Plane) : positiveSimilarity 1 w z = z - w := by
  rw [positiveSimilarity_apply, one_smul]

/-- Re-rooting an environment at `w`: the canonical similarity action of
`z ↦ z - w`.  This is the existing `EnvironmentLaws.similarityTargetEnv` at unit
scale, so no new action is constructed. -/
noncomputable def translateEnv (w : Plane) (e : Env) : Env :=
  similarityTargetEnv 1 w one_pos e

theorem isSimilarity_translateEnv (w : Plane) (e : Env) :
    IsSimilarity 1 w one_pos e (translateEnv w e) :=
  isSimilarity_similarityTargetEnv 1 w one_pos e

theorem eq_translateEnv_of_isSimilarity {w : Plane} {e e' : Env}
    (h : IsSimilarity 1 w one_pos e e') : e' = translateEnv w e :=
  eq_similarityTargetEnv_of_isSimilarity h

@[simp] theorem translateEnv_zero (e : Env) : translateEnv 0 e = e :=
  (eq_translateEnv_of_isSimilarity (isSimilarity_refl e)).symm

theorem transformCell_transformCell_one (w v : Plane) (K : CompactCell) :
    transformCell 1 v one_pos (transformCell 1 w one_pos K)
      = transformCell 1 (w + v) one_pos K := by
  have hfun : (fun z : Plane => positiveSimilarity 1 v (positiveSimilarity 1 w z))
      = positiveSimilarity 1 (w + v) := by
    funext z
    simp only [positiveSimilarity_one]
    abel
  apply SetLike.coe_injective
  rw [coe_transformCell, coe_transformCell, coe_transformCell, Set.image_image, hfun]

theorem isSimilarity_trans_one {w v : Plane} {e e₁ e₂ : Env}
    (h₁ : IsSimilarity 1 w one_pos e e₁) (h₂ : IsSimilarity 1 v one_pos e₁ e₂) :
    IsSimilarity 1 (w + v) one_pos e e₂ := by
  obtain ⟨q₁, hc₁, hg₁⟩ := h₁
  obtain ⟨q₂, hc₂, hg₂⟩ := h₂
  refine ⟨q₁.trans q₂, fun x => ?_, fun x y => ?_⟩
  · show (decode e₂).cell (q₂ (q₁ x)) = transformCell 1 (w + v) one_pos ((decode e).cell x)
    rw [hc₂ (q₁ x), hc₁ x, transformCell_transformCell_one]
  · show (decode e₂).graph.c (q₂ (q₁ x)) (q₂ (q₁ y)) = (decode e).graph.c x y
    rw [hg₂, hg₁]

theorem translateEnv_translateEnv (w v : Plane) (e : Env) :
    translateEnv v (translateEnv w e) = translateEnv (w + v) e :=
  eq_translateEnv_of_isSimilarity
    (isSimilarity_trans_one (isSimilarity_translateEnv w e)
      (isSimilarity_translateEnv v (translateEnv w e)))

/-- Re-rooting is the joint canonical similarity action at unit scale. -/
theorem translateEnv_eq_similarityActionEnv (w : Plane) (e : Env) :
    translateEnv w e = similarityActionEnv ((⟨1, one_pos⟩ : PositiveScale), w, e) := rfl

/-- Re-rooting environments is jointly measurable in the environment and the
shift: this is the checked `CanonicalSimilarity.measurable_similarityActionEnv`
at unit scale. -/
theorem measurable_translateEnv :
    Measurable fun p : Env × Plane => translateEnv p.2 p.1 := by
  have h : Measurable fun p : Env × Plane => ((⟨1, one_pos⟩ : PositiveScale), p.2, p.1) :=
    measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
  have h2 : Measurable fun p : Env × Plane =>
      similarityActionEnv ((⟨1, one_pos⟩ : PositiveScale), p.2, p.1) := by
    simpa only [Function.comp_def] using measurable_similarityActionEnv.comp h
  have heq : (fun p : Env × Plane => translateEnv p.2 p.1)
      = fun p : Env × Plane => similarityActionEnv ((⟨1, one_pos⟩ : PositiveScale), p.2, p.1) :=
    funext fun p => translateEnv_eq_similarityActionEnv p.2 p.1
  rw [heq]
  exact h2

/-! ### The position of a point inside the origin square -/

/-- The position of `w` inside the level-`k` origin square, in units of the side
length.  `w` lies in the half-open level-`k` origin square exactly when every
coordinate of this vector lies in `[0, 1)`. -/
noncomputable def originCoord (D : Grid) (w : Plane) (k : ℤ) (i : Fin 2) : ℝ :=
  relativeOrigin D k i + w i / side D k

theorem originCoord_eq (D : Grid) (w : Plane) (k : ℤ) (i : Fin 2) :
    originCoord D w k i = (w i - D.origin k i) / side D k := by
  show -D.origin k i / side D k + w i / side D k = (w i - D.origin k i) / side D k
  ring

/-- Reading a half-open interval of length `s` in units of `s`. -/
theorem div_mem_unit_Ico_iff {a s x : ℝ} (hs : 0 < s) :
    (0 ≤ (x - a) / s ∧ (x - a) / s < 1) ↔ (a ≤ x ∧ x < a + s) := by
  rw [div_nonneg_iff, div_lt_one hs]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    rcases h1 with ⟨hx, -⟩ | ⟨-, hs'⟩
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inl ⟨by linarith, hs.le⟩, by linarith⟩

theorem mem_halfOpenSquare_originIndex_iff (D : Grid) (w : Plane) (k : ℤ) :
    w ∈ halfOpenSquare D (originIndex k) ↔
      ∀ i, 0 ≤ originCoord D w k i ∧ originCoord D w k i < 1 := by
  have hs : (0 : ℝ) < side D k := side_pos D k
  have hlow : ∀ i, (square D (originIndex k)).lower i = D.origin k i := by
    intro i
    show D.origin k i + side D k * (((0 : ℤ)) : ℝ) = D.origin k i
    push_cast
    ring
  have hupp : ∀ i, (square D (originIndex k)).upper i = D.origin k i + side D k := by
    intro i
    show D.origin k i + side D k * (((0 : ℤ)) : ℝ) + side D k = D.origin k i + side D k
    push_cast
    ring
  constructor
  · intro h i
    have h1 : (square D (originIndex k)).lower i ≤ w i := (h i).1
    have h2 : w i < (square D (originIndex k)).upper i := (h i).2
    rw [hlow i] at h1
    rw [hupp i] at h2
    rw [originCoord_eq]
    exact (div_mem_unit_Ico_iff hs).2 ⟨h1, h2⟩
  · intro h i
    have h1 := (h i).1
    have h2 := (h i).2
    rw [originCoord_eq] at h1 h2
    obtain ⟨ha, hb⟩ := (div_mem_unit_Ico_iff hs).1 ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hlow i]
      exact ha
    · rw [hupp i]
      exact hb

theorem originCoord_succ (D : Grid) (w : Plane) (k : ℤ) (i : Fin 2) :
    2 * originCoord D w (k + 1) i = originCoord D w k i + ((D.digit k i).val : ℝ) := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  have hr := two_mul_relativeOrigin_succ D k i
  have hu : (2 : ℝ) * (w i / (2 * side D k)) = w i / side D k := by
    field_simp
  show 2 * (relativeOrigin D (k + 1) i + w i / side D (k + 1))
    = relativeOrigin D k i + w i / side D k + ((D.digit k i).val : ℝ)
  rw [DyadicGridTranslation.side_succ]
  calc 2 * (relativeOrigin D (k + 1) i + w i / (2 * side D k))
      = 2 * relativeOrigin D (k + 1) i + 2 * (w i / (2 * side D k)) := by ring
    _ = (relativeOrigin D k i + ((D.digit k i).val : ℝ)) + w i / side D k := by rw [hr, hu]
    _ = relativeOrigin D k i + w i / side D k + ((D.digit k i).val : ℝ) := by ring

theorem mem_halfOpenSquare_originIndex_succ (D : Grid) (w : Plane) (k : ℤ)
    (h : w ∈ halfOpenSquare D (originIndex k)) :
    w ∈ halfOpenSquare D (originIndex (k + 1)) := by
  rw [mem_halfOpenSquare_originIndex_iff] at h ⊢
  intro i
  have hd0 : (0 : ℝ) ≤ ((D.digit k i).val : ℝ) := Nat.cast_nonneg _
  have hd1 : ((D.digit k i).val : ℝ) ≤ 1 := by
    have hlt : (D.digit k i).val < 2 := (D.digit k i).isLt
    have hle : (D.digit k i).val ≤ 1 := by omega
    exact_mod_cast hle
  have hrec := originCoord_succ D w k i
  obtain ⟨h1, h2⟩ := h i
  constructor <;> linarith

theorem mem_halfOpenSquare_originIndex_add (D : Grid) (w : Plane) (k : ℤ) (n : ℕ)
    (h : w ∈ halfOpenSquare D (originIndex k)) :
    w ∈ halfOpenSquare D (originIndex (k + (n : ℤ))) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have hidx : k + ((n + 1 : ℕ) : ℤ) = (k + (n : ℤ)) + 1 := by push_cast; ring
      rw [hidx]
      exact mem_halfOpenSquare_originIndex_succ D w (k + (n : ℤ)) ih

/-- The half-open origin squares increase along the origin ancestor chain. -/
theorem mem_halfOpenSquare_originIndex_of_le (D : Grid) (w : Plane) {k l : ℤ} (hkl : k ≤ l)
    (h : w ∈ halfOpenSquare D (originIndex k)) :
    w ∈ halfOpenSquare D (originIndex l) := by
  have hn : l = k + ((l - k).toNat : ℤ) := by omega
  rw [hn]
  exact mem_halfOpenSquare_originIndex_add D w k _ h

/-! ### Re-rooting inside the origin square leaves the lattice index trivial -/

theorem latticeShift_eq_zero (D : Grid) (w : Plane) {l : ℤ}
    (hw : w ∈ halfOpenSquare D (originIndex l)) (i : Fin 2) :
    latticeShift D w l i = 0 := by
  have h := (mem_halfOpenSquare_originIndex_iff D w l).1 hw i
  show ⌊relativeOrigin D l i + w i / side D l⌋ = 0
  exact Int.floor_eq_zero_iff.2 ⟨h.1, h.2⟩

theorem square_carrier_translate_originIndex (D : Grid) (w : Plane) {l : ℤ}
    (hw : w ∈ halfOpenSquare D (originIndex l)) :
    (square (translate w D) (originIndex l)).carrier
      = (fun z : Plane => z + w) ⁻¹' (square D (originIndex l)).carrier := by
  have hidx : ((originIndex l).1,
      fun j => (originIndex l).2 j + latticeShift D w (originIndex l).1 j) = originIndex l := by
    refine squareIndex_ext rfl fun j => ?_
    show (0 : ℤ) + latticeShift D w l j = 0
    rw [latticeShift_eq_zero D w hw j, add_zero]
  rw [square_carrier_translate D w (originIndex l), hidx]

theorem originCoord_translate (D : Grid) (w y : Plane) (l : ℤ)
    (hw : w ∈ halfOpenSquare D (originIndex l)) (i : Fin 2) :
    originCoord (translate w D) y l i = originCoord D (w + y) l i := by
  have h := (mem_halfOpenSquare_originIndex_iff D w l).1 hw i
  have hrel : relativeOrigin (translate w D) l i = originCoord D w l i := by
    rw [relativeOrigin_translate]
    show Int.fract (relativeOrigin D l i + w i / side D l)
      = relativeOrigin D l i + w i / side D l
    exact Int.fract_eq_self.2 h
  show relativeOrigin (translate w D) l i + y i / side (translate w D) l
    = relativeOrigin D l i + ((w + y) i) / side D l
  rw [hrel, side_translate]
  show relativeOrigin D l i + w i / side D l + y i / side D l
    = relativeOrigin D l i + (w i + y i) / side D l
  ring

/-- Re-rooting at a point of the level-`k` origin square translates every higher
origin square of the grid. -/
theorem halfOpenSquare_translate (D : Grid) (w : Plane) {k l : ℤ} (hkl : k ≤ l)
    (hw : w ∈ halfOpenSquare D (originIndex k)) :
    halfOpenSquare (translate w D) (originIndex l)
      = (fun y : Plane => w + y) ⁻¹' halfOpenSquare D (originIndex l) := by
  have hw' := mem_halfOpenSquare_originIndex_of_le D w hkl hw
  ext y
  rw [Set.mem_preimage, mem_halfOpenSquare_originIndex_iff, mem_halfOpenSquare_originIndex_iff]
  exact forall_congr' fun i => by rw [originCoord_translate D w y l hw' i]

/-! ### Transport of the selection statistic -/

theorem isometry_sub_right_plane (w : Plane) : Isometry fun z : Plane => z - w :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel

theorem diam_transformCell_one (w : Plane) (K : CompactCell) :
    Metric.diam ((transformCell 1 w one_pos K : Set Plane)) = Metric.diam (K : Set Plane) := by
  have hfun : positiveSimilarity 1 w = fun z : Plane => z - w :=
    funext fun z => positiveSimilarity_one w z
  rw [coe_transformCell, hfun]
  exact (isometry_sub_right_plane w).diam_image _

/-- The maximal cell diameter of a patch only depends on the family of cells
meeting the square, through any relabelling. -/
theorem maxCellDiameter_congr_map {V W : Type*} (F : IndexedCells V) (G : IndexedCells W)
    (D E : Grid) (s t : SquareIndex) (q : V ≃ W)
    (hpatch : ∀ v : V, Hits G (square E t).carrier (q v) ↔ Hits F (square D s).carrier v)
    (hdiam : ∀ v : V, Metric.diam (G.cell (q v) : Set Plane)
      = Metric.diam (F.cell v : Set Plane)) :
    maxCellDiameter G E t = maxCellDiameter F D s := by
  have hcomp : (⨆ v : patchVertices F (square D s),
        ENNReal.ofReal (Metric.diam (G.cell (q v.1) : Set Plane)))
      = ⨆ v : patchVertices G (square E t),
        ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)) :=
    Equiv.iSup_comp
      (g := fun v : patchVertices G (square E t) =>
        ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)))
      (Equiv.subtypeEquiv q fun v => (hpatch v).symm)
  show (⨆ v : patchVertices G (square E t),
      ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)))
    = ⨆ v : patchVertices F (square D s),
      ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane))
  rw [← hcomp]
  exact iSup_congr fun v => by rw [hdiam v.1]

/-- The patch of the re-rooted origin square is the patch of the original origin
square, so the whole diameter statistic is unchanged. -/
theorem maxCellDiameter_translateEnv (e : Env) (D : Grid) (w : Plane) {l : ℤ}
    (hw : w ∈ halfOpenSquare D (originIndex l)) :
    maxCellDiameter (decode (translateEnv w e)) (translate w D) (originIndex l)
      = maxCellDiameter (decode e) D (originIndex l) := by
  obtain ⟨q, hcell, -⟩ := isSimilarity_translateEnv w e
  have hpre : positiveSimilarity 1 w ⁻¹' (square (translate w D) (originIndex l)).carrier
      = (square D (originIndex l)).carrier := by
    rw [square_carrier_translate_originIndex D w hw]
    ext z
    have hz : positiveSimilarity 1 w z + w = z := by
      rw [positiveSimilarity_one]
      abel
    show (positiveSimilarity 1 w z + w) ∈ (square D (originIndex l)).carrier
      ↔ z ∈ (square D (originIndex l)).carrier
    rw [hz]
  refine maxCellDiameter_congr_map (decode e) (decode (translateEnv w e)) D (translate w D)
    (originIndex l) (originIndex l) q (fun v => ?_) (fun v => ?_)
  · have hH : Hits (decode (translateEnv w e))
          (square (translate w D) (originIndex l)).carrier (q v)
        ↔ Hits (transformIndexedCells 1 w one_pos (decode e))
          (square (translate w D) (originIndex l)).carrier v := by
      unfold Hits
      rw [hcell v, transformIndexedCells_cell]
    rw [hH, hits_transformIndexedCells, hpre]
  · rw [hcell v, diam_transformCell_one]

theorem inverseRatio_originIndex_translateEnv (e : Env) (D : Grid) (w : Plane) {k l : ℤ}
    (hkl : k ≤ l) (hw : w ∈ halfOpenSquare D (originIndex k)) :
    inverseRatio (decode (translateEnv w e)) (translate w D) (originIndex l)
      = inverseRatio (decode e) D (originIndex l) := by
  show (ancestorRatio (decode (translateEnv w e)) (translate w D) (originIndex l))⁻¹
    = (ancestorRatio (decode e) D (originIndex l))⁻¹
  congr 1
  show (⨆ j : ℕ, maxCellDiameter (decode (translateEnv w e)) (translate w D)
        (ancestor (translate w D) (originIndex l) j) /
      ENNReal.ofReal (side (translate w D) (ancestor (translate w D) (originIndex l) j).1))
    = ⨆ j : ℕ, maxCellDiameter (decode e) D (ancestor D (originIndex l) j) /
      ENNReal.ofReal (side D (ancestor D (originIndex l) j).1)
  refine iSup_congr fun j => ?_
  rw [ancestor_originIndex, ancestor_originIndex, side_translate,
    maxCellDiameter_translateEnv e D w
      (mem_halfOpenSquare_originIndex_of_le D w (by omega : k ≤ l + (j : ℤ)) hw)]

theorem blockIndex_originIndex_translateEnv (e : Env) (D : Grid) (w : Plane) {k l : ℤ}
    (hkl : k ≤ l) (hw : w ∈ halfOpenSquare D (originIndex k)) :
    blockIndex (decode (translateEnv w e)) (translate w D) (originIndex l)
      = blockIndex (decode e) D (originIndex l) := by
  show (∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ *
      inverseRatio (decode (translateEnv w e)) (translate w D)
        (ancestor (translate w D) (originIndex l) j))
    = ∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ *
      inverseRatio (decode e) D (ancestor D (originIndex l) j)
  refine tsum_congr fun j => ?_
  rw [ancestor_originIndex, ancestor_originIndex,
    inverseRatio_originIndex_translateEnv e D w (by omega : k ≤ l + (j : ℤ)) hw]

/-- Re-rooting inside the level-`k` origin square preserves the manuscript's
selection condition at every level `l ≥ k`. -/
theorem originSelected_translateEnv (m : ℝ) (e : Env) (D : Grid) (w : Plane) {k l : ℤ}
    (hkl : k ≤ l) (hw : w ∈ halfOpenSquare D (originIndex k)) :
    OriginSelected (decode (translateEnv w e)) (translate w D) m l
      ↔ OriginSelected (decode e) D m l := by
  show (0 < m ∧ blockIndex (decode (translateEnv w e)) (translate w D) (originIndex l)
        ≤ ENNReal.ofReal m ∧
      ENNReal.ofReal m < blockIndex (decode (translateEnv w e)) (translate w D)
        (parent (translate w D) (originIndex l)))
    ↔ (0 < m ∧ blockIndex (decode e) D (originIndex l) ≤ ENNReal.ofReal m ∧
      ENNReal.ofReal m < blockIndex (decode e) D (parent D (originIndex l)))
  rw [parent_originIndex, parent_originIndex,
    blockIndex_originIndex_translateEnv e D w hkl hw,
    blockIndex_originIndex_translateEnv e D w (by omega : k ≤ l + 1) hw]

/-! ### The actual marked re-rooting -/

/-- The actual marked configuration space of the manuscript: a trace-measurable
environment together with the independent uniform dyadic system of the marks,
with the canonical similarity action at unit scale on the environment and the
dyadic re-rooting action on the marks. -/
noncomputable def actualReRooting : MarkedReRooting (Env × Grid) where
  env := Prod.fst
  grid := Prod.snd
  shift w p := (translateEnv w p.1, translate w p.2)
  measurable_shift := by
    have h1 : Measurable fun p : (Env × Grid) × Plane => translateEnv p.2 p.1.1 := by
      simpa only [Function.comp_def] using
        measurable_translateEnv.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun p : (Env × Grid) × Plane => translate p.2 p.1.2 := by
      simpa only [Function.comp_def] using
        measurable_translate.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact h1.prodMk h2
  shift_zero p := by
    show (translateEnv 0 p.1, translate 0 p.2) = p
    rw [translateEnv_zero, translate_zero]
  shift_shift w z p := by
    show (translateEnv z (translateEnv w p.1), translate z (translate w p.2))
      = (translateEnv (w + z) p.1, translate (w + z) p.2)
    rw [translateEnv_translateEnv, translate_translate]

@[simp] theorem actualReRooting_blockSetAt (m : ℝ) (p : Env × Grid) :
    actualReRooting.blockSetAt m p
      = halfOpenSquare p.2 (originIndex (blockLevel (decode p.1) p.2 m)) := rfl

@[simp] theorem actualReRooting_blockSideAt (m : ℝ) (p : Env × Grid) :
    actualReRooting.blockSideAt m p = side p.2 (blockLevel (decode p.1) p.2 m) := rfl

@[simp] theorem actualReRooting_shift (w : Plane) (p : Env × Grid) :
    actualReRooting.shift w p = (translateEnv w p.1, translate w p.2) := rfl

end ReflectedGMS.ActualMarkedBlockTransport
