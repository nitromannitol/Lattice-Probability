/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.DilatedSelectedBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualMarkedBlockTransport
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# Dilation covariance of the selected origin block

`ReflectedGMS.Spatial.ActualMarkedBlockTransport` transports the manuscript's
selected origin block along a *translation* of the environment and the dyadic
grid.  This module proves the exact *dilation* analogue: scaling the environment
by `s > 0` about the origin (the canonical similarity action
`EnvironmentLaws.similarityTargetEnv s 0`) and simultaneously dilating the grid
(`UniformGridDilationInvariance.dilate s`) shifts the level index of every origin
square by `UniformGridDilationInvariance.levelShift s D` and leaves the whole
selection statistic invariant:

* `halfOpenSquare_originIndex_dilate` and `side_dilate_add` — the origin squares
  and their side lengths scale exactly, with the level reindexing;
* `maxCellDiameter_dilate` — the patch of the dilated origin square is the patch
  of the original one (through the checked `hits_transformIndexedCells`) and
  every cell diameter is multiplied by `s`;
* `inverseRatio_originIndex_dilate`, `blockIndex_originIndex_dilate` — the
  factor `s` cancels in the diameter/side ratio, so the manuscript's `b` and `κ`
  are invariant along the whole origin chain;
* `originSelected_dilate_iff`, `blockLevel_dilate`, `blockSet_dilate`,
  `blockSide_dilate` — the selected level shifts by `levelShift s D`, so the
  selected block is dilated by `s` and its side length is multiplied by `s`.

The last two statements are exactly the field `scaleCovariant` of
`SimilarityBlockAveraging.SimilarityBlockData` for the actual marked
configuration space, under the same pathwise existence and uniqueness
hypotheses on the selected origin square as `ActualMarkedBlockTransport`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.DilatedSelectedBlocks

open StatementIngredients DyadicApproximation DiameterBlockIndex Code
open MarkedBlockAveraging EnvironmentLaws UniformGridDilationInvariance
open ActualMarkedBlockTransport

/-! ### The dilated origin squares -/

/-- The level reindexing of `UniformGridDilationInvariance` maps the origin square
at level `k + levelShift s D` back to the origin square at level `k`. -/
theorem originIndex_add_sub (s : ℝ) (D : Grid) (k : ℤ) :
    ((originIndex (k + levelShift s D)).1 - levelShift s D,
        (originIndex (k + levelShift s D)).2)
      = originIndex k := by
  show (k + levelShift s D - levelShift s D, fun _ : Fin 2 => (0 : ℤ))
    = (k, fun _ : Fin 2 => (0 : ℤ))
  rw [add_sub_cancel_right]

/-- The half-open origin square of the dilated grid is the `s`-dilate of the
half-open origin square of the original grid, with the level reindexing. -/
theorem halfOpenSquare_originIndex_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) :
    halfOpenSquare (dilate s hs D) (originIndex (k + levelShift s D))
      = (fun z : Plane => s⁻¹ • z) ⁻¹' halfOpenSquare D (originIndex k) := by
  ext z
  have hz : ∀ i : Fin 2, (s⁻¹ • z) i = s⁻¹ * z i := fun _ => rfl
  simp only [halfOpenSquare, Set.mem_preimage, Set.mem_ofPred_eq, hz,
    square_lower_dilate hs D (originIndex (k + levelShift s D)),
    square_upper_dilate hs D (originIndex (k + levelShift s D)), originIndex_add_sub s D k]
  constructor
  · intro h i
    exact ⟨(le_inv_mul_iff₀ hs).2 (h i).1, (inv_mul_lt_iff₀ hs).2 (h i).2⟩
  · intro h i
    exact ⟨(le_inv_mul_iff₀ hs).1 (h i).1, (inv_mul_lt_iff₀ hs).1 (h i).2⟩

/-- The side length of the dilated grid at the shifted level is `s` times the
original side length. -/
theorem side_dilate_add {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) :
    side (dilate s hs D) (k + levelShift s D) = s * side D k := by
  rw [side_dilate hs D, add_sub_cancel_right]

/-! ### Transport of the selection statistic -/

/-- The scaled variant of `ActualMarkedBlockTransport.maxCellDiameter_congr_map`:
if a relabelling identifies the two patches and multiplies every cell diameter by
`a`, then the maximal cell diameter is multiplied by `a`. -/
theorem maxCellDiameter_congr_map_mul {V W : Type*} (F : IndexedCells V) (G : IndexedCells W)
    (D E : Grid) (c t : SquareIndex) (q : V ≃ W) (a : ℝ≥0∞)
    (hpatch : ∀ v : V, Hits G (square E t).carrier (q v) ↔ Hits F (square D c).carrier v)
    (hdiam : ∀ v : V, ENNReal.ofReal (Metric.diam (G.cell (q v) : Set Plane))
      = a * ENNReal.ofReal (Metric.diam (F.cell v : Set Plane))) :
    maxCellDiameter G E t = a * maxCellDiameter F D c := by
  have hcomp : (⨆ v : patchVertices F (square D c),
        ENNReal.ofReal (Metric.diam (G.cell (q v.1) : Set Plane)))
      = ⨆ v : patchVertices G (square E t),
        ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)) :=
    Equiv.iSup_comp
      (g := fun v : patchVertices G (square E t) =>
        ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)))
      (Equiv.subtypeEquiv q fun v => (hpatch v).symm)
  show (⨆ v : patchVertices G (square E t),
      ENNReal.ofReal (Metric.diam (G.cell v.1 : Set Plane)))
    = a * ⨆ v : patchVertices F (square D c),
      ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane))
  rw [← hcomp, ENNReal.mul_iSup]
  exact iSup_congr fun v => hdiam v.1

/-- The positive similarity about the origin is the dilation `z ↦ s • z`. -/
theorem positiveSimilarity_zero_right (s : ℝ) (z : Plane) :
    positiveSimilarity s 0 z = s • z := by
  rw [positiveSimilarity_apply, sub_zero]

/-- The patch of the dilated origin square is the patch of the original origin
square, and every cell diameter is multiplied by `s`. -/
theorem maxCellDiameter_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (k : ℤ) :
    maxCellDiameter (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (originIndex (k + levelShift s D))
      = ENNReal.ofReal s * maxCellDiameter (decode e) D (originIndex k) := by
  obtain ⟨q, hcell, -⟩ := isSimilarity_similarityTargetEnv s 0 hs e
  have hpre : positiveSimilarity s 0 ⁻¹'
        (square (dilate s hs D) (originIndex (k + levelShift s D))).carrier
      = (square D (originIndex k)).carrier := by
    rw [square_carrier_dilate hs D, originIndex_add_sub s D k]
    ext z
    show s⁻¹ • positiveSimilarity s 0 z ∈ (square D (originIndex k)).carrier
      ↔ z ∈ (square D (originIndex k)).carrier
    rw [positiveSimilarity_zero_right, inv_smul_smul₀ hs.ne']
  refine maxCellDiameter_congr_map_mul (decode e) (decode (similarityTargetEnv s 0 hs e))
    D (dilate s hs D) (originIndex k) (originIndex (k + levelShift s D)) q (ENNReal.ofReal s)
    (fun v => ?_) (fun v => ?_)
  · have hH : Hits (decode (similarityTargetEnv s 0 hs e))
          (square (dilate s hs D) (originIndex (k + levelShift s D))).carrier (q v)
        ↔ Hits (transformIndexedCells s 0 hs (decode e))
          (square (dilate s hs D) (originIndex (k + levelShift s D))).carrier v := by
      unfold Hits
      rw [hcell v, transformIndexedCells_cell]
    rw [hH, hits_transformIndexedCells, hpre]
  · rw [hcell v, coe_transformCell, Spatial.diam_image_positiveSimilarity s 0 hs,
      ENNReal.ofReal_mul hs.le]

/-- The factor `s` cancels in the diameter/side ratio, so the manuscript's `b` is
invariant along the origin chain. -/
theorem inverseRatio_originIndex_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (k : ℤ) :
    inverseRatio (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (originIndex (k + levelShift s D))
      = inverseRatio (decode e) D (originIndex k) := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  show (ancestorRatio (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
      (originIndex (k + levelShift s D)))⁻¹
    = (ancestorRatio (decode e) D (originIndex k))⁻¹
  congr 1
  show (⨆ j : ℕ, maxCellDiameter (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (ancestor (dilate s hs D) (originIndex (k + levelShift s D)) j) /
      ENNReal.ofReal (side (dilate s hs D)
        (ancestor (dilate s hs D) (originIndex (k + levelShift s D)) j).1))
    = ⨆ j : ℕ, maxCellDiameter (decode e) D (ancestor D (originIndex k) j) /
      ENNReal.ofReal (side D (ancestor D (originIndex k) j).1)
  refine iSup_congr fun j => ?_
  rw [ancestor_originIndex, ancestor_originIndex, originIndex_fst, originIndex_fst,
    show k + levelShift s D + (j : ℤ) = (k + (j : ℤ)) + levelShift s D by ring,
    maxCellDiameter_dilate hs e D, side_dilate_add hs D, ENNReal.ofReal_mul hs.le,
    ENNReal.mul_div_mul_left _ _ hs0 ENNReal.ofReal_ne_top]

/-- The manuscript's `κ` is invariant along the origin chain under the joint
dilation. -/
theorem blockIndex_originIndex_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (k : ℤ) :
    blockIndex (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (originIndex (k + levelShift s D))
      = blockIndex (decode e) D (originIndex k) := by
  show (∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ *
      inverseRatio (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (ancestor (dilate s hs D) (originIndex (k + levelShift s D)) j))
    = ∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ *
      inverseRatio (decode e) D (ancestor D (originIndex k) j)
  refine tsum_congr fun j => ?_
  rw [ancestor_originIndex, ancestor_originIndex,
    show k + levelShift s D + (j : ℤ) = (k + (j : ℤ)) + levelShift s D by ring,
    inverseRatio_originIndex_dilate hs e D]

/-- The joint dilation preserves the manuscript's selection condition, with the
level reindexing. -/
theorem originSelected_dilate_iff {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (m : ℝ) (k : ℤ) :
    OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m
        (k + levelShift s D)
      ↔ OriginSelected (decode e) D m k := by
  show (0 < m ∧ blockIndex (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (originIndex (k + levelShift s D)) ≤ ENNReal.ofReal m ∧
      ENNReal.ofReal m < blockIndex (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D)
        (parent (dilate s hs D) (originIndex (k + levelShift s D))))
    ↔ (0 < m ∧ blockIndex (decode e) D (originIndex k) ≤ ENNReal.ofReal m ∧
      ENNReal.ofReal m < blockIndex (decode e) D (parent D (originIndex k)))
  rw [parent_originIndex, parent_originIndex, blockIndex_originIndex_dilate hs e D,
    show k + levelShift s D + 1 = (k + 1) + levelShift s D by ring,
    blockIndex_originIndex_dilate hs e D]

/-! ### The selected block -/

/-- Under pathwise existence and uniqueness of the selected origin square, the
selected level of the dilated configuration is the original one shifted by
`levelShift s D`. -/
theorem blockLevel_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (m : ℝ)
    (hex : ∃ l : ℤ, OriginSelected (decode e) D m l)
    (huniq : ∀ l l' : ℤ,
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l →
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l' → l = l') :
    blockLevel (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m
      = blockLevel (decode e) D m + levelShift s D := by
  have hsel : OriginSelected (decode e) D m (blockLevel (decode e) D m) :=
    originSelected_blockLevel hex
  have hsel' : OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m
      (blockLevel (decode e) D m + levelShift s D) :=
    (originSelected_dilate_iff hs e D m _).2 hsel
  exact huniq _ _ (originSelected_blockLevel ⟨_, hsel'⟩) hsel'

/-- **Scale covariance of the selected block.**  The selected origin block of the
dilated configuration is the `s`-dilate of the original selected block. -/
theorem blockSet_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (m : ℝ)
    (hex : ∃ l : ℤ, OriginSelected (decode e) D m l)
    (huniq : ∀ l l' : ℤ,
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l →
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l' → l = l') :
    blockSet (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m
      = (fun z : Plane => s⁻¹ • z) ⁻¹' blockSet (decode e) D m := by
  show halfOpenSquare (dilate s hs D)
      (originIndex (blockLevel (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m))
    = (fun z : Plane => s⁻¹ • z) ⁻¹'
      halfOpenSquare D (originIndex (blockLevel (decode e) D m))
  rw [blockLevel_dilate hs e D m hex huniq, halfOpenSquare_originIndex_dilate hs D]

/-- **Scale covariance of the selected side length.**  The side length of the
selected block of the dilated configuration is `s` times the original one. -/
theorem blockSide_dilate {s : ℝ} (hs : 0 < s) (e : Env) (D : Grid) (m : ℝ)
    (hex : ∃ l : ℤ, OriginSelected (decode e) D m l)
    (huniq : ∀ l l' : ℤ,
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l →
      OriginSelected (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m l' → l = l') :
    blockSide (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m
      = s * blockSide (decode e) D m := by
  show side (dilate s hs D) (blockLevel (decode (similarityTargetEnv s 0 hs e)) (dilate s hs D) m)
    = s * side D (blockLevel (decode e) D m)
  rw [blockLevel_dilate hs e D m hex huniq, side_dilate_add hs D]

end ReflectedGMS.DilatedSelectedBlocks
