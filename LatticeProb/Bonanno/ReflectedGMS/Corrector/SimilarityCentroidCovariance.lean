/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SimilarityCentroidCovariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Similarity covariance of the cell centroid

`StatementIngredients.cellCentroid F v = (cellArea F v)⁻¹ • ∫_{H_v} z dz` is the anchor of the
whole block-interpolation specification: `DyadicApproximation.IsBlockInterpolation F D 0 f` says
`f = cellCentroid F`, the skeleton clause pins `f` to the centroid on `skeleton F D m`, and
`CentroidTraceMinimizer` prescribes the centroid as the boundary trace.  Consequently *every*
route to `HarmonicCoordinateAssembly.ApproximantGradientCovariant` needs

> the centroid of a similarity image is the similarity image of the centroid.

Before this module `cellCentroid` had **no** lemma at all beyond its definition — searched across
`ReflectedGMS/`, `2405_11673_main/BouRabeeGwynne/` and `2506_18827_reflected/`, with no hit for
`cellCentroid` next to any of `transform`, `similarity`, `dilate`, `translate`, `smul`.

## What is proved

* `map_positiveSimilarity_volume` — the push-forward of Lebesgue area under `z ↦ s • (z - u)`
  is `(s²)⁻¹ • volume`.  This is the measure-level form of the checked area identity
  `Spatial.volume_image_positiveSimilarity`, which alone does not move integrals.
* `setIntegral_image_positiveSimilarity` — the vector-valued change of variables
  `∫_{S(A)} z dz = s² • ∫_A S(w) dw`.
* `setIntegral_positiveSimilarity` — the affine expansion `∫_A S(w) dw = s • (∫_A w dw - |A| • u)`.
* `cellCentroid_eq_of_cell_eq` — **the covariance**, in the form in which
  `EnvironmentLaws.IsSimilarityRelabel` supplies it: if one cell of `G` is the `transformCell`
  image of one cell of `F`, then its centroid is the `positiveSimilarity` image of that centroid.
* `cellCentroid_transformIndexedCells` and `cellCentroid_similarityRelabel` — the two consumer
  shapes, for the label-preserving action and for a physical similarity of environments.

Positivity of the source cell's area is genuinely needed and is not a technicality: at zero area
`cellCentroid` is `0` on both sides while `positiveSimilarity s u 0 = -s • u ≠ 0`.  It is supplied
by the `Geometry` clause "every cell has nonempty interior" through `cellVolume_pos_lt_top`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SimilarityCentroidCovariance

open StatementIngredients EnvironmentLaws Code

/-! ### The similarity as a measurable equivalence -/

theorem measurable_positiveSimilarity (s : ℝ) (u : Plane) :
    Measurable (positiveSimilarity s u) := by
  unfold positiveSimilarity
  fun_prop

theorem positiveSimilarity_injective {s : ℝ} (hs : 0 < s) (u : Plane) :
    Function.Injective (positiveSimilarity s u) :=
  (positiveSimilarityHomeomorph s u hs).injective

/-- The image of a set under a positive similarity is the preimage under the inverse
similarity. -/
theorem image_positiveSimilarity_eq_preimage {s : ℝ} (hs : 0 < s) (u : Plane) (A : Set Plane) :
    positiveSimilarity s u '' A = positiveSimilarity s⁻¹ (-s • u) ⁻¹' A := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := positiveSimilarity_inverse_left s u w hs
    exact Set.mem_preimage.2 (by rw [h]; exact hw)
  · intro hz
    exact ⟨positiveSimilarity s⁻¹ (-s • u) z, hz, positiveSimilarity_inverse_right s u z hs⟩

theorem measurableSet_image_positiveSimilarity {s : ℝ} (hs : 0 < s) (u : Plane)
    {A : Set Plane} (hA : MeasurableSet A) :
    MeasurableSet (positiveSimilarity s u '' A) := by
  rw [image_positiveSimilarity_eq_preimage hs u A]
  exact measurable_positiveSimilarity s⁻¹ (-s • u) hA

/-! ### The push-forward of Lebesgue area -/

/-- **The measure-level change of variables.**  A positive similarity pushes Lebesgue area
forward to `(s²)⁻¹` times Lebesgue area. -/
theorem map_positiveSimilarity_volume {s : ℝ} (hs : 0 < s) (u : Plane) :
    Measure.map (positiveSimilarity s u) (volume : Measure Plane)
      = ENNReal.ofReal ((s ^ 2)⁻¹) • (volume : Measure Plane) := by
  have hfun : positiveSimilarity s u
      = (fun y : Plane => s • y) ∘ (fun z : Plane => z - u) := by
    funext z
    rfl
  have hsub : Measure.map (fun z : Plane => z - u) (volume : Measure Plane) = volume :=
    (measurePreserving_sub_right (volume : Measure Plane) u).map_eq
  have hsmulm : Measurable fun y : Plane => s • y := measurable_const_smul s
  have hsubm : Measurable fun z : Plane => z - u := measurable_id.sub_const u
  have habs : |((s ^ 2)⁻¹ : ℝ)| = (s ^ 2)⁻¹ := abs_of_nonneg (by positivity)
  rw [hfun, ← Measure.map_map hsmulm hsubm, hsub,
    Measure.map_addHaar_smul (volume : Measure Plane) hs.ne', finrank_euclideanSpace_fin, habs]

/-! ### The vector-valued change of variables -/

/-- **The vector change of variables.**  `∫_{S(A)} z dz = s² • ∫_A S(w) dw`. -/
theorem setIntegral_image_positiveSimilarity {s : ℝ} (hs : 0 < s) (u : Plane)
    {A : Set Plane} (hA : MeasurableSet A) :
    (∫ z in positiveSimilarity s u '' A, z ∂volume)
      = (s ^ 2) • ∫ w in A, positiveSimilarity s u w ∂volume := by
  have hTm : Measurable (positiveSimilarity s u) := measurable_positiveSimilarity s u
  have himg : MeasurableSet (positiveSimilarity s u '' A) :=
    measurableSet_image_positiveSimilarity hs u hA
  have hg : Measurable
      ((positiveSimilarity s u '' A).indicator (fun z : Plane => z)) :=
    measurable_id.indicator himg
  have hmap : (∫ z, (positiveSimilarity s u '' A).indicator (fun z : Plane => z) z
        ∂(Measure.map (positiveSimilarity s u) volume))
      = ∫ w, (positiveSimilarity s u '' A).indicator (fun z : Plane => z)
          (positiveSimilarity s u w) ∂volume :=
    integral_map hTm.aemeasurable hg.aestronglyMeasurable
  have hcomp : (fun w : Plane =>
        (positiveSimilarity s u '' A).indicator (fun z : Plane => z) (positiveSimilarity s u w))
      = A.indicator (fun w : Plane => positiveSimilarity s u w) := by
    funext w
    by_cases hw : w ∈ A
    · have hmem : positiveSimilarity s u w ∈ positiveSimilarity s u '' A := ⟨w, hw, rfl⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hw]
    · have hmem : positiveSimilarity s u w ∉ positiveSimilarity s u '' A := by
        rintro ⟨y, hy, hyw⟩
        exact hw (by rwa [positiveSimilarity_injective hs u hyw] at hy)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hw]
  have hscal : (∫ z, (positiveSimilarity s u '' A).indicator (fun z : Plane => z) z
        ∂(Measure.map (positiveSimilarity s u) volume))
      = ((s ^ 2)⁻¹ : ℝ) • ∫ z in positiveSimilarity s u '' A, z ∂volume := by
    rw [map_positiveSimilarity_volume hs u, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), integral_indicator himg]
  rw [hcomp, integral_indicator hA] at hmap
  rw [hscal] at hmap
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← hmap, smul_smul, mul_inv_cancel₀ hs2, one_smul]

/-- The affine expansion of the similarity integral. -/
theorem setIntegral_positiveSimilarity (s : ℝ) (u : Plane) {A : Set Plane}
    (hfin : volume A ≠ ∞)
    (hint : IntegrableOn (fun w : Plane => w) A volume) :
    (∫ w in A, positiveSimilarity s u w ∂volume)
      = s • ((∫ w in A, w ∂volume) - (volume A).toReal • u) := by
  have hfinm : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hconst : IntegrableOn (fun _ : Plane => s • u) A volume := by
    haveI := hfinm
    exact integrable_const _
  have hintS : IntegrableOn (fun w : Plane => s • w) A volume := hint.smul s
  have hsplit : (fun w : Plane => positiveSimilarity s u w)
      = fun w : Plane => s • w - s • u := by
    funext w
    show s • (w - u) = s • w - s • u
    rw [smul_sub]
  have hrhs : s • ((∫ w in A, w ∂volume) - (volume A).toReal • u)
      = s • (∫ w in A, w ∂volume) - (volume A).toReal • (s • u) := by
    rw [smul_sub, smul_comm]
  rw [hsplit, integral_sub hintS hconst, integral_smul, setIntegral_const, measureReal_def, hrhs]

/-! ### Covariance of the centroid -/

/-- **The centroid of a similarity image is the similarity image of the centroid.**  Stated in
the shape supplied by `EnvironmentLaws.IsSimilarityRelabel`: a single cell equation. -/
theorem cellCentroid_eq_of_cell_eq {V W : Type*} (F : IndexedCells V) (G : IndexedCells W)
    {s : ℝ} {u : Plane} (hs : 0 < s) (v : V) (w : W)
    (hcell : G.cell w = transformCell s u hs (F.cell v))
    (hpos : 0 < volume (F.cell v : Set Plane)) :
    cellCentroid G w = positiveSimilarity s u (cellCentroid F v) := by
  have hKmeas : MeasurableSet (F.cell v : Set Plane) :=
    (F.cell v).isCompact.isClosed.measurableSet
  have hKfin : volume (F.cell v : Set Plane) ≠ ∞ := (F.cell v).isCompact.measure_lt_top.ne
  have hKint : IntegrableOn (fun z : Plane => z) (F.cell v : Set Plane) volume :=
    (continuous_id.continuousOn).integrableOn_compact (F.cell v).isCompact
  have hGcell : (G.cell w : Set Plane) = positiveSimilarity s u '' (F.cell v : Set Plane) := by
    rw [hcell, coe_transformCell]
  have harea : cellArea G w = s ^ 2 * cellArea F v := by
    unfold cellArea
    rw [hGcell, Spatial.volume_image_positiveSimilarity s u (F.cell v : Set Plane),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hapos : (0 : ℝ) < cellArea F v := by
    unfold cellArea
    exact ENNReal.toReal_pos hpos.ne' hKfin
  have hane : (cellArea F v) ≠ 0 := hapos.ne'
  have hsne : (s : ℝ) ≠ 0 := hs.ne'
  have hI : (∫ z in (G.cell w : Set Plane), z ∂volume)
      = (s ^ 2 : ℝ) • (s • ((∫ z in (F.cell v : Set Plane), z ∂volume)
          - (cellArea F v) • u)) := by
    rw [hGcell, setIntegral_image_positiveSimilarity hs u hKmeas,
      setIntegral_positiveSimilarity s u hKfin hKint]
    rfl
  have hc1 : (s ^ 2 * cellArea F v)⁻¹ * s ^ 2 * s = s * (cellArea F v)⁻¹ := by
    field_simp
  have hc2 : s * (cellArea F v)⁻¹ * cellArea F v = s := by
    field_simp
  show (cellArea G w)⁻¹ • (∫ z in (G.cell w : Set Plane), z ∂volume)
      = s • ((cellArea F v)⁻¹ • (∫ z in (F.cell v : Set Plane), z ∂volume) - u)
  rw [harea, hI, smul_smul, smul_smul, smul_sub, smul_sub, smul_smul, smul_smul, hc1, hc2]

/-- **The consumer form.**  Along a physical similarity of environments the centroids transform
by the similarity. -/
theorem cellCentroid_similarityRelabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    [Countable (Vertex e.val)] {relabel : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' relabel) (hF : Geometry (decode e)) (v : Vertex e.val) :
    cellCentroid (decode e') (relabel v) = positiveSimilarity s u (cellCentroid (decode e) v) :=
  cellCentroid_eq_of_cell_eq (decode e) (decode e') hs v (relabel v) (h.1 v)
    (cellVolume_pos_lt_top (decode e) hF v).1

end ReflectedGMS.SimilarityCentroidCovariance
