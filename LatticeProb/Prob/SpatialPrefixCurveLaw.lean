import LatticeProb.Topology.LipschitzCurveMap
import LatticeProb.Topology.CurveSpaceComparison
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import LatticeProb.Prob.NormalizedPrefixCurve
import LatticeProb.Prob.LevyProkhorovLipschitz
import LatticeProb.Prob.LevyProkhorovIsometricEmbedding

/-! # Spatial transformations of finite-prefix curve laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- Forming a normalized path prefix commutes with spatial composition. -/
theorem normalizedPathPrefix_comp {E G : Type*} [TopologicalSpace E] [TopologicalSpace G]
    (F : C(E, G)) (w : C(ℝ≥0, E)) (T : ℝ≥0) :
    normalizedPathPrefix (F.comp w) T = F.comp (normalizedPathPrefix w T) := by
  ext u
  rfl

/-- A spatial map commutes with taking the class of a finite path prefix. -/
theorem normalizedPrefixCurve_comp {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F)
    (w : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T : ℝ≥0) :
    normalizedPrefixCurve (F.comp w) T =
      CurveSpace.spatialMap F hF (normalizedPrefixCurve w T) := by
  change CurveSpace.project (normalizedPathPrefix (F.comp w) T) =
    CurveSpace.spatialMap F hF (CurveSpace.project (normalizedPathPrefix w T))
  rw [normalizedPathPrefix_comp, CurveSpace.spatialMap_project]

/-- The transformed finite-prefix law is the image of the original curve law. -/
theorem map_spatial_normalizedPrefixCurve {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F)
    (μ : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    μ.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal) =
      (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)).map
        (CurveSpace.spatialMap F hF) := by
  rw [Measure.map_map (CurveSpace.spatialMap_lipschitz F hF).continuous.measurable
    measurable_normalizedPrefixCurve_toNNReal]
  congr 1

/-- Spatial transformation of both path laws changes their curve-law distance by
at most the larger of one and the spatial Lipschitz constant. -/
theorem levyProkhorovEDist_spatial_normalizedPrefixCurve_le {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F)
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal))
      (ν.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal)) ≤
      ((max 1 K : ℝ≥0) : ℝ≥0∞) * levyProkhorovEDist
        (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))
        (ν.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal)) := by
  rw [map_spatial_normalizedPrefixCurve F hF μ, map_spatial_normalizedPrefixCurve F hF ν]
  exact levyProkhorovEDist_map_le_of_lipschitz (le_max_left 1 K)
    ((CurveSpace.spatialMap_lipschitz F hF).weaken (le_max_right 1 K))
    (CurveSpace.spatialMap_lipschitz F hF).continuous.measurable _ _


/-- The same estimate holds on the isometric source presentation of curves. -/
theorem levyProkhorovEDist_source_spatial_normalizedPrefixCurve_le {d e : ℕ}
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin e)))
    {K : ℝ≥0} (hF : LipschitzWith K F)
    (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (fun p => CurveSpaceComparison.isometryEquiv e
        (normalizedPrefixCurve (F.comp p.1) p.2.toNNReal)))
      (ν.map (fun p => CurveSpaceComparison.isometryEquiv e
        (normalizedPrefixCurve (F.comp p.1) p.2.toNNReal))) ≤
      ((max 1 K : ℝ≥0) : ℝ≥0∞) * levyProkhorovEDist
        (μ.map (fun p => CurveSpaceComparison.isometryEquiv d
          (normalizedPrefixCurve p.1 p.2.toNNReal)))
        (ν.map (fun p => CurveSpaceComparison.isometryEquiv d
          (normalizedPrefixCurve p.1 p.2.toNNReal))) := by
  let ed := CurveSpaceComparison.isometryEquiv d
  let ee := CurveSpaceComparison.isometryEquiv e
  have hed : MeasurableEmbedding ed := ed.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hee : MeasurableEmbedding ee := ee.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpath : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      (F.comp p.1, p.2)) :=
    ((ContinuousMap.continuous_postcomp F).measurable.comp measurable_fst).prodMk measurable_snd
  have hpre : Measurable (fun p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0∞ =>
      normalizedPrefixCurve (F.comp p.1) p.2.toNNReal) :=
    measurable_normalizedPrefixCurve_toNNReal.comp hpath
  have hs := levyProkhorovEDist_map_eq_of_isometry ee.isometry hee
    (μ.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal))
    (ν.map (fun p => normalizedPrefixCurve (F.comp p.1) p.2.toNNReal))
  have ht := levyProkhorovEDist_map_eq_of_isometry ed.isometry hed
    (μ.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))
    (ν.map (fun p => normalizedPrefixCurve p.1 p.2.toNNReal))
  rw [Measure.map_map hee.measurable hpre, Measure.map_map hee.measurable hpre] at hs
  rw [Measure.map_map hed.measurable measurable_normalizedPrefixCurve_toNNReal,
    Measure.map_map hed.measurable measurable_normalizedPrefixCurve_toNNReal] at ht
  exact hs.trans_le ((levyProkhorovEDist_spatial_normalizedPrefixCurve_le F hF μ ν).trans_eq
    (congrArg (((max 1 K : ℝ≥0) : ℝ≥0∞) * ·) ht.symm))

end LatticeProb
