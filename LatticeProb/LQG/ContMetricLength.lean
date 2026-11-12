import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.LQG.LengthMetric

/-! # Continuous length metrics are Euclidean length metrics

A continuous metric `d` on `ℂ` whose small balls are Euclidean-small (`LQGMetric.ContMetric`) gives
the function `D u v = d (u, v)`. The `D`-length of a curve (`curveLength`, a supremum over finite
monotone families of parameters) is the variation of the curve in the metric space `(ℂ, d)`; the
internal metric `D(z, w; U)` (`internalMetric`, an infimum over Euclidean-continuous paths in `U`) is
the internal metric of `U` in `(ℂ, d)`, since `d` and the Euclidean metric induce the same topology.
Hence, if `(ℂ, d)` is a length space, `D` is a Euclidean length metric (`IsEuclideanLengthMetric`):
this is Axiom I of the LQG metric (Gwynne-Miller 2021, Section 1.2) in the form of the pairing
functional formulation. -/

noncomputable section
open Set
open scoped ENNReal

namespace LatticeProb.LQG

variable (d : LQGMetric.ContMetric)

/-- The `D`-length of a curve is its variation in the metric space `(ℂ, d)`. -/
theorem curveLength_contMetric (p : ℝ → ℂ) (a b : ℝ) :
    curveLength (fun u v => d.1 (u, v)) p a b =
      LQGMetric.MetricGeometry.curveLength (d.pt ∘ p) a b := by
  simp only [curveLength, LQGMetric.MetricGeometry.curveLength, eVariationOn, Function.comp_apply,
    edist_dist]
  rfl

/-- The `D`-length of a Euclidean-continuous path is the length of the same path in `(ℂ, d)`. -/
theorem pathLength_contMetric {z w : ℂ} (P : Path z w) :
    pathLength (fun u v => d.1 (u, v)) P =
      LQGMetric.MetricGeometry.pathLength (P.map d.continuous_pt) := by
  rw [pathLength, LQGMetric.MetricGeometry.pathLength, curveLength_contMetric]
  congr 1

/-- The internal metric of `D` in a set `U` is the internal metric of `U` in `(ℂ, d)`. -/
theorem internalMetric_contMetric (U : Set ℂ) (z w : ℂ) :
    internalMetric (fun u v => d.1 (u, v)) U z w = d.internal U z w := by
  apply le_antisymm
  · refine le_iInf fun γ => ?_
    let P : Path z w := γ.1.map d.continuous_unpt
    have hP : ∀ t, P t ∈ U := fun t => d.mem_image_pt.1 (γ.2 t)
    refine (iInf₂_le P hP).trans_eq ?_
    rw [pathLength_contMetric]
    rfl
  · refine le_iInf₂ fun P hP => ?_
    refine (iInf_le _ ⟨P.map d.continuous_pt, fun t => ⟨P t, hP t, rfl⟩⟩).trans_eq ?_
    rw [pathLength_contMetric]

/-- If `(ℂ, d)` is a length space, then `D u v = d (u, v)` is a Euclidean length metric. -/
theorem isEuclideanLengthMetric_of_isLength (hd : d.IsLength) :
    IsEuclideanLengthMetric (fun u v => d.1 (u, v)) where
  self_eq_zero z := d.2.self_eq_zero z
  eq_of_eq_zero z w h := d.2.eq_of_eq_zero z w h
  symm z w := d.2.symm z w
  triangle x y z := d.2.triangle x y z
  isOpen_iff U := by
    rw [← d.ptHomeomorph.isOpen_image, Metric.isOpen_iff]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, hball⟩ := h (d.pt z) ⟨z, hz, rfl⟩
      refine ⟨ε, hε, fun w hw => ?_⟩
      have hmem : d.pt w ∈ Metric.ball (d.pt z) ε := by
        rw [Metric.mem_ball, LQGMetric.ContMetric.dist_pt, d.2.symm]
        exact hw
      obtain ⟨w', hw', hww'⟩ := hball hmem
      exact (show w' = w from hww') ▸ hw'
    · rintro h _ ⟨z, hz, rfl⟩
      obtain ⟨ε, hε, hw⟩ := h z hz
      refine ⟨ε, hε, fun y hy => ⟨d.unpt y, hw (d.unpt y) ?_, rfl⟩⟩
      rw [Metric.mem_ball] at hy
      rw [d.2.symm]
      exact hy
  ofReal_eq_internalMetric z w := by
    rw [internalMetric_contMetric, LQGMetric.ContMetric.internal,
      show d.pt '' univ = univ from image_univ_of_surjective (fun y => ⟨y, rfl⟩),
      LQGMetric.MetricGeometry.internalEDist_univ_of_isLengthSpace hd, edist_dist]
    rfl

end LatticeProb.LQG
