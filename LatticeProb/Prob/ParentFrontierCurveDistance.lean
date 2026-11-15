import LatticeProb.Prob.ParentFrontierProkhorov
import LatticeProb.Prob.DyadicCellConfig

/-! # Frontier distances and normalized curve laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set BouRabeeGwynne ReflectedGMS.GMS

namespace LatticeProb

/-- If spatially normalized frontier laws are endpoint laws of normalized curves,
their frontier distance is bounded by the distance of the curve laws. -/
theorem levyProkhorovEDist_parentFrontier_le_curve
    (μ ν : Measure ℂ) (κ τ : Measure (CurveSpace 2)) (c : ℂ) {a : ℝ}
    (ha : 0 < a)
    (hμ : ∀ᵐ z ∂μ, z ∈ frontier (ParentBlock.parentBlock c a))
    (hν : ∀ᵐ z ∂ν, z ∈ frontier (ParentBlock.parentBlock c a))
    (hκ : μ.map (fun z : ℂ => (z - c) / (a : ℂ)) =
      (κ.map CurveSpace.endPoint).map Complex.orthonormalBasisOneI.repr.symm)
    (hτ : ν.map (fun z : ℂ => (z - c) / (a : ℂ)) =
      (τ.map CurveSpace.endPoint).map Complex.orthonormalBasisOneI.repr.symm) :
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : S → MetricPlane))
        ((ν.map MetricPlane.up).comap ((↑) : S → MetricPlane)) ≤
      levyProkhorovEDist κ τ := by
  dsimp only
  rw [levyProkhorovEDist_parentFrontier μ ν c ha hμ hν, hκ, hτ]
  exact (levyProkhorovEDist_map_le_of_lipschitz_one
    Complex.orthonormalBasisOneI.repr.symm.isometry.lipschitzWith
    Complex.orthonormalBasisOneI.repr.symm.continuous.measurable _ _).trans
      (levyProkhorovEDist_map_endPoint_le κ τ)

end LatticeProb
end
