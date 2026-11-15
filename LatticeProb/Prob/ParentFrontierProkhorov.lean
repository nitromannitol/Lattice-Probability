import LatticeProb.Prob.LevyProkhorovIsometricEmbedding
import LatticeProb.Prob.ScaledProkhorovNormalization
import LatticeProb.Euclidean.ParentBlock

/-!
# Prokhorov distance on a parent-square frontier

The inherited inverse-side-scaled metric on the frontier gives the same
Prokhorov edistance as spatially normalized ambient measures.
-/

open MeasureTheory Set

namespace LatticeProb

/-- On the frontier of a parent block, inverse-side-scaled Prokhorov edistance
is the usual edistance of the spatially normalized supported measures. -/
theorem levyProkhorovEDist_parentFrontier (μ ν : Measure ℂ) (c : ℂ) {a : ℝ}
    (ha : 0 < a)
    (hμ : ∀ᵐ z ∂μ, z ∈ frontier (ParentBlock.parentBlock c a))
    (hν : ∀ᵐ z ∂ν, z ∈ frontier (ParentBlock.parentBlock c a)) :
    letI : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
    let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
    levyProkhorovEDist ((μ.map MetricPlane.up).comap ((↑) : S → MetricPlane))
        ((ν.map MetricPlane.up).comap ((↑) : S → MetricPlane)) =
      levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / (a : ℂ)))
        (ν.map (fun z : ℂ => (z - c) / (a : ℂ))) := by
  let f : MetricPlane → ℂ := fun z => (z.down - c) / (a : ℂ)
  have hdown : Measurable MetricPlane.down := comap_measurable _
  have hup : Measurable MetricPlane.up := by
    rw [measurable_comap_iff]
    exact measurable_id
  have hf : Measurable f := (hdown.sub measurable_const).div measurable_const
  let : MetricSpace MetricPlane := normalizedPlaneMetric c a ha.ne'
  let : OpensMeasurableSpace MetricPlane := opensMeasurableSpace_iff_forall_measurableSet.mpr <| by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.mp hs
    exact ht.measurableSet.preimage hf
  let S : Set MetricPlane := MetricPlane.down ⁻¹' frontier (ParentBlock.parentBlock c a)
  have hS : MeasurableSet S := isClosed_frontier.measurableSet.preimage hdown
  have hm : ∀ᵐ z ∂μ.map MetricPlane.up, z ∈ S := by
    apply (ae_map_iff hup.aemeasurable hS).2
    exact hμ
  have hn : ∀ᵐ z ∂ν.map MetricPlane.up, z ∈ S := by
    apply (ae_map_iff hup.aemeasurable hS).2
    exact hν
  exact (levyProkhorovEDist_comap_subtype_eq hS _ _ hm hn).trans
    (levyProkhorovEDist_normalizedPlaneMetric μ ν c ha)

end LatticeProb
