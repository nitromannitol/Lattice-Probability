import LatticeProb.Euclidean.ParentBlockExitGeometry
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicNearClosureBrownianExit

/-! # Brownian exit law on a parent-block frontier -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne

namespace LatticeProb.ParentBlock

/-- The complex-coordinate endpoint of Brownian motion stopped on leaving the
interior of a parent block lies on the block's frontier almost surely. -/
theorem stoppedBrownianLaw_endPoint_complex_ae_mem_frontier
    (c : ℂ) {s : ℝ} (hs : 0 ≤ s)
    (z : Euc 2) (hz : Complex.orthonormalBasisOneI.repr.symm z ∈
      interior (parentBlock c s))
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) :
    ∀ᵐ w ∂(((stoppedBrownianLaw
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock c s)) z ρ).map
        CurveSpace.endPoint).map Complex.orthonormalBasisOneI.repr.symm),
      w ∈ frontier (parentBlock c s) := by
  let f := Complex.orthonormalBasisOneI.repr.symm
  let U : Set (Euc 2) := f ⁻¹' interior (parentBlock c s)
  have hU : IsOpen U := isOpen_interior.preimage f.continuous
  have hUb : Bornology.IsBounded U :=
    (isCompact_parentBlock_preimage c hs).isBounded.subset
      (preimage_mono interior_subset)
  have hfront := standardBrownianLaw_stopped_endPoint_ae_mem_frontier
    (by norm_num : 1 ≤ 2) hρ hU hUb hz
  apply (ae_map_iff f.continuous.measurable.aemeasurable
    isClosed_frontier.measurableSet).2
  filter_upwards [hfront] with y hy
  have heq : f ⁻¹' frontier (interior (parentBlock c s)) = frontier U :=
    f.toHomeomorph.preimage_frontier _
  have hy' : y ∈ f ⁻¹' frontier (interior (parentBlock c s)) := by
    rw [heq]
    exact hy
  exact frontier_interior_subset hy'

end LatticeProb.ParentBlock
