import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.GraphMeasurability
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBRescale

/-! # Measurable edge codes on shifted time grids -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic

namespace LatticeProb

/-- The boundary-length path viewed on a shifted time grid. -/
def shiftedMeshPath (w : MatedCRT.Path2) (ε θ : ℝ) : MatedCRT.Path2 where
  toFun t := w (ε * (t + θ))
  continuous_toFun := w.continuous.comp (by fun_prop)

@[simp] theorem shiftedMeshPath_apply (w : MatedCRT.Path2) (ε θ t : ℝ) :
    shiftedMeshPath w ε θ t = w (ε * (t + θ)) := rfl

/-- The shifted mesh path depends continuously on its path and grid parameters. -/
theorem continuous_shiftedMeshPath :
    Continuous (fun p : MatedCRT.Path2 × ℝ × ℝ => shiftedMeshPath p.1 p.2.1 p.2.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have ht : Continuous (fun p : (MatedCRT.Path2 × ℝ × ℝ) × ℝ =>
      p.1.2.1 * (p.2 + p.1.2.2)) := by fun_prop
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk ht)

/-- The side-labelled edge code on the shifted grid. -/
def shiftedMeshEdgeCode (w : MatedCRT.Path2) (ε θ : ℝ) : ℤ × ℤ × Bool → Bool :=
  MatedCRT.edgePredicate 1 (shiftedMeshPath w ε θ)

/-- Edge codes, including the labels of parallel edges, are jointly measurable. -/
theorem measurable_shiftedMeshEdgeCode :
    Measurable (fun p : MatedCRT.Path2 × ℝ × ℝ => shiftedMeshEdgeCode p.1 p.2.1 p.2.2) :=
  (MatedCRT.matedCRT_edgePredicate_measurable_holds 1).comp continuous_shiftedMeshPath.measurable

/-- The unshifted code is the ordinary positive-mesh edge code. -/
theorem shiftedMeshEdgeCode_zero_shift {ε : ℝ} (hε : 0 < ε) (w : MatedCRT.Path2) :
    shiftedMeshEdgeCode w ε 0 = MatedCRT.edgePredicate ε w := by
  have hp : shiftedMeshPath w ε 0 = GMSMain.EpsB.rescalePath ε w := by
    apply ContinuousMap.ext
    intro t
    simp only [shiftedMeshPath_apply, GMSMain.EpsB.rescalePath_apply, add_zero]
  unfold shiftedMeshEdgeCode
  rw [hp]
  funext e
  unfold MatedCRT.edgePredicate
  rw [GMSMain.EpsB.isEdge_rescale hε 1 w]
  simp

/-- Infima on a unit interval of the shifted path are infima on the corresponding shifted grid interval. -/
theorem intervalInf_shiftedMesh {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (X : ℝ → ℝ) (a b : ℝ) :
    MatedCRT.intervalInf (fun t => X (ε * (t + θ))) a b =
      MatedCRT.intervalInf X (ε * (a + θ)) (ε * (b + θ)) := by
  unfold MatedCRT.intervalInf
  rw [show (fun t => X (ε * (t + θ))) = X ∘ (fun s => ε * s) ∘ (fun t => t + θ) from rfl,
    Set.image_comp, Set.image_comp, Set.image_add_const_Icc, Set.image_mul_left_Icc' hε]

/-- The two side-labelled edge tests use the exact shifted grid intervals. -/
theorem sideCond_shiftedMesh {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (X : ℝ → ℝ) (x y : ℤ) :
    MatedCRT.SideCond 1 (fun t => X (ε * (t + θ))) x y ↔
      max (MatedCRT.intervalInf X (ε * ((x : ℝ) - 1 + θ)) (ε * ((x : ℝ) + θ)))
          (MatedCRT.intervalInf X (ε * ((y : ℝ) - 1 + θ)) (ε * ((y : ℝ) + θ))) ≤
        MatedCRT.intervalInf X (ε * ((x : ℝ) + θ)) (ε * ((y : ℝ) - 1 + θ)) := by
  simp only [MatedCRT.SideCond, one_mul, intervalInf_shiftedMesh hε]

end LatticeProb
