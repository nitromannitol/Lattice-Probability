/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedExcursionRange at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   local import paths are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.TilingClockedExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.Section4BallHarmonicMeasure

/-! The actual clocked walk excursion stays in any closed convex set containing
all embedded vertices of the finite network. The clocked law pushes forward to
the previously defined walk excursion law along the normalized curve, so the
convex-range statement transfers from the latter. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal

namespace BouRabeeGwynne
namespace FiniteConductanceNetwork

variable {d : ℕ} {V : Type*} [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

lemma clockedWalkExcursionKernel_ae_mem_convex (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (hclosed : IsClosed S)
    (hvertices : ∀ w, pos w ∈ S) :
    ∀ᵐ e ∂N.clockedWalkExcursionKernel pos B hB v,
      ∀ t, ClockedWalkExcursion.curve e t ∈ S := by
  have h := N.walkExcursionKernel_ae_mem_convex pos B hB v hS hclosed hvertices
  rw [← N.clockedWalkExcursionKernel_curve pos B hB v] at h
  exact ae_of_ae_map ClockedWalkExcursion.measurable_curve.aemeasurable h

end FiniteConductanceNetwork
namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) {W : Set (Euc d)} {c : Euc d} {r : ℝ}
  [Fintype (T.closedVertices W)]
  [MeasurableSpace (T.closedVertices W)] [MeasurableSingletonClass (T.closedVertices W)]
  [Fintype (T.closedVertices (ball c r))]
  [MeasurableSpace (T.closedVertices (ball c r))]
  [MeasurableSingletonClass (T.closedVertices (ball c r))]

theorem ambient_clockedExcursion_ae_mem_enlarged_ball (hBW : ball c r ⊆ W)
    (hmesh : T.mesh ≠ ∞)
    (hR : ∀ v ∈ T.finiteInterior (ball c r),
      0 < (T.finiteNetwork (T.closedVertices (ball c r))).totalConductance v)
    (hB : ∀ v ∈ {v : T.closedVertices W | T.pos v ∈ ball c r},
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (v : T.closedVertices W) (hv : T.pos v ∈ ball c r) :
    ∀ᵐ e ∂(T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel
      (fun w => T.pos w) {w | T.pos w ∈ ball c r} hB v,
      ∀ t, ClockedWalkExcursion.curve e t ∈ closedBall c (r + 2 * T.mesh.toReal) := by
  let vR : T.closedVertices (ball c r) := ⟨v.val, Or.inl hv⟩
  have hRS := T.closedVertices_mono hBW
  have heq := T.finiteNetwork_clockedExcursion_inclusion hRS
    (T.interiorVertices (ball c r))
    (fun w hw _ hwa => T.neighbor_mem_closedVertices hw hwa) hR hB vR
  have hvR : T.regionInclusion hRS vR = v := Subtype.ext rfl
  rw [hvR] at heq
  change (T.finiteNetwork (T.closedVertices (ball c r))).clockedWalkExcursionKernel
      (fun w => T.pos w) (T.finiteInterior (ball c r)) hR vR =
    (T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel
      (fun w => T.pos w) {w | T.pos w ∈ ball c r} hB v at heq
  rw [← heq]
  exact (T.finiteNetwork (T.closedVertices (ball c r))).clockedWalkExcursionKernel_ae_mem_convex
    (fun w => T.pos w) (T.finiteInterior (ball c r)) hR vR
    (convex_closedBall _ _) isClosed_closedBall
    (fun w => T.closedVertices_pos_mem_enlarged_ball hmesh w.property)

theorem ambient_clockedExcursion_ae_oscillation (hBW : ball c r ⊆ W)
    (hmesh : T.mesh ≠ ∞)
    (hR : ∀ v ∈ T.finiteInterior (ball c r),
      0 < (T.finiteNetwork (T.closedVertices (ball c r))).totalConductance v)
    (hB : ∀ v ∈ {v : T.closedVertices W | T.pos v ∈ ball c r},
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (v : T.closedVertices W) (hv : T.pos v ∈ ball c r) :
    ∀ᵐ e ∂(T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel
      (fun w => T.pos w) {w | T.pos w ∈ ball c r} hB v,
      ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + 2 * T.mesh.toReal) := by
  filter_upwards [T.ambient_clockedExcursion_ae_mem_enlarged_ball hBW hmesh hR hB v hv,
    (T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel_ae_start
      (fun w => T.pos w) {w | T.pos w ∈ ball c r} hB v] with e he hs
  have hstart : ClockedWalkExcursion.curve e 0 ∈ closedBall c r := by
    rw [ClockedWalkExcursion.curve_start, hs]
    exact mem_closedBall.mpr (mem_ball.mp hv).le
  have h := mem_curveOscillationLe_of_closedBall he hstart
  have hsum : (r + 2 * T.mesh.toReal) + r = 2 * r + 2 * T.mesh.toReal := by ring
  rw [hsum] at h
  exact h

/-- Positivity in the ambient presentation already supplies positivity in
the smaller ball presentation, since every interior neighbor belongs to it. -/
theorem ambient_clockedExcursion_ae_oscillation_of_positive (hBW : ball c r ⊆ W)
    (hmesh : T.mesh ≠ ∞)
    (hB : ∀ v ∈ {v : T.closedVertices W | T.pos v ∈ ball c r},
      0 < (T.finiteNetwork (T.closedVertices W)).totalConductance v)
    (v : T.closedVertices W) (hv : T.pos v ∈ ball c r) :
    ∀ᵐ e ∂(T.finiteNetwork (T.closedVertices W)).clockedWalkExcursionKernel
      (fun w => T.pos w) {w | T.pos w ∈ ball c r} hB v,
      ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + 2 * T.mesh.toReal) := by
  have hRS := T.closedVertices_mono hBW
  have hR : ∀ w ∈ T.finiteInterior (ball c r),
      0 < (T.finiteNetwork (T.closedVertices (ball c r))).totalConductance w := by
    intro w hw
    rw [T.finiteNetwork_totalConductance_inclusion hRS w
      (fun _ hwa => T.neighbor_mem_closedVertices hw hwa)]
    exact hB (T.regionInclusion hRS w) hw
  exact T.ambient_clockedExcursion_ae_oscillation hBW hmesh hR hB v hv

end OrthogonalTiling
end BouRabeeGwynne
