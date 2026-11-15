import LatticeProb.Walk.SourceFinalEdgeCurve
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-! # Discrete and continuous stopped curves -/

set_option autoImplicit false
noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb

/-- The first exit from a vertex set is the first hit of its complement,
including the case where no hit occurs. -/
theorem exitTime_eq_hitTime_compl {V : Type*} (A : Set V) (ω : ℕ → V) :
    FiniteConductanceNetwork.exitTime A ω = hitTime Aᶜ ω := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  change (FiniteConductanceNetwork.exitTime A ω ≤ (n : WithTop ℕ)) ↔
    (hitTime Aᶜ ω ≤ (n : ℕ∞))
  exact (FiniteConductanceNetwork.exitTime_le_iff A ω n).trans
    (hitTime_le_coe_iff (A := Aᶜ) (ω := ω) (n := n)).symm

namespace CellConfigInterpolation

/-- The continuous exit curve is close to the discrete stopped polygonal curve,
with error controlled by the two cells on the final edge. -/
theorem source_edist_exit_stoppedPolygonalCurve_le (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) {U : Set Plane}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ,
      FiniteConductanceNetwork.exitTime {K : H.cells | (ε : ℝ) • p K ∈ U} ω =
        (n + 1 : ℕ) ∧
      let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
      continuousExitTime U 0 g ≠ ∞ ∧
      edist (CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))
        (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
          {K : H.cells | (ε : ℝ) • p K ∈ U} ω) ≤
        ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  obtain ⟨n, hn, hf, hd⟩ := source_edist_exit_curve_le H hH p hp ω hpos hunb hadj
    hε hm hU hconv hstart hfin
  have he : FiniteConductanceNetwork.exitTime {K : H.cells | (ε : ℝ) • p K ∈ U} ω =
      (n + 1 : ℕ) := by
    rw [exitTime_eq_hitTime_compl]
    exact hn
  refine ⟨n, he, hf, ?_⟩
  unfold stoppedPolygonalCurve
  have hi : (FiniteConductanceNetwork.exitTime
      {K : H.cells | (ε : ℝ) • p K ∈ U} ω).untopD 0 = n + 1 := by
    rw [he]
    rfl
  rw [hi]
  exact hd

end CellConfigInterpolation
end LatticeProb
end
