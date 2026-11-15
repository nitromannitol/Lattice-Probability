import LatticeProb.Walk.SourceStoppedCurveFinalEdge
import LatticeProb.Walk.AdjacentPrefixClock
import LatticeProb.Walk.StoppedPolygonalPrefix
import LatticeProb.Walk.ConstantStepPrefix

/-! # Final-edge estimates from a finite walk prefix -/

set_option autoImplicit false
noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The final-edge bound needs adjacency only through the first exterior vertex;
no divergence assumption is imposed on the original path's holding clock. -/
theorem source_edist_exit_stoppedPolygonalCurve_le_of_prefix (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (n : ℕ)
    (hadj : ∀ j ≤ n, H.Adj (ω j) (ω (j + 1)))
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) {U : Set Plane}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hhit : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ)) :
    let g := ConstantStepInterpolation.continuousPlanePath m (fun j => (ε : ℝ) • p (ω j))
    continuousExitTime U 0 g ≠ ∞ ∧
    edist (CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal))
      (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
        {K : H.cells | (ε : ℝ) • p K ∈ U} ω) ≤
      ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  let A : Set H.cells := {K | (ε : ℝ) • p K ∈ U}
  let ξ := alternateLastEdge ω n
  have hpre : ∀ j ≤ n + 1, ξ j = ω j := fun j hj => alternateLastEdge_eq ω n j hj
  have he : FiniteConductanceNetwork.exitTime A ω = (n + 1 : ℕ) := by
    rw [exitTime_eq_hitTime_compl]
    exact hhit
  have heξ : FiniteConductanceNetwork.exitTime A ξ = (n + 1 : ℕ) := by
    rw [FiniteConductanceNetwork.exitTime_congr_prefix_of_le A hpre (le_of_eq he), he]
  have hhitξ : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ξ = (n + 1 : ℕ) := by
    rw [exitTime_eq_hitTime_compl] at heξ
    exact heξ
  have hsymm : ∀ ⦃a b : H.cells⦄, H.Adj a b → H.Adj b a := by
    intro a b h
    simpa only [CellConfig.Adj, hH.c_symm] using h
  have hadjξ := alternateLastEdge_adjacent (fun a b : H.cells => H.Adj a b) hsymm ω n hadj
  have hunb := jumpTimesUnbounded_alternateLastEdge H ω n (fun j _ => hpos (ω j))
  have hstartξ : (ε : ℝ) • p (ξ 0) ∈ U := by simpa only [hpre 0 (by omega)] using hstart
  have hfinξ : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ξ ≠ ⊤ := by
    rw [hhitξ]
    exact ENat.natCast_ne_top _
  obtain ⟨k, hk, _, hd⟩ := source_edist_exit_stoppedPolygonalCurve_le H hH p hp ξ
    hpos hunb hadjξ hε hm hU hconv hstartξ hfinξ
  have hkn : k = n := by
    rw [heξ] at hk
    have hk' : k + 1 = n + 1 := WithTop.coe_injective hk.symm
    omega
  subst k
  have hout : (ε : ℝ) • p (ω (n + 1)) ∉ U := (hitTime_eq_coe_iff.mp hhit).1
  have hc := ConstantStepInterpolation.continuousExitTime_and_curve_eq_of_prefix hm
    (p := fun j => (ε : ℝ) • p (ω j)) (q := fun j => (ε : ℝ) • p (ξ j))
    (M := n + 1) (fun j hj => by rw [hpre j hj]) hU hout
  have hpoly := stoppedPolygonalCurve_eq_of_prefix (fun K => (ε : ℝ) • p K) A
    hpre (le_of_eq he)
  refine ⟨hc.1, ?_⟩
  rw [hc.2.2, hpoly, hpre n (by omega), hpre (n + 1) le_rfl] at hd
  exact hd

end LatticeProb.CellConfigInterpolation
end
