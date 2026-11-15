import LatticeProb.Bonanno.BouRabeeGwynne.FiniteStoppedCurveComparison
import LatticeProb.Bonanno.BouRabeeGwynne.PolygonalVertexExitGeometry
import LatticeProb.Walk.StoppedCurveRepresentativeDistance

/-! # Exit comparison for nearby polygonal representatives -/

set_option autoImplicit false
noncomputable section

open Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- A first vertex exit for one embedding can be compared with a continuous
curve coupled to a nearby embedding. The stopping parameter belongs to the
first embedding, and the curve oscillation is measured across its collar. -/
theorem exists_vertexExit_prefix_edist_le_of_nearby_embedding
    {d : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (p q : V → Euc d) (ω : ℕ → V) {M m : ℕ} (hmM : m ≤ M)
    {U : Set (Euc d)} (hU : IsOpen U)
    (hτ : FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω = (m : WithTop ℕ))
    {a e mesh δ η : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hmesh : 0 ≤ mesh)
    (hbuffer : a + e + mesh < δ)
    (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (hedge : ∀ k < m, dist (p (ω (k + 1))) (p (ω k)) ≤ mesh)
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (g : C(unitInterval, Euc d))
    (hclose : ∀ t, dist ((polygonalCurve q ω M).comp φ t) (g t) ≤ e)
    (hgexit : ∃ t, g t ∉ thickening δ U)
    (hgood : g ∉ unitCurveExitOscillationBad (innerDomain U (a + e))
      (thickening δ U) η) :
    ∃ s b : unitInterval, (b : ℝ) = (m : ℝ) / M ∧ φ s = b ∧
      ((polygonalCurve p ω M).comp φ) s = p (ω m) ∧
      edist (CurveSpace.project (prefixUnitCurve ((polygonalCurve p ω M).comp φ) s))
        (unitCurveExitProjection U g) ≤ ENNReal.ofReal (a + e + η) := by
  obtain ⟨s, b, hb, hsb, hs, hsout, hspre⟩ :=
    exists_vertexExit_parameter_of_exitTime p ω hmM hτ hedge
      ((polygonalCurve p ω M).comp φ) φ hmono hzero hone rfl
  refine ⟨s, b, hb, hsb, hs, ?_⟩
  apply curveSpace_edist_prefix_unitExit_le_of_not_bad hU _ g s
    (add_pos_of_nonneg_of_pos ha he) hmesh hbuffer ?_ hspre hsout hgexit hgood
  intro t
  exact (dist_triangle _ _ _).trans (add_le_add
    (dist_polygonalCurve_le_of_dist_le p q ω M hpq (φ t)) (hclose t))

end LatticeProb
end
