import LatticeProb.Walk.RepresentativeCollarExit
import LatticeProb.Bonanno.BouRabeeGwynne.MonotoneStoppedPrefixes
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSegmentRestriction

/-! # Stopped polygonal curves from monotone-clock prefixes -/

set_option autoImplicit false
noncomputable section

open Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- A clocked polygonal prefix ending at a finite exit vertex represents the
stopped polygonal curve, including a zero exit or a zero-length polygon. -/
theorem project_polygonal_prefix_eq_stoppedPolygonalCurve
    {d : ℕ} {V : Type*} (p : V → Euc d) (ω : ℕ → V)
    {A : Set V} {M m : ℕ} (hmM : m ≤ M)
    (hτ : FiniteConductanceNetwork.exitTime A ω = (m : WithTop ℕ))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ) (hzero : φ 0 = 0)
    (s b : unitInterval) (hsb : φ s = b) (hb : (M : ℝ) * (b : ℝ) = m) :
    CurveSpace.project (prefixUnitCurve ((polygonalCurve p ω M).comp φ) s) =
      stoppedPolygonalCurve p A ω := by
  rw [curveSpace_project_prefix_comp_monotone _ φ hmono hzero s b hsb]
  have hp : prefixUnitCurve (polygonalCurve p ω M) b = polygonalCurve p ω m := by
    apply ContinuousMap.ext
    intro u
    change polygonalCurve p ω M (b * u) = polygonalCurve p ω m u
    simpa only [Nat.zero_add] using polygonalCurve_shift_of_scaled_time p ω
      (a := 0) (m := m) (M := M) (by simpa only [Nat.zero_add] using hmM) u (b * u)
      (by rw [Set.Icc.coe_mul, Nat.cast_zero, zero_add, ← mul_assoc, hb])
  rw [hp]
  unfold stoppedPolygonalCurve
  rw [hτ]
  rfl

/-- The collar comparison controls the actual discrete stopped curve. -/
theorem edist_stoppedPolygonalCurve_le_of_nearby_embedding
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
    edist (stoppedPolygonalCurve p (p ⁻¹' U) ω) (unitCurveExitProjection U g) ≤
      ENNReal.ofReal (a + e + η) := by
  obtain ⟨s, b, hb, hsb, _, hd⟩ :=
    exists_vertexExit_prefix_edist_le_of_nearby_embedding p q ω hmM hU hτ
      ha he hmesh hbuffer hpq hedge φ hmono hzero hone g hclose hgexit hgood
  have hbscale : (M : ℝ) * (b : ℝ) = m := by
    by_cases hM : M = 0
    · subst M
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmM
      subst m
      simp only [Nat.cast_zero, zero_mul]
    · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
      rw [hb]
      field_simp
  rw [project_polygonal_prefix_eq_stoppedPolygonalCurve p ω hmM hτ φ hmono hzero s b hsb
    hbscale] at hd
  exact hd

end LatticeProb
end
