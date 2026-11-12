/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.GeodCurve at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `IsGeod01` versus geodesic curves parametrized by length (D31 rule 1, F.GEO-MEAS bridge)

A constant-speed geodesic `η : C([0,1], ℂ)` (`ContMetric.IsGeod01`) reparametrized by `D`-length,
`P(t) = η(t / D(z,w))` on `[0, D(z,w)]`, is a `MetricGeometry.IsGeodesicCurve` of unit speed in
`D.Space` from `z` to `w` (`ContMetric.IsGeod01.isGeodesicCurve`); conversely a unit-speed geodesic
curve `P` on `[0, L]` from `z` to `w` gives the `IsGeod01` path `s ↦ P(L s)`
(`ContMetric.isGeod01_of_isGeodesicCurve`). Elementary reparametrization (own argument); the
curve-side facts are `MetricGeometry.isGeodesicCurve_of_edist_eq` and
`IsGeodesicCurve.edist_eq_of_hasUnitSpeedOn` (Metric/Geodesic.lean).
-/

open Set
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

namespace ContMetric

/-- the length parametrization `t ↦ η(t / L)` of a path on `[0,1]` -/
noncomputable def lengthCurve (D : ContMetric) (η : C(unitInterval, ℂ)) (L : ℝ) : ℝ → D.Space :=
  fun t => D.pt (η (projIcc 0 1 zero_le_one (t / L)))

theorem IsGeod01.isGeodesicCurve {D : ContMetric} {z w : ℂ} {η : C(unitInterval, ℂ)}
    (h : D.IsGeod01 z w η) :
    IsGeodesicCurve (D.lengthCurve η (D.1 (z, w))) 0 (D.1 (z, w)) ∧
      HasUnitSpeedOn (D.lengthCurve η (D.1 (z, w))) (Icc 0 (D.1 (z, w))) ∧
      D.lengthCurve η (D.1 (z, w)) 0 = D.pt z ∧
      D.lengthCurve η (D.1 (z, w)) (D.1 (z, w)) = D.pt w := by
  obtain ⟨h0, h1, hd⟩ := h
  set L := D.1 (z, w) with hL
  have hL0 : 0 ≤ L := D.nonneg z w
  have hstart : D.lengthCurve η L 0 = D.pt z := by
    simp only [lengthCurve]
    rw [zero_div, projIcc_left]
    exact congrArg D.pt h0
  refine ⟨(isGeodesicCurve_of_edist_eq hL0 fun s hs t ht => ?_).1,
    (isGeodesicCurve_of_edist_eq hL0 fun s hs t ht => ?_).2, hstart, ?_⟩
  rotate_right
  · rcases hL0.eq_or_lt with h' | h'
    · have hzw : z = w := D.2.eq_of_eq_zero z w h'.symm
      rw [← h'] at hstart ⊢
      rw [hstart, hzw]
    · simp only [lengthCurve]
      rw [div_self h'.ne', projIcc_right]
      exact congrArg D.pt h1
  all_goals
    rcases hL0.eq_or_lt with h' | h'
    · have hs0 : s = 0 := le_antisymm (h' ▸ hs.2) hs.1
      have ht0 : t = 0 := le_antisymm (h' ▸ ht.2) ht.1
      subst hs0; subst ht0; simp
    · have hsm : s / L ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hs.1 hL0, (div_le_one h').2 hs.2⟩
      have htm : t / L ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hL0, (div_le_one h').2 ht.2⟩
      simp only [lengthCurve]
      rw [projIcc_of_mem _ hsm, projIcc_of_mem _ htm, edist_pt, hd, edist_dist, Real.dist_eq]
      congr 1
      rw [show t / L - s / L = (t - s) / L by ring, abs_div, abs_of_pos h',
        div_mul_cancel₀ _ h'.ne', abs_sub_comm]

end ContMetric

end LQGMetric
