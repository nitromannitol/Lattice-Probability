/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCircleAnnulusLower
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeLocal.CircleMin
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP

 


set_option autoImplicit false
noncomputable section

open Set Metric SupercriticalLQGUniqueness.B2.Iface
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_finite_cross_below_across
    (A : EuclideanAnnulus) (d : ℝ) (hd : 0 < d)
    (q : Set ℂ)
    (hcover : ∀ u ∈ A.innerBoundary, ∀ v ∈ A.outerBoundary,
      ∃ z ∈ q, dist u z < d / 16 ∧ 3 * d / 4 < dist v z)
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    ∃ z ∈ q, ENNReal.ofReal (a : ℝ)⁻¹ *
      crossLenIn ξ φ (closedBall z d) (sphere z (d / 16))
        (sphere z (3 * d / 4)) ≤
      acrossDist (PfeWeyl.normalizedLFPPMetric ξ a φ) A := by
  let D := PfeWeyl.normalizedLFPPMetric ξ a φ
  obtain ⟨u, hu, v, hv, hmin⟩ := B2.PfeLocal.setDistance_eq_at_min D
    (isCompact_sphere A.center A.innerRadius)
    (isCompact_sphere A.center A.outerRadius)
    (NormedSpace.sphere_nonempty.mpr A.innerRadius_pos.le)
    (NormedSpace.sphere_nonempty.mpr (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius).le)
  obtain ⟨z, hz, huz, hvz⟩ := hcover u hu v hv
  refine ⟨z, hz, ?_⟩
  have hcross := B2.DG20Lim.normalized_annulus_cross_le_point_distance
    ξ a φ z u v d huz hvz hd
  have hpoint : ENNReal.ofReal ((B2.DG20Lim.normalizedContLFPP ξ a φ).1 (u, v)) =
      D (u, v) := by
    rw [B2.DG20Lim.normalizedContLFPP, LQGMetric.ContMetric.smulPos_apply,
      LQGMetric.LFPP.lfppContMetric_apply,
      ENNReal.ofReal_mul (inv_pos.mpr a.property).le,
      ENNReal.ofReal_toReal (LQGMetric.LFPP.lfppD_ne_top φ.continuous u v),
      PfeWeyl.normalizedLFPPMetric_apply, B2.LscTop.lfppDistance_eq_lfppD]
  simpa only [acrossDist, setDistance, EuclideanAnnulus.innerBoundary,
    EuclideanAnnulus.outerBoundary, D, hpoint] using (hcross.trans_eq hpoint).trans_eq hmin.symm

end SupercriticalLQGUniqueness.B2.PfeAxioms
