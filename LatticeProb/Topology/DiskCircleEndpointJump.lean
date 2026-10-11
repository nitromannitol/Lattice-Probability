/-
# Crossing signs on the original unit circle

The transverse derivative of the circle at an endpoint is the outward radial
pairing of the ray. The determinant against an incident edge has derivative
equal to that edge's radial pairing. Nonzero derivatives control the signs on
both sides of the original angle. The exact level-line meeting formula then
determines which incident half-open marker changes.
-/
import LatticeProb.Topology.PolygonalEndpointJump
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv



open Set Metric Filter
open scoped Topology
namespace LatticeProb.Topology.PolygonalParity

private theorem div_pos_iff_of_neg_right {x y : ℝ} (hy : y < 0) :
    0 < x / y ↔ x < 0 := by
  constructor
  · intro h
    rcases div_pos_iff.mp h with h | h
    · exact (not_lt_of_ge hy.le h.2).elim
    · exact h.1
  · intro h
    exact div_pos_of_neg_of_neg h hy

/-- A nonzero scalar derivative gives the sign of the nearby difference
quotient on both sides of its base point. -/
theorem exists_slope_sign {f : ℝ → ℝ} {k θ : ℝ} (hf : HasDerivAt f k θ)
    (hk : k ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ℝ, |φ - θ| < δ → φ ≠ θ →
      (0 < (f φ - f θ) / (φ - θ) ↔ 0 < k) ∧
      ((f φ - f θ) / (φ - θ) < 0 ↔ k < 0) := by
  have he : ∀ᶠ φ in 𝓝[≠] θ,
      (0 < slope f θ φ ↔ 0 < k) ∧ (slope f θ φ < 0 ↔ k < 0) := by
    rcases lt_or_gt_of_ne hk with hk | hk
    · have hn := hf.tendsto_slope.eventually_lt tendsto_const_nhds hk
      filter_upwards [hn] with φ hφ
      exact ⟨iff_of_false (not_lt_of_ge hφ.le) (not_lt_of_ge hk.le), iff_of_true hφ hk⟩
    · have hp := tendsto_const_nhds.eventually_lt hf.tendsto_slope hk
      filter_upwards [hp] with φ hφ
      exact ⟨iff_of_true hφ hk, iff_of_false (not_lt_of_ge hφ.le) (not_lt_of_ge hk.le)⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp he)
  refine ⟨δ, hδ, fun φ hφ hne => ?_⟩
  have hdist : φ ∈ ball θ δ := by
    rw [mem_ball, Real.dist_eq]
    exact hφ
  simpa only [slope_def_field] using hball φ hdist hne

/-- The original circle's transverse derivative is the outward radial
forward coordinate of the ray. -/
theorem hasDerivAt_hgt_circle (u : Plane) (θ : ℝ) :
    HasDerivAt (fun φ => hgt u (coordinateEquiv (Real.cos φ, Real.sin φ)))
      (fwd u (coordinateEquiv (Real.cos θ, Real.sin θ))) θ := by
  rw [fwd_eq]
  change HasDerivAt (fun φ => u 0 * Real.sin φ - u 1 * Real.cos φ)
    (Real.cos θ * u 0 + Real.sin θ * u 1) θ
  have h := ((Real.hasDerivAt_sin θ).const_mul (u 0)).sub
    ((Real.hasDerivAt_cos θ).const_mul (u 1))
  convert h using 1 <;> first | rfl | ring

/-- Against an incident edge, the circle's determinant derivative is the
edge's radial pairing at the original endpoint. -/
theorem hasDerivAt_det_circle (v : Plane) (θ : ℝ) :
    HasDerivAt (fun φ => Plane.det v (coordinateEquiv (Real.cos φ, Real.sin φ)))
      (inner ℝ v (coordinateEquiv (Real.cos θ, Real.sin θ))) θ := by
  rw [Plane.inner_eq]
  change HasDerivAt (fun φ => v 0 * Real.sin φ - v 1 * Real.cos φ)
    (v 0 * Real.cos θ + v 1 * Real.sin θ) θ
  have h := ((Real.hasDerivAt_sin θ).const_mul (v 0)).sub
    ((Real.hasDerivAt_cos θ).const_mul (v 1))
  convert h using 1 <;> first | rfl | ring

/-- The two ray-frame coordinates recover the original determinant. -/
theorem det_eq_frame {u : Plane} (hu : Plane.IsDirection u) (v w : Plane) :
    Plane.det v w = fwd u v * hgt u w - hgt u v * fwd u w := by
  have hid : fwd u v * hgt u w - hgt u v * fwd u w =
      (u 0 ^ 2 + u 1 ^ 2) * Plane.det v w := by
    rw [fwd_eq, fwd_eq, hgt_eq, hgt_eq, Plane.det]
    ring
  rw [hid, norm_sq_one hu, one_mul]

/-- **Incident forward gap formula.** For a nonlevel edge, the signed
forward gap at its level-line meeting equals its determinant against the base
point displacement divided by the edge's transverse displacement. -/
theorem fwd_meet_sub_eq_det_div {u a b q : Plane} (hu : Plane.IsDirection u)
    (hab : hgt u a ≠ hgt u b) :
    fwd u (meet u a b (hgt u q)) - fwd u q =
      Plane.det (b - a) (q - a) / (hgt u b - hgt u a) := by
  have hd : hgt u b - hgt u a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [fwd_meet, det_eq_frame hu, fwd_sub, fwd_sub, hgt_sub, hgt_sub]
  field_simp
  ring

/-- Near a nonlevel incident edge of nonzero radial pairing, the original
circle ray crosses precisely when the edge points outward and its transverse
side agrees with the side of the original angle. No tangency condition on the
ray or circle is assumed: their transverse derivative is the proved positive
outward pairing. -/
theorem exists_circle_incident_mark (θ : ℝ) {u b : Plane}
    (hu : Plane.IsDirection u)
    (hout : 0 < fwd u (coordinateEquiv (Real.cos θ, Real.sin θ)))
    (hab : hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ hgt u b)
    (hrad : inner ℝ (b - coordinateEquiv (Real.cos θ, Real.sin θ))
      (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ℝ, |φ - θ| < δ → φ ≠ θ →
      mark u (coordinateEquiv (Real.cos θ, Real.sin θ), b)
          (coordinateEquiv (Real.cos φ, Real.sin φ)) =
        if 0 < inner ℝ (b - coordinateEquiv (Real.cos θ, Real.sin θ))
            (coordinateEquiv (Real.cos θ, Real.sin θ)) ∧
          ((hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) < hgt u b ∧ θ < φ) ∨
            (hgt u b < hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ∧ φ < θ))
        then 1 else 0 := by
  let a := coordinateEquiv (Real.cos θ, Real.sin θ)
  let rad := inner ℝ (b - a) a
  obtain ⟨ε₁, hε₁, hH⟩ := exists_slope_sign (hasDerivAt_hgt_circle u θ) hout.ne'
  obtain ⟨ε₂, hε₂, hD⟩ := exists_slope_sign (hasDerivAt_det_circle (b - a) θ) hrad
  have hcont : Continuous (fun φ => |hgt u (coordinateEquiv (Real.cos φ, Real.sin φ)) - hgt u a|) :=
    (((continuous_hgt_right u).comp (continuous_coordinateEquiv.comp
      (Real.continuous_cos.prodMk Real.continuous_sin))).sub continuous_const).abs
  have hbound0 : |hgt u a - hgt u a| < |hgt u b - hgt u a| := by
    rw [sub_self, abs_zero]
    exact abs_pos.mpr (sub_ne_zero.mpr hab.symm)
  obtain ⟨ε₃, hε₃, hbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.continuousAt.eventually_lt continuousAt_const hbound0)
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun φ hφ hne => ?_⟩
  let q := coordinateEquiv (Real.cos φ, Real.sin φ)
  change mark u (a, b) q = if 0 < rad ∧
    ((hgt u a < hgt u b ∧ θ < φ) ∨ (hgt u b < hgt u a ∧ φ < θ)) then 1 else 0
  have hφ1 := hφ.trans_le (min_le_left ε₁ (min ε₂ ε₃))
  have hφ2 := hφ.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃))
  have hφ3 := hφ.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃))
  have hh : 0 < (hgt u q - hgt u a) / (φ - θ) := (hH φ hφ1 hne).1.mpr hout
  have hd : (0 < Plane.det (b - a) (q - a) / (φ - θ) ↔ 0 < rad) := by
    have h := (hD φ hφ2 hne).1
    change (0 < (hgt (b - a) q - hgt (b - a) a) / (φ - θ) ↔ 0 < rad) at h
    rwa [← hgt_sub] at h
  have hnear : |hgt u q - hgt u a| < |hgt u b - hgt u a| :=
    hbound φ (by rw [mem_ball, Real.dist_eq]; exact hφ3)
  have hgap := fwd_meet_sub_eq_det_div (q := q) hu hab
  rcases lt_or_gt_of_ne hab with hup | hdown
  · have he : 0 < hgt u b - hgt u a := sub_pos.mpr hup
    rw [abs_of_pos he] at hnear
    rcases lt_or_gt_of_ne hne with hleft | hright
    · have hτ : φ - θ < 0 := sub_neg.mpr hleft
      have hqlo : hgt u q < hgt u a := sub_neg.mp ((div_pos_iff_of_neg_right hτ).mp hh)
      have hmiss : ¬ Crosses u (a, b) q := by
        rintro ⟨h, _, _⟩
        rw [min_eq_left hup.le] at h
        exact (not_le_of_gt hqlo) h
      have hcond : ¬ (0 < rad ∧ ((hgt u a < hgt u b ∧ θ < φ) ∨
          (hgt u b < hgt u a ∧ φ < θ))) := by
        rintro ⟨_, h | h⟩
        · exact (not_lt_of_ge hleft.le) h.2
        · exact (not_lt_of_ge hup.le) h.1
      rw [mark, if_neg hmiss, if_neg hcond]
    · have hτ : 0 < φ - θ := sub_pos.mpr hright
      have hqlo : hgt u a < hgt u q := sub_pos.mp ((div_pos_iff_of_pos_right hτ).mp hh)
      have hqhi : hgt u q < hgt u b := by
        have h := (abs_lt.mp hnear).2
        linarith only [h]
      have hsign : 0 < Plane.det (b - a) (q - a) / (hgt u b - hgt u a) ↔ 0 < rad :=
        (div_pos_iff_of_pos_right he).trans ((div_pos_iff_of_pos_right hτ).symm.trans hd)
      have hcross : Crosses u (a, b) q ↔ 0 < rad := by
        constructor
        · intro h
          apply hsign.mp
          rw [← hgap]
          exact sub_pos.mpr h.2.2
        · intro h
          refine ⟨by rw [min_eq_left hup.le]; exact hqlo.le,
            by rw [max_eq_right hup.le]; exact hqhi, ?_⟩
          apply sub_pos.mp
          rw [hgap]
          exact hsign.mpr h
      have hcond : (0 < rad ∧ ((hgt u a < hgt u b ∧ θ < φ) ∨
          (hgt u b < hgt u a ∧ φ < θ))) ↔ 0 < rad :=
        ⟨And.left, fun h => ⟨h, Or.inl ⟨hup, hright⟩⟩⟩
      simp only [mark, hcross, hcond]
  · have he : hgt u b - hgt u a < 0 := sub_neg.mpr hdown
    rw [abs_of_neg he] at hnear
    rcases lt_or_gt_of_ne hne with hleft | hright
    · have hτ : φ - θ < 0 := sub_neg.mpr hleft
      have hqhi : hgt u q < hgt u a := sub_neg.mp ((div_pos_iff_of_neg_right hτ).mp hh)
      have hqlo : hgt u b < hgt u q := by
        have h := (abs_lt.mp hnear).1
        linarith only [h]
      have hsign : 0 < Plane.det (b - a) (q - a) / (hgt u b - hgt u a) ↔ 0 < rad :=
        (div_pos_iff_of_neg_right he).trans ((div_pos_iff_of_neg_right hτ).symm.trans hd)
      have hcross : Crosses u (a, b) q ↔ 0 < rad := by
        constructor
        · intro h
          apply hsign.mp
          rw [← hgap]
          exact sub_pos.mpr h.2.2
        · intro h
          refine ⟨by rw [min_eq_right hdown.le]; exact hqlo.le,
            by rw [max_eq_left hdown.le]; exact hqhi, ?_⟩
          apply sub_pos.mp
          rw [hgap]
          exact hsign.mpr h
      have hcond : (0 < rad ∧ ((hgt u a < hgt u b ∧ θ < φ) ∨
          (hgt u b < hgt u a ∧ φ < θ))) ↔ 0 < rad :=
        ⟨And.left, fun h => ⟨h, Or.inr ⟨hdown, hleft⟩⟩⟩
      simp only [mark, hcross, hcond]
    · have hτ : 0 < φ - θ := sub_pos.mpr hright
      have hqhi : hgt u a < hgt u q := sub_pos.mp ((div_pos_iff_of_pos_right hτ).mp hh)
      have hmiss : ¬ Crosses u (a, b) q := by
        rintro ⟨_, h, _⟩
        rw [max_eq_left hdown.le] at h
        exact (not_lt_of_ge hqhi.le) h
      have hcond : ¬ (0 < rad ∧ ((hgt u a < hgt u b ∧ θ < φ) ∨
          (hgt u b < hgt u a ∧ φ < θ))) := by
        rintro ⟨_, h | h⟩
        · exact (not_lt_of_ge hdown.le) h.1
        · exact (not_lt_of_ge hright.le) h.2
      rw [mark, if_neg hmiss, if_neg hcond]

/-- **Original-circle endpoint jump (internal).** A finite chain with just
two incident edges at an original circle endpoint has opposite parity on the
two nearby original angular sides when the first edge is radially inward and
the second radially outward. The ray and remaining endpoint heights are finite
geometric prerequisites; every crossing sign and neighborhood is derived. -/
theorem exists_circle_endpoint_jump_internal (θ : ℝ) {u b c : Plane} {R : List Piece}
    (hu : Plane.IsDirection u)
    (hout : 0 < fwd u (coordinateEquiv (Real.cos θ, Real.sin θ)))
    (hab : hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ hgt u b)
    (hac : hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ hgt u c)
    (hb : inner ℝ (b - coordinateEquiv (Real.cos θ, Real.sin θ))
      (coordinateEquiv (Real.cos θ, Real.sin θ)) < 0)
    (hc : 0 < inner ℝ (c - coordinateEquiv (Real.cos θ, Real.sin θ))
      (coordinateEquiv (Real.cos θ, Real.sin θ)))
    (hR : ∀ P ∈ R, hgt u P.1 ≠ hgt u P.2)
    (haR : coordinateEquiv (Real.cos θ, Real.sin θ) ∉ cover R)
    (hheight : ∀ P ∈ R,
      hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ hgt u P.1 ∧
      hgt u (coordinateEquiv (Real.cos θ, Real.sin θ)) ≠ hgt u P.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      parity u ((coordinateEquiv (Real.cos θ, Real.sin θ), b) ::
          (coordinateEquiv (Real.cos θ, Real.sin θ), c) :: R)
          (coordinateEquiv (Real.cos (θ - t), Real.sin (θ - t))) =
        parity u ((coordinateEquiv (Real.cos θ, Real.sin θ), b) ::
          (coordinateEquiv (Real.cos θ, Real.sin θ), c) :: R)
          (coordinateEquiv (Real.cos (θ + t), Real.sin (θ + t))) + 1 := by
  let a := coordinateEquiv (Real.cos θ, Real.sin θ)
  obtain ⟨ε₁, hε₁, hbm⟩ := exists_circle_incident_mark θ hu hout hab hb.ne
  obtain ⟨ε₂, hε₂, hcm⟩ := exists_circle_incident_mark θ hu hout hac hc.ne'
  have hcont : Continuous (fun φ => coordinateEquiv (Real.cos φ, Real.sin φ)) :=
    continuous_coordinateEquiv.comp (Real.continuous_cos.prodMk Real.continuous_sin)
  obtain ⟨ε₃, hε₃, hrest⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.continuousAt.eventually (parity_eventually_eq_of_endpoint_heights hu hR haR hheight))
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun t ht htδ => ?_⟩
  have ht1 := htδ.trans_le (min_le_left ε₁ (min ε₂ ε₃))
  have ht2 := htδ.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃))
  have ht3 := htδ.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃))
  have hminus : θ - t < θ := sub_lt_self θ ht
  have hplus : θ < θ + t := lt_add_of_pos_right θ ht
  have hmabs : |θ - t - θ| = t := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos ht]
  have hpabs : |θ + t - θ| = t := by rw [add_sub_cancel_left, abs_of_pos ht]
  have hm := hbm (θ - t) (by rw [hmabs]; exact ht1) hminus.ne
  have hp := hbm (θ + t) (by rw [hpabs]; exact ht1) hplus.ne'
  have hfalse : ∀ φ : ℝ, ¬ (0 < inner ℝ (b - a) a ∧
      ((hgt u a < hgt u b ∧ θ < φ) ∨ (hgt u b < hgt u a ∧ φ < θ))) :=
    fun _ h => (not_lt_of_ge hb.le) h.1
  rw [if_neg (hfalse _)] at hm hp
  have hcm' := hcm (θ - t) (by rw [hmabs]; exact ht2) hminus.ne
  have hcp' := hcm (θ + t) (by rw [hpabs]; exact ht2) hplus.ne'
  have hsum : mark u (a, c) (coordinateEquiv (Real.cos (θ - t), Real.sin (θ - t))) +
      mark u (a, c) (coordinateEquiv (Real.cos (θ + t), Real.sin (θ + t))) = 1 := by
    rcases lt_or_gt_of_ne hac with hup | hdown
    · have hfm : ¬ (0 < inner ℝ (c - a) a ∧
          ((hgt u a < hgt u c ∧ θ < θ - t) ∨ (hgt u c < hgt u a ∧ θ - t < θ))) := by
        rintro ⟨_, h | h⟩
        · exact (not_lt_of_ge hminus.le) h.2
        · exact (not_lt_of_ge hup.le) h.1
      rw [if_neg hfm] at hcm'
      rw [if_pos ⟨hc, Or.inl ⟨hup, hplus⟩⟩] at hcp'
      rw [hcm', hcp', zero_add]
    · have hfp : ¬ (0 < inner ℝ (c - a) a ∧
          ((hgt u a < hgt u c ∧ θ < θ + t) ∨ (hgt u c < hgt u a ∧ θ + t < θ))) := by
        rintro ⟨_, h | h⟩
        · exact (not_lt_of_ge hdown.le) h.1
        · exact (not_lt_of_ge hplus.le) h.2
      rw [if_pos ⟨hc, Or.inr ⟨hdown, hminus⟩⟩] at hcm'
      rw [if_neg hfp] at hcp'
      rw [hcm', hcp', add_zero]
  have hrm := hrest (θ - t) (by rw [mem_ball, Real.dist_eq, hmabs]; exact ht3)
  have hrp := hrest (θ + t) (by rw [mem_ball, Real.dist_eq, hpabs]; exact ht3)
  rw [parity_cons, parity_cons, parity_cons, parity_cons, hm, hp, zero_add, zero_add, hrm, hrp]
  have harith : ∀ x y z : ZMod 2, x + y = 1 → x + z = y + z + 1 := by decide
  exact harith _ _ _ hsum

end LatticeProb.Topology.PolygonalParity
