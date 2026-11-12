import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Directions in which a ray from a point meets a far set

Let `u` be a point of the plane and `H` a bounded set at positive distance `δ = dist(u, H)` from
`u`. The set of directions `θ ∈ (0, 2π]` for which the ray `{u + t e^{iθ} : t ≥ 0}` meets `H`
has Lebesgue measure at most `2π · diam H / δ`. In other words, a ray from `u` in a uniformly
random direction meets `H` with probability at most `diam H / dist(u, H)`: this is the bound on
the angle subtended by `H` seen from `u`, used to control the unit flows obtained by averaging
over random straight paths in planar packing arguments (effective resistance upper bounds).

## Main results

* `LatticeProb.norm_addCircle_le_mul_norm_exp_sub_one`: on `AddCircle (2π)`, the arc distance is
  at most `π/2` times the chord: `‖(x : AddCircle (2π))‖ ≤ π/2 · ‖e^{ix} - 1‖`.
* `LatticeProb.norm_div_norm_sub_div_norm_le`: `‖a/‖a‖ - b/‖b‖‖ ≤ 2 ‖a - b‖ / ‖b‖`.
* `LatticeProb.volume_setOf_ray_meets_le`: the measure of the set of directions of rays from `u`
  meeting `H` is at most `2π · diam H / infDist u H`.
* `LatticeProb.uniformDirection_ray_meets_le`: the normalized form, `≤ diam H / infDist u H`.
-/

open Complex Metric MeasureTheory Set

namespace LatticeProb

/-- Arc length versus chord on the circle of circumference `2π`: the distance from `x` to `0` in
`AddCircle (2π)` is at most `π/2` times the chord `‖e^{ix} - 1‖` (Jordan's inequality
`sin s ≥ 2s/π` on `[0, π/2]`). -/
theorem norm_addCircle_le_mul_norm_exp_sub_one (x : ℝ) :
    ‖(x : AddCircle (2 * Real.pi))‖ ≤ Real.pi / 2 * ‖exp (x * I) - 1‖ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set n : ℤ := round ((2 * Real.pi)⁻¹ * x) with hn
  set y : ℝ := x - n * (2 * Real.pi) with hy
  have hnorm : ‖(x : AddCircle (2 * Real.pi))‖ = |y| := AddCircle.norm_eq (2 * Real.pi)
  have hyle : |y| ≤ Real.pi := by
    rw [← hnorm]
    refine (AddCircle.norm_le_half_period (p := 2 * Real.pi) (by positivity)).trans (le_of_eq ?_)
    rw [abs_of_pos (by positivity)]; ring
  have hexp : exp (x * I) = exp (y * I) := by
    have : (x : ℂ) * I = (y : ℂ) * I + (n : ℂ) * (2 * Real.pi * I) := by
      rw [hy]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hchord : ‖exp (y * I) - 1‖ = 2 * |Real.sin (y / 2)| := by
    rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsin : |y| / Real.pi ≤ |Real.sin (y / 2)| := by
    rcases le_or_gt 0 y with h0 | h0
    · have h1 := Real.mul_le_sin (x := y / 2) (by linarith) (by
        have := (abs_of_nonneg h0) ▸ hyle; linarith)
      rw [abs_of_nonneg h0]
      calc y / Real.pi = 2 / Real.pi * (y / 2) := by field_simp
        _ ≤ Real.sin (y / 2) := h1
        _ ≤ |Real.sin (y / 2)| := le_abs_self _
    · have h1 := Real.mul_le_sin (x := -y / 2) (by linarith) (by
        have := (abs_of_neg h0) ▸ hyle; linarith)
      rw [abs_of_neg h0]
      calc -y / Real.pi = 2 / Real.pi * (-y / 2) := by field_simp
        _ ≤ Real.sin (-y / 2) := h1
        _ = -Real.sin (y / 2) := by rw [neg_div, Real.sin_neg]
        _ ≤ |Real.sin (y / 2)| := neg_le_abs _
  rw [hnorm, hexp, hchord]
  have := mul_le_mul_of_nonneg_left hsin hπ.le
  rw [mul_div_cancel₀ _ hπ.ne'] at this
  linarith

/-- Chord comparison for directions: for nonzero `a, b ∈ ℂ`,
`‖a/‖a‖ - b/‖b‖‖ ≤ 2 ‖a - b‖ / ‖b‖`. -/
theorem norm_div_norm_sub_div_norm_le {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ)‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hca : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hna.ne'
  have hcb : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnb.ne'
  have key : a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ)
      = (a - b) / (‖b‖ : ℂ) + a / (‖a‖ : ℂ) * ((‖b‖ - ‖a‖ : ℝ) : ℂ) / (‖b‖ : ℂ) := by
    push_cast
    field_simp
    ring
  have hunit : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hna, div_self hna.ne']
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, hunit, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnb]
  have h1 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
  rw [← add_div]
  gcongr
  linarith

/-- **Angle subtended by a far set.** For a bounded set `H ⊆ ℂ` at positive distance from `u`,
the set of directions `θ ∈ (0, 2π]` for which the ray `{u + t e^{iθ} : t ≥ 0}` meets `H` has
Lebesgue measure at most `2π · diam H / dist(u, H)`. -/
theorem volume_setOf_ray_meets_le (u : ℂ) {H : Set ℂ} (hb : Bornology.IsBounded H)
    (hpos : 0 < infDist u H) :
    volume {θ ∈ Ioc (0 : ℝ) (2 * Real.pi) | ∃ t : ℝ, 0 ≤ t ∧ u + t * exp (θ * I) ∈ H}
      ≤ ENNReal.ofReal (2 * Real.pi * diam H / infDist u H) := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hne : H.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hpos
  obtain ⟨h0, hh0⟩ := hne
  have hnotmem : ∀ z ∈ H, z ≠ u := by
    rintro z hz rfl
    exact hpos.ne' (infDist_zero_of_mem hz)
  have hb0 : h0 - u ≠ 0 := sub_ne_zero.mpr (hnotmem h0 hh0)
  set δ := infDist u H with hδ
  set d := diam H with hd
  set φ0 : ℝ := arg (h0 - u) with hφ0
  set B : Set (AddCircle (2 * Real.pi)) := closedBall (φ0 : AddCircle (2 * Real.pi))
    (Real.pi * d / δ) with hB
  have hsub : {θ ∈ Ioc (0 : ℝ) (2 * Real.pi) | ∃ t : ℝ, 0 ≤ t ∧ u + t * exp (θ * I) ∈ H}
      ⊆ QuotientAddGroup.mk ⁻¹' B ∩ Ioc 0 (0 + 2 * Real.pi) := by
    rintro θ ⟨hθ, t, ht, hmem⟩
    refine ⟨?_, by simpa using hθ⟩
    set h := u + t * exp (θ * I) with hh
    have hha : h - u = t * exp (θ * I) := by rw [hh]; ring
    have hnt : ‖(t : ℂ) * exp (θ * I)‖ = t := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht]
    have ha0 : h - u ≠ 0 := sub_ne_zero.mpr (hnotmem h hmem)
    have htpos : 0 < t := by
      rcases ht.lt_or_eq with h' | h'
      · exact h'
      · exfalso; apply ha0; rw [hha, ← h']; simp
    -- the two unit directions
    have hdirθ : exp (θ * I) = (h - u) / (‖h - u‖ : ℂ) := by
      rw [hha, hnt]
      field_simp [Complex.ofReal_ne_zero.mpr htpos.ne']
    have hdirφ : exp (φ0 * I) = (h0 - u) / (‖h0 - u‖ : ℂ) := by
      have := Complex.norm_mul_exp_arg_mul_I (h0 - u)
      rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hb0).ne'), mul_comm]
      exact this
    have hchord : ‖exp (θ * I) - exp (φ0 * I)‖ ≤ 2 * d / δ := by
      rw [hdirθ, hdirφ]
      refine (norm_div_norm_sub_div_norm_le ha0 hb0).trans ?_
      have hab : ‖(h - u) - (h0 - u)‖ ≤ d := by
        rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
        exact dist_le_diam_of_mem hb hmem hh0
      have hbδ : δ ≤ ‖h0 - u‖ := by
        rw [← dist_eq_norm, dist_comm]
        exact infDist_le_dist_of_mem hh0
      gcongr
    have hrot : ‖exp (((θ - φ0 : ℝ) : ℂ) * I) - 1‖ = ‖exp (θ * I) - exp (φ0 * I)‖ := by
      have : exp (θ * I) - exp (φ0 * I) = exp (φ0 * I) * (exp (((θ - φ0 : ℝ) : ℂ) * I) - 1) := by
        rw [mul_sub, ← Complex.exp_add, mul_one]
        congr 2
        push_cast; ring
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    show (θ : AddCircle (2 * Real.pi)) ∈ B
    rw [hB, mem_closedBall, dist_eq_norm, ← AddCircle.coe_sub]
    refine (norm_addCircle_le_mul_norm_exp_sub_one (θ - φ0)).trans ?_
    rw [hrot]
    calc Real.pi / 2 * ‖exp (θ * I) - exp (φ0 * I)‖ ≤ Real.pi / 2 * (2 * d / δ) := by gcongr
      _ = Real.pi * d / δ := by ring
  calc volume {θ ∈ Ioc (0 : ℝ) (2 * Real.pi) | ∃ t : ℝ, 0 ≤ t ∧ u + t * exp (θ * I) ∈ H}
      ≤ volume (QuotientAddGroup.mk ⁻¹' B ∩ Ioc 0 (0 + 2 * Real.pi)) := measure_mono hsub
    _ = volume B := (AddCircle.add_projection_respects_measure (2 * Real.pi) 0
        measurableSet_closedBall).symm
    _ = ENNReal.ofReal (min (2 * Real.pi) (2 * (Real.pi * d / δ))) :=
        AddCircle.volume_closedBall _ _
    _ ≤ ENNReal.ofReal (2 * Real.pi * d / δ) := by
        apply ENNReal.ofReal_le_ofReal
        exact (min_le_right _ _).trans (le_of_eq (by ring))

/-- **A ray in a uniformly random direction meets a far set with probability at most
`diam H / dist(u, H)`.** Normalized form of `volume_setOf_ray_meets_le`: the direction is uniform
on `(0, 2π]`, i.e. distributed as `(2π)⁻¹ • volume` restricted to `(0, 2π]`. -/
theorem uniformDirection_ray_meets_le (u : ℂ) {H : Set ℂ} (hb : Bornology.IsBounded H)
    (hpos : 0 < infDist u H) :
    ENNReal.ofReal (2 * Real.pi)⁻¹
        * volume {θ ∈ Ioc (0 : ℝ) (2 * Real.pi) | ∃ t : ℝ, 0 ≤ t ∧ u + t * exp (θ * I) ∈ H}
      ≤ ENNReal.ofReal (diam H / infDist u H) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  calc ENNReal.ofReal (2 * Real.pi)⁻¹
        * volume {θ ∈ Ioc (0 : ℝ) (2 * Real.pi) | ∃ t : ℝ, 0 ≤ t ∧ u + t * exp (θ * I) ∈ H}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * ENNReal.ofReal (2 * Real.pi * diam H / infDist u H) :=
        by gcongr; exact volume_setOf_ray_meets_le u hb hpos
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * Real.pi * diam H / infDist u H)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (diam H / infDist u H) := by
        congr 1
        field_simp

end LatticeProb
