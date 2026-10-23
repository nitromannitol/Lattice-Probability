import LatticeProb.Graph.LongRangeKernel.CriticalScale

/-!
# Critical logarithmic asymptotics

Ratio limits identify the normalization of the explicit critical inverse.
-/

namespace LatticeProb.Graph.LongRangeKernel

open Filter Topology

noncomputable section

/-- A fixed additive shift does not change the leading linear asymptotics. -/
theorem tendsto_add_div_self (a : ℝ) :
    Tendsto (fun t : ℝ => (t + a) / t) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atTop (𝓝 a)).div_atTop tendsto_id)
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp
    field_simp

/-- A fixed additive shift does not change the leading logarithmic asymptotics. -/
theorem tendsto_log_add_div_log (a : ℝ) :
    Tendsto (fun t : ℝ => Real.log (t + a) / Real.log t) atTop (𝓝 1) := by
  have h := (Asymptotics.isEquivalent_of_tendsto_one (tendsto_add_div_self a)).log
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  exact (Asymptotics.isEquivalent_iff_tendsto_one
    (Real.tendsto_log_atTop.eventually_ne_atTop 0)).mp h

/-- The quadratic scale is regularly varying with index two. -/
theorem quadraticScale_regularlyVarying : LatticeProb.RegularlyVaryingAtTop quadraticScale 2 := by
  intro a _
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlin := (hi.add_const a).div (hi.add_const 1) (by norm_num : (0 : ℝ) + 1 ≠ 0)
  have h := hlin.pow 2
  rw [Real.rpow_two]
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp [quadraticScale]
    have hden : 1 + t ≠ 0 := by linarith
    field_simp [ht.ne', hden]

/-- The quadratic jump scale satisfies all of the source jump-scale assumptions. -/
theorem quadraticScale_isJumpScale : IsJumpScale quadraticScale :=
  ⟨continuous_quadraticScale.continuousOn, fun _ hr => one_le_quadraticScale hr,
    2, by norm_num, quadraticScale_regularlyVarying⟩

/-- The critical primitive is asymptotic to the logarithm. -/
theorem tendsto_criticalPrimitive_div_log :
    Tendsto (fun t : ℝ => criticalPrimitive t / Real.log t) atTop (𝓝 1) := by
  have hinv : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left atTop 1 tendsto_id).inv_tendsto_atTop
  have hsmall := (hinv.sub (tendsto_const_nhds (x := (1 : ℝ)))).div_atTop Real.tendsto_log_atTop
  have h := (tendsto_log_add_div_log 1).add hsmall
  convert h using 1
  · ext t
    dsimp [criticalPrimitive]
    rw [add_comm t 1]
    ring
  · norm_num

/-- The critical primitive tends to infinity. -/
theorem tendsto_criticalPrimitive : Tendsto criticalPrimitive atTop atTop := by
  exact (Asymptotics.isEquivalent_of_tendsto_one
    tendsto_criticalPrimitive_div_log).symm.tendsto_atTop Real.tendsto_log_atTop

/-- The primitive's logarithm has negligible size relative to the original logarithm. -/
theorem tendsto_log_criticalPrimitive_div_log :
    Tendsto (fun t : ℝ => Real.log (criticalPrimitive t) / Real.log t) atTop (𝓝 0) := by
  have hratio := tendsto_criticalPrimitive_div_log.log (by norm_num : (1 : ℝ) ≠ 0)
  have hsmall := hratio.div_atTop Real.tendsto_log_atTop
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop
  have h := hsmall.add hloglog
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hD : criticalPrimitive t ≠ 0 := (criticalPrimitive_pos ht0).ne'
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    dsimp
    rw [Real.log_div hD hl]
    ring

/-- The exact η has the asymptotic critical profile. -/
theorem tendsto_eta_mul_log_div_sq :
    Tendsto (fun t : ℝ => eta 2 quadraticScale t * Real.log t / t ^ 2)
      atTop (𝓝 1) := by
  have h := tendsto_criticalPrimitive_div_log.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    rw [eta_quadratic ht0]
    have hD : criticalPrimitive t ≠ 0 := (criticalPrimitive_pos ht0).ne'
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    field_simp

/-- The exact η tends to infinity. -/
theorem tendsto_eta_quadratic : Tendsto (eta 2 quadraticScale) atTop atTop := by
  have hbase : Tendsto (fun t : ℝ => t ^ 2 / Real.log t) atTop atTop := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hinv : Tendsto (fun t : ℝ => t / Real.log t) atTop atTop := by
      have hgt : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨h, by
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
          exact div_pos (Real.log_pos ht) (by linarith)⟩
      convert hgt.inv_tendsto_nhdsGT_zero using 1
      ext t
      change t / Real.log t = (Real.log t / t)⁻¹
      rw [inv_div]
    have hmul := (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_atTop₀ hinv
    convert hmul using 1
    ext t
    change t ^ 2 / Real.log t = t * (t / Real.log t)
    ring
  have hratio : Tendsto (fun t : ℝ => eta 2 quadraticScale t /
      (t ^ 2 / Real.log t)) atTop (𝓝 1) := by
    convert tendsto_eta_mul_log_div_sq using 1
    ext t
    simp only [div_div_eq_mul_div]
  exact (Asymptotics.isEquivalent_of_tendsto_one hratio).symm.tendsto_atTop hbase

/-- The logarithm of η has leading coefficient two. -/
theorem tendsto_log_eta_div_log :
    Tendsto (fun t : ℝ => Real.log (eta 2 quadraticScale t) / Real.log t)
      atTop (𝓝 2) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
    tendsto_log_criticalPrimitive_div_log
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hD : criticalPrimitive t ≠ 0 := (criticalPrimitive_pos ht0).ne'
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    rw [eta_quadratic ht0, Real.log_div (pow_ne_zero 2 ht0.ne') hD, Real.log_pow]
    dsimp
    field_simp

/-- The explicit inverse has squared leading profile `t log(t)/2`. -/
theorem tendsto_criticalInverse_sq_div_mul_log :
    Tendsto (fun t : ℝ => criticalInverse t ^ 2 / (t * Real.log t))
      atTop (𝓝 (1 / 2)) := by
  have hprod : Tendsto (fun t : ℝ => t * Real.log t) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (t * Real.log t)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hprod
  have hratio := ((tendsto_add_div_self 2).mul (tendsto_log_add_div_log 2)).div_const 2
  have hroot := hratio.sqrt
  have hsum := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hsqrt).add hroot
  have hnorm : Tendsto (fun t : ℝ => criticalInverse t /
      Real.sqrt (t * Real.log t)) atTop (𝓝 (Real.sqrt (1 / 2))) := by
    convert hsum.congr' ?_ using 1
    · norm_num
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have ht0 : 0 < t := by linarith
      have hl : 0 < Real.log t := Real.log_pos ht
      have harg : 0 ≤ (t + 2) * Real.log (t + 2) / 2 := by
        have := Real.log_pos (show 1 < t + 2 by linarith)
        positivity
      dsimp [criticalInverse]
      have hquot :
          Real.sqrt ((t + 2) / t * (Real.log (t + 2) / Real.log t) / 2) =
            Real.sqrt ((t + 2) * Real.log (t + 2) / 2) /
              Real.sqrt (t * Real.log t) := by
        rw [← Real.sqrt_div harg]
        congr 1
        field_simp
      rw [hquot, add_div]
  have h := hnorm.pow 2
  convert h.congr' ?_ using 1
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [div_pow, Real.sq_sqrt (mul_nonneg (by linarith) (Real.log_pos ht).le)]

/-- The explicit inverse tends to infinity. -/
theorem tendsto_criticalInverse : Tendsto criticalInverse atTop atTop := by
  have ht : Tendsto (fun t : ℝ => t + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hp := ht.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp ht)
  have hs := Real.tendsto_sqrt_atTop.comp (hp.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  exact tendsto_atTop_add_const_left atTop 1 hs

/-- The logarithm of the inverse has leading coefficient one half. -/
theorem tendsto_log_criticalInverse_div_log :
    Tendsto (fun t : ℝ => Real.log (criticalInverse t) / Real.log t)
      atTop (𝓝 (1 / 2)) := by
  have hsmall := (tendsto_criticalInverse_sq_div_mul_log.log
    (by norm_num : (1 / 2 : ℝ) ≠ 0)).div_atTop Real.tendsto_log_atTop
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop
  have h := ((hsmall.add (tendsto_const_nhds (x := (1 : ℝ)))).add hloglog).div_const 2
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    have hz : criticalInverse t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_criticalInverse t))
    dsimp
    rw [Real.log_div (pow_ne_zero 2 hz) (mul_ne_zero ht0.ne' hl),
      Real.log_pow, Real.log_mul ht0.ne' hl]
    field_simp
    ring

/-- Applying η to the concrete inverse gives ratio one at infinity. -/
theorem tendsto_eta_criticalInverse_div_self :
    Tendsto (fun t : ℝ => eta 2 quadraticScale (criticalInverse t) / t)
      atTop (𝓝 1) := by
  have hD := tendsto_criticalPrimitive_div_log.comp tendsto_criticalInverse
  have h := tendsto_criticalInverse_sq_div_mul_log.div
    (hD.mul tendsto_log_criticalInverse_div_log) (by norm_num : (1 : ℝ) * (1 / 2) ≠ 0)
  convert h.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hz : 0 < criticalInverse t := lt_of_lt_of_le zero_lt_one (one_le_criticalInverse t)
    have hD0 : criticalPrimitive (criticalInverse t) ≠ 0 := (criticalPrimitive_pos hz).ne'
    have hlz : Real.log (criticalInverse t) ≠ 0 :=
      (Real.log_pos (one_lt_criticalInverse ht0.le)).ne'
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    dsimp
    rw [eta_quadratic hz]
    field_simp

/-- Applying the concrete inverse to η gives ratio one at infinity. -/
theorem tendsto_criticalInverse_eta_div_self :
    Tendsto (fun t : ℝ => criticalInverse (eta 2 quadraticScale t) / t)
      atTop (𝓝 1) := by
  have h := ((tendsto_criticalInverse_sq_div_mul_log.comp tendsto_eta_quadratic).mul
    tendsto_eta_mul_log_div_sq).mul tendsto_log_eta_div_log
  have hs : Tendsto (fun t : ℝ => (criticalInverse (eta 2 quadraticScale t) / t) ^ 2)
      atTop (𝓝 1) := by
    convert h.congr' ?_ using 1
    · norm_num
    · filter_upwards [eventually_gt_atTop (1 : ℝ),
        tendsto_eta_quadratic.eventually_gt_atTop 1] with t ht he
      have ht0 : t ≠ 0 := ne_of_gt (by linarith)
      have he0 : eta 2 quadraticScale t ≠ 0 := ne_of_gt (by linarith)
      have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
      have hle : Real.log (eta 2 quadraticScale t) ≠ 0 := (Real.log_pos he).ne'
      dsimp
      field_simp
  have hroot := hs.sqrt
  convert hroot.congr' ?_ using 1
  · norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.sqrt_sq (div_nonneg (le_trans zero_le_one (one_le_criticalInverse _)) ht.le)]

/-- The concrete scale satisfies both compositions in the source's asymptotic inverse sense. -/
theorem criticalInverse_isAsymptoticInverse :
    IsAsymptoticInverse (eta 2 quadraticScale) criticalInverse :=
  ⟨tendsto_eta_criticalInverse_div_self, tendsto_criticalInverse_eta_div_self⟩

/-- All inverse-scale conditions in the Murugan–Saloff-Coste estimate hold for this concrete function. -/
theorem criticalInverse_isInverseScale : IsInverseScale 2 quadraticScale criticalInverse :=
  ⟨continuousOn_criticalInverse, monotoneOn_criticalInverse,
    fun t _ => one_le_criticalInverse t, criticalInverse_isAsymptoticInverse⟩

end

end LatticeProb.Graph.LongRangeKernel
