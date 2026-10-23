import LatticeProb.Graph.LongRangeKernel.Scale

/-!
# The critical quadratic jump scale

The primitive of `s / (1+s)²` determines the critical integral scale. The inverse-scale
candidate includes the factor `1 / √2` required for asymptotic equivalence, rather than
only equivalence up to constants.
-/

namespace LatticeProb.Graph.LongRangeKernel

open Filter Topology MeasureTheory

noncomputable section

/-- The quadratic jump scale, with its required value one at the origin. -/
def quadraticScale (r : ℝ) : ℝ := (1 + r) ^ 2

/-- The explicit logarithmic primitive of the critical integrand. -/
def criticalPrimitive (r : ℝ) : ℝ := Real.log (1 + r) + (1 + r)⁻¹ - 1

/-- A continuous nondecreasing candidate for the critical asymptotic inverse. -/
def criticalInverse (t : ℝ) : ℝ :=
  1 + Real.sqrt ((t + 2) * Real.log (t + 2) / 2)

/-- The quadratic scale has the range prescribed by the source on nonnegative radii. -/
theorem one_le_quadraticScale {r : ℝ} (hr : 0 ≤ r) : 1 ≤ quadraticScale r := by
  dsimp [quadraticScale]
  nlinarith

/-- The quadratic jump scale is continuous. -/
theorem continuous_quadraticScale : Continuous quadraticScale := by
  unfold quadraticScale
  fun_prop

/-- The critical integral is an elementary logarithmic primitive at every positive radius. -/
theorem integral_critical {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r, s / (1 + s) ^ 2) = criticalPrimitive r := by
  have hderiv : ∀ s ∈ Set.uIcc 0 r,
      HasDerivAt criticalPrimitive (s / (1 + s) ^ 2) s := by
    intro s hs
    rw [Set.uIcc_of_le hr] at hs
    have hs0 : 0 ≤ s := hs.1
    have hne : 1 + s ≠ 0 := by linarith
    have hlog := ((hasDerivAt_id s).const_add 1).log hne
    have hinv := ((hasDerivAt_id s).const_add 1).inv hne
    convert (hlog.add hinv).sub_const 1 using 1 <;>
      (try dsimp only [id_eq]) <;> first | rfl | (field_simp [hne]; ring)
  have hcont : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.uIcc 0 r) := by
    refine continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro s hs
    rw [Set.uIcc_of_le hr] at hs
    have hs0 : 0 ≤ s := hs.1
    positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simpa only [criticalPrimitive, add_zero, Real.log_one, inv_one, sub_self,
    zero_add, sub_zero] using h

/-- At a positive radius, η is exactly `r² / (log(1+r) + (1+r)⁻¹ - 1)`. -/
theorem eta_quadratic {r : ℝ} (hr : 0 < r) :
    eta 2 quadraticScale r = r ^ 2 / criticalPrimitive r := by
  rw [eta, if_neg hr.ne']
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, quadraticScale]
  rw [integral_critical hr.le]

/-- The proposed inverse is continuous on the source half-line. -/
theorem continuousOn_criticalInverse : ContinuousOn criticalInverse (Set.Ici 0) := by
  unfold criticalInverse
  refine continuousOn_const.add (ContinuousOn.sqrt ?_)
  refine ((continuousOn_id.add continuousOn_const).mul
    ((continuousOn_id.add continuousOn_const).log ?_)).div_const 2
  intro t ht
  have ht0 : 0 ≤ t := ht
  change t + 2 ≠ 0
  linarith

/-- The proposed inverse is nondecreasing on the source half-line. -/
theorem monotoneOn_criticalInverse : MonotoneOn criticalInverse (Set.Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hlog : Real.log (a + 2) ≤ Real.log (b + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (a + 2) := Real.log_nonneg (by linarith)
  unfold criticalInverse
  gcongr

/-- The proposed inverse takes values in `[1,∞)`. -/
theorem one_le_criticalInverse (t : ℝ) : 1 ≤ criticalInverse t := by
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- At nonnegative arguments the explicit inverse is strictly greater than one. -/
theorem one_lt_criticalInverse {t : ℝ} (ht : 0 ≤ t) : 1 < criticalInverse t := by
  have hl : 0 < Real.log (t + 2) := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt ((t + 2) * Real.log (t + 2) / 2) :=
    Real.sqrt_pos.2 (by positivity)
  exact lt_add_of_pos_right 1 hs

/-- The primitive is strictly positive at positive radii, so η has a genuine denominator. -/
theorem criticalPrimitive_pos {r : ℝ} (hr : 0 < r) : 0 < criticalPrimitive r := by
  rw [← integral_critical hr.le]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro s hs
    rw [Set.uIcc_of_le hr.le] at hs
    have hs0 : 0 ≤ s := hs.1
    positivity
  · intro s hs
    exact div_pos hs.1 (sq_pos_of_pos (by linarith [hs.1]))
  · exact hr

/-- The explicit inverse has the critical square-root-log growth, uniformly down to zero. -/
theorem criticalInverse_comparison {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt ((t + 1) * Real.log (t + 2)) / Real.sqrt 2 ≤ criticalInverse t ∧
      criticalInverse t ≤
        (1 + (Real.sqrt (Real.log 2))⁻¹) *
          Real.sqrt ((t + 1) * Real.log (t + 2)) := by
  have hlog : 0 < Real.log (t + 2) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hslog : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2
  have hbase : Real.sqrt (Real.log 2) ≤
      Real.sqrt ((t + 1) * Real.log (t + 2)) := by
    apply Real.sqrt_le_sqrt
    have hl : Real.log 2 ≤ Real.log (t + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    nlinarith
  have hlower : Real.sqrt ((t + 1) * Real.log (t + 2)) / Real.sqrt 2 ≤
      Real.sqrt ((t + 2) * Real.log (t + 2) / 2) := by
    rw [← Real.sqrt_div (mul_nonneg (by linarith) hlog.le)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hupper : Real.sqrt ((t + 2) * Real.log (t + 2) / 2) ≤
      Real.sqrt ((t + 1) * Real.log (t + 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hone : 1 ≤ (Real.sqrt (Real.log 2))⁻¹ *
      Real.sqrt ((t + 1) * Real.log (t + 2)) := by
    rw [inv_mul_eq_div, le_div_iff₀ hslog]
    simpa only [one_mul] using hbase
  constructor
  · exact hlower.trans (le_add_of_nonneg_left (by norm_num))
  · unfold criticalInverse
    calc
      1 + Real.sqrt ((t + 2) * Real.log (t + 2) / 2)
          ≤ (Real.sqrt (Real.log 2))⁻¹ *
              Real.sqrt ((t + 1) * Real.log (t + 2)) +
              Real.sqrt ((t + 1) * Real.log (t + 2)) := add_le_add hone hupper
      _ = _ := by ring

end

end LatticeProb.Graph.LongRangeKernel
