import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import LatticeProb.Bonanno.LQGMetric.Field.WholePlaneCov

/-!
# Circle averages of the whole-plane covariance kernel

For the whole-plane Gaussian free field with covariance kernel `wholePlaneCov`, normalised so that its average
over the unit circle vanishes (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Section 3.1, eq. (3.2)), this file computes the circle averages of the kernel: the logarithmic mean value property
`∮ log ‖w - z‖ = log max(r, ‖z‖)` on a circle centred at `0`, the circle average of `wholePlaneCov z ·`, and the
circle-circle covariance `∮_{∂B_s} ∮_{∂B_r} wholePlaneCov z w`.

References: Armitage–Gardiner, *Classical Potential Theory*, Springer 2001, Section 3.1 (logarithmic potential of a
circle); Duplantier–Sheffield, loc. cit.
-/

noncomputable section

namespace LatticeProb

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Average of `w ↦ log ‖w - z‖` over `∂B_r(0)`: the logarithmic mean value property, `log max(r, |z|)`
(Armitage–Gardiner, Section 3.1). -/
lemma circleAverage_log_norm_sub_eq {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r = Real.log (max r ‖z‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := (0 : ℂ)) (a := z) hr.ne'
  rw [h, zero_sub, norm_neg]
  rcases le_total ‖z‖ r with hz | hz
  · rw [max_eq_left hz]
    have hle : r⁻¹ * ‖z‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hr, mul_one]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = 0 := by
      unfold Real.posLog
      exact max_eq_left (Real.log_nonpos (by positivity) hle)
    rw [hpos, add_zero]
  · rw [max_eq_right hz]
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hr hz
    have h1 : 1 ≤ r⁻¹ * ‖z‖ := by
      rw [inv_mul_eq_div, one_le_div hr]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = Real.log (r⁻¹ * ‖z‖) := by
      unfold Real.posLog
      exact max_eq_right (Real.log_nonneg h1)
    rw [hpos, Real.log_mul (inv_ne_zero hr.ne') hz0.ne', Real.log_inv]
    ring

/-- The circle average of the covariance kernel `wholePlaneCov z ·` over `∂B_r(0)`, for every `z ∈ ℂ`
(Duplantier–Sheffield 2011, Section 3.1; the mean value property of `log |· - z|`). The point `w = z` of the
circle, where `wholePlaneCov` takes the junk value `0`, is a single point of the codiscrete filter and does not
contribute. -/
lemma circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r =
      Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log (max r ‖z‖) := by
  have hA : max ‖z‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hB : max r 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hgood : (Metric.sphere (0 : ℂ) |r| \ {z}) ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |r|) := by
    rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
    intro x _
    refine ⟨univ, univ_mem, (Set.finite_singleton z).subset ?_⟩
    rintro y ⟨-, hyS, hy⟩
    exact Set.mem_singleton_iff.mp (not_not.mp fun hne => hy ⟨hyS, hne⟩)
  have hcod : (fun w : ℂ => wholePlaneCov z w) =ᶠ[codiscreteWithin (Metric.sphere (0 : ℂ) |r|)]
      (fun w : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log ‖w - z‖) := by
    filter_upwards [hgood] with w hw
    obtain ⟨hwS, hwz⟩ := hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hwS
    have hwz' : ‖z - w‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact fun h => hwz (Set.mem_singleton_iff.mpr h.symm)
    unfold wholePlaneCov
    rw [hwS, Real.log_div (mul_ne_zero hA hB) hwz', Real.log_mul hA hB, norm_sub_rev]
  have h1 : CircleIntegrable (fun _ : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1)) 0 r := by
    unfold CircleIntegrable
    exact intervalIntegrable_const
  have h2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) 0 r :=
    circleIntegrable_log_norm_sub_const (c := (0 : ℂ)) (a := z) r
  rw [Real.circleAverage_congr_codiscreteWithin hcod hr.ne']
  have key := Real.circleAverage_fun_sub h1 h2
  beta_reduce at key
  rw [key, Real.circleAverage_const, circleAverage_log_norm_sub_eq hr z]

/-- The circle-circle covariance of the whole-plane GFF: the circle average over `∂B_s(0)` of the circle averages
of `wholePlaneCov · ` over `∂B_r(0)`, for `s ≠ r` (Duplantier–Sheffield 2011, eq. (3.2)). -/
lemma circleAverage_circleAverage_wholePlaneCov {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s =
      Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s) := by
  have hc : EqOn (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r)
      (fun _ : ℂ => Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s))
      (Metric.sphere (0 : ℂ) |s|) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hs] at hz
    dsimp only
    rw [circleAverage_wholePlaneCov hr z, hz]
  rw [Real.circleAverage_congr_sphere hc, Real.circleAverage_const]

end LatticeProb

end
