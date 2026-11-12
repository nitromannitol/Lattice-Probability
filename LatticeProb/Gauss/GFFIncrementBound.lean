import Mathlib
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.Gauss.CircleAverageCovariance
import LatticeProb.Gauss.GFFCovSymm
import LatticeProb.Gauss.GFFCovPSD7

/-!
# The increment variance bound for circle averages, and existence of the whole-plane GFF

For the whole-plane covariance kernel `wholePlaneGFFCov` the covariance of two circle averages is given by the mean value
identity (Jensen's formula for the logarithmic potential; Duplantier-Sheffield, Section 3.1):
`Cov(h_r(z), h_s(w)) = A_r(z) + A_s(w) - avg_{x ∈ ∂B_r(z)} log max(s, |x - w|)`, where `A_r(z)` is the average of
`log max(|·|, 1)` over `∂B_r(z)`.

* the identity is `wholePlaneGFFCov_circle_circle_eq` (module `CircleAverageCovariance`).
* `wholePlaneGFFCov_circle_self_eq_sub_log`: the variance of a circle average, `2 A_r(z) - log r`.
* `wholePlaneGFFCov_circle_increment_le`: for `a ≤ r, s`, `Var(h_r(z) - h_s(w)) ≤ (|r - s| + 2 |z - w|) / a`.
* `wholePlaneGFF_increment_bound`: the kernel increment bound on the parameter space `ℝ × (Fin 2 → ℝ)` of circle
  observables, which is the Kolmogorov-Chentsov input of `exists_isWholePlaneGFF`.
* `exists_isWholePlaneGFF_proved`: a whole-plane GFF exists on a probability space in `Type`, without hypotheses.
-/

open MeasureTheory Filter Set Metric Topology
open LatticeProb.LQG.AffineDerived

namespace LatticeProb.Gauss

/-- The variance of a circle average: `Var(h_r(z)) = 2 A_r(z) - log r`, with `A_r(z)` the average of `logMaxAbs` on
`∂B_r(z)`. -/
theorem wholePlaneGFFCov_circle_self_eq_sub_log {r : ℝ} (hr : 0 < r) (z : ℂ) :
    wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle r z) =
      2 * Real.circleAverage logMaxAbs z r - Real.log r := by
  rw [wholePlaneGFFCov_circle_circle_eq hr r z z]
  unfold circlePairPotential
  have hEq : Set.EqOn (fun x : ℂ => Real.log (max r ‖x - z‖)) (fun _ : ℂ => Real.log r)
      (sphere z |r|) := by
    intro x hx
    have hx' : ‖x - z‖ = r := by
      have h := (mem_sphere_iff_norm).1 hx
      rwa [abs_of_pos hr] at h
    show Real.log (max r ‖x - z‖) = Real.log r
    rw [hx', max_self]
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]
  ring

/-- Variance of a difference of two circle averages: for `a ≤ r`, `a ≤ s`,
`Var(h_r(z) - h_s(w)) ≤ 2 log(max r s + |z - w|) - log r - log s ≤ (|r - s| + 2 |z - w|) / a`. The covariance of the
difference is `K_rr + K_ss - 2 K_rs`; the averages `A_r(z)`, `A_s(w)` cancel, and the cross term is
`avg_{x ∈ ∂B_r(z)} log max(s, |x - w|) ≤ log (max r s + |z - w|)` since `|x - w| ≤ r + |z - w|` on `∂B_r(z)`. -/
theorem wholePlaneGFFCov_circle_increment_le {a r s : ℝ} (ha : 0 < a) (har : a ≤ r) (has : a ≤ s)
    (z w : ℂ) :
    wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle r z)
      + wholePlaneGFFCov (GFFObservable.circle s w) (GFFObservable.circle s w)
      - 2 * wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle s w)
      ≤ (|r - s| + 2 * ‖z - w‖) / a := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have hs : 0 < s := lt_of_lt_of_le ha has
  rw [wholePlaneGFFCov_circle_self_eq_sub_log hr z, wholePlaneGFFCov_circle_self_eq_sub_log hs w,
    wholePlaneGFFCov_circle_circle_eq hs r z w]
  unfold circlePairPotential
  have hcLog : Continuous (fun x : ℂ => Real.log (max s ‖x - w‖)) :=
    continuous_log_max_norm_sub hs w
  have hML : Real.circleAverage (fun x : ℂ => Real.log (max s ‖x - w‖)) z r
      ≤ Real.log (max r s + ‖z - w‖) := by
    have hmono := Real.circleAverage_mono hcLog.continuousOn.circleIntegrable'
      continuous_const.continuousOn.circleIntegrable'
      (f₂ := fun _ : ℂ => Real.log (max r s + ‖z - w‖))
      (fun x hx => by
        have hx' : ‖x - z‖ = r := by
          have h := (mem_sphere_iff_norm).1 hx
          rwa [abs_of_pos hr] at h
        have h1 : ‖x - w‖ ≤ r + ‖z - w‖ := by
          have e : x - w = (x - z) + (z - w) := by ring
          rw [e]
          exact (norm_add_le _ _).trans (by rw [hx'])
        have h2 : max s ‖x - w‖ ≤ max r s + ‖z - w‖ :=
          max_le (by linarith [le_max_right r s, norm_nonneg (z - w)])
            (by linarith [le_max_left r s])
        exact Real.log_le_log (lt_of_lt_of_le hs (le_max_left _ _)) h2)
    rw [Real.circleAverage_const] at hmono
    exact hmono
  have key := two_log_max_add_sub_log_le ha har has (norm_nonneg (z - w))
  linarith

/-- The circle observable of a parameter point. -/
lemma ptObs_eq_circle {p : ℝ × (Fin 2 → ℝ)} (hp : 0 < p.1) :
    ptObs p = GFFObservable.circle p.1 (cplxOf p.2) := by
  simp [ptObs, hp]

/-- `‖cplxOf v - cplxOf u‖ ≤ 2 dist (r, v) (s, u)` for the centre components in the sup norm. -/
lemma norm_cplxOf_sub_le (p q : ℝ × (Fin 2 → ℝ)) :
    ‖cplxOf p.2 - cplxOf q.2‖ ≤ 2 * dist p q := by
  have hd0 : dist (p.2 0) (q.2 0) ≤ dist p q :=
    (dist_le_pi_dist p.2 q.2 0).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  have hd1 : dist (p.2 1) (q.2 1) ≤ dist p q :=
    (dist_le_pi_dist p.2 q.2 1).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  rw [Real.dist_eq] at hd0 hd1
  have hre : |(cplxOf p.2 - cplxOf q.2).re| ≤ dist p q := by
    simpa [cplxOf] using hd0
  have him : |(cplxOf p.2 - cplxOf q.2).im| ≤ dist p q := by
    simpa [cplxOf] using hd1
  calc ‖cplxOf p.2 - cplxOf q.2‖
      ≤ |(cplxOf p.2 - cplxOf q.2).re| + |(cplxOf p.2 - cplxOf q.2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * dist p q := by linarith

/-- **The kernel increment bound** on circle parameters: the hypothesis `hvarK` of `exists_isWholePlaneGFF`. -/
theorem wholePlaneGFF_increment_bound :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℝ × (Fin 2 → ℝ), a ≤ p.1 → a ≤ q.1 →
      wholePlaneGFFCov (ptObs p) (ptObs p) + wholePlaneGFFCov (ptObs q) (ptObs q)
        - 2 * wholePlaneGFFCov (ptObs p) (ptObs q) ≤ C * dist p q := by
  intro a ha
  refine ⟨5 / a, by positivity, fun p q hp hq => ?_⟩
  have hp0 : 0 < p.1 := lt_of_lt_of_le ha hp
  have hq0 : 0 < q.1 := lt_of_lt_of_le ha hq
  rw [ptObs_eq_circle hp0, ptObs_eq_circle hq0]
  have h := wholePlaneGFFCov_circle_increment_le ha hp hq (cplxOf p.2) (cplxOf q.2)
  refine h.trans ?_
  have h1 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_left _ _
  have h2 := norm_cplxOf_sub_le p q
  have hsum : |p.1 - q.1| + 2 * ‖cplxOf p.2 - cplxOf q.2‖ ≤ 5 * dist p q := by linarith
  calc (|p.1 - q.1| + 2 * ‖cplxOf p.2 - cplxOf q.2‖) / a
      ≤ (5 * dist p q) / a := div_le_div_of_nonneg_right hsum ha.le
    _ = 5 / a * dist p q := by ring

/-- **Existence of the whole-plane GFF.** There is a probability space in `Type` carrying a whole-plane GFF
(pairings `hC` and circle averages `hcirc`). -/
theorem exists_isWholePlaneGFF_proved :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc :=
  exists_isWholePlaneGFF_of_psd wholePlaneCovPSD_proved wholePlaneGFF_increment_bound

end LatticeProb.Gauss
