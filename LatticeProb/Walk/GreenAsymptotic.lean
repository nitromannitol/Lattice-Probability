import Mathlib
import LatticeProb.Walk.GaussTimeIntegral

/-!
# The asymptotics of the Green function of the simple random walk, `d ≥ 3`

`G(x) = 2/((d - 2) ω_d) |x|^{2-d} + O(|x|^{-d})`, where `ω_d` is the volume of the unit ball of
`ℝ^d` (Lawler–Limic, *Random Walk: A Modern Introduction*, Theorem 4.3.1). The proof writes
`G(x) = ∫_0^∞ q_t(x) dt` for the continuous-time kernel `q_t`, whose Gaussian counterpart
integrates exactly to the main term; the difference is the local limit error integrated over
`t ≥ 1`, and the times `t ≤ 1` contribute an exponentially small amount.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb

open ContinuousTime

/-- **The Green function asymptotics** (Lawler–Limic, Theorem 4.3.1): for `d ≥ 3`,
`|G(x) - 2/((d - 2) ω_d) |x|^{2-d}| ≤ C |x|^{-d}` for `|x| ≥ 1`, where `ω_d` is the volume
of the unit ball. The Green function is the time integral of the continuous-time kernel,
whose Gaussian part integrates to the main term; the rest is split at time one. -/
theorem exists_abs_srwGreenInf_sub_le {d : ℕ} (hd : 3 ≤ d) :
    ∃ C R : ℝ, 1 ≤ R ∧ ∀ x : Site d, R ≤ euclidNorm x →
      |srwGreenInf d x
          - 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
            * euclidNorm x ^ (2 - (d : ℝ))|
        ≤ C * euclidNorm x ^ (-(d : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_integral_ctHeat_sub_ctGauss_le hd1
  obtain ⟨C₃, hC₃, h₃⟩ := exists_ctGauss_le hd1
  refine ⟨Real.exp 1 * (2 ^ d * d.factorial) + C₃ + C₁, 1, le_rfl, fun x hx => ?_⟩
  set r := euclidNorm x with hr
  have hr0 : 0 < r := by linarith
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [hr] at hr0
  have hgnn : ∀ t, 0 ≤ ctGauss d t x := fun t =>
    Finset.prod_nonneg fun i _ => by unfold lineGauss; positivity
  have hg0 := integrableOn_ctGauss hd hx0
  have hgI : IntegrableOn (fun t => ctGauss d t x) (Set.Ioc 0 1) :=
    hg0.mono_set Set.Ioc_subset_Ioi_self
  have hqI : IntegrableOn (fun t => ctHeat d t x) (Set.Ioc 0 1) :=
    (continuous_ctHeat x).integrableOn_Ioc
  have hdI1 := integrableOn_ctHeat_sub_ctGauss hd1 x
  have hq1 : IntegrableOn (fun t => ctHeat d t x) (Set.Ioi 1) :=
    (hdI1.add (hg0.mono_set (Set.Ioi_subset_Ioi zero_le_one))).congr_fun
      (fun t _ => by simp) measurableSet_Ioi
  have hq0 : IntegrableOn (fun t => ctHeat d t x) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hqI.union hq1
  -- the difference as the integral of the kernel difference, split at time one
  have hdiff : srwGreenInf d x
      - 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
        * r ^ (2 - (d : ℝ))
      = ((∫ t in Set.Ioc 0 1, ctHeat d t x) - ∫ t in Set.Ioc 0 1, ctGauss d t x)
        + ∫ t in Set.Ioi 1, (ctHeat d t x - ctGauss d t x) := by
    rw [srwGreenInf_eq_integral_ctHeat hd, hr, ← integral_ctGauss hd hx0,
      ← integral_sub hq0 hg0, ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (f := fun t => ctHeat d t x - ctGauss d t x)
        (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hqI.sub hgI) hdI1,
      integral_sub hqI hgI]
  -- the three pieces
  have hsmall : ‖∫ t in Set.Ioc 0 1, ctHeat d t x‖
      ≤ Real.exp 1 * (2 ^ d * d.factorial) * r ^ (-(d : ℝ)) := by
    refine (norm_integral_Ioc_ctHeat_le hd1 x).trans ?_
    rw [mul_assoc]
    gcongr
    exact exp_neg_half_le_rpow hr0 d
  have hgauss : ‖∫ t in Set.Ioc 0 1, ctGauss d t x‖ ≤ C₃ * r ^ (-(d : ℝ)) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
      (f := fun t => ctGauss d t x) (C := C₃ * r ^ (-(d : ℝ)))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
        exact h₃ t ht.1 x hx0)
    simpa [Measure.real, Real.volume_Ioc] using h
  rw [hdiff, ← Real.norm_eq_abs]
  calc _ ≤ ‖(∫ t in Set.Ioc 0 1, ctHeat d t x) - ∫ t in Set.Ioc 0 1, ctGauss d t x‖
        + ‖∫ t in Set.Ioi 1, (ctHeat d t x - ctGauss d t x)‖ := norm_add_le _ _
    _ ≤ (‖∫ t in Set.Ioc 0 1, ctHeat d t x‖ + ‖∫ t in Set.Ioc 0 1, ctGauss d t x‖)
        + ‖∫ t in Set.Ioi 1, (ctHeat d t x - ctGauss d t x)‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (Real.exp 1 * (2 ^ d * d.factorial) * r ^ (-(d : ℝ)) + C₃ * r ^ (-(d : ℝ)))
        + C₁ * r ^ (-(d : ℝ)) := by
        gcongr
        exact h₁ x hx
    _ = _ := by ring

end LatticeProb
