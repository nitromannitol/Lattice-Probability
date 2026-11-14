/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianRate

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_point_gaussian_sum
    (ξ L β : ℝ) (hξ : 0 < ξ) (hL : 0 ≤ L) (hβ : 0 < β)
    (n : ℕ) :
    let a := β / (2 * ξ ^ 2 * Real.log 2)
    let q := Real.exp (-a * β)
    ∑ k ∈ Finset.Icc 1 n, 2 * Real.exp
      (-((L + β * (k : ℝ)) / ξ) ^ 2 /
        (2 * ((k : ℝ) * Real.log 2))) ≤
      2 * Real.exp (-a * L) * (q / (1 - q)) := by
  dsimp
  let a : ℝ := β / (2 * ξ ^ 2 * Real.log 2)
  let q : ℝ := Real.exp (-a * β)
  have ha : 0 < a := by dsimp [a]; positivity
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos ha hβ])
  have hstep (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      2 * Real.exp
        (-((L + β * (k : ℝ)) / ξ) ^ 2 /
          (2 * ((k : ℝ) * Real.log 2))) ≤
      2 * Real.exp (-a * L) * q ^ k := by
    have hr := pt_dist_point_gaussian_rate_linear ξ L β k hξ hL hβ
      (Finset.mem_Icc.mp hk).1
    have he : Real.exp (-a * (L + β * (k : ℝ))) =
        Real.exp (-a * L) * q ^ k := by
      rw [show -a * (L + β * (k : ℝ)) = -a * L + (k : ℝ) * (-a * β) by ring,
        Real.exp_add, Real.exp_nat_mul]
    have hr' : a * (L + β * (k : ℝ)) ≤
        ((L + β * (k : ℝ)) / ξ) ^ 2 /
          (2 * ((k : ℝ) * Real.log 2)) := by
      simpa only [a] using hr
    have hneg : -((L + β * (k : ℝ)) / ξ) ^ 2 /
        (2 * ((k : ℝ) * Real.log 2)) ≤
        -a * (L + β * (k : ℝ)) := by
      simpa only [neg_div, neg_mul] using neg_le_neg hr'
    calc
      _ ≤ 2 * Real.exp (-a * (L + β * (k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg)
        norm_num
      _ = _ := by rw [he]; ring
  have hgeom : ∑ k ∈ Finset.Icc 1 n, q ^ k ≤ q / (1 - q) := by
    simpa only [Finset.Ico_add_one_right_eq_Icc, pow_one] using
      (geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) hq0 hq1)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
      2 * Real.exp (-a * L) * q ^ k := Finset.sum_le_sum hstep
    _ = 2 * Real.exp (-a * L) *
      (∑ k ∈ Finset.Icc 1 n, q ^ k) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp (-a * L) * (q / (1 - q)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)

theorem pt_dist_point_field_uniform_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ L β : ℝ) (hξ : 0 < ξ) (hL : 0 ≤ L) (hβ : 0 < β)
    (n : ℕ) (z : ℂ) :
    let a := β / (2 * ξ ^ 2 * Real.log 2)
    let q := Real.exp (-a * β)
    P (ptDistPointFieldGood P W ξ L β n z)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-a * L) * (q / (1 - q))) := by
  dsimp
  have htail := pt_dist_point_field_finite_tail P W hW ξ L β hξ hL hβ.le n z
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ENNReal.ofReal (2 * Real.exp
      (-((L + β * (k : ℝ)) / ξ) ^ 2 /
        (2 * ((k : ℝ) * Real.log 2)))) := htail
    _ = ENNReal.ofReal (∑ k ∈ Finset.Icc 1 n,
      2 * Real.exp
        (-((L + β * (k : ℝ)) / ξ) ^ 2 /
          (2 * ((k : ℝ) * Real.log 2)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (pt_dist_point_gaussian_sum ξ L β hξ hL hβ n)

end SupercriticalLQGUniqueness.B2.DG20Pt
