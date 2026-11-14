/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseNormalized at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseMetricCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.LFPP

theorem j1_coarse_normalized_comparison
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (U E F : Set ℂ) (v : ℂ) (M : ℝ)
    (hosc : ∀ z ∈ U, |g z - g v| ≤ M) :
    crossLenIn ξ f U E F ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        (ENNReal.ofReal (Real.exp (-ξ * g v)) *
          crossLenIn ξ (fun z => g z + f z) U E F) ∧
    ENNReal.ofReal (Real.exp (-ξ * g v)) *
      (lfppContMetric ξ (fun z => g z + f z) (hg.add hf)).aroundDist U E F ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        (lfppContMetric ξ f hf).aroundDist U E F := by
  obtain ⟨hlow, _, _, hupp⟩ :=
    j1_coarse_cross_around_compare ξ hf hg U E F v M hosc
  have hfactor :
      ENNReal.ofReal (Real.exp (-ξ * g v + |ξ| * M)) =
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        ENNReal.ofReal (Real.exp (-ξ * g v)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  have hfactor' :
      ENNReal.ofReal (Real.exp (-ξ * g v)) *
        ENNReal.ofReal (Real.exp (ξ * g v + |ξ| * M)) =
      ENNReal.ofReal (Real.exp (|ξ| * M)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [hfactor, mul_assoc] at hlow
    exact hlow
  · calc
      ENNReal.ofReal (Real.exp (-ξ * g v)) *
          (lfppContMetric ξ (fun z => g z + f z) (hg.add hf)).aroundDist
            U E F ≤
        ENNReal.ofReal (Real.exp (-ξ * g v)) *
          (ENNReal.ofReal (Real.exp (ξ * g v + |ξ| * M)) *
            (lfppContMetric ξ f hf).aroundDist U E F) :=
          mul_le_mul_of_nonneg_left hupp (zero_le : (0 : ℝ≥0∞) ≤ _)
      _ = _ := by rw [← mul_assoc, hfactor']

end SupercriticalLQGUniqueness.B2.DG20Conc
