/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateReal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistThreeRate

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistScaleRateReal (Cnet : ℕ) (a₀ a₁ b₀ b₁ D σ2 ζ T : ℝ)
    (k : ℕ) (t : ℝ) : ℝ :=
  let S := T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))
  (Cnet : ℝ) * (4 : ℝ) ^ k *
      (a₀ * Real.exp (-a₁ * (Real.log S) ^ 2 / Real.log (Real.log S)) +
       b₀ * Real.exp (-b₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) +
    D * (4 : ℝ) ^ k * Real.exp (-t ^ 2 / (2 * σ2))

theorem pt_dist_scale_rate_real_nonneg
    (Cnet : ℕ) {a₀ a₁ b₀ b₁ D σ2 ζ T : ℝ}
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D)
    (k : ℕ) (t : ℝ) :
    0 ≤ ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k t := by
  unfold ptDistScaleRateReal
  positivity

theorem pt_dist_scale_rate_eq_ofReal
    (Cnet : ℕ) {a₀ a₁ b₀ b₁ D σ2 ζ T : ℝ}
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D)
    (k : ℕ) (t : ℝ) :
    ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k t =
      ENNReal.ofReal (ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k t) := by
  simp [ptDistScaleRate, ptDistScaleRateReal,
    ENNReal.ofReal_mul, Nat.cast_mul, Nat.cast_pow,
    ha₀, hb₀, hD, mul_add, mul_assoc, mul_left_comm, mul_comm]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [ENNReal.ofReal_mul ha₀, ENNReal.ofReal_mul hb₀,
    ENNReal.ofReal_mul hD]
  simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ (Cnet : ℝ)),
    ENNReal.ofReal_natCast]
  simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ k),
    ENNReal.ofReal_pow (by norm_num : 0 ≤ (4 : ℝ)) k]
  norm_num

end SupercriticalLQGUniqueness.B2.DG20Pt
