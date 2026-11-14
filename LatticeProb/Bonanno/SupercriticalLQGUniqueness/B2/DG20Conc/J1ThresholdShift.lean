/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1ThresholdShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1QuantileStep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_induction_parameter_shift {A₀ C T : ℝ}
    (hA₀ : 0 < A₀) (hC : 0 ≤ C) (K : ℕ)
    (hT : Real.exp ((A₀ + 5) * (C + 1) *
      Real.sqrt ((K : ℝ) + 1)) ≤ T) :
    let B := Real.exp (C * Real.sqrt (K : ℝ))
    3 < T / B ∧
    Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T / B := by
  dsimp
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  let y : ℝ := Real.sqrt (K : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    simpa using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ (K : ℝ) + 1 by positivity)
  have hyx : y ≤ x := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hB : 0 < Real.exp (C * y) := Real.exp_pos _
  have h3exp : (3 : ℝ) < Real.exp 5 := by
    have h := Real.add_one_le_exp (5 : ℝ)
    linarith
  have hsum : C * y + A₀ * (C + 1) * x + 5 ≤
      (A₀ + 5) * (C + 1) * x := by
    have hCy : C * y ≤ C * x := mul_le_mul_of_nonneg_left hyx hC
    nlinarith
  have hproduct : Real.exp (C * y) *
      Real.exp (A₀ * (C + 1) * x) * Real.exp 5 ≤ T := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr hsum).trans hT
  constructor
  · apply (lt_div_iff₀ hB).2
    have hfactor : (3 : ℝ) * Real.exp (C * y) <
        Real.exp (C * y) *
          Real.exp (A₀ * (C + 1) * x) * Real.exp 5 := by
      have hA : 1 ≤ Real.exp (A₀ * (C + 1) * x) :=
        Real.one_le_exp (by positivity)
      nlinarith [mul_pos hB (Real.exp_pos (A₀ * (C + 1) * x))]
    exact hfactor.trans_le hproduct
  · apply (le_div_iff₀ hB).2
    have h5 : 1 ≤ Real.exp 5 := by linarith
    have hsmall : Real.exp (A₀ * (C + 1) * x) *
        Real.exp (C * y) ≤
        Real.exp (C * y) * Real.exp (A₀ * (C + 1) * x) * Real.exp 5 := by
      have hp : 0 ≤ Real.exp (C * y) *
          Real.exp (A₀ * (C + 1) * x) := by positivity
      nlinarith
    exact hsmall.trans hproduct

end SupercriticalLQGUniqueness.B2.DG20Conc
