/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1BoundedRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockUnion

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_bounded_sqrt_range {A₀ C : ℝ}
    (hA₀ : 0 < A₀) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : ℕ) (hK : 1 ≤ K) (T : ℝ) (hT : 3 < T),
        T ≤ Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) →
        1 ≤ (5 : ℝ)^K * Real.exp (-c * (Real.log T)^2) := by
  let D : ℝ := A₀ * (C + 1)
  have hD : 0 < D := mul_pos hA₀ (by linarith)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 5 / (2 * D^2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro K hK T hT hTU
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hlogT : 0 ≤ Real.log T := (Real.log_pos (by linarith)).le
  have hlogTU : Real.log T ≤ D * x := by
    have h := Real.log_le_log (by linarith : 0 < T) hTU
    simpa [D, x] using h
  have hsq : (Real.log T)^2 ≤ D^2 * ((K : ℝ) + 1) := by
    have hx2 : x^2 = (K : ℝ) + 1 := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (D * x - Real.log T)]
  have hrate : c * (Real.log T)^2 ≤ (K : ℝ) * Real.log 5 := by
    have hsqmul := mul_le_mul_of_nonneg_left hsq hc.le
    have hcd : c * D^2 = Real.log 5 / 2 := by
      dsimp [c]
      field_simp
    rw [← mul_assoc, hcd] at hsqmul
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have h5 : (5 : ℝ)^K = Real.exp ((K : ℝ) * Real.log 5) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  rw [h5, ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Conc
