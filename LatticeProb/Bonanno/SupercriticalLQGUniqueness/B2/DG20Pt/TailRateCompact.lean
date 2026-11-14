/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.TailRateCompact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldAbsorbLarge

 




set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem tail_rate_compact_bound (c₀ c₁ H T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hH : 9 ≤ H)
    (hT : 3 < T) (hTH : T ≤ H) :
    let c₀' := (c₀ + 1) * Real.exp
      (c₁ * (Real.log H) ^ 2 * (1 + (Real.log (Real.log 3))⁻¹))
    0 < c₀' ∧ c₀ ≤ c₀' ∧
      1 ≤ c₀' * Real.exp (-c₁ * (Real.log T) ^ 2) ∧
      1 ≤ c₀' * Real.exp
        (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) := by
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 Real.exp_one_lt_three
  have hLL3 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hlogle : Real.log T ≤ Real.log H :=
    Real.log_le_log (by linarith) hTH
  have hsq : (Real.log T) ^ 2 ≤ (Real.log H) ^ 2 :=
    (sq_le_sq₀ hlogT hlogH).2 hlogle
  have hLLT : 0 < Real.log (Real.log T) := by
    have hlogT1 : 1 < Real.log T :=
      (Real.lt_log_iff_exp_lt (by linarith : 0 < T)).2
        (lt_trans Real.exp_one_lt_three hT)
    exact Real.log_pos hlogT1
  have hLLle : Real.log (Real.log 3) ≤ Real.log (Real.log T) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hT.le)
  let A : ℝ := c₁ * (Real.log H) ^ 2 * (1 + (Real.log (Real.log 3))⁻¹)
  let c₀' : ℝ := (c₀ + 1) * Real.exp A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc₀' : 0 < c₀' := by dsimp [c₀']; positivity
  have hcle : c₀ ≤ c₀' := by
    calc
      c₀ ≤ c₀ + 1 := by linarith
      _ ≤ (c₀ + 1) * Real.exp A :=
        le_mul_of_one_le_right (by linarith) (Real.one_le_exp hA)
  have hgauss : c₁ * (Real.log T) ^ 2 ≤ A := by
    calc
      c₁ * (Real.log T) ^ 2 ≤ c₁ * (Real.log H) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hc₁.le
      _ ≤ A := by
        dsimp [A]
        nlinarith [mul_nonneg (mul_nonneg hc₁.le (sq_nonneg (Real.log H)))
          (inv_nonneg.mpr hLL3.le)]
  have hloglog : c₁ * (Real.log T) ^ 2 /
      Real.log (Real.log T) ≤ A := by
    calc
      _ ≤ c₁ * (Real.log H) ^ 2 / Real.log (Real.log T) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq hc₁.le) hLLT.le
      _ ≤ c₁ * (Real.log H) ^ 2 / Real.log (Real.log 3) :=
        div_le_div_of_nonneg_left (by positivity) hLL3 hLLle
      _ ≤ A := by
        dsimp [A]
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg hc₁.le (sq_nonneg (Real.log H))]
  have hgeneral (q : ℝ) (hq : q ≤ A) :
      1 ≤ c₀' * Real.exp (-q) := by
    calc
      1 ≤ Real.exp (A - q) := Real.one_le_exp (sub_nonneg.mpr hq)
      _ ≤ (c₀ + 1) * Real.exp (A - q) :=
        le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith)
      _ = c₀' * Real.exp (-q) := by
        dsimp [c₀']
        rw [show A - q = A + -q by ring, Real.exp_add]
        ring
  dsimp
  refine ⟨hc₀', hcle, ?_, ?_⟩
  · simpa only [c₀', A, neg_mul] using hgeneral _ hgauss
  · simpa only [c₀', A, neg_div, neg_mul] using hgeneral _ hloglog

end SupercriticalLQGUniqueness.B2.DG20Pt
