/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1TwoRateAbsorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_two_rate_absorb (K : ℕ)
    (CN Cg f g r : ℝ)
    (hCN : 0 ≤ CN) (hCg : 0 ≤ Cg)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hfr : f ≤ r) (hgr : g ≤ r) :
    ENNReal.ofReal ((5 : ℝ)^K) * ENNReal.ofReal (CN * f) +
      ENNReal.ofReal (Cg * 4^K * g) ≤
      ENNReal.ofReal ((CN + Cg) * (5 : ℝ)^K * r) := by
  have h45 : (4 : ℝ)^K ≤ (5 : ℝ)^K := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : 4 ≤ 5) K
  have hp4 : 0 ≤ (4 : ℝ)^K := by positivity
  have hp5 : 0 ≤ (5 : ℝ)^K := by positivity
  have hreal : (5 : ℝ)^K * (CN * f) + Cg * 4^K * g ≤
      (CN + Cg) * (5 : ℝ)^K * r := by
    have hf' : CN * f ≤ CN * r := mul_le_mul_of_nonneg_left hfr hCN
    have hg' : Cg * 4^K * g ≤ Cg * (5 : ℝ)^K * r := by
      have hpow : Cg * 4^K ≤ Cg * (5 : ℝ)^K :=
        mul_le_mul_of_nonneg_left h45 hCg
      calc
        Cg * 4^K * g ≤ Cg * 4^K * r :=
          mul_le_mul_of_nonneg_left hgr (mul_nonneg hCg hp4)
        _ ≤ Cg * (5 : ℝ)^K * r :=
          mul_le_mul_of_nonneg_right hpow hr
    nlinarith [mul_le_mul_of_nonneg_left hf' hp5, hg']
  rw [← ENNReal.ofReal_mul hp5,
    ← ENNReal.ofReal_add (mul_nonneg hp5 (mul_nonneg hCN hf))
      (by positivity : 0 ≤ Cg * 4^K * g)]
  exact ENNReal.ofReal_le_ofReal hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
