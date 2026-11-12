/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyNashRate at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The two scalar dissipation regimes in Proposition 3.1. -/

namespace BouRabeeGwynne

/-- The defective Nash inequality forces one of two power-law dissipation
rates. In the application `p=1/d`, `X` is squared L² mass and `Q` is energy. -/
theorem defective_nash_min_rate {X Q C ε p : ℝ}
    (hX : 0 < X) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hε : 0 < ε)
    (hnash : X ^ (2 + 2 * p) ≤ C * Q * (X + ε ^ 2 * Q)) :
    min (X ^ (1 + 2 * p)) (X ^ (1 + p) / ε) ≤ (2 * C + 1) * Q := by
  by_cases hphase : ε ^ 2 * Q ≤ X
  · have hpow : X * X ^ (1 + 2 * p) = X ^ (2 + 2 * p) := by
      calc
        _ = X ^ (1 : ℝ) * X ^ (1 + 2 * p) := by rw [Real.rpow_one]
        _ = X ^ ((1 : ℝ) + (1 + 2 * p)) := (Real.rpow_add hX _ _).symm
        _ = _ := by congr 1; ring
    have hbound : X * X ^ (1 + 2 * p) ≤ X * (2 * C * Q) := by
      calc
        _ = X ^ (2 + 2 * p) := hpow
        _ ≤ C * Q * (X + ε ^ 2 * Q) := hnash
        _ ≤ C * Q * (2 * X) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hQ)
        _ = _ := by ring
    have hrate := le_of_mul_le_mul_left hbound hX
    exact (min_le_left _ _).trans (hrate.trans (by nlinarith))
  · have hphase' : X ≤ ε ^ 2 * Q := (lt_of_not_ge hphase).le
    have hpow : (X ^ (1 + p)) ^ 2 = X ^ (2 + 2 * p) := by
      calc
        _ = (X ^ (1 + p)) ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ = X ^ ((1 + p) * 2) := (Real.rpow_mul hX.le _ _).symm
        _ = _ := by congr 1; ring
    have hCbound : 2 * C ≤ (2 * C + 1) ^ 2 := by nlinarith [sq_nonneg C]
    have hbound : (X ^ (1 + p)) ^ 2 ≤ ((2 * C + 1) * ε * Q) ^ 2 := by
      calc
        _ = X ^ (2 + 2 * p) := hpow
        _ ≤ C * Q * (X + ε ^ 2 * Q) := hnash
        _ ≤ C * Q * (2 * (ε ^ 2 * Q)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hQ)
        _ = (2 * C) * (ε * Q) ^ 2 := by ring
        _ ≤ (2 * C + 1) ^ 2 * (ε * Q) ^ 2 :=
          mul_le_mul_of_nonneg_right hCbound (sq_nonneg _)
        _ = _ := by ring
    have hrate : X ^ (1 + p) ≤ (2 * C + 1) * ε * Q :=
      (sq_le_sq₀ (Real.rpow_nonneg hX.le _) (by positivity)).mp hbound
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ hε).mpr
    nlinarith

end BouRabeeGwynne
