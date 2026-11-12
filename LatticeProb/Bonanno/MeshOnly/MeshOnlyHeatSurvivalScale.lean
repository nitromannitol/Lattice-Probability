/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatSurvivalScale at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The final scalar conversion from the two-term heat bound to the survival
bound on times at least mesh squared. -/

namespace BouRabeeGwynne.MeshOnlyHeat

lemma second_heat_term_le {d : ℕ} {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hscale : ε^2 ≤ t) :
    ε^d * t^(-(d : ℝ)) ≤ t^(-(d : ℝ)/2) := by
  have hb := Real.rpow_le_rpow (sq_nonneg ε) hscale
    (show 0 ≤ (d : ℝ)/2 by positivity)
  rw [← Real.rpow_two ε, ← Real.rpow_mul hε] at hb
  have he : (2 : ℝ) * ((d : ℝ)/2) = d := by ring
  rw [he, Real.rpow_natCast] at hb
  calc
    _ ≤ t^((d : ℝ)/2) * t^(-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht.le _)
    _ = _ := by
      rw [← Real.rpow_add ht]
      congr 1
      ring

lemma survival_bound_of_sq {d : ℕ} {ε t K M p : ℝ} (hε : 0 ≤ ε)
    (ht : 0 < t) (hscale : ε^2 ≤ t) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hsq : p^2 ≤ M * (K * (t^(-(d : ℝ)/2) + ε^d*t^(-(d : ℝ))))) :
    p ≤ Real.sqrt (2*K) * Real.sqrt M * t^(-(d : ℝ)/4) := by
  have htime := second_heat_term_le hε ht hscale (d := d)
  have hbound : p^2 ≤ M * (2*K*t^(-(d : ℝ)/2)) := by
    calc
      _ ≤ _ := hsq
      _ ≤ M * (K * (t^(-(d : ℝ)/2) + t^(-(d : ℝ)/2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl htime) hK) hM
      _ = _ := by ring
  have hp : (t^(-(d : ℝ)/4))^2 = t^(-(d : ℝ)/2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hrhs : (Real.sqrt (2*K) * Real.sqrt M * t^(-(d : ℝ)/4))^2 =
      M * (2*K*t^(-(d : ℝ)/2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hM, hp]
    ring
  have hpos : 0 ≤ Real.sqrt (2*K) * Real.sqrt M * t^(-(d : ℝ)/4) := by positivity
  nlinarith

end BouRabeeGwynne.MeshOnlyHeat
