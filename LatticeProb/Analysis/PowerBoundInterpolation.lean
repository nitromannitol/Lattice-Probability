import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Interpolation of power bounds -/

namespace LatticeProb

/-- Two bounds with opposing powers of a positive parameter give a bound
independent of that parameter. -/
theorem le_interpolated_power_bound {x A B d r a b k : ℝ}
    (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d) (hr : 0 ≤ r)
    (ha : 0 < a) (hb : 0 < b)
    (h₁ : x ≤ A * d ^ a) (h₂ : x ≤ B * d ^ (-b) * r ^ k) :
    x ≤ A ^ (b / (a + b)) * B ^ (a / (a + b)) * r ^ (k * (a / (a + b))) := by
  have hab : 0 < a + b := add_pos ha hb
  have hu : 0 ≤ b / (a + b) := div_nonneg hb.le hab.le
  have ht : 0 ≤ a / (a + b) := div_nonneg ha.le hab.le
  have hsum : b / (a + b) + a / (a + b) = 1 := by field_simp; ring
  have hcancel : a * (b / (a + b)) + -b * (a / (a + b)) = 0 := by ring
  have hfirst := Real.rpow_le_rpow hx h₁ hu
  have hsecond := Real.rpow_le_rpow hx h₂ ht
  have hprod := mul_le_mul hfirst hsecond (Real.rpow_nonneg hx _) (Real.rpow_nonneg (mul_nonneg hA (Real.rpow_nonneg hd.le _)) _)
  rw [← Real.rpow_add_of_nonneg hx hu ht, hsum, Real.rpow_one] at hprod
  rw [Real.mul_rpow hA (Real.rpow_nonneg hd.le _),
    Real.mul_rpow (mul_nonneg hB (Real.rpow_nonneg hd.le _)) (Real.rpow_nonneg hr _),
    Real.mul_rpow hB (Real.rpow_nonneg hd.le _),
    ← Real.rpow_mul hd.le, ← Real.rpow_mul hd.le, ← Real.rpow_mul hr] at hprod
  have hpow : d ^ (a * (b / (a + b))) * d ^ (-b * (a / (a + b))) = 1 := by
    rw [← Real.rpow_add hd, hcancel, Real.rpow_zero]
  calc
    x ≤ (A ^ (b / (a + b)) * d ^ (a * (b / (a + b)))) *
        ((B ^ (a / (a + b)) * d ^ (-b * (a / (a + b)))) *
          r ^ (k * (a / (a + b)))) := hprod
    _ = A ^ (b / (a + b)) * B ^ (a / (a + b)) * r ^ (k * (a / (a + b))) := by
      calc
        _ = (A ^ (b / (a + b)) * B ^ (a / (a + b)) * r ^ (k * (a / (a + b)))) *
            (d ^ (a * (b / (a + b))) * d ^ (-b * (a / (a + b)))) := by ring
        _ = _ := by rw [hpow, mul_one]

end LatticeProb
