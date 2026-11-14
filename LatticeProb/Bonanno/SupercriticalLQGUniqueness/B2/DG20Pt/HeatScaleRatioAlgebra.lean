/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleRatioAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleTransfer

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_scale_ratio_fine_first
    {r q ζ α β m₁ m₂ : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β) (hm₁ : 0 < m₁)
    (hlo : α * r ^ (1 - q + ζ) * m₂ ≤ m₁)
    (hhi : m₁ ≤ β * r ^ (1 - q - ζ) * m₂) :
    β⁻¹ * r ^ (q + ζ) ≤ r * m₂ / m₁ ∧
      r * m₂ / m₁ ≤ α⁻¹ * r ^ (q - ζ) := by
  have hpHi : r ^ (q + ζ) * r ^ (1 - q - ζ) = r := by
    convert dg20_rpow_complement hr (q + ζ) using 1 <;> ring
  have hpLo : r ^ (q - ζ) * r ^ (1 - q + ζ) = r := by
    convert dg20_rpow_complement hr (q - ζ) using 1 <;> ring
  constructor
  · apply (le_div_iff₀ hm₁).2
    calc
      (β⁻¹ * r ^ (q + ζ)) * m₁ ≤
          (β⁻¹ * r ^ (q + ζ)) * (β * r ^ (1 - q - ζ) * m₂) :=
        mul_le_mul_of_nonneg_left hhi
          (mul_nonneg (inv_pos.mpr hβ).le (Real.rpow_pos_of_pos hr _).le)
      _ = r * m₂ := by
        calc
          (β⁻¹ * r ^ (q + ζ)) * (β * r ^ (1 - q - ζ) * m₂) =
              (r ^ (q + ζ) * r ^ (1 - q - ζ)) * m₂ := by
            field_simp
          _ = r * m₂ := by rw [hpHi]
  · apply (div_le_iff₀ hm₁).2
    calc
      r * m₂ = (α⁻¹ * r ^ (q - ζ)) *
          (α * r ^ (1 - q + ζ) * m₂) := by
        calc
          r * m₂ = (r ^ (q - ζ) * r ^ (1 - q + ζ)) * m₂ := by rw [hpLo]
          _ = (α⁻¹ * r ^ (q - ζ)) *
              (α * r ^ (1 - q + ζ) * m₂) := by
            field_simp
      _ ≤ (α⁻¹ * r ^ (q - ζ)) * m₁ :=
        mul_le_mul_of_nonneg_left hlo
          (mul_nonneg (inv_pos.mpr hα).le (Real.rpow_pos_of_pos hr _).le)

theorem dg20_scale_ratio_coarse_first
    {r q ζ α β m₁ m₂ : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β) (hm₂ : 0 < m₂)
    (hlo : α * (r⁻¹) ^ (1 - q + ζ) * m₂ ≤ m₁)
    (hhi : m₁ ≤ β * (r⁻¹) ^ (1 - q - ζ) * m₂) :
    α * r ^ (q - ζ) ≤ r * m₁ / m₂ ∧
      r * m₁ / m₂ ≤ β * r ^ (q + ζ) := by
  have hpLo : r * (r⁻¹) ^ (1 - q + ζ) = r ^ (q - ζ) := by
    convert dg20_rpow_scale_inverse hr (1 - q + ζ) using 1 <;> ring
  have hpHi : r * (r⁻¹) ^ (1 - q - ζ) = r ^ (q + ζ) := by
    convert dg20_rpow_scale_inverse hr (1 - q - ζ) using 1 <;> ring
  constructor
  · apply (le_div_iff₀ hm₂).2
    calc
      (α * r ^ (q - ζ)) * m₂ =
          r * (α * (r⁻¹) ^ (1 - q + ζ) * m₂) := by
        rw [← hpLo]
        ring
      _ ≤ r * m₁ := mul_le_mul_of_nonneg_left hlo hr.le
  · apply (div_le_iff₀ hm₂).2
    calc
      r * m₁ ≤ r * (β * (r⁻¹) ^ (1 - q - ζ) * m₂) :=
        mul_le_mul_of_nonneg_left hhi hr.le
      _ = (β * r ^ (q + ζ)) * m₂ := by
        rw [← hpHi]
        ring

end SupercriticalLQGUniqueness.B2.DG20Pt
