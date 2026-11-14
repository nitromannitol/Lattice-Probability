/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatScalePowerIdentities

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_scale_pair_transfer
    {G L U t aLo aHi m₁ m₂ l₁ l₂ : ℝ}
    (hG : 0 < G) (hL : 0 < L) (hU : 0 < U) (ht : 0 < t)
    (hcomp₁ : G⁻¹ * l₁ ≤ m₁ ∧ m₁ ≤ G * l₁)
    (hcomp₂ : G⁻¹ * l₂ ≤ m₂ ∧ m₂ ≤ G * l₂)
    (hpair : L * t ^ aLo * l₂ ≤ l₁ ∧ l₁ ≤ U * t ^ aHi * l₂) :
    (L / (G * G)) * t ^ aLo * m₂ ≤ m₁ ∧
      m₁ ≤ (G * G * U) * t ^ aHi * m₂ := by
  have hm₂l₂ : G⁻¹ * m₂ ≤ l₂ := by
    calc
      G⁻¹ * m₂ ≤ G⁻¹ * (G * l₂) :=
        mul_le_mul_of_nonneg_left hcomp₂.2 (inv_pos.mpr hG).le
      _ = l₂ := by field_simp
  have hl₂m₂ : l₂ ≤ G * m₂ := by
    calc
      l₂ = G * (G⁻¹ * l₂) := by field_simp
      _ ≤ G * m₂ := mul_le_mul_of_nonneg_left hcomp₂.1 hG.le
  constructor
  · calc
      (L / (G * G)) * t ^ aLo * m₂ =
          G⁻¹ * (L * t ^ aLo * (G⁻¹ * m₂)) := by
        field_simp
      _ ≤ G⁻¹ * (L * t ^ aLo * l₂) := by
        gcongr
      _ ≤ G⁻¹ * l₁ :=
        mul_le_mul_of_nonneg_left hpair.1 (inv_pos.mpr hG).le
      _ ≤ m₁ := hcomp₁.1
  · calc
      m₁ ≤ G * l₁ := hcomp₁.2
      _ ≤ G * (U * t ^ aHi * l₂) :=
        mul_le_mul_of_nonneg_left hpair.2 hG.le
      _ ≤ G * (U * t ^ aHi * (G * m₂)) := by gcongr
      _ = (G * G * U) * t ^ aHi * m₂ := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
