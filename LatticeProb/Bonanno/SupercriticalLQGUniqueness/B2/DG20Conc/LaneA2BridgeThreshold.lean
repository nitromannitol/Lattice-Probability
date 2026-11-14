/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2BridgeThreshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Threshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneA2_lower_bridge_threshold {D B S T x y : ℝ}
    (hD : 0 < D) (hB : 0 < B) (hS : 0 < S) (hSsq : S ^ 2 = T)
    (hxy : x ≤ D ^ 3 * B ^ 4 * y) :
    (8 * D ^ 3 * B ^ 4 * T)⁻¹ * x ≤
      S⁻¹ * ((1 / 8 : ℝ) * S⁻¹ * y) := by
  have hDB : 0 < D ^ 3 * B ^ 4 := by positivity
  have hT : 0 < T := by rw [← hSsq]; positivity
  have hscaled : (D ^ 3 * B ^ 4)⁻¹ * x ≤ y := by
    calc
      (D ^ 3 * B ^ 4)⁻¹ * x ≤
          (D ^ 3 * B ^ 4)⁻¹ * (D ^ 3 * B ^ 4 * y) :=
        mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = y := by field_simp
  calc
    (8 * D ^ 3 * B ^ 4 * T)⁻¹ * x =
        (8 * T)⁻¹ * ((D ^ 3 * B ^ 4)⁻¹ * x) := by field_simp
    _ ≤ (8 * T)⁻¹ * y :=
      mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = S⁻¹ * ((1 / 8 : ℝ) * S⁻¹ * y) := by
      rw [← hSsq]
      field_simp

 

theorem laneA2_upper_bridge_threshold {D S T Λprev Λnow ℓprev ℓnow : ℝ}
    (hD : 0 ≤ D) (hS : 0 < S) (hSsq : S ^ 2 = T)
    (hΛ : Λprev ≤ Λnow) (hΛnow : 0 ≤ Λnow)
    (hℓprev : 0 ≤ ℓprev) (hℓnow : 0 ≤ ℓnow)
    (hℓ : ℓprev ≤ D * ℓnow) :
    S * ((1 / 8 : ℝ) * S * Λprev * ℓprev) ≤
      D * T * Λnow * ℓnow := by
  have hT : 0 ≤ T := by rw [← hSsq]; positivity
  have hchain : Λprev * ℓprev ≤ D * Λnow * ℓnow := by
    calc
      Λprev * ℓprev ≤ Λnow * ℓprev :=
        mul_le_mul_of_nonneg_right hΛ hℓprev
      _ ≤ Λnow * (D * ℓnow) :=
        mul_le_mul_of_nonneg_left hℓ hΛnow
      _ = D * Λnow * ℓnow := by ring
  have hnonneg : 0 ≤ D * T * Λnow * ℓnow := by positivity
  calc
    S * ((1 / 8 : ℝ) * S * Λprev * ℓprev) =
        (T / 8) * (Λprev * ℓprev) := by rw [← hSsq]; ring
    _ ≤ (T / 8) * (D * Λnow * ℓnow) :=
      mul_le_mul_of_nonneg_left hchain (by positivity)
    _ ≤ D * T * Λnow * ℓnow := by nlinarith [hnonneg]

end SupercriticalLQGUniqueness.B2.DG20Conc
