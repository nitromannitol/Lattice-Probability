import LatticeProb.Topology.KnotInterpolation
import LatticeProb.Walk.CellConfigScaledAffine

/-!
# Time changes of cell walks

An interpolated cell walk agrees with any affine interpolation of the same
scaled representatives after an increasing change of time.
-/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- The jump clock after diffusive scaling. -/
def scaledJumpTime (H : CellConfig) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (ε : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ⟨(ε : ℝ) ^ 2 * H.jumpTime ω n, mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos n)⟩

/-- The scaled jump clock and any other affine clock through the same points
are related by an increasing time change. -/
theorem exists_orderIso_interpolatedWalk_eq
    (H : CellConfig) (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {ε : ℝ≥0} (hε : 0 < ε) (σ : ℕ → ℝ≥0)
    (hσ : StrictMono σ) (hσ0 : σ 0 = 0) (hσu : ∀ b, ∃ n, b < σ n)
    (g : ℝ≥0 → Plane)
    (hg : ∀ n t, σ n ≤ t → t < σ (n + 1) →
      g t = AffineMap.lineMap ((ε : ℝ) • p (ω n)) ((ε : ℝ) • p (ω (n + 1)))
        (((t : ℝ) - σ n) / ((σ (n + 1) : ℝ) - σ n))) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0,
      (∀ n, φ (scaledJumpTime H ω hpos ε n) = σ n) ∧
      ∀ t, (H.interpolatedWalk p ε ω) t = g (φ t) := by
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  have hτ : StrictMono (scaledJumpTime H ω hpos ε) := by
    intro a b hab
    apply NNReal.coe_lt_coe.mp
    exact mul_lt_mul_of_pos_left (H.jumpTime_strictMono hpos hab) he
  have hτ0 : scaledJumpTime H ω hpos ε 0 = 0 := by
    apply NNReal.coe_injective
    change (ε : ℝ) ^ 2 * H.jumpTime ω 0 = 0
    rw [H.jumpTime_zero ω, mul_zero]
  have hτu : ∀ b, ∃ n, b < scaledJumpTime H ω hpos ε n := by
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt ((b : ℝ) / (ε : ℝ) ^ 2)
    obtain ⟨n, hn⟩ := hunb N
    refine ⟨n, NNReal.coe_lt_coe.mp ?_⟩
    change (b : ℝ) < (ε : ℝ) ^ 2 * H.jumpTime ω n
    have hb : (b : ℝ) / (ε : ℝ) ^ 2 < H.jumpTime ω n := hN.trans hn
    exact (div_lt_iff₀ he).mp hb |>.trans_eq (mul_comm _ _)
  apply LatticeProb.KnotReparam.exists_orderIso_eq_of_affine_knots hτ hσ hτ0 hσ0 hτu hσu
    (fun n => (ε : ℝ) • p (ω n))
  · intro n t ht ht'
    exact interpolatedWalk_eq_lineMap_of_scaled_jumpTime H p ω hpos hunb hε t
      (NNReal.coe_le_coe.mpr ht) (NNReal.coe_le_coe.mpr ht'.le)
  · exact hg

end LatticeProb.CellConfigInterpolation

end
