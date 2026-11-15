import LatticeProb.LQG.CoupledClockedStrictProduct
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-! # Strict sides for shifted cell windows -/

set_option autoImplicit false

open Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

namespace LatticeProb

/-- Strict cell windows for both coordinates give strict sides after translating
by the dimensionless phase multiplied by the mesh. -/
theorem sideStrict_shift_of_cellWindowStrict (w : Path2) {ε θ : ℝ} (hε : 0 < ε)
    (h : ∀ k : Fin 2, cellWindowStrict ε (lrCoordPath k w) θ) :
    RouteM.SideStrict ε
      ⟨fun t => w (t + ε * θ), w.continuous.comp (by fun_prop)⟩ := by
  intro q i j hij hside
  have hij' : (i : ℝ) + 1 < j := by exact_mod_cast hij
  have hab : ε * ((i : ℝ) - 1 + θ) ≤ ε * ((i : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have hbc : ε * ((i : ℝ) + θ) ≤ ε * ((j : ℝ) - 1 + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have hcd : ε * ((j : ℝ) - 1 + θ) ≤ ε * ((j : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith
  have hshift (f : ℝ → ℝ) (a b : ℝ) :
      (fun t => f (t + ε * θ)) '' Icc a b =
        f '' Icc (a + ε * θ) (b + ε * θ) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t + ε * θ, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t - ε * θ, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp⟩
  have hcoord := h (if q then 1 else 0) i j hij
  simp only [uIcc_of_le hab, uIcc_of_le hbc, uIcc_of_le hcd,
    lrCoordPath, lrCoord, ContinuousMap.coe_mk] at hcoord
  simp only [SideCond, intervalInf, ContinuousMap.coe_mk] at hside ⊢
  cases q <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcoord hside ⊢
  · rw [hshift (fun t => (w t).1), hshift (fun t => (w t).1),
      hshift (fun t => (w t).1)] at hside ⊢
    simp only [mul_add, mul_sub, mul_one] at hcoord hside ⊢
    exact hcoord hside
  · rw [hshift (fun t => (w t).2), hshift (fun t => (w t).2),
      hshift (fun t => (w t).2)] at hside ⊢
    simp only [mul_add, mul_sub, mul_one] at hcoord hside ⊢
    exact hcoord hside

end LatticeProb
