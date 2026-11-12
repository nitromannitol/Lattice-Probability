/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1Arith at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Up

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, "T"), T:1559–1563: "Given `A > 0`, we now choose `ε = A^{-b/√M}`"
so that the right side of (3.11) is `≥ A⁻¹ 𝔠_𝕣 e^{ξh_𝕣(0)}` and that of (3.12) `≤ A 𝔠_𝕣 e^{ξh_𝕣(0)}`.
Here `ε = A^{-β}` with `β = 1/(2(a + 6))`, `a = 2Λ + ξq` the exponent of (3.11)/(3.12) and `6`
the exponent of the circle count (`P31.card_circles_le`).
-/

noncomputable section

namespace LQGMetric.DFGPS

namespace P31

lemma step3_arith {a Bc C Λ A : ℝ} (ha : 0 ≤ a) (hBc : 1 ≤ Bc) (hC : 1 < C) (hΛ : 1 < Λ)
    (hA : (Bc * C * Λ) ^ 2 ≤ A) :
    0 < A ^ (-(1 / (2 * (a + 6)))) ∧ 1 ≤ A ∧
      A⁻¹ ≤ C⁻¹ * (Λ⁻¹ * (A ^ (-(1 / (2 * (a + 6))))) ^ a) ∧
      Bc / (A ^ (-(1 / (2 * (a + 6))))) ^ 6 *
        (C * (Λ * (A ^ (-(1 / (2 * (a + 6))))) ^ (-a))) ≤ A := by
  set β := 1 / (2 * (a + 6)) with hβ
  have hBCΛ : 1 ≤ Bc * C * Λ := by
    have : 1 ≤ C * Λ := by nlinarith
    nlinarith
  have hA1 : 1 ≤ A := le_trans (by nlinarith) hA
  have hA0 : 0 < A := by linarith
  set u := Real.sqrt A with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hA0
  have huu : u * u = A := Real.mul_self_sqrt hA0.le
  have hub : Bc * C * Λ ≤ u := by
    rw [hu, ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Bc * C * Λ)]
    exact Real.sqrt_le_sqrt hA
  have hCΛu : C * Λ ≤ u := le_trans (by nlinarith) hub
  have hurp : u = A ^ (1 / (2 : ℝ)) := by rw [hu, Real.sqrt_eq_rpow]
  have hβe : β * (a + 6) = 1 / 2 := by rw [hβ]; field_simp
  have hpow : ∀ x : ℝ, (A ^ (-β)) ^ x = A ^ (-β * x) := fun x => (Real.rpow_mul hA0.le _ _).symm
  refine ⟨Real.rpow_pos_of_pos hA0 _, hA1, ?_, ?_⟩
  · have h1 : u⁻¹ ≤ (A ^ (-β)) ^ a := by
      rw [hpow, hurp, ← Real.rpow_neg hA0.le]
      refine Real.rpow_le_rpow_of_exponent_le hA1 ?_
      have : β * a ≤ 1 / 2 := by
        rw [← hβe]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h2 : A⁻¹ ≤ C⁻¹ * (Λ⁻¹ * u⁻¹) := by
      rw [← huu, ← mul_assoc, ← mul_inv, ← mul_inv, mul_inv, mul_inv (C * Λ)]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hCΛu) (by positivity)
    refine h2.trans ?_
    gcongr
  · have e6 : (A ^ (-β)) ^ 6 = A ^ (-β * 6) := by
      rw [← hpow]; exact (Real.rpow_natCast _ 6).symm
    have key : (A ^ (-β)) ^ (-a) / (A ^ (-β)) ^ 6 = u := by
      rw [e6, hpow, ← Real.rpow_sub hA0, hurp]
      congr 1
      linarith
    calc Bc / (A ^ (-β)) ^ 6 * (C * (Λ * (A ^ (-β)) ^ (-a)))
        = Bc * C * Λ * ((A ^ (-β)) ^ (-a) / (A ^ (-β)) ^ 6) := by ring
      _ = Bc * C * Λ * u := by rw [key]
      _ ≤ u * u := mul_le_mul_of_nonneg_right hub hu0.le
      _ = A := huu

end P31

end LQGMetric.DFGPS
