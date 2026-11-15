import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingWirt

/-! # Sharp Dirichlet inequality on an interval -/

set_option autoImplicit false

open MeasureTheory Set
open scoped Real

namespace LatticeProb

/-- Sharp one-dimensional Dirichlet inequality on an interval of positive length. -/
theorem dirichlet_interval_inequality {f f' : ℝ → ℝ} {a θ : ℝ} (hθ : 0 < θ)
    (hd : ∀ x ∈ Icc a (a + θ), HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc a (a + θ)))
    (ha : f a = 0) (hb : f (a + θ) = 0) :
    (∫ x in a..a + θ, f x ^ 2) ≤
      (θ / Real.pi) ^ 2 * (∫ x in a..a + θ, f' x ^ 2) := by
  let c : ℝ := θ / (2 * Real.pi)
  have hcpos : 0 < c := div_pos hθ (by positivity)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcend : c * (2 * Real.pi) = θ := by
    dsimp [c]
    field_simp
  have hmap : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), a + c * t ∈ Icc a (a + θ) := by
    intro t ht
    constructor
    · nlinarith [mul_nonneg hcpos.le ht.1]
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 hcpos.le]
  have hder : ∀ t ∈ Icc (0 : ℝ) (0 + 2 * Real.pi),
      HasDerivAt (fun t => f (a + c * t)) (c * f' (a + c * t)) t := by
    intro t ht
    have h := (hd (a + c * t) (hmap t (by simpa using ht))).comp t
      ((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul c))
    convert h using 1 <;> simp [Function.comp_def, mul_comm]
  have hcont : ContinuousOn (fun t => c * f' (a + c * t))
      (Icc (0 : ℝ) (0 + 2 * Real.pi)) := by
    apply ContinuousOn.const_mul
    apply hc.comp (by fun_prop)
    intro t ht
    exact hmap t (by simpa using ht)
  have hleft : (fun t => f (a + c * t)) 0 = 0 := by simpa using ha
  have hright : (fun t => f (a + c * t)) (0 + 2 * Real.pi) = 0 := by
    simpa [hcend] using hb
  have hw := QuantumZipper.Thm18Asm.LWFar.wirtingerDirStmt_holds
    (fun t => f (a + c * t)) (fun t => c * f' (a + c * t)) 0
    hder hcont hleft hright
  have hint₁ : (∫ t in (0 : ℝ)..2 * Real.pi, f (a + c * t) ^ 2) =
      c⁻¹ * (∫ x in a..a + θ, f x ^ 2) := by
    simpa [hcend, smul_eq_mul] using
      (intervalIntegral.integral_comp_add_mul (fun x => f x ^ 2) hcne a
        (a := (0 : ℝ)) (b := 2 * Real.pi))
  have hint₂ : (∫ t in (0 : ℝ)..2 * Real.pi, (c * f' (a + c * t)) ^ 2) =
      c * (∫ x in a..a + θ, f' x ^ 2) := by
    have heq : (fun t => (c * f' (a + c * t)) ^ 2) =
        fun t => c ^ 2 * (f' (a + c * t)) ^ 2 := by
      funext t
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    rw [show (∫ t in (0 : ℝ)..2 * Real.pi, f' (a + c * t) ^ 2) =
      c⁻¹ * (∫ x in a..a + θ, f' x ^ 2) by
        simpa [hcend, smul_eq_mul] using
          (intervalIntegral.integral_comp_add_mul (fun x => f' x ^ 2) hcne a
            (a := (0 : ℝ)) (b := 2 * Real.pi))]
    field_simp
  simp only [zero_add] at hw
  rw [hint₁, hint₂] at hw
  have hbound := mul_le_mul_of_nonneg_left hw hcpos.le
  have hinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcne
  rw [← mul_assoc, hinv, one_mul] at hbound
  have hid : 4 * c * c = (θ / Real.pi) ^ 2 := by
    dsimp [c]
    field_simp
    ring
  rw [← hid]
  nlinarith [hbound]

end LatticeProb
