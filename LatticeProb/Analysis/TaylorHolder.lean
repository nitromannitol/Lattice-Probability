import LatticeProb.Analysis.HessianTaylorRemainder
import LatticeProb.Euclidean.Lattice

/-!
# Taylor bounds with a Hölder continuous Hessian

The calculus uses the usual Pi norm, while all final displacement bounds use the
Euclidean radius. Derivatives are the actual Fréchet derivatives of the given function.
-/

noncomputable section

open Set

namespace LatticeProb.TaylorHolder

open LatticeProb.Euclidean.Lattice

variable {d : ℕ} {v : (Fin d → ℝ) → ℝ}

/-- The Pi norm is bounded by the Euclidean radius, including in dimension zero. -/
lemma norm_le_radius (z : Fin d → ℝ) : ‖z‖ ≤ radius z := by
  apply (pi_norm_le_iff_of_nonneg (radius_nonneg z)).2
  intro i
  exact (Real.norm_eq_abs _).trans_le (abs_coord_le_radius z i)

/-- Bounded values and bounded actual derivatives give linear growth of the remainder. -/
theorem remainder_le_linear {B₀ B₁ : ℝ}
    (hv : ∀ x, |v x| ≤ B₀) (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    (x z : Fin d → ℝ) :
    |v (x + z) - v x - fderiv ℝ v x z| ≤ 2 * B₀ + B₁ * radius z := by
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hDv x)
  have hlinear : |fderiv ℝ v x z| ≤ B₁ * radius z := by
    calc
      |fderiv ℝ v x z| ≤ ‖fderiv ℝ v x‖ * ‖z‖ := by
        simpa only [Real.norm_eq_abs] using (fderiv ℝ v x).le_opNorm z
      _ ≤ B₁ * radius z := mul_le_mul (hDv x) (norm_le_radius z)
        (norm_nonneg z) hB₁
  calc
    |v (x + z) - v x - fderiv ℝ v x z| ≤
        |v (x + z)| + |v x| + |fderiv ℝ v x z| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ B₀ + B₀ + B₁ * radius z := add_le_add (add_le_add (hv _) (hv _)) hlinear
    _ = _ := by ring

/-- A globally bounded derivative of a C² function gives a Euclidean Lipschitz bound. -/
theorem sub_le_radius (hv : ContDiff ℝ 2 v) {B₁ : ℝ}
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁) (x y : Fin d → ℝ) :
    |v y - v x| ≤ B₁ * radius (y - x) := by
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hDv x)
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ ↦ hv.differentiable (by norm_num) w) (fun w _ ↦ hDv w)
    (mem_univ x) (mem_univ y)
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_radius _) hB₁)

/-- A bounded Hessian and bounded gradient control each coordinate derivative by a minimum. -/
theorem partial_sub_le_min (hv : ContDiff ℝ 2 v) {B₁ B₂ : ℝ}
    (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    (hD₂v : ∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B₂)
    (x z : Fin d → ℝ) (i : Fin d) :
    |fderiv ℝ v (x + z) (Pi.single i 1) - fderiv ℝ v x (Pi.single i 1)| ≤
      min (B₂ * radius z) (2 * B₁) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans (hD₂v x)
  have hH (w : Fin d → ℝ) : ‖fderiv ℝ (fderiv ℝ v) w‖ ≤ B₂ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hD₂v w
  have hgrad := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ ↦ hD.differentiable (by norm_num) w) (fun w _ ↦ hH w)
    (mem_univ x) (mem_univ (x + z))
  have heval : ∀ A : (Fin d → ℝ) →L[ℝ] ℝ, |A (Pi.single i 1)| ≤ ‖A‖ := by
    intro A
    simpa only [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      A.le_opNorm (Pi.single i 1)
  apply le_min
  · calc
      _ ≤ ‖fderiv ℝ v (x + z) - fderiv ℝ v x‖ := heval _
      _ ≤ B₂ * ‖z‖ := by simpa only [add_sub_cancel_left] using hgrad
      _ ≤ B₂ * radius z := mul_le_mul_of_nonneg_left (norm_le_radius z) hB₂
  · calc
      _ ≤ |fderiv ℝ v (x + z) (Pi.single i 1)| +
          |fderiv ℝ v x (Pi.single i 1)| := abs_sub _ _
      _ ≤ B₁ + B₁ := add_le_add ((heval _).trans (hDv _)) ((heval _).trans (hDv _))
      _ = 2 * B₁ := by ring

/-- Taylor's formula along a line, with the actual Hessian in the integral remainder. -/
theorem remainder_eq_integral (hv : ContDiff ℝ 2 v) (x z : Fin d → ℝ) :
    v (x + z) - v x - fderiv ℝ v x z =
      ∫ t in (0 : ℝ)..1,
        (1 - t) * iteratedFDeriv ℝ 2 v (x + t • z) ![z, z] := by
  have hD : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ v)) := hD.continuous_fderiv (by norm_num)
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have hder (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ v (x + s • z) +
        (1 - s) * fderiv ℝ v (x + s • z) z)
        ((1 - t) * iteratedFDeriv ℝ 2 v (x + t • z) ![z, z]) t := by
    have hf := (hv.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hg := (hD.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hg' := (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp_hasDerivAt t hg
    apply (hf.add (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul hg')).congr_deriv
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.comp_apply, zero_sub, ContinuousLinearMap.apply_apply]
    change fderiv ℝ v (x + t • z) z +
        ((-1) * fderiv ℝ v (x + t • z) z +
          (1 - t) * fderiv ℝ (fderiv ℝ v) (x + t • z) z z) =
      (1 - t) * fderiv ℝ (fderiv ℝ v) (x + t • z) z z
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * iteratedFDeriv ℝ 2 v (x + t • z) ![z, z])
      MeasureTheory.volume 0 1 := by
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact (continuous_const.sub continuous_id |>.mul
      ((hH.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const |>.clm_apply continuous_const)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hder t) hint
  simpa only [zero_smul, one_smul, add_zero, sub_zero, sub_self, zero_mul, zero_add,
    one_mul, sub_add_eq_sub_sub] using h.symm

/-- Currying the difference of two Hessians does not increase its operator norm. -/
lemma norm_hessian_sub_le (x y : Fin d → ℝ) :
    ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
      ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ := by
  let H := iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg H) (norm_nonneg a))
  intro b
  have h := H.le_opNorm ![a, b]
  simpa only [H, sub_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Fin.prod_univ_two, mul_assoc] using h

/-- Scalar multiplication scales the Euclidean radius by the absolute scalar. -/
lemma radius_smul (t : ℝ) (z : Fin d → ℝ) : radius (t • z) = |t| * radius z := by
  rw [radius_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, radius_norm]

/-- A Hölder Hessian gives the second-order Taylor error with the stated Euclidean power. -/
theorem remainder_sub_quadratic_le (hv : ContDiff ℝ 2 v) {σ M : ℝ}
    (hσ : 0 ≤ σ ∧ σ ≤ 1)
    (hHolder : ∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
      M * radius (x - y) ^ σ) (x z : Fin d → ℝ) :
    |v (x + z) - v x - fderiv ℝ v x z -
        (1 / 2) * iteratedFDeriv ℝ 2 v x ![z, z]| ≤ M * radius z ^ (2 + σ) := by
  by_cases hz : z = 0
  · subst z
    simp only [add_zero, map_zero, sub_self, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, abs_zero]
    have hr : radius (0 : Fin d → ℝ) = 0 := by simp [radius]
    rw [hr, Real.zero_rpow (by linarith : 2 + σ ≠ 0), mul_zero]
  have hr : 0 < radius z := radius_pos hz
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hHolder (x + z) x)
    rw [add_sub_cancel_left] at h
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos hr σ)
  have hD : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hosc (w : Fin d → ℝ) (hw : w ∈ segment ℝ x (x + z)) :
      ‖fderiv ℝ (fderiv ℝ v) w - fderiv ℝ (fderiv ℝ v) x‖ ≤
        M * radius z ^ σ := by
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    have hrad : radius (x + t • (x + z - x) - x) ≤ radius z := by
      simp only [add_sub_cancel_left, radius_smul,
        abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (radius_nonneg z) ht.2
    exact (norm_hessian_sub_le _ _).trans ((hHolder _ _).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (radius_nonneg _) hrad hσ.1) hM))
  have h := LatticeProb.taylor_remainder_le_of_hessian_oscillation
    (convex_segment x (x + z))
    (fun w _ ↦ hv.differentiable (by norm_num) w)
    (fun w _ ↦ hD.differentiable (by norm_num) w)
    (left_mem_segment ℝ x (x + z)) (right_mem_segment ℝ x (x + z))
    (mul_nonneg hM (Real.rpow_nonneg (radius_nonneg z) σ)) hosc
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ ≤ (M * radius z ^ σ) * ‖z‖ ^ 2 := h
    _ ≤ (M * radius z ^ σ) * radius z ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) (norm_le_radius z) 2)
        (mul_nonneg hM (Real.rpow_nonneg (radius_nonneg z) σ))
    _ = M * radius z ^ (2 + σ) := by
      rw [Real.rpow_add hr, Real.rpow_two, mul_assoc,
        mul_comm (radius z ^ σ) (radius z ^ 2)]

end LatticeProb.TaylorHolder
