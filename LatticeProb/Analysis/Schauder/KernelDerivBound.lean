import LatticeProb.Analysis.Schauder.KernelDerivSpace

/-!
# Gaussian-times-polynomial bound for every space derivative of the heat kernel

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` and `t > 0`, the `n`-th Fréchet derivative
satisfies
`‖D^n p_t(y)‖ ≤ n! · p_t(y) · (‖y‖/(2t) + 1/√(2t))^n`.

The kernel is the constant `(4πt)^{-d/2}` times `exp ∘ φ` with `φ(y) = -(4t)⁻¹ ‖y‖²`, so the bound
is the Faà di Bruno estimate for the composition of `exp` (all of whose derivatives equal `exp`)
with `φ`. The quadratic `φ` has `‖Dφ(y)‖ ≤ ‖y‖/(2t)`, `‖D²φ‖ ≤ 1/(2t)` and vanishing derivatives
of order at least three, which is dominated by `D^i` with `D = ‖y‖/(2t) + 1/√(2t)`. These
derivatives of `‖y‖² = ⟪y, y⟫` come from the Leibniz bound for the bilinear map `⟪·, ·⟫`, applied to
the identity, whose derivatives of order at least two vanish.
-/

namespace LatticeProb.Analysis.Schauder

open Real

open scoped Nat

noncomputable section

variable {d : ℕ}

/-- Every derivative of `exp` has norm `exp z` at `z`. -/
private theorem norm_iteratedFDeriv_exp (i : ℕ) (z : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp z‖ = Real.exp z := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_of_nonneg (Real.exp_pos z).le]

/-- The identity map of `ℝ^d` has no derivatives of order at least two. -/
private theorem norm_iteratedFDeriv_id_of_two_le {k : ℕ} (hk : 2 ≤ k) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (id : Euc d → Euc d) y‖ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hid : fderiv ℝ (id : Euc d → Euc d) = fun _ => ContinuousLinearMap.id ℝ (Euc d) :=
    funext fun _ => fderiv_id
  rw [show m + 2 = (m + 1) + 1 from rfl, ← norm_iteratedFDeriv_fderiv, hid,
    iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]

/-- The first derivative of the identity map of `ℝ^d` has norm at most one. -/
private theorem norm_iteratedFDeriv_id_one_le (y : Euc d) :
    ‖iteratedFDeriv ℝ 1 (id : Euc d → Euc d) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one, fderiv_id]
  exact ContinuousLinearMap.norm_id_le

/-- Leibniz bound for the derivatives of `‖y‖² = ⟪y, y⟫`, in terms of those of the identity. -/
private theorem norm_iteratedFDeriv_sq_norm_le (n : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ n (fun z : Euc d => ‖z‖ ^ 2) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (id : Euc d → Euc d) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (id : Euc d → Euc d) y‖ := by
  have hB : ‖innerSL ℝ (E := Euc d)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [innerSL_apply_norm, one_mul]
  have hfun : (fun z : Euc d => ‖z‖ ^ 2) = fun z => innerSL ℝ (id z) (id z) := by
    funext z
    simp [innerSL_apply_apply]
  rw [hfun]
  exact (innerSL ℝ (E := Euc d)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (contDiff_id (n := ⊤)) (contDiff_id (n := ⊤)) y le_top hB

/-- The first derivative of `‖y‖²` has norm at most `2‖y‖`. -/
private theorem norm_iteratedFDeriv_one_sq_norm_le (y : Euc d) :
    ‖iteratedFDeriv ℝ 1 (fun z : Euc d => ‖z‖ ^ 2) y‖ ≤ 2 * ‖y‖ := by
  refine (norm_iteratedFDeriv_sq_norm_le 1 y).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le y
  have hy := norm_nonneg y
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, norm_iteratedFDeriv_zero, id_eq, one_mul, zero_add]
  nlinarith [mul_le_mul_of_nonneg_left h1 hy]

/-- The second derivative of `‖y‖²` has norm at most `2`. -/
private theorem norm_iteratedFDeriv_two_sq_norm_le (y : Euc d) :
    ‖iteratedFDeriv ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) y‖ ≤ 2 := by
  refine (norm_iteratedFDeriv_sq_norm_le 2 y).trans ?_
  have h1 := norm_iteratedFDeriv_id_one_le y
  have h0 := norm_nonneg (iteratedFDeriv ℝ 1 (id : Euc d → Euc d) y)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, norm_iteratedFDeriv_id_of_two_le (le_refl 2),
    mul_zero, zero_mul, zero_add, add_zero]
  push_cast
  nlinarith [mul_le_mul h1 h1 h0 zero_le_one]

/-- The derivatives of `‖y‖²` of order at least three vanish. -/
private theorem norm_iteratedFDeriv_sq_norm_of_three_le {n : ℕ} (hn : 3 ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ n (fun z : Euc d => ‖z‖ ^ 2) y‖ ≤ 0 := by
  refine (norm_iteratedFDeriv_sq_norm_le n y).trans (le_of_eq ?_)
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : 2 ≤ j
  · rw [norm_iteratedFDeriv_id_of_two_le hj, mul_zero, zero_mul]
  · rw [norm_iteratedFDeriv_id_of_two_le (show 2 ≤ n - j by omega), mul_zero]

/-- The derivatives of order `i ≥ 1` of the Gaussian exponent `-(4t)⁻¹ ‖y‖²` are bounded by the
`i`-th power of `‖y‖/(2t) + 1/√(2t)`. -/
private theorem norm_iteratedFDeriv_exponent_le {t : ℝ} (ht : 0 < t) (y : Euc d) {i : ℕ}
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) y‖ ≤
      (‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t)) ^ i := by
  have hfun : (fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) =
      fun z => (-(4 * t)⁻¹) • (fun w : Euc d => ‖w‖ ^ 2) z := by
    funext z
    rw [smul_eq_mul]
  have hcoef : ‖(-(4 * t)⁻¹ : ℝ)‖ = (4 * t)⁻¹ := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  rw [hfun, iteratedFDeriv_const_smul_apply' (contDiff_norm_sq ℝ).contDiffAt, norm_smul, hcoef]
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have hD1 : ‖y‖ / (2 * t) ≤ ‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t) :=
    le_add_of_nonneg_right (by positivity)
  have hD2 : 1 / Real.sqrt (2 * t) ≤ ‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t) :=
    le_add_of_nonneg_left (by positivity)
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · interval_cases i
    · calc (4 * t)⁻¹ * ‖iteratedFDeriv ℝ 1 (fun z : Euc d => ‖z‖ ^ 2) y‖
          ≤ (4 * t)⁻¹ * (2 * ‖y‖) :=
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_one_sq_norm_le y) (by positivity)
        _ = ‖y‖ / (2 * t) := by field_simp; ring
        _ ≤ _ := by rw [pow_one]; exact hD1
    · calc (4 * t)⁻¹ * ‖iteratedFDeriv ℝ 2 (fun z : Euc d => ‖z‖ ^ 2) y‖
          ≤ (4 * t)⁻¹ * 2 :=
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_two_sq_norm_le y) (by positivity)
        _ = (1 / Real.sqrt (2 * t)) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by positivity)]
            field_simp
            ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hD2 2
  · have h0 := norm_iteratedFDeriv_sq_norm_of_three_le h3 y
    have h00 : ‖iteratedFDeriv ℝ i (fun z : Euc d => ‖z‖ ^ 2) y‖ = 0 :=
      le_antisymm h0 (norm_nonneg _)
    rw [h00, mul_zero]
    positivity

/-- Every derivative of the heat kernel is bounded by the Gaussian times a polynomial:
`‖D^n p_t(y)‖ ≤ n! · p_t(y) · (‖y‖/(2t) + 1/√(2t))^n` for `t > 0`. -/
theorem norm_iteratedFDeriv_heatKernel_le (n : ℕ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ ≤
      n ! * ((4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
        (‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t)) ^ n := by
  have hc0 : 0 ≤ (4 * π * t) ^ (-(d : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  have hφ : ContDiff ℝ ⊤ fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2 :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hcomp : ContDiff ℝ ⊤ (Real.exp ∘ fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) :=
    Real.contDiff_exp.comp hφ
  have hfun : heatKernel d t = (4 * π * t) ^ (-(d : ℝ) / 2) •
      (Real.exp ∘ fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) := by
    funext z
    rw [heatKernel_eq, Pi.smul_apply, smul_eq_mul]
    rfl
  have hbound := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Real.exp)
    (f := fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) (n := n) (N := ⊤)
    Real.contDiff_exp hφ le_top y
    (C := Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2)) (D := ‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t))
    (fun i _ => (norm_iteratedFDeriv_exp i _).le)
    (fun i hi _ => norm_iteratedFDeriv_exponent_le ht y hi)
  have hexp : -(4 * t)⁻¹ * ‖y‖ ^ 2 = -‖y‖ ^ 2 / (4 * t) := by ring
  rw [hfun, iteratedFDeriv_const_smul_apply ((hcomp.of_le le_top).contDiffAt), norm_smul,
    Real.norm_of_nonneg hc0]
  calc (4 * π * t) ^ (-(d : ℝ) / 2) *
        ‖iteratedFDeriv ℝ n
          (Real.exp ∘ fun z : Euc d => -(4 * t)⁻¹ * ‖z‖ ^ 2) y‖
      ≤ (4 * π * t) ^ (-(d : ℝ) / 2) *
        (n ! * Real.exp (-(4 * t)⁻¹ * ‖y‖ ^ 2) *
          (‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t)) ^ n) :=
        mul_le_mul_of_nonneg_left hbound hc0
    _ = _ := by rw [hexp]; ring

end

end LatticeProb.Analysis.Schauder
