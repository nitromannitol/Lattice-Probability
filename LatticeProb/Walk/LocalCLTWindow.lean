import Mathlib
import LatticeProb.Walk.PairedLocalCLT
import LatticeProb.Walk.LatticeGreen

/-!
# The local central limit theorem on parabolic windows

The consequences of the local limit theorem in the forms cited by the divisible-sandpile and the
parking formalizations: in dimension four,
`|p_n(x,y) + p_{n+1}(x,y) - 8/(π²n²) e^{-2|x-y|²/n}| ≤ C/n³`
(`exists_abs_heatKernel_four_add_succ_sub_le`), and on the parabolic windows
`δR² ≤ ℓ ≤ TR²`, `R^d |p_ℓ(x,y) - 2R^{-d} p^{BM}_{ℓ/R²}(x/R, y/R)| → 0` as
`R → ∞`, uniformly (`exists_window_abs_heatKernel_sub_heatKernelBM_le`,
`exists_window_abs_srwHeat_sub_gauss_lt`). The Brownian kernel at the parabolic scale is exactly
`2 ctGauss d ℓ (x - y)`, and the error `C ℓ^{-(d+2)/2}` of the parity form is
`C δ^{-(d+2)/2} R^{-d-2}` on the window.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- Rewrites `(R²)^{d/2}` as `R^d`. -/
private lemma rpow_sq_half (R : ℝ) (hR : 0 < R) (d : ℕ) :
    (R ^ 2) ^ ((d : ℝ) / 2) = R ^ d := by
  rw [← Real.rpow_natCast R 2]
  rw [← Real.rpow_mul hR.le]
  rw [show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by ring, Real.rpow_natCast]

/-- Splits the Brownian heat-kernel rpow factor into the Gaussian prefactor and `R^d`. -/
private lemma heatKernel_rpow_eq (d : ℕ) (hd : 1 ≤ d) (R ℓ : ℝ) (hR : 0 < R)
    (hℓ : 0 < ℓ) :
    (4 * Real.pi * (ℓ / R ^ 2) / (2 * d)) ^ (-(d : ℝ) / 2)
      = (2 * Real.pi / d) ^ (-(d : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) * R ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hRpow : (R ^ 2) ^ (-(d : ℝ) / 2) = (R ^ d)⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring]
    rw [Real.rpow_neg hR2.le, rpow_sq_half R hR d]
  rw [show 4 * Real.pi * (ℓ / R ^ 2) / (2 * d) = (2 * Real.pi / d) * (ℓ / R ^ 2) by
        field_simp
        ring]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.div_rpow hℓ.le hR2.le, hRpow, div_inv_eq_mul]
  ring

/-- In dimension four, `2 ctGauss 4 n z = 8/(π² n²) e^{-2|z|²/n}`. -/
theorem two_mul_ctGauss_four {n : ℕ} (hn : 1 ≤ n) (z : Site 4) :
    2 * ctGauss 4 n z
      = 8 / (Real.pi ^ 2 * (n : ℝ) ^ 2)
          * Real.exp (-2 * (∑ i : Fin 4, ((z i : ℤ) : ℝ) ^ 2) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ctGauss_eq (by norm_num : 1 ≤ 4) hn0 z]
  simp only [Nat.cast_ofNat]
  have hnorm : euclidNorm z ^ 2 = ∑ i : Fin 4, ((z i : ℤ) : ℝ) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [hnorm]
  have hbase : (2 * Real.pi / 4) ^ (-(4 : ℝ) / 2) = 4 / Real.pi ^ 2 := by
    rw [show (2 * Real.pi / 4 : ℝ) = Real.pi / 2 by ring,
      show -(4 : ℝ) / 2 = -((2 : ℝ)) by norm_num]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    ring
  have hpow : (n : ℝ) ^ (-((4 : ℝ) / 2)) = 1 / (n : ℝ) ^ 2 := by
    rw [show -((4 : ℝ) / 2) = -((2 : ℝ)) by norm_num]
    rw [Real.rpow_neg hn0.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [hbase, hpow]
  have hexp : -(4 * (∑ i : Fin 4, ((z i : ℤ) : ℝ) ^ 2) / 2) / (n : ℝ)
      = -2 * (∑ i : Fin 4, ((z i : ℤ) : ℝ) ^ 2) / n := by ring
  rw [hexp]
  field_simp
  ring

/-- The parabolic scaling of the Brownian kernel:
`2 R^{-d} p^{BM}_{ℓ/R²}(x/R, y/R) = 2 ctGauss d ℓ (x - y)`. -/
theorem two_div_pow_mul_heatKernelBM_scaledSite (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (x y : Site d) :
    2 / R ^ d * heatKernelBM d ((ℓ : ℝ) / R ^ 2) (scaledSite R x) (scaledSite R y)
      = 2 * ctGauss d ℓ (x - y) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hnorm : ‖scaledSite R x - scaledSite R y‖ ^ 2
      = (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) / R ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    rw [show (scaledSite R x - scaledSite R y) i
          = ((x i : ℤ) : ℝ) / R - ((y i : ℤ) : ℝ) / R by simp [scaledSite]]
    rw [show ((x i : ℤ) : ℝ) / R - ((y i : ℤ) : ℝ) / R
          = (((x i - y i : ℤ) : ℝ)) / R by rw [Int.cast_sub]; ring]
    rw [div_pow]
  have heuclid : euclidNorm (x - y) ^ 2 = ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.sub_apply, Int.cast_sub]
  have hrpow := heatKernel_rpow_eq d hd R (ℓ : ℝ) hR hℓ0
  have hexp : -(d : ℝ) * ‖scaledSite R x - scaledSite R y‖ ^ 2 / (2 * ((ℓ : ℝ) / R ^ 2))
      = -(d * euclidNorm (x - y) ^ 2 / 2) / (ℓ : ℝ) := by
    rw [hnorm, heuclid]
    field_simp
  rw [heatKernelBM, hrpow, hexp, ctGauss_eq hd hℓ0 (x - y)]
  field_simp

/-- The parabolic scaling of the Brownian kernel written out coordinatewise. -/
theorem two_mul_inv_pow_mul_gauss_eq (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {ℓ : ℕ}
    (hℓ : 0 < ℓ)
    (x y : Site d) :
    2 * (R ^ d)⁻¹ *
        ((4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * d)) ^ (-(d : ℝ) / 2) *
          Real.exp (-(d : ℝ) * (∑ i, ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2)
            / (2 * ((ℓ : ℝ) / R ^ 2))))
      = 2 * ctGauss d ℓ (x - y) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hsum : (∑ i : Fin d, ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2)
      = (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) / R ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (x i : ℝ) / R - (y i : ℝ) / R = ((x i : ℝ) - (y i : ℝ)) / R by ring,
      ← Int.cast_sub, div_pow]
  have heuclid : euclidNorm (x - y) ^ 2 = ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.sub_apply, Int.cast_sub]
  have hrpow := heatKernel_rpow_eq d hd R (ℓ : ℝ) hR hℓ0
  have hexp : -(d : ℝ) * (∑ i : Fin d, ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2)
        / (2 * ((ℓ : ℝ) / R ^ 2))
      = -(d * euclidNorm (x - y) ^ 2 / 2) / (ℓ : ℝ) := by
    rw [hsum, heuclid]
    field_simp
  rw [hrpow, hexp, ctGauss_eq hd hℓ0 (x - y)]
  field_simp

/-- On the parabolic window `ℓ ≥ δR²`, `R^d ℓ^{-(d+2)/2} ≤ δ^{-(d+2)/2} R^{-2}`. -/
theorem pow_mul_rpow_le_of_window {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) {ℓ : ℕ}
    (hℓ : δ * R ^ 2 ≤ ℓ) :
    R ^ d * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2) ≤ δ ^ (-((d : ℝ) + 2) / 2)
        * R ^ (-2 : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hz : -((d : ℝ) + 2) / 2 ≤ 0 := by linarith
  have hδR2 : 0 < δ * R ^ 2 := mul_pos hδ (pow_pos hR 2)
  have hle1 : (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2) ≤ (δ * R ^ 2) ^ (-((d : ℝ) + 2) / 2) :=
    Real.rpow_le_rpow_of_nonpos hδR2 hℓ hz
  have hsq : (δ * R ^ 2) ^ (-((d : ℝ) + 2) / 2)
      = δ ^ (-((d : ℝ) + 2) / 2) * R ^ (-((d : ℝ) + 2)) := by
    rw [Real.mul_rpow hδ.le (by positivity : (0 : ℝ) ≤ R ^ 2)]
    congr 1
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hcomb : R ^ d * R ^ (-((d : ℝ) + 2)) = R ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast R d, ← Real.rpow_add hR]
    congr 1
    ring
  calc R ^ d * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2)
      ≤ R ^ d * (δ * R ^ 2) ^ (-((d : ℝ) + 2) / 2) :=
        mul_le_mul_of_nonneg_left hle1 (pow_nonneg hR.le d)
    _ = R ^ d * (δ ^ (-((d : ℝ) + 2) / 2) * R ^ (-((d : ℝ) + 2))) := by rw [hsq]
    _ = δ ^ (-((d : ℝ) + 2) / 2) * (R ^ d * R ^ (-((d : ℝ) + 2))) := by ring
    _ = δ ^ (-((d : ℝ) + 2) / 2) * R ^ (-2 : ℝ) := by rw [hcomb]

/-- Where the kernel is positive the site has the parity of the time. -/
theorem parity_of_srwHeat_pos {n : ℕ} {x : Site d} (h : 0 < srwHeat d n x) :
    ((graphNorm x : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) := by
  by_contra hne
  exact absurd (srwHeat_eq_zero_of_parity hne) (ne_of_gt h)

/-- The paired local limit estimate in dimension four, in the two-point form cited by the
divisible-sandpile formalization:
`|p_n(x,y) + p_{n+1}(x,y) - 8/(π²n²) e^{-2|x-y|²/n}| ≤ C/n³`. -/
theorem exists_abs_heatKernel_four_add_succ_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site 4,
      |heatKernel 4 n x y + heatKernel 4 (n + 1) x y -
        8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) *
          Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / n)| ≤
        C / (n : ℝ) ^ 3 := by
  obtain ⟨C, hC, h⟩ := exists_abs_srwHeat_add_succ_sub_le (d := 4) (by norm_num)
  refine ⟨C, hC, fun n hn x y => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hG := two_mul_ctGauss_four hn (x - y)
  simp only [Pi.sub_apply] at hG
  rw [heatKernel_eq_srwHeat, heatKernel_eq_srwHeat, ← hG]
  refine (h n hn (x - y)).trans (le_of_eq ?_)
  rw [show (-(((4 : ℕ) : ℝ) + 2) / 2) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hnpos.le,
    Real.rpow_natCast, div_eq_mul_inv]

/-- The local central limit theorem on parabolic windows, in the parity form
`R^d |p_ℓ(x,y) - 2R^{-d} p^{BM}_{ℓ/R²}(x/R, y/R)| ≤ ε` for `δR² ≤ ℓ ≤ TR²`
and `R ≥ R₀`
(Lawler–Limic, Theorem 2.1.3, Eq. (2.8)). -/
theorem exists_window_abs_heatKernel_sub_heatKernelBM_le :
    ∀ d : ℕ, 1 ≤ d →
      ∀ δ T C₀ : ℝ, 0 < δ → δ < T →
        ∀ ε : ℝ, 0 < ε →
          ∃ R₀ : ℝ, 0 < R₀ ∧
            ∀ R : ℝ, R₀ ≤ R →
              ∀ (ℓ : ℕ) (x y : Site d),
                δ * R ^ 2 ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ T * R ^ 2 →
                  latticeDist x y ≤ C₀ * R →
                    0 < heatKernel d ℓ x y →
                      R ^ d *
                          |heatKernel d ℓ x y -
                            2 / R ^ d *
                              heatKernelBM d ((ℓ : ℝ) / R ^ 2) (scaledSite R x)
                                  (scaledSite R y)|
                        ≤ ε := by
  intro d hd δ T C₀ hδ _ ε hε
  obtain ⟨C, hC, h⟩ := exists_abs_srwHeat_sub_le hd
  set A : ℝ := C * δ ^ (-((d : ℝ) + 2) / 2) with hA
  have hApos : 0 < A := by positivity
  refine ⟨max 1 (Real.sqrt (A / ε)), by positivity, fun R hR ℓ x y hℓ _ _ hpos => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := by linarith
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hℓnat : 0 < ℓ := by exact_mod_cast hℓpos
  rw [heatKernel_eq_srwHeat] at hpos ⊢
  rw [two_div_pow_mul_heatKernelBM_scaledSite hd hR0 hℓnat]
  have hpar := parity_of_srwHeat_pos hpos
  have hb := h ℓ hℓnat (x - y) hpar
  have hwin := pow_mul_rpow_le_of_window (d := d) hδ hR0 hℓ
  have hRsq : A / ε ≤ R ^ 2 := by
    have h1 : Real.sqrt (A / ε) ≤ R := le_trans (le_max_right _ _) hR
    have h2 := Real.sq_sqrt (show 0 ≤ A / ε by positivity)
    nlinarith [Real.sqrt_nonneg (A / ε)]
  have hR2 : R ^ (-2 : ℝ) = (R ^ 2)⁻¹ := by
    rw [Real.rpow_neg hR0.le, Real.rpow_two]
  calc R ^ d * |srwHeat d ℓ (x - y) - 2 * ctGauss d ℓ (x - y)|
      ≤ R ^ d * (C * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * (R ^ d * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2)) := by ring
    _ ≤ C * (δ ^ (-((d : ℝ) + 2) / 2) * R ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hwin hC.le
    _ = A / R ^ 2 := by rw [hR2, hA]; ring
    _ ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hε] at hRsq
        linarith

/-- The local central limit theorem on parabolic windows, with the Brownian kernel written
out: `R^d |p_ℓ(x - y) - 2R^{-d} p^{BM}_{ℓ/R²}(x/R, y/R)| < ε` for `δR² ≤ ℓ ≤ TR²`,
`R ≥ R₀`. -/
theorem exists_window_abs_srwHeat_sub_gauss_lt :
    ∀ d : ℕ, 1 ≤ d → ∀ δ T C₀ : ℝ, 0 < δ → δ ≤ T → 0 ≤ C₀ →
      ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ∀ ℓ : ℕ, δ * R ^ 2 ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ T * R ^ 2 →
          ∀ x y : Site d, (∑ i, ((x i : ℝ) - (y i : ℝ)) ^ 2) ≤ (C₀ * R) ^ 2 →
          0 < srwHeat d ℓ (x - y) →
            R ^ d * |srwHeat d ℓ (x - y) -
                2 * (R ^ d)⁻¹ *
                  ((4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * d)) ^ (-(d : ℝ) / 2) *
                    Real.exp (-(d : ℝ) * (∑ i, ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2)
                      / (2 * ((ℓ : ℝ) / R ^ 2))))| < ε := by
  intro d hd δ T C₀ hδ _ _ ε hε
  obtain ⟨C, hC, h⟩ := exists_abs_srwHeat_sub_le hd
  set A : ℝ := C * δ ^ (-((d : ℝ) + 2) / 2) with hA
  have hApos : 0 < A := by positivity
  refine ⟨max 1 (Real.sqrt (2 * A / ε)), fun R hR ℓ hℓ _ x y _ hpos => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := by linarith
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hℓnat : 0 < ℓ := by exact_mod_cast hℓpos
  rw [two_mul_inv_pow_mul_gauss_eq hd hR0 hℓnat]
  have hpar := parity_of_srwHeat_pos hpos
  have hb := h ℓ hℓnat (x - y) hpar
  have hwin := pow_mul_rpow_le_of_window (d := d) hδ hR0 hℓ
  have hRsq : 2 * A / ε ≤ R ^ 2 := by
    have h1 : Real.sqrt (2 * A / ε) ≤ R := le_trans (le_max_right _ _) hR
    have h2 := Real.sq_sqrt (show 0 ≤ 2 * A / ε by positivity)
    nlinarith [Real.sqrt_nonneg (2 * A / ε)]
  have hR2 : R ^ (-2 : ℝ) = (R ^ 2)⁻¹ := by
    rw [Real.rpow_neg hR0.le, Real.rpow_two]
  calc R ^ d * |srwHeat d ℓ (x - y) - 2 * ctGauss d ℓ (x - y)|
      ≤ R ^ d * (C * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * (R ^ d * (ℓ : ℝ) ^ (-((d : ℝ) + 2) / 2)) := by ring
    _ ≤ C * (δ ^ (-((d : ℝ) + 2) / 2) * R ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hwin hC.le
    _ = A / R ^ 2 := by rw [hR2, hA]; ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_le_iff₀ hε] at hRsq
        linarith

end LatticeProb.LocalCLT
