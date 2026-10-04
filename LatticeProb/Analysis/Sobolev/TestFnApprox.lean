import LatticeProb.Analysis.Sobolev.Defs
import LatticeProb.Analysis.Sobolev.Weight

/-!
# The support/mollification repair: Peetre's inequality and the bounded multiplier bound

The Rellich–Kondrachov residual `rkLowFreqNet`
(`LatticeProb/Analysis/Sobolev/RellichLowFreqNet.lean`) still needs the **support/mollification
repair**: the finite net's centres must be `IsTestFn D` (smooth, compactly supported in `D`),
whereas the band-limited functions produced by the frequency truncation are not compactly
supported.  The analytic content of the repair is that `sobolevNormSq` is continuous under
multiplication by a smooth compactly-supported cut-off `χ`,

  `sobolevNormSq d s (fun x => χ x * u x) ≤ C_χ · sobolevNormSq d s u`,

and under convolution with a mollifier `k`,
`sobolevNormSq d s (fun x => u x - (u * k) x) → 0` for a
concentrating mollifier.

This file lands the two algebraic ingredients that do not depend on Mathlib's Fourier-convolution
API:

* `peetre_le` — **Peetre's inequality** for the Sobolev weight,
  `(1 + (2π‖ξ‖)²)^s ≤ 2^{|s|} (1 + (2π‖ξ−η‖)²)^s (1 + (2π‖η‖)²)^{|s|}`;
* `sobolevNormSq_le_of_fourier_norm_le` — the **bounded-multiplier bound**: a pointwise bound
  `‖𝓕v(ξ)‖ ≤ C ‖𝓕u(ξ)‖` gives
  `sobolevNormSq d s v ≤ ofReal (C²) · sobolevNormSq d s u`.

## The missing input, precisely

What is **not** in Mathlib and not proved here is the step that produces the pointwise Fourier
bound for the actual cut-off and mollifier:

* the **Fourier product theorem** `𝓕(χ · u) = 𝓕χ * 𝓕u` for `u ∈ H^s` and `χ` a test
  function.
  Mathlib's `Real.fourier_mul_convolution_eq`
  (`Mathlib/Analysis/Fourier/Convolution.lean:119`) gives the dual direction
  `𝓕(f * g) = 𝓕f · 𝓕g` for `Integrable f, g`; the product direction needs Fourier
  inversion,
  available in Mathlib only for Schwartz functions — an `H^s` function is not Schwartz and need
  not be integrable.
* **Young's inequality for convolutions** `‖w * V‖₂ ≤ ‖w‖₁ ‖V‖₂`, which with `peetre_le`
  turns the
  product theorem into the weighted integral bound
  `‖(1+(2π‖·‖)²)^{s/2} 𝓕(χu)‖₂ ≤ C_χ ‖(1+(2π‖·‖)²)^{s/2} 𝓕u‖₂`.  There is no Young
  inequality in
  Mathlib (`grep -rn young Mathlib/Analysis/Convolution.lean` is empty).

Neither (1) (density of test functions in `H^s(D)`) nor (2) (the localised continuity lemma)
therefore closes here; the two lemmas below are the largest pieces that do.
-/

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **Peetre's inequality for the Sobolev weight.**
`(1 + (2π‖ξ‖)²)^s ≤ 2^{|s|} (1 + (2π‖ξ−η‖)²)^s (1 + (2π‖η‖)²)^{|s|}`.

The two elementary comparisons are `W ≤ 2 A B` (from `‖ξ‖ ≤ ‖ξ−η‖ + ‖η‖`, used for
`s ≥ 0`) and `A ≤ 2 W B` (from `‖ξ−η‖ ≤ ‖ξ‖ + ‖η‖`, used for `s < 0`), where
`B = 1 + (2π‖η‖)²`, `W = 1 + (2π‖ξ‖)²`. -/
theorem peetre_le {d : ℕ} (s : ℝ) (ξ η : Space d) :
    (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s ≤
      (2 : ℝ) ^ |s| * (1 + (2 * Real.pi * ‖ξ - η‖) ^ 2) ^ s *
        (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ |s| := by
  set A : ℝ := 1 + (2 * Real.pi * ‖ξ - η‖) ^ 2 with hAdef
  set B : ℝ := 1 + (2 * Real.pi * ‖η‖) ^ 2 with hBdef
  set W : ℝ := 1 + (2 * Real.pi * ‖ξ‖) ^ 2 with hWdef
  have hA1 : 1 ≤ A := by rw [hAdef]; nlinarith [sq_nonneg (2 * Real.pi * ‖ξ - η‖)]
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith [sq_nonneg (2 * Real.pi * ‖η‖)]
  have hW1 : 1 ≤ W := by rw [hWdef]; nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have hWAB : W ≤ 2 * (A * B) := by
    have htri : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
      calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
        _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hs : 2 * Real.pi * ‖ξ‖ ≤ 2 * Real.pi * ‖ξ - η‖ + 2 * Real.pi * ‖η‖ :=
      le_trans (by nlinarith [mul_le_mul_of_nonneg_left htri hp.le]) le_rfl
    have hsq : (2 * Real.pi * ‖ξ‖) ^ 2
        ≤ ((2 * Real.pi * ‖ξ - η‖) + 2 * Real.pi * ‖η‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    rw [hWdef, hAdef, hBdef]
    nlinarith [hsq, sq_nonneg (2 * Real.pi * ‖ξ - η‖), sq_nonneg (2 * Real.pi * ‖η‖),
      sq_nonneg (2 * Real.pi * ‖ξ - η‖ - 2 * Real.pi * ‖η‖),
      mul_nonneg (sq_nonneg (2 * Real.pi * ‖ξ - η‖)) (sq_nonneg (2 * Real.pi * ‖η‖))]
  have hAWB : A ≤ 2 * (W * B) := by
    have htri : ‖ξ - η‖ ≤ ‖ξ‖ + ‖η‖ := by
      calc ‖ξ - η‖ = ‖ξ + (-η)‖ := by rw [sub_eq_add_neg]
        _ ≤ ‖ξ‖ + ‖-η‖ := norm_add_le _ _
        _ = ‖ξ‖ + ‖η‖ := by rw [norm_neg]
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hs : 2 * Real.pi * ‖ξ - η‖ ≤ 2 * Real.pi * ‖ξ‖ + 2 * Real.pi * ‖η‖ :=
      le_trans (by nlinarith [mul_le_mul_of_nonneg_left htri hp.le]) le_rfl
    have hsq : (2 * Real.pi * ‖ξ - η‖) ^ 2
        ≤ ((2 * Real.pi * ‖ξ‖) + 2 * Real.pi * ‖η‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    rw [hWdef, hAdef, hBdef]
    nlinarith [hsq, sq_nonneg (2 * Real.pi * ‖ξ‖), sq_nonneg (2 * Real.pi * ‖η‖),
      sq_nonneg (2 * Real.pi * ‖ξ‖ - 2 * Real.pi * ‖η‖),
      mul_nonneg (sq_nonneg (2 * Real.pi * ‖ξ‖)) (sq_nonneg (2 * Real.pi * ‖η‖))]
  rcases lt_or_ge s 0 with hs | hs
  · have ht : 0 < -s := by linarith
    have hkey : A ^ (-s) ≤ 2 ^ (-s) * (W ^ (-s) * B ^ (-s)) := by
      have h := Real.rpow_le_rpow hApos.le hAWB ht.le
      rwa [Real.mul_rpow (by norm_num) (mul_nonneg hWpos.le hBpos.le),
        Real.mul_rpow hWpos.le hBpos.le] at h
    have hWa : W ^ s = (W ^ (-s))⁻¹ := by
      conv_lhs => rw [show s = -(-s) by ring]
      exact Real.rpow_neg hWpos.le (-s)
    have hAa : A ^ s = (A ^ (-s))⁻¹ := by
      conv_lhs => rw [show s = -(-s) by ring]
      exact Real.rpow_neg hApos.le (-s)
    have h2a : (2 : ℝ) ^ |s| = 2 ^ (-s) := by rw [abs_of_neg hs]
    have hBa : (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ |s| = B ^ (-s) := by
      rw [show B = 1 + (2 * Real.pi * ‖η‖) ^ 2 from hBdef.symm, abs_of_neg hs]
    rw [hWa, hAa, h2a, hBa]
    have hAt : 0 < A ^ (-s) := Real.rpow_pos_of_pos hApos (-s)
    have hWt : 0 < W ^ (-s) := Real.rpow_pos_of_pos hWpos (-s)
    have h2t : 0 < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) (-s)
    have hBt : 0 < B ^ (-s) := Real.rpow_pos_of_pos hBpos (-s)
    field_simp
    nlinarith [hkey, hAt, hWt, h2t, hBt]
  · have h1 : W ^ s ≤ (2 * (A * B)) ^ s := Real.rpow_le_rpow hWpos.le hWAB hs
    rw [Real.mul_rpow (by norm_num) (mul_nonneg hApos.le hBpos.le),
      Real.mul_rpow hApos.le hBpos.le] at h1
    have h2 : (2 : ℝ) ^ s ≤ 2 ^ |s| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self s)
    have h3 : B ^ s ≤ B ^ |s| := Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self s)
    have hA0 : 0 ≤ A ^ s := Real.rpow_nonneg hApos.le s
    have hB0 : 0 ≤ B ^ s := Real.rpow_nonneg hBpos.le s
    have h20 : 0 ≤ (2 : ℝ) ^ |s| := Real.rpow_nonneg (by norm_num) |s|
    calc W ^ s ≤ 2 ^ s * (A ^ s * B ^ s) := h1
      _ ≤ 2 ^ |s| * (A ^ s * B ^ |s|) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_left h3 hA0) (mul_nonneg hA0 hB0) h20
      _ = 2 ^ |s| * A ^ s * B ^ |s| := by ring

/-- **The bounded-multiplier bound.**  A pointwise bound `‖𝓕v(ξ)‖ ≤ C ‖𝓕u(ξ)‖` on the
Fourier transforms gives `sobolevNormSq d s v ≤ ofReal (C²) · sobolevNormSq d s u`.  This is
the abstract
form of the localised continuity lemma: it reduces statement (2) to a pointwise Fourier bound on
`𝓕(χu)` in terms of `𝓕u`. -/
theorem sobolevNormSq_le_of_fourier_norm_le {d : ℕ} {s : ℝ} {u v : Space d → ℝ} {C : ℝ}
    (h : ∀ ξ : Space d,
      ‖𝓕 (fun x => (v x : ℂ)) ξ‖ ≤ C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) :
    sobolevNormSq d s v ≤ ENNReal.ofReal (C ^ 2) * sobolevNormSq d s u := by
  unfold sobolevNormSq
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        ‖𝓕 (fun x => (v x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2) := by
        refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h ξ) 2)
          (Real.rpow_nonneg (by positivity) s)
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2) := by
        rw [show (fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2))
            = fun ξ => ENNReal.ofReal (C ^ 2) *
              ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
                ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2) from by
          funext ξ
          have hCpow : (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2
              = C ^ 2 * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2 :=
            mul_pow C ‖𝓕 (fun x => (u x : ℂ)) ξ‖ 2
          rw [hCpow,
            show (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
                (C ^ 2 * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2)
                = C ^ 2 * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
                  ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2) by ring,
            ENNReal.ofReal_mul (sq_nonneg C)]]
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end LatticeProb.Sobolev
