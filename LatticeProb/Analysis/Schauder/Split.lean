import LatticeProb.Analysis.Schauder.KernelDef

/-!
# Splitting a mean-zero kernel convolution with a bump at the origin

Let `K` be an integrable kernel on `ℝ^d` with `∫ K = 0`, let `g` be bounded and continuous, and
let `χ` be a bump function centred at the origin, so that `0 ≤ χ ≤ 1`. Writing
`K y g(x - y) = χ(y) K(y) (g(x - y) - g(x)) + (1 - χ(y)) K(y) g(x - y) + g(x) χ(y) K(y)` and using
`∫ χ K = ∫ K - ∫ (1 - χ) K = -∫ (1 - χ) K`, the convolution `∫ K(y) g(x - y) dy` splits into a
near part, in which the cancellation of the mean is encoded by the difference `g(x - y) - g(x)`,
and a far part `(1 - χ) K` together with a correction `g(x) ∫ (1 - χ) K`. Every piece is
integrable, because `K` is integrable and the other factors are bounded and continuous.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Splitting a mean-zero kernel with a bump at the origin: for an integrable kernel `K` of mean
zero and a bounded continuous `g`, the convolution `∫ K(y) g(x - y) dy` equals the near part
`∫ χ K (g(x - ·) - g x)`, plus the far part `∫ (1 - χ) K g(x - ·)`, minus the correction
`g x ∫ (1 - χ) K`. -/
theorem integral_mul_comp_sub_eq_split (χ : ContDiffBump (0 : Euc d)) {K g : Euc d → ℝ}
    (hK : Integrable K) (hK0 : ∫ y, K y = 0) (hg : Continuous g) {B : ℝ}
    (hgB : ∀ y, |g y| ≤ B) (x : Euc d) :
    ∫ y, K y * g (x - y) =
      (∫ y, χ y * K y * (g (x - y) - g x)) + (∫ y, (1 - χ y) * K y * g (x - y)) -
        g x * ∫ y, (1 - χ y) * K y := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hgB x)
  have hgc : Continuous fun y : Euc d => g (x - y) := hg.comp (continuous_const.sub continuous_id)
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => χ.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y => χ.le_one
  -- the bump `χ`, the complement `1 - χ`, and the translate `g (x - ·)` are bounded
  have hχK : Integrable fun y => χ y * K y :=
    hK.bdd_mul (c := 1) χ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 y)]
        exact hχ1 y)
  have hcK : Integrable fun y => (1 - χ y) * K y :=
    hK.bdd_mul (c := 1) (continuous_const.sub χ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hχ1 y))]
        linarith [hχ0 y])
  have hfar : Integrable fun y => (1 - χ y) * K y * g (x - y) :=
    hcK.mul_bdd (c := B) hgc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact hgB _)
  have hnear : Integrable fun y => χ y * K y * (g (x - y) - g x) :=
    hχK.mul_bdd (c := 2 * B) (hgc.sub continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        calc |g (x - y) - g x| ≤ |g (x - y)| + |g x| := abs_sub _ _
          _ ≤ B + B := add_le_add (hgB _) (hgB _)
          _ ≤ 2 * B := by linarith)
  have hmean : ∫ y, (1 - χ y) * K y = -∫ y, χ y * K y := by
    have h : ∫ y, (1 - χ y) * K y = (∫ y, K y) - ∫ y, χ y * K y := by
      rw [← integral_sub hK hχK]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [h, hK0, zero_sub]
  have hsplit : ∀ y, K y * g (x - y) =
      χ y * K y * (g (x - y) - g x) + (1 - χ y) * K y * g (x - y) + g x * (χ y * K y) :=
    fun y => by ring
  calc ∫ y, K y * g (x - y)
      = ∫ y, (χ y * K y * (g (x - y) - g x) + (1 - χ y) * K y * g (x - y)
          + g x * (χ y * K y)) := integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = (∫ y, χ y * K y * (g (x - y) - g x)) + (∫ y, (1 - χ y) * K y * g (x - y))
          + g x * ∫ y, χ y * K y := by
      have hAB : Integrable fun y => χ y * K y * (g (x - y) - g x)
          + (1 - χ y) * K y * g (x - y) := hnear.add hfar
      rw [integral_add hAB (hχK.const_mul (g x)), integral_add hnear hfar, integral_const_mul]
    _ = (∫ y, χ y * K y * (g (x - y) - g x)) + (∫ y, (1 - χ y) * K y * g (x - y)) -
          g x * ∫ y, (1 - χ y) * K y := by
      rw [hmean]
      ring

end

end LatticeProb.Analysis.Schauder
