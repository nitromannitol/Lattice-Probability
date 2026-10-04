/-
The l2-versus-sup transport step for the Gaussian Herbst input, and the
`Fin n` Gaussian concentration in the l2 (Cameron–Martin) form.

`LatticeProb.gaussian_lipschitz_concentration` (`Prob/GaussianHerbst.lean`)
consumes `GaussianHerbstBound n`, whose `LipschitzWith` is taken with respect to
the Pi (sup) metric on `Fin n → ℝ`.  The frozen form used downstream
(`Sandpile.External.GaussianLipschitzConcentration`) instead hypothesises the
l2 Lipschitz condition
`HasSum (fun i => (w i - e i) ^ 2) M → |F w - F e| ≤ L * sqrt M`.

The two classes differ: `sup_i |a i| ≤ sqrt (∑ i, a i ^ 2) ≤ sqrt n * sup_i |a i|`.
Hence the l2 condition at constant `L` gives the sup-metric `LipschitzWith` only
at constant `L * sqrt n`, and the concentration below loses a factor `n` in the
exponent.  The exact frozen constant `L` is not reachable this way; this module
proves the closest available reduction, together with the deterministic
`l2`-versus-sup comparison it rests on.
-/
import LatticeProb.Prob.GaussianHerbst
import LatticeProb.Gauss.Coords

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

noncomputable section

/-- On `Fin n → ℝ` the l2 distance is at most `sqrt n` times the sup distance. -/
theorem sqrt_sum_sq_le_sqrt_card_mul_dist {n : ℕ} (x y : Fin n → ℝ) :
    Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Real.sqrt n * dist x y := by
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hcoord : ∀ i : Fin n, |x i - y i| ≤ dist x y := by
    intro i
    have h := (dist_pi_le_iff hdist).mp le_rfl i
    simpa [Real.dist_eq] using h
  have hsum : ∑ i, (x i - y i) ^ 2 ≤ (n : ℝ) * (dist x y) ^ 2 := by
    calc ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin n, (dist x y) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs (x i - y i)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
      _ = (n : ℝ) * (dist x y) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc Real.sqrt (∑ i, (x i - y i) ^ 2)
      ≤ Real.sqrt ((n : ℝ) * (dist x y) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * dist x y := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hdist]

/-- The l2-Lipschitz condition at constant `L` implies the Pi-metric
`LipschitzWith` at constant `L * sqrt n`. -/
theorem lipschitzWith_pi_of_hasSum_sq {n : ℕ} {F : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hLip : ∀ (ω η : Fin n → ℝ) (M : ℝ), HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * Real.sqrt M) :
    LipschitzWith ⟨L * Real.sqrt n, mul_nonneg hL (Real.sqrt_nonneg n)⟩ F := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  have h1 := hLip x y (∑ i, (x i - y i) ^ 2) (hasSum_fintype _)
  have h2 := sqrt_sum_sq_le_sqrt_card_mul_dist x y
  calc |F x - F y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2) := h1
    _ ≤ L * (Real.sqrt n * dist x y) := mul_le_mul_of_nonneg_left h2 hL
    _ = (L * Real.sqrt n) * dist x y := by ring

/-- **The l2 form of Gaussian concentration on `Fin n`.**  The event and the
`ℝ≥0∞` bound are those of the frozen
`Sandpile.External.GaussianLipschitzConcentration` at index type `Fin n`; the
constant is `L * sqrt n` because the library's Herbst input is sup-metric while
the frozen hypothesis is l2. -/
theorem gaussian_lipschitz_concentration_l2_fin (n : ℕ)
    (hHerbst : GaussianHerbstBound n)
    (F : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ (ω η : Fin n → ℝ) (M : ℝ), HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * Real.sqrt M)
    (t : ℝ) (ht : 0 ≤ t) :
    (gaussLaw (Fin n)) {ω | ∫ η, F η ∂(gaussLaw (Fin n)) + t ≤ F ω}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (L * Real.sqrt n) ^ 2))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    rw [measure_univ]
    norm_num [Real.sqrt_zero, Real.exp_zero]
  · rw [gaussLaw, Measure.infinitePi_eq_pi]
    have hf := lipschitzWith_pi_of_hasSum_sq hL.le hLip
    have hconc := gaussian_lipschitz_concentration n hHerbst F (L * Real.sqrt n)
      (mul_pos hL (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))) hf t ht
    have hev : {ω : Fin n → ℝ |
          (∫ η, F η ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) + t ≤ F ω}
        = {x : Fin n → ℝ |
          t ≤ F x - ∫ y, F y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [hev]
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (Real.exp_pos _).le).mpr ?_
    simpa only [MeasureTheory.Measure.real] using hconc

end

end LatticeProb
