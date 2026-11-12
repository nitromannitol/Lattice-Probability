import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Packing of disjoint discs and the inverse-square kernel on planar annuli

Two elementary facts of plane geometry used for crude effective-resistance bounds on planar
cell graphs (cells with disjoint interiors, each containing a disc comparable to its diameter):

* `card_mul_le_measure_of_pairwiseDisjoint`: pairwise disjoint measurable sets of measure at
  least `m` contained in `B` number at most `μ B / m` (packing by measure).
* `card_mul_sq_le_sq_of_pairwiseDisjoint_ball`: pairwise disjoint open discs of radius at least
  `r > 0` contained in a closed disc of radius `R` number at most `(R / r) ^ 2`.
* `integral_indicator_inv_sq_norm_sub`: polar coordinates
  (`MeasureTheory.integral_fun_norm_addHaar`) give
  `∫_{r ≤ |w - u| ≤ R} |w - u|⁻² dw = 2π log (R / r)`.
* `lintegral_inv_sq_norm_sub_le_of_subset_annulus`: the Lebesgue integral of `|w - u|⁻²` over
  any set contained in the closed annulus `r ≤ |w - u| ≤ R` is at most `2π log (R / r)`; this is
  the logarithmic energy of the radial unit flow from a disc of radius `r` to a circle of
  radius `R`.
-/

open MeasureTheory Set Metric
open scoped ENNReal Real

namespace LatticeProb

/-- Packing by measure: if the sets `A i`, `i ∈ s`, are pairwise disjoint, measurable, contained
in `B`, and each has measure at least `m`, then `#s * m ≤ μ B`. -/
theorem card_mul_le_measure_of_pairwiseDisjoint {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) {s : Finset ι} {A : ι → Set α} {B : Set α} {m : ℝ≥0∞}
    (hd : (s : Set ι).PairwiseDisjoint A) (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hsub : ∀ i ∈ s, A i ⊆ B) (hm : ∀ i ∈ s, m ≤ μ (A i)) :
    (s.card : ℝ≥0∞) * m ≤ μ B := by
  calc (s.card : ℝ≥0∞) * m = ∑ _i ∈ s, m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, μ (A i) := Finset.sum_le_sum hm
    _ = μ (⋃ i ∈ s, A i) := (measure_biUnion_finset hd hmeas).symm
    _ ≤ μ B := measure_mono (iUnion₂_subset hsub)

/-- Packing of discs in the plane: pairwise disjoint open discs `ball (c i) (ρ i)`, `i ∈ s`, of
radii `ρ i ≥ r > 0`, all contained in the closed disc `closedBall z R`, satisfy
`#s * r ^ 2 ≤ R ^ 2`. -/
theorem card_mul_sq_le_sq_of_pairwiseDisjoint_ball {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {ρ : ι → ℝ} {z : ℂ} {r R : ℝ} (hr : 0 < r)
    (hd : (s : Set ι).PairwiseDisjoint fun i => ball (c i) (ρ i))
    (hsub : ∀ i ∈ s, ball (c i) (ρ i) ⊆ closedBall z R) (hρ : ∀ i ∈ s, r ≤ ρ i) :
    (s.card : ℝ) * r ^ 2 ≤ R ^ 2 := by
  have hpack := card_mul_le_measure_of_pairwiseDisjoint volume (m := ENNReal.ofReal r ^ 2 * NNReal.pi)
    hd (fun i _ => measurableSet_ball) hsub (fun i hi => by
      rw [Complex.volume_ball]
      gcongr
      exact hρ i hi)
  rw [Complex.volume_closedBall, ← mul_assoc] at hpack
  have hpi0 : ((NNReal.pi : ℝ≥0∞)) ≠ 0 := by simp [NNReal.pi_ne_zero]
  have hpitop : ((NNReal.pi : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  have h1 : (s.card : ℝ≥0∞) * ENNReal.ofReal r ^ 2 ≤ ENNReal.ofReal R ^ 2 :=
    (ENNReal.mul_le_mul_iff_left hpi0 hpitop).1 hpack
  have h2 : ENNReal.ofReal ((s.card : ℝ) * r ^ 2) ≤ ENNReal.ofReal (R ^ 2) := by
    rcases le_or_gt 0 R with hR | hR
    · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hr.le,
        ENNReal.ofReal_pow hR, ENNReal.ofReal_natCast]
      exact h1
    · rw [ENNReal.ofReal_of_nonpos hR.le] at h1
      have h0 : (s.card : ℝ≥0∞) * ENNReal.ofReal r ^ 2 = 0 := by
        rw [zero_pow two_ne_zero] at h1
        exact le_antisymm h1 zero_le
      have hr2 : ENNReal.ofReal r ^ 2 ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le.2 hr]
      have hs : (s.card : ℝ≥0∞) = 0 := (mul_eq_zero.1 h0).resolve_right hr2
      have hs' : (s.card : ℝ) = 0 := by exact_mod_cast hs
      rw [hs', zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg R)).1 h2

/-- The inverse-square kernel cut to the closed annulus `r ≤ t ≤ R`. -/
private theorem integrableOn_Ioi_mul_indicator_inv_sq {r R : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y * (Icc r R).indicator (fun t : ℝ => (t ^ 2)⁻¹) y) (Ioi 0) := by
  have heq : (fun y : ℝ => y * (Icc r R).indicator (fun t : ℝ => (t ^ 2)⁻¹) y)
      = (Icc r R).indicator (fun y : ℝ => y * (y ^ 2)⁻¹) := by
    funext y
    by_cases hy : y ∈ Icc r R <;> simp [hy]
  rw [heq]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_ |>.integrableOn
  refine ContinuousOn.integrableOn_Icc ?_
  refine ContinuousOn.mul continuousOn_id (ContinuousOn.inv₀ (by fun_prop) ?_)
  intro y hy
  exact pow_ne_zero 2 (lt_of_lt_of_le hr hy.1).ne'

/-- Polar coordinates in the plane: `∫_{r ≤ |w - u| ≤ R} |w - u|⁻² dw = 2π log (R / r)`. -/
theorem integral_indicator_inv_sq_norm_sub (u : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∫ w : ℂ, (Icc r R).indicator (fun t : ℝ => (t ^ 2)⁻¹) ‖w - u‖ = 2 * π * Real.log (R / r) := by
  set f : ℝ → ℝ := (Icc r R).indicator (fun t : ℝ => (t ^ 2)⁻¹) with hf
  rw [integral_sub_right_eq_self (fun w : ℂ => f ‖w‖) u, integral_fun_norm_addHaar volume f,
    Complex.finrank_real_complex]
  have hball : (volume : Measure ℂ).real (ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [hball]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f y = Real.log (R / r) := by
    have h1 : ∀ y : ℝ, y ^ (2 - 1) • f y = (Icc r R).indicator (fun y : ℝ => y⁻¹) y := by
      intro y
      by_cases hy : y ∈ Icc r R
      · have hy0 : y ≠ 0 := (lt_of_lt_of_le hr hy.1).ne'
        simp only [hf, indicator_of_mem hy, smul_eq_mul, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
        field_simp
      · simp [hf, hy]
    simp_rw [h1]
    rw [setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 (show Icc r R ⊆ Ioi (0 : ℝ) from fun y hy => lt_of_lt_of_le hr hy.1), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hrR, integral_inv_of_pos hr (lt_of_lt_of_le hr hrR)]
  rw [hint, nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The inverse-square kernel on a set inside a closed annulus: if `A ⊆ closedBall u R \ ball u r`
with `0 < r ≤ R`, then `∫⁻_{A} |w - u|⁻² dw ≤ 2π log (R / r)`. -/
theorem lintegral_inv_sq_norm_sub_le_of_subset_annulus (u : ℂ) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) {A : Set ℂ} (hA : A ⊆ closedBall u R \ ball u r) :
    ∫⁻ w in A, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹)
      ≤ ENNReal.ofReal (2 * π * Real.log (R / r)) := by
  set f : ℝ → ℝ := (Icc r R).indicator (fun t : ℝ => (t ^ 2)⁻¹) with hf
  have hS : MeasurableSet (closedBall u R \ ball u r) :=
    measurableSet_closedBall.diff measurableSet_ball
  have hpt : ∀ w : ℂ, (closedBall u R \ ball u r).indicator
      (fun w => ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹)) w = ENNReal.ofReal (f ‖w - u‖) := by
    intro w
    have hmem : w ∈ closedBall u R \ ball u r ↔ ‖w - u‖ ∈ Icc r R := by
      simp only [mem_sdiff, mem_closedBall, mem_ball, not_lt, mem_Icc, dist_eq_norm]
      exact and_comm
    by_cases hw : w ∈ closedBall u R \ ball u r
    · rw [indicator_of_mem hw, hf, indicator_of_mem (hmem.1 hw)]
    · rw [indicator_of_notMem hw, hf, indicator_of_notMem (fun h => hw (hmem.2 h)),
        ENNReal.ofReal_zero]
  have hfi : Integrable (fun w : ℂ => f ‖w - u‖) := by
    have h0 : Integrable (fun w : ℂ => f ‖w‖) :=
      (integrable_fun_norm_addHaar volume (f := f)).2 (by
        rw [Complex.finrank_real_complex]
        simpa [smul_eq_mul, hf] using integrableOn_Ioi_mul_indicator_inv_sq (R := R) hr)
    exact h0.comp_sub_right u
  have hfnn : 0 ≤ᵐ[volume] fun w : ℂ => f ‖w - u‖ :=
    Filter.Eventually.of_forall fun w => by
      simp only [hf]
      exact indicator_nonneg (fun t _ => inv_nonneg.2 (sq_nonneg t)) _
  calc ∫⁻ w in A, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹)
      ≤ ∫⁻ w in closedBall u R \ ball u r, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) :=
        lintegral_mono_set hA
    _ = ∫⁻ w, ENNReal.ofReal (f ‖w - u‖) := by
        rw [← lintegral_indicator hS]
        exact lintegral_congr fun w => hpt w
    _ = ENNReal.ofReal (∫ w : ℂ, f ‖w - u‖) := (ofReal_integral_eq_lintegral_ofReal hfi hfnn).symm
    _ = ENNReal.ofReal (2 * π * Real.log (R / r)) := by
        rw [hf, integral_indicator_inv_sq_norm_sub u hr hrR]

end LatticeProb
