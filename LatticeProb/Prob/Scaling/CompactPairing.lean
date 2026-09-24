/- Bounded measurable pairings and their uniform-distance estimates.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.BoundedFunctionalLift

open MeasureTheory Set
open LatticeProb.Scaling.BoundedFunctionalLift
noncomputable section
namespace LatticeProb.Scaling.CompactPairing
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : Set E}

/-- Bounded measurable factors are integrable on a finite-measure set. -/
theorem integrableOn_mul [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    {f a : E → ℝ} (hf : Measurable f) (ha : Measurable a)
    {B M : ℝ} (hb : ∀ p ∈ K, |f p| ≤ B) (hm : ∀ p ∈ K, |a p| ≤ M) :
    IntegrableOn (fun p => f p * a p) K μ := by
  apply Integrable.of_bound (hf.mul ha).aestronglyMeasurable (|B| * |M|)
  filter_upwards [ae_restrict_mem hK] with p hp
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul ((hb p hp).trans (le_abs_self B)) ((hm p hp).trans (le_abs_self M))
    (abs_nonneg _) (abs_nonneg _)

/-- Pairing against a bounded coefficient is Lipschitz for uniform distance on its support. -/
theorem abs_pairing_sub_le [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    {f g a : E → ℝ} (hf : Measurable f) (hg : Measurable g) (ha : Measurable a)
    (hfb : ∃ B : ℝ, ∀ p ∈ K, |f p| ≤ B) (hgb : ∃ B : ℝ, ∀ p ∈ K, |g p| ≤ B)
    {M : ℝ} (_hM : 0 ≤ M) (hab : ∀ p ∈ K, |a p| ≤ M) :
    |(∫ p in K, f p * a p ∂μ) - (∫ p in K, g p * a p ∂μ)| ≤
      (μ.real K * M) * supDistOn K f g := by
  obtain ⟨B, hb⟩ := hfb
  obtain ⟨C, hc⟩ := hgb
  have hi := integrableOn_mul (μ := μ) hK hf ha hb hab
  have hj := integrableOn_mul (μ := μ) hK hg ha hc hab
  have he : (fun p => f p * a p - g p * a p) = fun p => (f p - g p) * a p := by
    funext p; ring
  rw [← integral_sub hi hj, he]
  apply abs_integral_le_integral_abs.trans
  have hdom : ∀ p ∈ K, |(f p - g p) * a p| ≤ supDistOn K f g * M := by
    intro p hp
    rw [abs_mul]
    apply mul_le_mul _ (hab p hp) (abs_nonneg _) (supDistOn_nonneg K f g)
    apply le_supDistOn (M := |B| + |C|) (by positivity) _ hp
    intro q hq
    exact (abs_sub _ _).trans (add_le_add ((hb q hq).trans (le_abs_self B)) ((hc q hq).trans (le_abs_self C)))
  calc
    (∫ p in K, |(f p - g p) * a p| ∂μ) ≤ ∫ _p in K, supDistOn K f g * M ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) (integrable_const _)
        ((ae_restrict_mem hK).mono fun p hp => hdom p hp)
    _ = _ := by simp [Measure.real, smul_eq_mul]; ring

/-- A bounded coefficient error is controlled by the actual nonnegative local mass. -/
theorem abs_integral_mul_le_mass (hK : MeasurableSet K) {u a : E → ℝ} {ε : ℝ}
    (hu : IntegrableOn u K μ) (hpos : ∀ p ∈ K, 0 ≤ u p)
    (ha : ∀ p ∈ K, |a p| ≤ ε) :
    |∫ p in K, u p * a p ∂μ| ≤ ε * ∫ p in K, u p ∂μ := by
  apply abs_integral_le_integral_abs.trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) (hu.const_mul ε)
  filter_upwards [ae_restrict_mem hK] with p hp
  rw [abs_mul, abs_of_nonneg (hpos p hp), mul_comm ε]
  exact mul_le_mul_of_nonneg_left (ha p hp) (hpos p hp)

end LatticeProb.Scaling.CompactPairing
