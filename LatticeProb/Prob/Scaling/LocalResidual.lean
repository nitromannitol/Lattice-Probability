/- Bounded tests of local weak residuals, localized by positivity.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.CompactPairing
import LatticeProb.Prob.Scaling.PositiveCutoff

open MeasureTheory Set
open LatticeProb.Scaling.BoundedFunctionalLift
noncomputable section
namespace LatticeProb.Scaling.LocalResidual
open LatticeProb.Scaling.PositiveCutoff
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K S : Set E}

/-- A bounded, positivity-cutoff-localized test of the local weak residual
`∫_K f · a - b`: the cutoff detects positivity of `f` on `S`, and the capped absolute
residual is bounded so the whole test lies in `[0, 1]`. -/
def test (μ : Measure E) (K S : Set E) (δ : ℝ) (a : E → ℝ) (b : ℝ) (f : E → ℝ) : ℝ :=
  cutoff S δ f * min 1 |(∫ p in K, f p * a p ∂μ) - b|

/-- The test is nonnegative. -/
theorem test_nonneg (μ : Measure E) (K S : Set E) (δ : ℝ) (a : E → ℝ) (b : ℝ) (f : E → ℝ) :
    0 ≤ test μ K S δ a b f := mul_nonneg (cutoff_nonneg _ _ _) (le_min zero_le_one (abs_nonneg _))

/-- The test is bounded by `1`. -/
theorem test_le_one (μ : Measure E) (K S : Set E) (δ : ℝ) (a : E → ℝ) (b : ℝ) (f : E → ℝ) :
    test μ K S δ a b f ≤ 1 := by
  exact (mul_le_mul (cutoff_le_one _ _ _) (min_le_left _ _) (le_min zero_le_one (abs_nonneg _)) zero_le_one).trans_eq (mul_one 1)

/-- The unit-capped absolute value is `1`-Lipschitz. -/
theorem abs_cap_sub_le (x y : ℝ) : |min 1 |x| - min 1 (|y|)| ≤ |x - y| := by
  have hl : LipschitzWith 1 (fun z : ℝ => min 1 z) := LipschitzWith.id.const_min 1
  have hm : |min 1 |x| - min 1 (|y|)| ≤ |(|x|) - (|y|)| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul |x| |y|
  exact hm.trans (abs_abs_sub_abs_le_abs_sub x y)

/-- The test is Lipschitz in the field `f`, for the sup distance on `K`, with a constant
depending on the cutoff scale `δ`, the measure of `K` and a uniform bound `M` on `a`. -/
theorem abs_test_sub_le [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    (hSK : S ⊆ K) {δ : ℝ} (hδ : 0 < δ) {a : E → ℝ} (ha : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (hab : ∀ p ∈ K, |a p| ≤ M)
    (b : ℝ) {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ B : ℝ, ∀ p ∈ K, |f p| ≤ B) (hgb : ∃ B : ℝ, ∀ p ∈ K, |g p| ≤ B) :
    |test μ K S δ a b f - test μ K S δ a b g| ≤
      (1 / δ + μ.real K * M) * supDistOn K f g := by
  have hpair := CompactPairing.abs_pairing_sub_le (μ := μ) hK hf hg ha hfb hgb hM hab
  obtain ⟨B, hb⟩ := hfb
  obtain ⟨C, hc⟩ := hgb
  have hd : ∀ p ∈ S, |f p - g p| ≤ supDistOn K f g := by
    intro p hp
    apply le_supDistOn (M := |B| + |C|) (by positivity) _ (hSK hp)
    intro q hq
    exact (abs_sub _ _).trans (add_le_add ((hb q hq).trans (le_abs_self B)) ((hc q hq).trans (le_abs_self C)))
  have hcut := abs_cutoff_sub_le hδ (supDistOn_nonneg K f g) hd
  let x := (∫ p in K, f p * a p ∂μ) - b
  let y := (∫ p in K, g p * a p ∂μ) - b
  have hr : |min 1 |x| - min 1 (|y|)| ≤ (μ.real K * M) * supDistOn K f g := by
    apply (abs_cap_sub_le x y).trans
    simpa only [x, y, sub_sub_sub_cancel_right] using hpair
  have he : test μ K S δ a b f - test μ K S δ a b g =
      (cutoff S δ f - cutoff S δ g) * min 1 |x| +
        cutoff S δ g * (min 1 |x| - min 1 |y|) := by unfold test; dsimp [x,y]; ring
  rw [he]
  calc
    _ ≤ |(cutoff S δ f - cutoff S δ g) * min 1 (|x|)| +
      |cutoff S δ g * (min 1 |x| - min 1 |y|)| := abs_add_le _ _
    _ ≤ (supDistOn K f g / δ) * 1 + 1 * ((μ.real K * M) * supDistOn K f g) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (le_min zero_le_one (abs_nonneg x)),
        abs_of_nonneg (cutoff_nonneg S δ g)]
      exact add_le_add (mul_le_mul hcut (min_le_left _ _) (le_min zero_le_one (abs_nonneg _))
        (div_nonneg (supDistOn_nonneg K f g) hδ.le))
        (mul_le_mul (cutoff_le_one _ _ _) hr (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- The test is `1`-Lipschitz in the target value `b`. -/
theorem abs_test_block_sub_le (μ : Measure E) (K S : Set E) (δ : ℝ)
    (a : E → ℝ) (b c : ℝ) (f : E → ℝ) :
    |test μ K S δ a b f - test μ K S δ a c f| ≤ |b - c| := by
  unfold test
  rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
  have he : |min 1 |(∫ p in K, f p * a p ∂μ) - b| - min 1 (|(∫ p in K, f p * a p ∂μ) - c|)| ≤ |b - c| := by
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using abs_cap_sub_le
      ((∫ p in K, f p * a p ∂μ) - b) ((∫ p in K, f p * a p ∂μ) - c)
  exact (mul_le_mul (cutoff_le_one _ _ _) he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Vanishing expectations of the cutoff tests imply the local identity almost surely. -/
theorem ae_pairing_eq_of_cutoff_integrals
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    [TopologicalSpace E] (hS : IsCompact S) (u : Ω → E → ℝ) (b : Ω → ℝ) (a : E → ℝ)
    (hu : ∀ ω, Continuous (u ω))
    (hm : ∀ n : ℕ, Measurable fun ω => test μ K S (1 / ((n : ℝ) + 1)) a (b ω) (u ω))
    (hz : ∀ n : ℕ, (∫ ω, test μ K S (1 / ((n : ℝ) + 1)) a (b ω) (u ω) ∂Q) = 0) :
    ∀ᵐ ω ∂Q, (∀ p ∈ S, 0 < u ω p) → (∫ p in K, u ω p * a p ∂μ) = b ω := by
  have hall : ∀ᵐ ω ∂Q, ∀ n : ℕ, test μ K S (1 / ((n : ℝ) + 1)) a (b ω) (u ω) = 0 := by
    apply ae_all_iff.mpr
    intro n
    have hi : Integrable (fun ω => test μ K S (1 / ((n : ℝ) + 1)) a (b ω) (u ω)) Q :=
      Integrable.of_bound (hm n).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (test_nonneg _ _ _ _ _ _ _)]
        exact test_le_one _ _ _ _ _ _ _)
    exact (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun ω => test_nonneg _ _ _ _ _ _ _) hi).mp (hz n)
  filter_upwards [hall] with ω hω hpos
  obtain ⟨n, hn⟩ := exists_cutoff_eq_one hS (hu ω).continuousOn hpos
  have he := hω n
  simp only [test, hn, one_mul] at he
  apply sub_eq_zero.mp
  by_contra hne
  have hp := lt_min one_pos (abs_pos.mpr hne)
  rw [he] at hp
  exact (lt_irrefl 0) hp

end LatticeProb.Scaling.LocalResidual
