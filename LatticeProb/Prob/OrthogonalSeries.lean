import LatticeProb.Analysis.WeightedSquareSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Second moments of orthogonal series

A uniformly bounded orthogonal real family with absolutely summable coefficients has a
diagonal second moment. A summable double-series bound justifies integration term by term.
-/

namespace LatticeProb

open MeasureTheory

noncomputable section

/-- The second moment of an absolutely summable orthogonal family is diagonal. -/
theorem integral_sq_tsum {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {b : ι → ℝ}
    (hb : Summable b) (hm : ∀ i, Measurable (X i)) {K : ℝ} (hK : 0 ≤ K)
    (hX : ∀ i ω, |X i ω| ≤ K)
    (horth : ∀ i j, i ≠ j → ∫ ω, X i ω * X j ω ∂P = 0) :
    ∫ ω, (∑' i, b i * X i ω) ^ 2 ∂P =
      ∑' i, b i ^ 2 * ∫ ω, X i ω ^ 2 ∂P := by
  classical
  let F : ι × ι → Ω → ℝ := fun ij ω =>
    (b ij.1 * X ij.1 ω) * (b ij.2 * X ij.2 ω)
  let bound : ι × ι → ℝ := fun ij => |b ij.1| * |b ij.2| * K ^ 2
  have hbound : ∀ ij ω, ‖F ij ω‖ ≤ bound ij := by
    intro ij ω
    dsimp only [F, bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    calc
      _ = (|b ij.1| * |b ij.2|) * (|X ij.1 ω| * |X ij.2 ω|) := by ring
      _ ≤ (|b ij.1| * |b ij.2|) * (K * K) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hX _ _) (hX _ _) (abs_nonneg _) hK) (by positivity)
      _ = _ := by ring
  have hsum : Summable bound :=
    (hb.abs.mul_of_nonneg hb.abs (fun i => abs_nonneg _) (fun i => abs_nonneg _)).mul_right _
  have hs (ω : Ω) : Summable (fun ij => F ij ω) := hsum.of_norm_bounded (fun ij => hbound ij ω)
  have hexpand (ω : Ω) : (∑' i, b i * X i ω) ^ 2 = ∑' ij, F ij ω := by
    rw [pow_two]
    exact (summable_weighted_bounded hb hX ω).tsum_mul_tsum
      (summable_weighted_bounded hb hX ω) (hs ω)
  simp_rw [hexpand]
  have hint : HasSum (fun ij => ∫ ω, F ij ω ∂P) (∫ ω, ∑' ij, F ij ω ∂P) := by
    apply hasSum_integral_of_dominated_convergence (fun ij _ => bound ij)
    · intro ij
      exact (((hm _).const_mul _).mul ((hm _).const_mul _)).aestronglyMeasurable
    · intro ij
      exact ae_of_all _ (hbound ij)
    · exact ae_of_all _ (fun _ => hsum)
    · exact integrable_const _
    · exact ae_of_all _ (fun ω => (hs ω).hasSum)
  rw [← hint.tsum_eq]
  have hdiag (ij : ι × ι) : (∫ ω, F ij ω ∂P) =
      if ij.2 = ij.1 then b ij.1 ^ 2 * ∫ ω, X ij.1 ω ^ 2 ∂P else 0 := by
    dsimp only [F]
    have hterm (ω) : (b ij.1 * X ij.1 ω) * (b ij.2 * X ij.2 ω) =
        (b ij.1 * b ij.2) * (X ij.1 ω * X ij.2 ω) := by ring
    simp_rw [hterm]
    rw [integral_const_mul]
    by_cases he : ij.2 = ij.1
    · simp only [he, ↓reduceIte, ← pow_two]
    · rw [horth _ _ (Ne.symm he), mul_zero, if_neg he]
  simp_rw [hdiag]
  have hd : Summable (fun ij : ι × ι =>
      if ij.2 = ij.1 then b ij.1 ^ 2 * ∫ ω, X ij.1 ω ^ 2 ∂P else 0) :=
    hint.summable.congr hdiag
  rw [hd.tsum_prod]
  simp only [tsum_ite_eq]

end

end LatticeProb
