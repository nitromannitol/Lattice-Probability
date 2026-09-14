/-
Basic facts about the Fourier-side Sobolev norms: monotonicity of the norm in
the order, antitonicity of the dual norm, and the elementary estimates on the
dual norm (scaling, sums, domination).
-/
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- For `s₀ ≤ s` the weight `(1 + (2π‖ξ‖)²)^s` dominates the weight at `s₀`,
so the `H^{s₀}` norm of a test function is at most its `H^s` norm. -/
theorem sobolevNormSq_mono {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (φ : Space d → ℝ) :
    sobolevNormSq d s₀ φ ≤ sobolevNormSq d s φ := by
  apply MeasureTheory.lintegral_mono
  intro ξ
  apply ENNReal.ofReal_le_ofReal
  have hbase : (1 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hbase h) (sq_nonneg _)

/-- The dual norm is monotone in the order: a larger `s` gives a smaller weight
on the test functions, hence a smaller dual norm. -/
theorem negSobolevNorm_anti {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D F ≤ negSobolevNorm d s₀ D F := by
  apply sSup_le_sSup
  rintro v ⟨φ, hφ, hnorm, rfl⟩
  refine ⟨φ, hφ, ?_, rfl⟩
  have hmono : sobolevNormSq d s₀ φ ≤ sobolevNormSq d s φ := sobolevNormSq_mono h φ
  exact le_trans hmono hnorm

/-- Scaling a functional by a constant scales its dual norm by the absolute
value of the constant. -/
theorem negSobolevNorm_smul_le {d : ℕ} (s : ℝ) (D : Set (Space d))
    (c : ℝ) (F : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D (fun φ => c * F φ)
      ≤ ENNReal.ofReal |c| * negSobolevNorm d s D F := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  have hF : ENNReal.ofReal |F φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |F ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  calc ENNReal.ofReal |c * F φ|
      = ENNReal.ofReal |c| * ENNReal.ofReal |F φ| := by
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    _ ≤ ENNReal.ofReal |c| * _ := mul_le_mul_right hF _

/-- The dual norm is subadditive: the norm of a sum of two functionals is at
most the sum of their norms. -/
theorem negSobolevNorm_add_le {d : ℕ} (s : ℝ) (D : Set (Space d))
    (F G : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D (fun φ => F φ + G φ)
      ≤ negSobolevNorm d s D F + negSobolevNorm d s D G := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  have hF : ENNReal.ofReal |F φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |F ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  have hG : ENNReal.ofReal |G φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |G ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  calc ENNReal.ofReal |F φ + G φ|
      ≤ ENNReal.ofReal (|F φ| + |G φ|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |F φ| + ENNReal.ofReal |G φ| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hF hG

/-- The dual norm is monotone in the size of the functional. -/
theorem negSobolevNorm_le_of_abs_le {d : ℕ} (s : ℝ) (D : Set (Space d))
    (F G : (Space d → ℝ) → ℝ)
    (h : ∀ φ : Space d → ℝ, |F φ| ≤ |G φ|) :
    negSobolevNorm d s D F ≤ negSobolevNorm d s D G := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  exact le_trans (ENNReal.ofReal_le_ofReal (h φ)) (le_sSup ⟨φ, hφ, hn, rfl⟩)

/-- The dual norm is subadditive for differences: the norm of a difference of
two functionals is at most the sum of their norms. -/
theorem negSobolevNorm_sub_le {d : ℕ} (s : ℝ) (D : Set (Space d))
    (F G : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D (fun φ => F φ - G φ)
      ≤ negSobolevNorm d s D F + negSobolevNorm d s D G := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  have hF : ENNReal.ofReal |F φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |F ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  have hG : ENNReal.ofReal |G φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |G ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  calc ENNReal.ofReal |F φ - G φ|
      ≤ ENNReal.ofReal (|F φ| + |G φ|) := ENNReal.ofReal_le_ofReal (abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self (F φ), neg_abs_le (G φ)],
          by linarith [neg_abs_le (F φ), le_abs_self (G φ)]⟩)
    _ = ENNReal.ofReal |F φ| + ENNReal.ofReal |G φ| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hF hG

end LatticeProb.Sobolev
