import LatticeProb.Prob.BernsteinPredictableProduct
import Mathlib.Probability.Process.Filtration

/-!
# Normalized exponential products

Conditional exponential bounds with predictable exponents give integrable
normalized products with decreasing conditional expectations.
-/

open MeasureTheory ProbabilityTheory Filter

namespace LatticeProb

variable {Ω : Type*}

/-- A product normalized by its predictable exponential bounds. -/
noncomputable def normalizedExponentialProduct (Y H : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun ω => normalizedExponentialProduct Y H n ω * Real.exp (-H n ω) * Y n ω

/-- Normalized products are nonnegative when the factors are nonnegative. -/
theorem normalizedExponentialProduct_nonneg {Y H : ℕ → Ω → ℝ}
    (hY0 : ∀ n ω, 0 ≤ Y n ω) :
    ∀ n ω, 0 ≤ normalizedExponentialProduct Y H n ω := by
  intro n
  induction n with
  | zero => intro ω; exact zero_le_one
  | succ n ih =>
    intro ω
    exact mul_nonneg (mul_nonneg (ih ω) (Real.exp_pos _).le) (hY0 n ω)

/-- Conditional exponential bounds yield an integrable normalized product and
its one-step conditional supermartingale inequality. -/
theorem normalizedExponentialProduct_step {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ] {F : Filtration ℕ m₀} {Y H : ℕ → Ω → ℝ} {k : ℕ}
    (hYmeas : ∀ n, n < k → Measurable[F (n + 1)] (Y n))
    (hHmeas : ∀ n, n < k → Measurable[F n] (H n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hYint : ∀ n, n < k → Integrable (Y n) μ)
    (hYcond : ∀ n, n < k → μ[Y n | F n] ≤ᵐ[μ] fun ω => Real.exp (H n ω)) :
    (∀ n, n ≤ k → Measurable[F n] (normalizedExponentialProduct Y H n)) ∧
    (∀ n, n ≤ k → Integrable (normalizedExponentialProduct Y H n) μ) ∧
    (∀ n, n < k → μ[normalizedExponentialProduct Y H (n + 1) | F n] ≤ᵐ[μ]
      normalizedExponentialProduct Y H n) := by
  have hmeas : ∀ n, n ≤ k → Measurable[F n] (normalizedExponentialProduct Y H n) := by
    intro n
    induction n with
    | zero => intro _; exact measurable_const
    | succ n ih =>
      intro hn
      change Measurable[F (n + 1)] (fun ω =>
        normalizedExponentialProduct Y H n ω * Real.exp (-H n ω) * Y n ω)
      exact ((((ih (by omega)).mono (F.mono (Nat.le_succ n)) le_rfl).mul
        (((hHmeas n (by omega)).neg.exp).mono (F.mono (Nat.le_succ n)) le_rfl)).mul
          (hYmeas n (by omega)))
  have hstep : ∀ n, n < k → Integrable (normalizedExponentialProduct Y H n) μ →
      Integrable (normalizedExponentialProduct Y H (n + 1)) μ ∧
      μ[normalizedExponentialProduct Y H (n + 1) | F n] ≤ᵐ[μ]
        normalizedExponentialProduct Y H n := by
    intro n hnk hn
    have hf : StronglyMeasurable[F n] (fun ω =>
        normalizedExponentialProduct Y H n ω * Real.exp (-H n ω)) :=
      ((hmeas n (by omega)).mul (hHmeas n hnk).neg.exp).stronglyMeasurable
    have hf0 : ∀ ω, 0 ≤ normalizedExponentialProduct Y H n ω * Real.exp (-H n ω) :=
      fun ω => mul_nonneg (normalizedExponentialProduct_nonneg hY0 n ω) (Real.exp_pos _).le
    have hb : ∀ᵐ ω ∂μ,
        (normalizedExponentialProduct Y H n ω * Real.exp (-H n ω)) * (μ[Y n | F n]) ω ≤
          normalizedExponentialProduct Y H n ω := by
      filter_upwards [hYcond n hnk] with ω hω
      calc
        _ ≤ (normalizedExponentialProduct Y H n ω * Real.exp (-H n ω)) *
            Real.exp (H n ω) := mul_le_mul_of_nonneg_left hω (hf0 ω)
        _ = _ := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact condExp_mul_le_of_condExp_le (F.le n) hf hf0 (hYint n hnk) (hY0 n) hn hb
  have hint : ∀ n, n ≤ k → Integrable (normalizedExponentialProduct Y H n) μ := by
    intro n
    induction n with
    | zero => intro _; exact integrable_const 1
    | succ n ih =>
      intro hn
      exact (hstep n (by omega) (ih (by omega))).1
  exact ⟨hmeas, hint, fun n hn => (hstep n hn (hint n (by omega))).2⟩

/-- The normalized product has expectation at most one. -/
theorem integral_normalizedExponentialProduct_le_one
    {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {F : Filtration ℕ m₀} {Y H : ℕ → Ω → ℝ} {k : ℕ}
    (hYmeas : ∀ n, n < k → Measurable[F (n + 1)] (Y n))
    (hHmeas : ∀ n, n < k → Measurable[F n] (H n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hYint : ∀ n, n < k → Integrable (Y n) μ)
    (hYcond : ∀ n, n < k → μ[Y n | F n] ≤ᵐ[μ] fun ω => Real.exp (H n ω)) :
    (∫ ω, normalizedExponentialProduct Y H k ω ∂μ) ≤ 1 := by
  obtain ⟨_, hint, hstep⟩ :=
    normalizedExponentialProduct_step hYmeas hHmeas hY0 hYint hYcond
  have h : ∀ n, n ≤ k → (∫ ω, normalizedExponentialProduct Y H n ω ∂μ) ≤ 1 := by
    intro n
    induction n with
    | zero => intro _; simp [normalizedExponentialProduct]
    | succ n ih =>
      intro hn
      calc
        (∫ ω, normalizedExponentialProduct Y H (n + 1) ω ∂μ) =
            ∫ ω, (μ[normalizedExponentialProduct Y H (n + 1) | F n]) ω ∂μ :=
          (integral_condExp (F.le n)).symm
        _ ≤ ∫ ω, normalizedExponentialProduct Y H n ω ∂μ :=
          integral_mono_ae integrable_condExp (hint n (by omega)) (hstep n (by omega))
        _ ≤ 1 := ih (by omega)
  exact h k le_rfl

end LatticeProb
