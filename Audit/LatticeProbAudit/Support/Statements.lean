import Mathlib
import LatticeProbAudit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/LatticeProbAudit/StatementRegression.lean` checks that each solution
theorem has exactly this type, so that no library name or instance leaks into a
solution statement.
-/

namespace LatticeProbAudit.Statements

open LatticeProbAudit MeasureTheory ProbabilityTheory Filter Topology

universe u

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/LatticeProbAudit/Kingman/Challenge.lean`. -/
def kingman : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ (m n : ℕ) (x : Ω), g (m + n) x ≤ g m x + g n (T^[m] x))
    (hgm : ∀ n, Measurable (g n)) (hint : ∀ n, Integrable (g n) μ)
    {c : ℝ} (hlow : ∀ (n : ℕ) (x : Ω), 1 ≤ n → c * n ≤ g n x),
    (∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ => g n x / n) atTop (𝓝 L)) ∧
      Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
        (𝓝 (sInf ((fun n : ℕ => (∫ x, g n x ∂μ) / n) '' Set.Ici 1)))

/-- The statement of `Audit/LatticeProbAudit/GFF/Challenge.lean`. -/
def gff : Prop :=
  ∀ {V : Type u} {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (C : Finset V) {q : V} (hq : q ∉ C),
    (Matrix.of fun x y : C => killedGreenReal G (C : Set V) x y).PosSemidef ∧
      ∃ μ : Measure (EuclideanSpace ℝ C), IsGaussian μ ∧ ∫ φ, φ ∂μ = 0 ∧
        ∀ x y : C, cov[fun φ : EuclideanSpace ℝ C => φ x, fun φ => φ y; μ]
          = killedGreenReal G (C : Set V) x y

/-- The statement of `Audit/LatticeProbAudit/BinomialLocalCLT/Challenge.lean`. -/
def binomialLocalCLT : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ, j ≡ (m : ℤ) [ZMOD 2] → |j| ≤ (m : ℤ) →
      |Real.sqrt m * ((m.choose ((m + j) / 2).toNat : ℝ) / 2 ^ m)
          - 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(((j : ℝ) / Real.sqrt m) ^ 2) / 2))|
        ≤ C / m

end LatticeProbAudit.Statements
