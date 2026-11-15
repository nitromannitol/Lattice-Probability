import LatticeProb.Analysis.Elliptic.Dirichlet

/-!
# Constant coefficient specializations of Gilbarg–Trudinger

These propositions describe cited inputs as explicit hypotheses. The operator in the book's
sign convention is `a₀ Δ − μ`, with right side `−f` and zero boundary data. Norms of
derivatives are taken on the open domain, independently of values outside its closure.
-/

namespace LatticeProb.External

open LatticeProb.Elliptic
open scoped ENNReal

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.19, printed p. 111,
with `k = 0`, zero boundary data, and operator `a₀ Δ − μ`; the theorem needs no sign on `c`.
The conclusion records the finite coordinate `C^{2,σ}` norm on the open domain. -/
def GilbargTrudingerBoundaryRegularity : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f u : (Fin d → ℝ) → ℝ),
          c0HolderNorm σ (closure U) f < ⊤ →
          IsClassicalDirichletSolution U μ a₀ f u → c2HolderNorm σ U u < ⊤

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.6, printed pp. 98–99,
for zero boundary data and constant operator `a₀ Δ − μ`, with `λ = Λ⁻¹` and the book's
`C(n, α, λ, Λ, Ω)` read as `C` depending on `d`, `σ`, `U`, `Λ` only: uniform in the
coefficients `a₀`, `μ`, the datum and the solution. Finite `C^{2,σ}` regularity is an a priori
hypothesis, supplied separately by Theorem 6.19. -/
def GilbargTrudingerSchauderEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (Λ : ℝ), 1 ≤ Λ → ∃ C : ℝ, 0 < C ∧
        ∀ (a₀ μ : ℝ), a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
          ∀ (f u : (Fin d → ℝ) → ℝ),
            c0HolderNorm σ (closure U) f < ⊤ →
            IsClassicalDirichletSolution U μ a₀ f u →
            c2HolderNorm σ U u < ⊤ →
            c2HolderNorm σ U u ≤
              ENNReal.ofReal C * (supNorm U u + c0HolderNorm σ (closure U) f)

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 3.7, printed p. 36,
equality case with zero boundary data, `b = 0`, and `c = −μ ≤ 0`.
The constant depends only on the bounded domain, uniformly in positive `a₀` and `μ ≥ 0`;
the minimum eigenvalue is `a₀`, giving exactly the factor `C / a₀`. -/
def GilbargTrudingerSupEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f u : (Fin d → ℝ) → ℝ), supNorm U f < ⊤ →
          IsClassicalDirichletSolution U μ a₀ f u →
          supNorm U u ≤ ENNReal.ofReal (C / a₀) * supNorm U f

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Lemma 6.37, printed
pp. 136–137, with `k = 2` and fixed `0 < σ < 1`; the book's `C(k, Ω, Ω')` is here allowed to
depend also on `σ`. A function with interior `C²` regularity and finite `C^{2,σ}` norm on
the domain extends to a compactly supported global `C²` function, supported inside the
prescribed open neighborhood of the closure. The bound is uniform in the function. -/
def GilbargTrudingerHolderExtension : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (U' : Set (Fin d → ℝ)), IsOpen U' → closure U ⊆ U' →
        ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin d → ℝ) → ℝ),
          ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
          ∃ v : (Fin d → ℝ) → ℝ,
            ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U' ∧
              Set.EqOn v u U ∧
              c2HolderNorm σ U' v ≤ ENNReal.ofReal C * c2HolderNorm σ U u

end LatticeProb.External
