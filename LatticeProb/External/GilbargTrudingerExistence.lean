import LatticeProb.External.GilbargTrudinger
import LatticeProb.Analysis.Elliptic.GTCheck

/-!
# Classical Dirichlet existence from Gilbarg–Trudinger

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 6.14
(existence and uniqueness of `C^{2,α}(Ω̄)` solutions of the Dirichlet problem on `C^{2,α}`
domains), specialized to the operator `a₀Δ − μ` with constant coefficients, zero boundary data
and Hölder right side, in dimension at least two. The proposition is stated so that a
formalization citing it can carry it as an explicit hypothesis; it is not proved here.
-/

namespace LatticeProb.External

open LatticeProb.Elliptic
open scoped ENNReal

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.14, printed p. 107,
for operator `a₀ Δ − μ`, right side `−f` and zero boundary data. The conclusion retains
existence and finite interior coordinate norm; no uniqueness of total extensions is claimed. -/
def GilbargTrudingerExistence : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f : (Fin d → ℝ) → ℝ), c0HolderNorm σ (closure U) f < ⊤ →
          ∃ u : (Fin d → ℝ) → ℝ,
            IsClassicalDirichletSolution U μ a₀ f u ∧ c2HolderNorm σ U u < ⊤

end LatticeProb.External

namespace LatticeProb.Elliptic

open LatticeProb.External
open scoped ENNReal BigOperators

variable {d : ℕ}

/-- The cited existence input supplies a classical solution on every admissible domain. -/
theorem exists_classicalDirichletSolution_of_gt (hGT : GilbargTrudingerExistence)
    (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {a₀ μ : ℝ} (ha₀ : 0 < a₀) (hμ : 0 ≤ μ)
    {f : (Fin d → ℝ) → ℝ} (hf : c0HolderNorm σ (closure U) f < ⊤) :
    ∃ u, IsClassicalDirichletSolution U μ a₀ f u := by
  obtain ⟨u, hu, _⟩ := hGT d hd σ hσ hσ1 U hU a₀ μ ha₀ hμ f hf
  exact ⟨u, hu⟩

/-- The Euclidean unit ball has the required domain regularity, proved in `Examples`. -/
theorem exists_classicalDirichletSolution_unitBall_of_gt (hGT : GilbargTrudingerExistence)
    (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {a₀ μ : ℝ} (ha₀ : 0 < a₀) (hμ : 0 < μ)
    {f : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm σ (closure (unitBall d)) f < ⊤) :
    ∃ u, IsClassicalDirichletSolution (unitBall d) μ a₀ f u ∧
      c2HolderNorm σ (unitBall d) u < ⊤ := by
  exact hGT d hd σ hσ hσ1 (unitBall d) (isC2HolderDomain_unitBall σ)
    a₀ μ ha₀ hμ.le f hf

/-- At positive mass, the input applies to the nonzero quadratic datum in dimension two. -/
theorem exists_quadratic_datum_solution_of_gt (hGT : GilbargTrudingerExistence) :
    ∃ u, IsClassicalDirichletSolution (unitBall 2) 1 1
      (fun x => 1 * (1 - ∑ k, x k ^ 2) + 2 * 2 * 1) u ∧
      c2HolderNorm (1 / 2) (unitBall 2) u < ⊤ := by
  exact exists_classicalDirichletSolution_unitBall_of_gt hGT (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (quadratic_datum_c0HolderNorm_lt_top (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) 1 1)

/-- The input's domain and datum premises occur at an actual nonzero classical solution,
independently of the existence input. The solution is one at zero and the datum is five. -/
theorem quadratic_existence_hypotheses_nonvacuous :
    IsC2HolderDomain (1 / 2) (unitBall 2) ∧
      IsClassicalDirichletSolution (unitBall 2) 1 1
        (fun x => 1 * (1 - ∑ k, x k ^ 2) + 2 * 2 * 1)
        (fun x => 1 - ∑ k, x k ^ 2) ∧
      c0HolderNorm (1 / 2) (closure (unitBall 2))
        (fun x => 1 * (1 - ∑ k, x k ^ 2) + 2 * 2 * 1) < ⊤ ∧
      c2HolderNorm (1 / 2) (unitBall 2) (fun x => 1 - ∑ k, x k ^ 2) < ⊤ ∧
      (1 - ∑ k : Fin 2, (0 : Fin 2 → ℝ) k ^ 2) = 1 ∧
      1 * (1 - ∑ k : Fin 2, (0 : Fin 2 → ℝ) k ^ 2) + 2 * 2 * 1 = 5 := by
  refine ⟨isC2HolderDomain_unitBall _, quadratic_isClassicalDirichletSolution 1 1,
    quadratic_datum_c0HolderNorm_lt_top (by norm_num) (by norm_num) 1 1,
    quadratic_c2HolderNorm_lt_top _, ?_, ?_⟩ <;> norm_num

end LatticeProb.Elliptic
