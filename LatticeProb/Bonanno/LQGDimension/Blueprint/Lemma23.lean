/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.Lemma23 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2Bounds
import LatticeProb.Bonanno.LQGDimension.Blueprint.GaussianConcentration

/-!
# Blueprint: Lemma 2.3 (a finite near-optimal family)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Blueprint

/-- Lemma 2.3: for all sufficiently large `n`, with `M = 16^n`, there is a finite `F_n ⊆ V_n`
containing `0` with `E(f) ≤ C n` and `‖f‖_∞ ≤ C √n` on `F_n` (2.5), `log |F_n| ≤ C M log M`
(2.6), and `E max_{f ∈ F_n} (Z_f - E(f)) ≥ a_n - 1` (2.7).  `C` is universal. -/
def Lemma23 : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset (V n),
    (∃ f ∈ F, ∀ x, (f : ℝ → ℝ) x = 0) ∧
    (∀ f ∈ F, energy f ≤ C * n) ∧
    (∀ f ∈ F, ∀ x, |(f : ℝ → ℝ) x| ≤ C * Real.sqrt n) ∧
    Real.log F.card ≤ C * (16 ^ n : ℝ) * Real.log (16 ^ n) ∧
    a n - 1 ≤ gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f)

end LQGDimension.Blueprint
