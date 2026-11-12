/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Blueprint.Section2Bounds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2

/-!
# Blueprint: the quantitative bounds (2.2) and (2.3) of Lemma 2.1

These are not needed for the first assertion of Theorem 1.1.  They enter Lemma 2.3 and
Sections 3–5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Blueprint

/-- Lemma 2.1, (2.2): `E sup_{f ∈ V_n, E(f) ≤ R} Z_f ≤ C n^{3/4} R^{1/4}` for `R > 0`, with `C`
universal.  In finite-subfamily form. -/
def ZSupBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ R : ℝ, 0 < R → ∀ F : Finset (V n),
    (∀ f ∈ F, energy f ≤ R) →
    gaussianExpectedMax F (fun f g => zCov f g) 0 ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ)

/-- Lemma 2.1, (2.3): `Var Z_f ≤ C √(E(f))` for `f ∈ V_n`, with `C` universal (equivalently,
`sup_{E(f) ≤ R} Var Z_f ≤ C √R`). -/
def ZVarBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ f ∈ V n, zCov f f ≤ C * Real.sqrt (energy f)

end LQGDimension.Blueprint
