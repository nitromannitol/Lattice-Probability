/-
The cited compact embedding of negative Sobolev order on a bounded domain
(Rellich–Kondrachov): for `s₀ < s` and `D` a bounded open set, the unit ball of
`H^s(D)` is totally bounded in `H^{s₀}(D)`.  This is the classical theorem of
Rellich and Kondrachov; the paper's linearization lemma
(`sandpile.tex:5610-5655`) uses it in the `H^{-s}_loc` clause and does not prove
it.  It enters here as an explicit hypothesis, never as an axiom.
-/
import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.External

/-- The Rellich–Kondrachov compact embedding `H^s(D) → H^{s₀}(D)` for `s₀ < s`
on a bounded domain, in the finite-`η`-net form: the unit ball of `H^s(D)` is
covered by finitely many `η`-balls in the `H^{s₀}(D)` norm, with centres that
are test functions on `D`. -/
def RellichKondrachovNegSobolev : Prop :=
  ∀ (d : ℕ) (D : Set (LatticeProb.Sobolev.Space d)),
    LatticeProb.Sobolev.IsDomain D →
    ∀ (s₀ s : ℝ), s₀ < s → ∀ η : ℝ, 0 < η →
      ∃ (N : ℕ) (ψ : Fin N → LatticeProb.Sobolev.Space d → ℝ),
        (∀ i, LatticeProb.Sobolev.IsTestFn D (ψ i)) ∧
        ∀ φ : LatticeProb.Sobolev.Space d → ℝ, LatticeProb.Sobolev.IsTestFn D φ →
          LatticeProb.Sobolev.sobolevNormSq d s φ ≤ 1 →
            ∃ i, LatticeProb.Sobolev.sobolevNormSq d s₀ (fun x => φ x - ψ i x)
              ≤ ENNReal.ofReal (η ^ 2)

end LatticeProb.External
