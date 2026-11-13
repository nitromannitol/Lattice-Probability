/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Blueprint.External2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm13

/-!
# External blueprint items, part 2 (used by the Theorem 1.3 ⇒ Theorem 1.4(a) implication)

`Prop`-valued statements of standard facts that are not proved in this project yet. Nothing is
proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.Blueprint

/-- **Regularity of the boundary measure of the reverse coupling** (blueprint level, M4).
In the setting of Theorems 1.3/1.4 (`κ ∈ (0,4)`, `T > 0`, `B` a Brownian motion, `X` an
independent free-boundary GFF modulo constants, `h = 𝔥_T + X∘f_T` = `couplingFieldRev`),
almost surely the `√κ`-LQG boundary measure `ν_h` on `ℝ`
* has no atoms,
* charges every nondegenerate open interval, and
* is finite on every compact interval.

These are exactly the properties that make `weldR` (defined by an infimum) the point `R(s)` with
`ν[s,0] = ν[0,R(s)]`, as used in Sheffield's proof of Theorem 1.4.

Justification (corrected per AUDIT3 M4, 2026-09-27). Duplantier–Sheffield (2011) §6 does **not**
apply on `(0₋,0₊)`: there `f_T` maps the interval onto the SLE curve, so `log|f_T'|` has no boundary
values and `X∘f_T` is not a free GFF near the interval (its kernel couples `x` with its welded
partner). The item is instead provable in-project: semicircle raw values are genuine pairings a.s.
(RC1), they are limits in probability of pairings with a fixed mollifier sequence (TREG), Theorem 1.2
transfers the law of the normalized `coordsFull` from `ofFun 𝔥₀ + X'`, and the M4 results (B3, P2,
P5, T6(a)) conclude. **Proved**: `RevCouplingReg.revCouplingBoundaryMeasureRegular`
(`Proofs/LQG/RevCouplingReg.lean:116`, entry L-RCBMR; standard axioms). -/
def RevCouplingBoundaryMeasureRegular : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P,
      (∀ x : ℝ,
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) {x} = 0) ∧
      (∀ u v : ℝ, u < v →
        0 < qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
          (Set.Ioo u v)) ∧
      (∀ u v : ℝ,
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
          (Set.Icc u v) < ∞)

end QuantumZipper.Blueprint
