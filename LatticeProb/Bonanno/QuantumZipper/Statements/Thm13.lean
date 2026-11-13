/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Statements.Thm13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Theorem 1.3 (conformal welding: quantum lengths agree)

Sheffield, *Conformal weldings of random surfaces*, Theorem 1.3. Specification only.

Setting (`κ ∈ (0,4)`, `γ = √κ`, `T > 0`): `B` is a standard Brownian motion, `f_T` the reverse
centered Loewner map driven by `W = √κ B` (`revMap W T`), `h̃` an independent free-boundary
GFF on `ℍ` (modulo additive constants), and
`h = 𝔥_T + h̃∘f_T`, where `𝔥_T(z) = (2/√κ) log|f_T(z)| + Q log|f_T'(z)|`, `Q = 2/γ + γ/2`.
The coordinate change of the GFF part carries no `Q`-term (it sits in `𝔥_T`), FOUNDATIONS §8.

Conclusion (STATEMENT_SPEC A10): almost surely, (i) every non-tip point `z` of `η_T` (the hull
`revHull W T`; the tip is `f_T(0) = revMapBdry W T 0`) has preimages `x₋ < 0 < x₊` under the
boundary extension of `f_T`, and (ii) whenever `x₋ < 0 < x₊` are identified by the boundary
extension at a point of `η_T` or at the base point `0` (DECISIONS D9), the quantum lengths
agree: `ν_h[x₋,0] = ν_h[0,x₊]`, and (iii) `ν_h` charges every nonempty open interval
(DECISIONS D13, excluding the junk measure).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

/-- The field of the reverse coupling (Theorem 1.2/1.3) for a deterministic driving function
`W` and a free-field sample `x`: `h = 𝔥_T + x∘f_T` with
`𝔥_T(z) = (2/√κ) log|f_T(z)| + Q log|f_T'(z)|`, `Q = Qc (√κ)`, and `f_T = revMap W T`.
The coordinate change of `x` carries no `Q`-term. (Local copy of the field of
`Statements/CouplingFields.lean`, kept independent on purpose.) -/
noncomputable def couplingFieldRev (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) :
    FieldSample :=
  ofFun (fun z => (2 / Real.sqrt κ) * Real.log ‖revMap W T z‖ +
      Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖) +
    coordChange x (revMap W T) 0

/-- **Theorem 1.3.** For `κ ∈ (0,4)`, `T > 0`, a Brownian motion `B` and an independent
free-boundary GFF `X` (modulo additive constants), let `W = √κ B`, `h = 𝔥_T + X∘f_T`, and
`ν = ν_h` the `√κ`-LQG boundary measure. Almost surely:
1. every point `z` of `η_T = revHull W T` other than the tip `revMapBdry W T 0 = f_T(0)` is the
   image under the boundary extension of `f_T` of some `x₋ < 0` and some `x₊ > 0`;
2. for all `x₋ < 0 < x₊` with `f_T(x₋) = f_T(x₊) ∈ η_T`, `ν[x₋,0] = ν[0,x₊]`.
   The base pair `(0₋, 0₊)` (preimages of `η(0) = 0`) is included, hence `insert 0`
   (DECISIONS D9).
3. `ν` charges every nonempty open interval (DECISIONS D13): this non-degeneracy conjunct
   excludes the junk value `qBoundaryMeasure = 0`, for which clause 2 would hold trivially.

The additive constant of the free field is arbitrary: `IsFreeGFFModConstH` allows any
convention (even a random one), matching the paper's remark that the conclusion is invariant
under `ν_h ↦ c ν_h`. -/
def theorem1_3 : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P,
      (∀ z ∈ revHull (drive κ B ω) T, z ≠ revMapBdry (drive κ B ω) T 0 →
        ∃ xm xp : ℝ, xm < 0 ∧ 0 < xp ∧
          revMapBdry (drive κ B ω) T xm = z ∧ revMapBdry (drive κ B ω) T xp = z) ∧
      (∀ xm xp : ℝ, xm < 0 → 0 < xp →
        revMapBdry (drive κ B ω) T xm = revMapBdry (drive κ B ω) T xp →
        revMapBdry (drive κ B ω) T xm ∈ insert 0 (revHull (drive κ B ω) T) →
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc xm 0) =
          qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc 0 xp)) ∧
      (∀ u v : ℝ, u < v →
        0 < qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
          (Set.Ioo u v))

end QuantumZipper
