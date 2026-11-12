/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12Nodes at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: the nodes of the assembly (D90)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1339–1386; decisions/DEC-90.md.

`T12Coupling` is the first sentence of the proof (T:1342): "Lemma 2.5 implies that for any
sequence of `ε`'s tending to zero, there is a subsequence `εₙ → 0` along which
`(h, D^{εₙ}_h) → (h, D_h)` in law". As in `Lem2_13`, `Lem2_17`, `Lem2_20` (D90), the field is
read through its coordinates `pairJ ⊤ ∘ h` (the Polish space `CoordJ → ℝ`, on which Prokhorov's
theorem applies; DV-D90), and the limit is realized on one probability space together with the
same field `h`, which is the form those lemmas consume.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.DFGPS
open Blueprint

/-- **DFGPS T:1342** (Step 0 of the proof of Theorem 1.2): along a subsequence of any `ε → 0`,
`(h, 𝔞_ε⁻¹ D^ε_h)` converges in law to a coupling `(h, D_h)` with the same normalized field. -/
def T12Coupling : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ε : ℕ → ℝ, (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (h : Ω → DistC) (Dh : Ω → ContMetric),
      IsNormalizedWPGFF h P ∧ Measurable Dh ∧
      ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
        Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
            (aEpsDF (xiGamma γ) (ε (ψ n)))⁻¹ * lfppDist (xiGamma γ) (ε (ψ n)) (h ω) p) ∂P)
          atTop (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))

end LQGMetric.DFGPS
