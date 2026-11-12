/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.ChiUnique at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence

/-!
# Uniqueness of the LGD exponent χ

`IsLGDExponent γ χ` holds for at most one `χ`. A zero-boundary GFF on the open unit square
exists on some `Ω : Type` (`QuantumZipper.K3.exists_zeroGFFOn openSquare`), so the defining
almost-sure limit is taken along a nonempty event and limits in `ℝ` are unique.

Source: statement audit P1-AUDIT (`audits/STATEMENT-AUDIT-2026-10-01.md` §4, fix B3); the
argument is the elementary uniqueness of limits (own elementary proof, no paper step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

open Set Filter

theorem isLGDExponent_unique {γ χ₁ χ₂ : ℝ} (h1 : IsLGDExponent γ χ₁)
    (h2 : IsLGDExponent γ χ₂) : χ₁ = χ₂ := by
  obtain ⟨Ω, _, P, X, hP, hX⟩ := QuantumZipper.K3.exists_zeroGFFOn openSquare
  have := hP
  have hu : (⟨1/4, 1/2⟩ : ℂ) ∈ openSquare := by
    simp only [openSquare, mem_ofPred_eq]; norm_num
  have hv : (⟨3/4, 1/2⟩ : ℂ) ∈ openSquare := by
    simp only [openSquare, mem_ofPred_eq]; norm_num
  have huv : (⟨1/4, 1/2⟩ : ℂ) ≠ ⟨3/4, 1/2⟩ := by
    intro h; have := congrArg Complex.re h; norm_num at this
  obtain ⟨ω, hω1, hω2⟩ := ((h1 P X hX _ hu _ hv huv).and (h2 P X hX _ hu _ hv huv)).exists
  exact tendsto_nhds_unique hω1 hω2

end LQGMetric
