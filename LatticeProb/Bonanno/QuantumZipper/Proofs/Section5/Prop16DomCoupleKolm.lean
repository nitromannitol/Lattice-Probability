/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Section5.Prop16DomCoupleKolm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample

/-!
# Proposition 1.6, node DOM-COUPLE (part 5): continuous versions for globally Lipschitz curves

`isoW_contVersion_global`: for an isonormal process `W` on `E` and a globally Lipschitz curve
`H : ℂ → E`, the process `z ↦ W(H z)` has a version `Y` with `Y ω` continuous on `ℂ` for
**every** `ω` and measurable coordinates. This is the global half of the continuous-version
sub-node `GaussContVersionStmt` (`Prop16DomCoupleVersion.lean`).

Source: Kolmogorov's continuity criterion (Revuz–Yor, *Continuous martingales and Brownian
motion*, Ch. I, Thm (2.1)), in the repository's dyadic form
`KolmD.exists_continuous_modification_D` (sixteenth moments, `d = 2`); the Gaussian sixteenth
moment is `RegSample.lintegral_pow16_of_map_eq`. The measurable modification (restriction to a
measurable full-measure subset of the convergence event) is an own elementary step.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- Coordinates `(Fin 2 → ℝ) → ℂ`. -/
def toCdom (q : Fin 2 → ℝ) : ℂ := ⟨q 0, q 1⟩

/-- Coordinates `ℂ → (Fin 2 → ℝ)`. -/
def fromCdom (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

theorem toCdom_fromCdom (z : ℂ) : toCdom (fromCdom z) = z := by
  simp [toCdom, fromCdom]

theorem continuous_fromCdom : Continuous fromCdom := by
  unfold fromCdom
  exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

theorem norm_toCdom_sub_le (q q' : Fin 2 → ℝ) : ‖toCdom q - toCdom q'‖ ≤ 2 * ‖q - q'‖ := by
  have h0 : |q 0 - q' 0| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 0
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 1
  have h := Complex.norm_le_abs_re_add_abs_im (toCdom q - toCdom q')
  simp only [toCdom, Complex.sub_re, Complex.sub_im] at h
  unfold toCdom
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : E → Ω → ℝ}
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) P)

end Prop16Asm

end QuantumZipper
