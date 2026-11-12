/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingCut at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDefs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, node B4a: a `C²` convex cut-off (`SmoothCutStmt`)

Plan: `handoff/LW-BEURLING.md`. Own elementary construction (standard; cost rule):
`φ(s) = ∫_0^s ψ`, `ψ(r) = smoothTransition((r − ε)/ε)`, so `φ' = ψ ∈ [0, 1]` is smooth and
nondecreasing, `ψ = 0` on `(−∞, ε]` and `ψ = 1` on `[2ε, ∞)`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The derivative of the cut-off. -/
def lwbCutPsi (ε : ℝ) (r : ℝ) : ℝ := Real.smoothTransition ((r - ε) / ε)

/-- The cut-off `φ_ε`. -/
def lwbCut (ε : ℝ) (s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, lwbCutPsi ε r

lemma lwbCutPsi_contDiff (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (lwbCutPsi ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε)

lemma lwbCutPsi_continuous (ε : ℝ) : Continuous (lwbCutPsi ε) :=
  (lwbCutPsi_contDiff ε (n := 0)).continuous

lemma lwbCutPsi_monotone {ε : ℝ} (hε : 0 < ε) : Monotone (lwbCutPsi ε) := by
  intro x y hxy
  unfold lwbCutPsi
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hε.le)

lemma lwbCutPsi_eq_zero {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : r ≤ ε) : lwbCutPsi ε r = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma lwbCutPsi_eq_one {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 2 * ε ≤ r) : lwbCutPsi ε r = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)

lemma lwbCut_hasDerivAt (ε s : ℝ) : HasDerivAt (lwbCut ε) (lwbCutPsi ε s) s :=
  ((lwbCutPsi_continuous ε).integral_hasStrictDerivAt 0 s).hasDerivAt

lemma lwbCut_deriv (ε : ℝ) : deriv (lwbCut ε) = lwbCutPsi ε :=
  funext fun s => (lwbCut_hasDerivAt ε s).deriv

lemma lwbCut_eq_zero {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε) : lwbCut ε s = 0 := by
  unfold lwbCut
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro r hr
  apply lwbCutPsi_eq_zero hε
  rcases le_total 0 s with h | h
  · rw [uIcc_of_le h] at hr; exact hr.2.trans hs
  · rw [uIcc_of_ge h] at hr; linarith [hr.2]

lemma lwbCut_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 ≤ lwbCut ε s := by
  rcases le_total s 0 with h | h
  · rw [lwbCut_eq_zero hε (h.trans hε.le)]
  · unfold lwbCut
    exact intervalIntegral.integral_nonneg h fun r _ => Real.smoothTransition.nonneg _

lemma lwbCut_ge {ε : ℝ} (hε : 0 < ε) (s : ℝ) : s - 2 * ε ≤ lwbCut ε s := by
  rcases le_total s (2 * ε) with h | h
  · linarith [lwbCut_nonneg hε s]
  · have hi : ∀ a b : ℝ, IntervalIntegrable (lwbCutPsi ε) volume a b := fun a b =>
      (lwbCutPsi_continuous ε).intervalIntegrable a b
    have hsplit : lwbCut ε s = lwbCut ε (2 * ε) + ∫ r in (2 * ε)..s, lwbCutPsi ε r := by
      unfold lwbCut
      rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
    have h2 : ∫ r in (2 * ε)..s, lwbCutPsi ε r = s - 2 * ε := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
      · simp
      intro r hr
      rw [uIcc_of_le h] at hr
      exact lwbCutPsi_eq_one hε hr.1
    rw [hsplit, h2]
    linarith [lwbCut_nonneg hε (2 * ε)]

/-- **B4a** (`SmoothCutStmt`). -/
theorem smoothCutStmt_holds : SmoothCutStmt := by
  intro ε hε
  refine ⟨lwbCut ε, ?_, fun s hs => lwbCut_eq_zero hε hs, ?_, ?_, lwbCut_ge hε⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun s => (lwbCut_hasDerivAt ε s).differentiableAt, by simp, ?_⟩
    rw [lwbCut_deriv]
    exact lwbCutPsi_contDiff ε
  · intro s
    rw [lwbCut_deriv]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro s
    rw [lwbCut_deriv]
    exact (lwbCutPsi_monotone hε).deriv_nonneg

end LWFar
end Thm18Asm
end QuantumZipper
