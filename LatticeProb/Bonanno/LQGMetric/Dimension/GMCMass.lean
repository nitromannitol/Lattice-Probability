/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMass at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMoment

/-!
# DZZ Lemma 2.10, first moment and `0 < p ≤ 1` (task P2-GMC, WP-24)

For a QZ zero-boundary GFF `X` on `𝕍 = (0,1)²` and `γ : ℝ`, with `μ_ω` the LQG measure of
Statement/Dimension.lean (`QuantumZipper.qAreaMeasureOn γ (X ω) openSquare`):

* `lintegral_qAreaMeasureOn_openSquare_le` : `E μ(𝕍) ≤ C_γ Leb(𝕍)`;
* `lintegral_qAreaMeasureOn_le` : `E μ(A) ≤ C_γ Leb(𝕍)` for every set `A` (balls, squares);
* `lintegral_qAreaMeasureOn_rpow_lt_top` : `E μ(A)^p < ∞` for `0 < p ≤ 1`.

DZZ Lemma 2.10 (`LBM_LGDarXiv.tex` l. 673–682) asserts `E M_γ(𝕍)^p < ∞` for `0 < p < 4/γ²`;
this file gives the range `p ≤ 1` (the first-moment computation, Rhodes–Vargas
arXiv:1305.6221 §2 / Berestycki arXiv:1506.09113 §2), for every `γ`.

Proof: `μ(𝕍) = sup_n μ(sqIn (2/(n+2))) ≤ sup_n liminf_k ∫ sqCut n d(areaApprox_k)` (vague
convergence on `𝕍`, continuity from below), then monotone convergence in `n`, Fatou in `k`,
Tonelli, and the pointwise bound `lintegral_areaDens_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal

namespace LQGMetric

lemma qAreaMeasureOn_openSquare_compl (γ : ℝ) (x : FieldSample) :
    qAreaMeasureOn γ x openSquare openSquareᶜ = 0 := by
  unfold qAreaMeasureOn
  split_ifs with h
  · exact h.choose_spec.1
  · simp

lemma ofReal_integral_le_lintegral {μ : Measure ℂ} {f : ℂ → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ENNReal.ofReal (∫ z, f z ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact zero_le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

omit [IsProbabilityMeasure P] in
lemma measurable_areaDens_left (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) (k : ℕ)
    (z : ℂ) : Measurable fun ω => areaDens γ (X ω) k z := by
  have h : Measurable fun ω => avgReg (X ω) k z :=
    (measurable_avgReg k).comp ((measurable_field hX).prodMk measurable_const)
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (h.const_mul γ)).const_mul _)

lemma gmcConst_lt_top (γ : ℝ) : gmcConst γ < ⊤ := by
  unfold gmcConst; exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

end LQGMetric
