/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Reg
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# DZZ Lemma 3.13 from its geometric part (P2-DZZ313)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1314–1340 (Lemma 3.13 and proof).

The proof has two parts. (G) the construction (l. 1327–1334) of the box sequence `B_{j,i}` inside the
good cell sequence and the geometric check behind (Eq.fine-field-independent) (l. 1334–1336:
`s_B log(1/s_B) < ε* s_𝖢 / 10`, goodness): this is the open node `L313Geom`, stated with the
space-time regions of `S3L13Reg`. (P) the probabilistic content of (Eq.fine-field-independent) and of
the conclusion ("the construction of `𝒱_δ` does not explore the white noise of the fine field, completing
the proof"), proved here (`dzz_lemma313_of_geom`):

* the sequence is selected as a function of the cell predicate (`l313Sel`), so `{seq = l₀}` is
  `σ(𝒱_δ)`-measurable;
* stopping-set argument: with `M'(b) = M(b)` if `boxReg b` misses `fineReg l₀` and `M'(b) = 0`
  otherwise, `M'` is measurable for the white noise off `fineReg l₀`, and on `{seq = l₀}` the partitions
  of `M` and `M'` coincide (`isCell_eq_of_eqOn_explored`), so every `σ(𝒱_δ)`-event inside `{seq = l₀}`
  is an event of the white noise off `fineReg l₀`;
* that σ-algebra is independent of the fine field (`indep_wnSigma_compl`), and
  `ae_condExp_indicator_eq_of_indep` concludes.
Own elementary formalization of these standard steps (DZZ give no details).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

set_option linter.unusedSectionVars false

/-- The mass `M_{γ,s_b}(b)` is measurable for the white noise on any region containing `boxReg b`. -/
lemma measurable_approxLQG_wnSigma (γ : ℝ) {S : Set (ℝ × ℂ)} (b : DyBox) (hS : boxReg b ⊆ S) :
    Measurable[wnSigma W S] fun ω => approxLQG γ W ω b := by
  unfold approxLQG etaInf etaField
  exact measurable_const.mul ((((measurable_wnSigma
    (supportedIn_mono (supportedIn_boxKer b) hS)).const_mul _).const_mul _).sub_const _).exp

omit [MeasurableSpace Ω] in
lemma measurable_pred_of_eval [m : MeasurableSpace Ω] {f : Ω → DyBox → Prop}
    (h : ∀ b, MeasurableSet {ω | f ω b}) : Measurable f :=
  Measurable.of_eval fun b => measurableSet_setOfPred.1 (h b)

end DZZ
end LQGMetric
