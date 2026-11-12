/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldOscExp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldExpTail

/-!
# DDDF Prop. 3, (2.17): exponential moments of the oscillation (task P2-DDDFFIELD, WP-94)

DDDF (arXiv:1904.08021, `tightness.tex` l. 337–352), (2.17): for `ε > 0` and `a > 0` there is
`c_a` with `E exp(a n^ε 2^{-n} ‖∇φ_{0,n}‖_{[0,1]²}) ≤ e^{c_a n^{1/2+ε} + O(n^{2ε})}`.
We follow DDDF's proof (l. 345–352): with `λ = a n^ε` and `x_n = λσ² + √(2σ² n log 4)`
(DDDF: `α²/2 = log 4`), `E e^{λO_n} ≤ e^{λx_n} + ∫_{x_n}^∞ λ e^{λt} P(O_n ≥ t) dt`, and the
tail (2.16). The Gaussian integral `∫ e^{−s²/2}` over `[α√n, ∞)` used by DDDF is replaced by
the tangent-line bound of the exponent at `x_n` (`lintegral_exp_le_of_tail`); the result is
the same `e^{λx_n} + O(e^{O(n^{2ε}) + λ})`.

`measurable_iSup_of_continuous`: the supremum over a compact separable space of a field with
continuous paths and measurable values is measurable (dense sequence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

/-- Measurability of the supremum of a continuous field over a compact separable space. -/
lemma measurable_iSup_of_continuous {Ω T : Type*} [MeasurableSpace Ω] [TopologicalSpace T]
    [CompactSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T] {X : T → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => X t ω) (hm : ∀ t, Measurable (X t)) :
    Measurable fun ω => ⨆ t, X t ω := by
  have hu := TopologicalSpace.denseRange_denseSeq T
  have e : (fun ω => ⨆ t, X t ω) = fun ω => ⨆ k, X (TopologicalSpace.denseSeq T k) ω :=
    funext fun ω => iSup_eq_iSup_seq hc hu ω
  rw [e]
  exact Measurable.iSup fun k => hm _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The oscillation `O_n = 2^{-n} sup_{[0,1]²} ‖∇Y‖` of any `C¹` modification is
a.e.-measurable. -/
lemma aemeasurable_osc (hW : IsWhiteNoise P W) (n : ℕ) {Y : ℂ → Ω → ℝ}
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x)
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    AEMeasurable (fun ω => ((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖) P := by
  have ha : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have ha1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y', G, hY', -, hY'c, hfd, -, hGm, -, -⟩ := exists_C1_modification_phi hW ha ha1
  have hfe := ae_fderiv_eq_of_modification (P := P) (Y₁ := Y) (Y₂ := Y')
    (fun ω => (hYc ω).continuous) (fun ω => (hY'c ω).continuous)
    (fun x => (hY x).trans (hY' x).symm)
  have : CompactSpace (ferniqueBox (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_ferniqueBox 0 1)
  have : Nonempty (ferniqueBox (0 : ℂ) 1) := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
  have hF : Continuous fun c : ℝ × ℝ => ‖c.1 • Complex.reCLM + c.2 • Complex.imCLM‖ := by
    fun_prop
  have hm : Measurable fun ω => ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y' x ω) z‖ := by
    refine measurable_iSup_of_continuous (X := fun (z : ferniqueBox (0 : ℂ) 1) ω =>
      ‖fderiv ℝ (fun x => Y' x ω) z‖) (fun ω => ?_) (fun z => ?_)
    · exact (continuous_norm.comp ((hY'c ω).continuous_fderiv (by norm_num))).comp
        continuous_subtype_val
    · have e : (fun ω => ‖fderiv ℝ (fun x => Y' x ω) (z : ℂ)‖) =
          (fun c : ℝ × ℝ => ‖c.1 • Complex.reCLM + c.2 • Complex.imCLM‖) ∘
            (fun ω => (G 0 z ω, G 1 z ω)) := by
        funext ω; rw [Function.comp_apply, hfd ω z]
      rw [e]
      exact hF.measurable.comp ((hGm 0 z).prodMk (hGm 1 z))
  refine (hm.const_mul ((2 : ℝ) ^ n)⁻¹).aemeasurable.congr ?_
  filter_upwards [hfe] with ω hω
  simp only [hω]

end DDDF
end LQGMetric
