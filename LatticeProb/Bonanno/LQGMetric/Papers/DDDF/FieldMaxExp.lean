/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldMaxExp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOscExp

/-!
# DDDF Prop. 2, (2.11): exponential moments of the maximum (task P2-DDDFFIELD, WP-94)

DDDF (arXiv:1904.08021, `tightness.tex` l. 306–309), (2.11): for `γ < 2`,
`E e^{γ max_{[0,1]²} |φ_{0,n}|} ≤ 4^{γn + O(√n)}`. DDDF give no proof; we follow DF
(arXiv:1809.02607) Lemma 10.2, l. 1860–1880: `E e^{γX} ≤ e^{γx₀} + ∫_{x₀}^∞ γ e^{γt} P(X ≥ t) dt`
with the tail (2.10) (`prop2_tail`) at `t = α s_n`, `s_n = n + C√n`, and the threshold
`x₀ = s_n² log 4 / n` (DF: `α = r_n log 4`, `r_n = s_n/n`). DF bound the remaining Gaussian
integral by `∫_a^∞ e^{−bx²} ≤ e^{−ba²}/(2ab)`; we use the tangent line of the exponent at `x₀`
(`lintegral_exp_le_of_tail`), which gives the same `(1 + Cγ/(2−γ)) 4^{γn + O(√n)}`.
At `n = 0` the field `φ_{1,1}` vanishes a.s. and the bound is `1 ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `sup_{[0,1]²} |Y|` of a continuous modification is a.e.-measurable. -/
lemma aemeasurable_sup_abs (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {Y : ℂ → Ω → ℝ} (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W a b x)
    (hYc : ∀ ω, Continuous fun x => Y x ω) :
    AEMeasurable (fun ω => ⨆ z : ferniqueBox 0 1, |Y z ω|) P := by
  obtain ⟨Y', -, hY', hY'm, hY'c, -⟩ := exists_C1_modification_phi hW ha hab
  have hsame := ae_eq_of_continuous_modification (P := P) hYc (fun ω => (hY'c ω).continuous)
    (fun x => (hY x).trans (hY' x).symm)
  have : CompactSpace (ferniqueBox (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_ferniqueBox 0 1)
  have : Nonempty (ferniqueBox (0 : ℂ) 1) := ⟨⟨0, mem_ferniqueBox_self zero_le_one⟩⟩
  have hm : Measurable fun ω => ⨆ z : ferniqueBox 0 1, |Y' z ω| :=
    measurable_iSup_of_continuous (X := fun (z : ferniqueBox (0 : ℂ) 1) ω => |Y' z ω|)
      (fun ω => (continuous_abs.comp (hY'c ω).continuous).comp continuous_subtype_val)
      (fun z => continuous_abs.measurable.comp (hY'm (z : ℂ)))
  refine hm.aemeasurable.congr ?_
  filter_upwards [hsame] with ω hω
  simp only [hω]

/-- The tangent-line identity at `x₀ = 1/β`. -/
lemma tangent_iden (β x₀ t γ c : ℝ) (h : β * x₀ = 1) :
    (c + x₀ + -(2 - γ) * t) - (γ * t + c + -β * t ^ 2) = β * (t - x₀) ^ 2 := by
  linear_combination (2 * t - x₀) * h

end DDDF
end LQGMetric
