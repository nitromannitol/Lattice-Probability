/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentBoch at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentKer

/-!
For a bounded open `A`, a time set `I ⊆ (c₀, ∞)` and a finite measure `μ` for which
`y ↦ K^I_y = 1_I(s) p_A(s/2; y, ·) ∈ L²` is Bochner integrable:

  `∫ K^I_y μ(dy) = K^I_μ` a.e. (`integral_wndKernelL2_ae_eq`), hence `K^I_μ ∈ L²` and
  `measKerL2 A I μ = ∫ K^I_y μ(dy)` (`measKerL2_eq_integral`).

Consequently `‖K^I_μ − K^I_z‖ ≤ ∫ ‖K^I_y − K^I_z‖ μ(dy)`, which with DZZ Lemma 2.5
(`pi_sq_norm_tildeHKernel_sub_le`) gives the convergence of the coarse part of the circle
average to `h̃_δ(z)` (the "continuity of `h^n`" in Berestycki arXiv:1506.09113 §4, l. 686).
Own elementary proof: integrals over finite-measure sets (`L2.inner_indicatorConstLp_one`), the
inner product commuting with the Bochner integral, Fubini, and
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

lemma measurable_wndKernel_uncurry {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable fun q : ℂ × (ℝ × ℂ) => wndKernel A I q.1 q.2 := by
  have e : (fun q : ℂ × (ℝ × ℂ) => wndKernel A I q.1 q.2) =
      ({q : ℂ × (ℝ × ℂ) | q.2.1 ∈ I}).indicator
        (fun q => killedHeat A (q.2.1 / 2).toNNReal q.1 q.2.2) := by
    funext q
    by_cases h : q.2.1 ∈ I <;> simp [wndKernel, h, Set.indicator]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage (measurable_fst.comp measurable_snd))
  exact (measurable_killedHeat hA).comp
    (((measurable_fst.comp measurable_snd).div_const 2).real_toNNReal.prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

section Circle

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end Circle

end GMCIdent
end LQGMetric
