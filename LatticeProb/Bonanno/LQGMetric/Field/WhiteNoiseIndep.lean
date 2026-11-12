/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseIndep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

/-!
# Mutual independence of the white noise over pairwise disjoint sets (task P2-WN)

DDDF (arXiv:1904.08021, `tightness.tex` l. 369–375) splits `ψ` into block fields `ψ_{k,P}`
(white noise on `[2^{-2k}, 2^{-2k+2}] × P`, `P` a square of a grid) and applies the
Efron–Stein inequality, which needs the block fields to be *mutually* independent; DDDF Lemma 6
(l. 543) uses joint independence of `W|_{U^c×(0,∞)}`, `W|_{U×(0,∞)}`, `W̃|_{V^c×(0,∞)}`.

`IsWhiteNoise.iIndepFun_of_pairwise_disjoint`: for pairwise disjoint sets `A i`, the
restrictions `(W f)_{f supported in A i}` are mutually independent (mathlib
`IsGaussianProcess.iIndepFun_of_covariance_eq_zero` and the Itô isometry).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Mutual independence over pairwise disjoint sets.** -/
theorem IsWhiteNoise.iIndepFun_of_pairwise_disjoint (hW : IsWhiteNoise P W) {ι : Type}
    {A : ι → Set (ℝ × ℂ)} (hA : Pairwise fun i j => Disjoint (A i) (A j)) :
    iIndepFun (fun i ω (f : {f // SupportedIn (A i) f}) => W f ω) P := by
  have := hW.isProbabilityMeasure
  have hG := hW.isGaussianProcess_comp
    (fun p : (i : ι) × {f // SupportedIn (A i) f} => (p.2 : WNSpace))
  exact hG.iIndepFun_of_covariance_eq_zero (X := fun i (f : {f // SupportedIn (A i) f}) => W f)
    (fun i f => (hW.measurable _).aemeasurable) fun i j hij f g => by
      rw [hW.cov_eq]
      exact inner_eq_zero_of_supportedIn (hA hij) f.2 g.2

end WhiteNoise
end LQGMetric
