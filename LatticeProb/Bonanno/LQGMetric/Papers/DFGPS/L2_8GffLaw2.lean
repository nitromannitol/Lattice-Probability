/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffLaw2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Path laws of `φ_δ` and the normalization `λ_δ` do not depend on the white noise
(DFGPS L2.8, step (a1))

DDDF (DD:153) defines `λ_δ` as the median of the left–right distance of `[0,1]²` for
`e^{ξ φ_δ} ds`; `DDDF.lambdaDelta ξ W P δ` computes it from a white noise `(W, P)`, and the
Blueprint reading (`Blueprint/DFGPSInputs.lean`, reading 2) says it does not depend on `(W, P)`.
We prove this (needed to compare `DDDFThm1_2`'s reference noise with the noise of the
`DDDFProp29` coupling):

* `map_comp_pathC` : functionals of continuous paths are transported by the path law;
* `map_pathC_phiVer_eq` : the path law of the continuous version of `φ_{a,b}` is the same for
  all white noises;
* `lambdaDelta_eq_of_isWhiteNoise` : `λ_δ` is the same for all white noises (`0 < δ ≤ 1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open Blueprint WhiteNoise DDDF

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- the canonical process on `C(ℂ, ℝ)` -/
def evalProc (x : ℂ) (f : C(ℂ, ℝ)) : ℝ := f x

lemma continuous_evalProc (f : C(ℂ, ℝ)) : Continuous fun x => evalProc x f := f.continuous

lemma measurable_evalProc (x : ℂ) : Measurable (evalProc x) :=
  ContinuousMap.measurable_eval x

/-- functionals of the path, through the path law -/
lemma map_comp_pathC {β : Type*} [MeasurableSpace β] {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) {Φ : C(ℂ, ℝ) → β}
    (hΦ : Measurable Φ) :
    P.map (fun ω => Φ (pathC Y hYc ω)) = (P.map (pathC Y hYc)).map Φ := by
  rw [Measure.map_map hΦ (measurable_pathC hYc hYm)]; rfl

/-- **The path law of `φ_{a,b}`** (continuous version) does not depend on the white noise. -/
theorem map_pathC_phiVer_eq {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    P.map (pathC (phiVer W P a b) (isPhiVersion_phiVer hW ha hab).cont) =
      P'.map (pathC (phiVer W' P' a b) (isPhiVersion_phiVer hW' ha hab).cont) := by
  have h := isPhiVersion_phiVer hW ha hab
  have h' := isPhiVersion_phiVer hW' ha hab
  refine map_pathC_eq_of_gaussian h.cont h'.cont h.meas h'.meas
    ((isGaussianProcess_phi_comp hW a b id).congr fun x => (h.ae_eq x).symm)
    ((isGaussianProcess_phi_comp hW' a b id).congr fun x => (h'.ae_eq x).symm)
    (fun x => ?_) fun x y => ?_
  · rw [integral_congr_ae (h.ae_eq x), integral_congr_ae (h'.ae_eq x), integral_phi hW,
      integral_phi hW']
  · rw [covariance_congr_ae (h.ae_eq x) (h.ae_eq y), covariance_congr_ae (h'.ae_eq x) (h'.ae_eq y),
      cov_phi hW ha, cov_phi hW' ha]

end LQGMetric.DFGPS
