/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.GaussFdd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Approx
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L13Limit
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationSqrt

/-!
# `φ_{0,n}` is a Gaussian field with nonnegative covariances; DDDF Lemma 13 for `φ_{0,n}`

Task P2-DDDFRSW (handoff/P2-DDDFL913.md item 5). DDDF = Ding–Dubédat–Dunlap–Falconet,
arXiv:1904.08021, `tightness.tex`. DDDF's field `φ_{0,n} = φ_{2^{-n},1}` (l. 289, 293) is
`√π ∫∫ p_{t/2}(x − y) W(dy, dt)`: every finite family is jointly Gaussian (white-noise integrals,
`WhiteNoise.isGaussianProcess_phi_comp`), and its covariance is
`∫_{a²}^{b²} (2t)⁻¹ e^{−|x−x'|²/(2t)} dt ≥ 0` (DDDF l. 287, `WhiteNoise.cov_phi`). These are the
hypotheses of DDDF Lemma 13 (l. 771–780, `lemma13`, `lemma13_sqrt`), which DDDF/DF apply to
`φ_{0,n}` (DF arXiv:1809.02607 §2.3: "the field is positively correlated").

* `isGaussianProcess_phiMN`, `hasGaussianLaw_phiMN`, `cov_phiMN_nonneg`;
* `lemma13_phiMN`, `lemma13_sqrt_phiMN`: Lemma 13 for `L^{(n)}(R) = lenObs ξ (phiMN W P 0 n) R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- covariance only depends on the a.e. classes -/
theorem covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  simp only [covariance]
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- `φ_{m,n}` (continuous version) is a Gaussian process -/
theorem isGaussianProcess_phiMN (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) :
    IsGaussianProcess (phiMN W P m n) P :=
  (isGaussianProcess_phi_comp hW ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) (fun x : ℂ => x)).congr
    fun x => ((isPhiVersion_phiMN hW hmn).ae_eq x).symm

/-- every finite family of `φ_{m,n}` is jointly Gaussian -/
theorem hasGaussianLaw_phiMN (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) (D : Finset ℂ) :
    HasGaussianLaw (fun ω (s : D) => phiMN W P m n s ω) P :=
  (isGaussianProcess_phiMN hW hmn).hasGaussianLaw D

/-- the covariances of `φ_{m,n}` are nonnegative (DDDF l. 287) -/
theorem cov_phiMN_nonneg (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) (x y : ℂ) :
    0 ≤ cov[phiMN W P m n x, phiMN W P m n y; P] := by
  have h := isPhiVersion_phiMN hW hmn
  rw [covariance_congr_ae (h.ae_eq x) (h.ae_eq y), cov_phi hW (by positivity)]
  exact setIntegral_nonneg measurableSet_Icc fun t ht => by
    have : 0 ≤ t := le_trans (by positivity) ht.1
    positivity

variable {ξ : ℝ}

end DDDF
end LQGMetric
