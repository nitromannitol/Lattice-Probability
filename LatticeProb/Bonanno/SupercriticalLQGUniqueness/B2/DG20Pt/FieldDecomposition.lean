/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.FieldDecomposition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem ae_crossLenIn_band_compare_center
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ δ : ℝ) (U A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n) :
    ∀ᵐ ω ∂P,
      (∀ x ∈ U, |phiMN W P 0 k x ω - phiMN W P 0 k 0 ω| ≤ δ) →
      crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B ≤
          ENNReal.ofReal (Real.exp (|ξ| * δ)) *
            (ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
              crossLenIn ξ (fun z => phiMN W P k n z ω) U A B) ∧
        ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 k 0 ω)) *
            crossLenIn ξ (fun z => phiMN W P k n z ω) U A B ≤
          ENNReal.ofReal (Real.exp (|ξ| * δ)) *
            crossLenIn ξ (fun z => phiMN W P 0 n z ω) U A B := by
  filter_upwards [ae_phiMN_add hW hkn] with ω hadd hosc
  have heq : (fun z => phiMN W P 0 n z ω) =
      fun z => phiMN W P k n z ω + phiMN W P 0 k z ω := by
    funext z
    rw [hadd z]
    ring
  rw [heq]
  exact crossLenIn_compare_center ξ (fun z => phiMN W P k n z ω)
    (fun z => phiMN W P 0 k z ω) (phiMN W P 0 k 0 ω) δ U A B hosc

end SupercriticalLQGUniqueness.B2.DG20Pt
