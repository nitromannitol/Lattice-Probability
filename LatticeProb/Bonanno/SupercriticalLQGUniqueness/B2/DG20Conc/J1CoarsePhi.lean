/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarsePhi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseNormalized
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem j1_ae_coarse_phi_normalized_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) :
    ∀ᵐ ω ∂P, ∀ (U E F : Set ℂ) (v : ℂ) (M : ℝ),
      (∀ z ∈ U,
        |phiMN W P 0 K z ω - phiMN W P 0 K v ω| ≤ M) →
      crossLenIn ξ (fun z => phiMN W P K n z ω) U E F ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          (ENNReal.ofReal
            (Real.exp (-ξ * phiMN W P 0 K v ω)) *
            crossLenIn ξ (fun z => phiMN W P 0 n z ω) U E F) ∧
      ENNReal.ofReal (Real.exp (-ξ * phiMN W P 0 K v ω)) *
        (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          U E F ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          (lfppContMetric ξ (fun z => phiMN W P K n z ω)
            ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist U E F := by
  filter_upwards [ae_phiMN_add hW hKn] with ω hadd
  intro U E F v M hosc
  have hfield : (fun z : ℂ =>
      phiMN W P 0 K z ω + phiMN W P K n z ω) =
      (fun z => phiMN W P 0 n z ω) := by
    funext z
    exact (hadd z).symm
  have hh := j1_coarse_normalized_comparison ξ
    ((isPhiVersion_phiMN hW hKn).cont ω)
    ((isPhiVersion_phiMN hW (Nat.zero_le K)).cont ω)
    U E F v M hosc
  simpa only [hfield] using hh

end SupercriticalLQGUniqueness.B2.DG20Conc
