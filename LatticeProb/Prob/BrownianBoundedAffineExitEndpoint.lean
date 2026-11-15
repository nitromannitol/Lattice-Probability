import LatticeProb.Prob.BrownianAffineExitEndpoint
import LatticeProb.Prob.BrownianOpenHarmonicExit

/-! # Brownian exit endpoints from bounded domains under affine scaling -/

set_option autoImplicit false

noncomputable section

open MeasureTheory BouRabeeGwynne Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The endpoint law for exit from a bounded open set under positive affine scaling. -/
theorem brownian_exit_endpoint_law_scale_of_bounded {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (r : ℝ≥0) (hr : 0 < r) (z : Euc d) {V : Set (Euc d)}
    (hV : IsOpen V) (hb : Bornology.IsBounded V) :
    (stoppedBrownianLaw V z μ).map BouRabeeGwynne.CurveSpace.endPoint =
      ((stoppedBrownianLaw ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V) 0 μ).map
        BouRabeeGwynne.CurveSpace.endPoint).map (fun x => z + (r : ℝ)⁻¹ • x) := by
  apply brownian_exit_endpoint_law_scale hd hμ r hr z hV
  exact isBounded_preimage_affine hb z (inv_ne_zero (by exact_mod_cast hr.ne'))

end LatticeProb
end
