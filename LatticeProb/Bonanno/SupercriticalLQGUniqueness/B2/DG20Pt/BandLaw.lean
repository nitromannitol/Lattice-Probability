/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BandLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem map_phiMN_dilate_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) {k n : ℕ} (hkn : k ≤ n) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    P.map (fun ω z => phiMN W P k n ((r : ℂ) * z) ω) =
      P.map (fun ω z => phiMN W P 0 (n - k) z ω) := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  have hφ := isPhiVersion_phiMN hW hkn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - k))
  have hra : (2 : ℝ)⁻¹ ^ n / r = (2 : ℝ)⁻¹ ^ (n - k) := by
    simp only [r]
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hkn]
  have hrb : (2 : ℝ)⁻¹ ^ k / r = (2 : ℝ)⁻¹ ^ 0 := by
    simp only [r]
    field_simp
  exact map_modification_scale hW
    (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ k)
    (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn)
    hr (Y₁ := fun z ω => phiMN W P k n ((r : ℂ) * z) ω)
    (Y₂ := phiMN W P 0 (n - k))
    (fun z => hφ.meas _) hφ0.meas
    (fun z => hφ.ae_eq _) (fun z => by rw [hra, hrb]; exact hφ0.ae_eq z)
    (F := id) measurable_id

 



end SupercriticalLQGUniqueness.B2.DG20Pt
