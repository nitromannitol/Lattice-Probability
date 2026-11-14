/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFieldScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB_fine_field_scale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) :
    P.map (fun ω x => phiMN W P K n
      (((2 : ℝ)⁻¹ ^ K : ℝ) * x) ω) =
      P.map (fun ω x => phiMN W P 0 (n - K) x ω) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ K
  have hr : 0 < r := by positivity
  have hφ := isPhiVersion_phiMN hW hKn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - K))
  have hra : (2 : ℝ)⁻¹ ^ n / r = (2 : ℝ)⁻¹ ^ (n - K) := by
    simp only [r]
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hKn]
  have hrb : (2 : ℝ)⁻¹ ^ K / r = (2 : ℝ)⁻¹ ^ 0 := by
    simp only [r]
    field_simp
  have hlaw := map_modification_scale hW
    (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ K)
    (by positivity) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn) hr
    (Y₁ := fun x ω => phiMN W P K n ((r : ℂ) * x) ω)
    (Y₂ := phiMN W P 0 (n - K))
    (fun x => hφ.meas _) hφ0.meas
    (fun x => hφ.ae_eq _)
    (fun x => by rw [hra, hrb]; exact hφ0.ae_eq x)
    (F := id) measurable_id
  simpa only [id] using hlaw

 

theorem laneB_fine_field_scale_motion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (u : Circle) (c : ℂ) :
    P.map (fun ω x => phiMN W P K n
      ((u : ℂ) * (((2 : ℝ)⁻¹ ^ K : ℝ) * x) + c) ω) =
      P.map (fun ω x => phiMN W P 0 (n - K) x ω) := by
  have hφ := isPhiVersion_phiMN hW hKn
  let F : (ℂ → ℝ) → (ℂ → ℝ) :=
    fun g x => g (((2 : ℝ)⁻¹ ^ K : ℝ) * x)
  have hF : Measurable F := measurable_pi_iff.mpr fun x => measurable_pi_apply _
  have hleft : Measurable (fun ω x =>
      phiMN W P K n ((u : ℂ) * x + c) ω) :=
    measurable_pi_iff.mpr fun x => hφ.meas _
  have hright : Measurable (fun ω x => phiMN W P K n x ω) :=
    measurable_pi_iff.mpr hφ.meas
  have hm := map_phiMN_motion hW hKn u c
  have hm' := congrArg (Measure.map F) hm
  rw [Measure.map_map hF hleft, Measure.map_map hF hright] at hm'
  exact hm'.trans (laneB_fine_field_scale P W hW hKn)

end SupercriticalLQGUniqueness.B2.DG20Conc
