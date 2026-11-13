/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Moments.ScaleLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Moments.Analytic
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law




 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Moments
open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

 

theorem tile_fine_field_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n) (v : ℂ) :
    P.map (fun ω x => phiMN W P m n
      (((((2 : ℝ)⁻¹ ^ m) : ℝ) : ℂ) * x + v) ω) =
    P.map (fun ω x => phiMN W P 0 (n - m) x ω) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ m
  have hr : 0 < r := by positivity
  let T : (ℂ → ℝ) → (ℂ → ℝ) := fun f x => f ((r : ℂ) * x)
  have hT : Measurable T := measurable_pi_iff.mpr fun x => measurable_pi_apply _
  have hφ := isPhiVersion_phiMN hW hmn
  have hF : Measurable fun ω x => phiMN W P m n x ω :=
    measurable_pi_iff.mpr hφ.meas
  have hFm : Measurable fun ω x => phiMN W P m n (x + v) ω :=
    measurable_pi_iff.mpr fun x => hφ.meas _
  have hmotion := map_phiMN_motion hW hmn 1 v
  have hmotionT : P.map (fun ω x => phiMN W P m n ((r : ℂ) * x + v) ω) =
      P.map (fun ω x => phiMN W P m n ((r : ℂ) * x) ω) := by
    have h := congrArg (Measure.map T) hmotion
    simp only [Circle.coe_one, one_mul] at h
    rw [Measure.map_map hT hFm, Measure.map_map hT hF] at h
    simpa only [Function.comp_def, T] using h
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - m))
  let Y₁ : ℂ → Ω → ℝ := fun x ω => phiMN W P m n ((r : ℂ) * x) ω
  have hra : (2 : ℝ)⁻¹ ^ n / r = (2 : ℝ)⁻¹ ^ (n - m) := by
    simp only [r]
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hmn]
  have hrb : (2 : ℝ)⁻¹ ^ m / r = (2 : ℝ)⁻¹ ^ 0 := by
    simp only [r]
    field_simp
  have hscale : P.map (fun ω x => phiMN W P m n ((r : ℂ) * x) ω) =
      P.map (fun ω x => phiMN W P 0 (n - m) x ω) := by
    have h := map_modification_scale hW (a := (2 : ℝ)⁻¹ ^ n)
      (b := (2 : ℝ)⁻¹ ^ m) (by positivity)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) hr
      (Y₁ := Y₁) (Y₂ := phiMN W P 0 (n - m))
      (fun x => hφ.meas _) hφ0.meas (fun x => hφ.ae_eq _)
      (fun x => by rw [hra, hrb]; exact hφ0.ae_eq x)
      (F := id) measurable_id
    simpa only [id] using h
  exact hmotionT.trans hscale


 


end SupercriticalLQGUniqueness.Exponent.Moments
