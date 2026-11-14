/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistShiftAnnulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFixedAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem image_add_closedBall (c : ℂ) (R : ℝ) :
    (fun x : ℂ => x + c) '' closedBall (0 : ℂ) R = closedBall c R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mem_closedBall, dist_eq_norm, add_comm, add_left_comm, add_assoc] using hx
  · intro hy
    refine ⟨y - c, ?_, by abel⟩
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hy

private theorem image_add_sphere (c : ℂ) (R : ℝ) :
    (fun x : ℂ => x + c) '' sphere (0 : ℂ) R = sphere c R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mem_sphere, dist_eq_norm, add_comm, add_left_comm, add_assoc] using hx
  · intro hy
    refine ⟨y - c, ?_, by abel⟩
    simpa only [mem_sphere, dist_eq_norm, sub_zero] using hy

theorem pt_dist_compact_annulus_law_shift
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : ℝ) (n : ℕ) (c : ℂ) (R a b : ℝ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω)
      (closedBall c R) (sphere c a) (sphere c b) ∈ S} =
    P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω)
      (closedBall 0 R) (sphere 0 a) (sphere 0 b) ∈ S} := by
  have hlaw := measure_crossLenIn_phiMN_motion hW (Nat.zero_le n)
    (1 : Circle) c (isCompact_closedBall (0 : ℂ) R) hS
    (ξ := ξ) (K := closedBall (0 : ℂ) R)
    (A := sphere (0 : ℂ) a) (B := sphere (0 : ℂ) b)
  simpa only [Circle.coe_one, one_mul, image_add_closedBall,
    image_add_sphere] using hlaw

end SupercriticalLQGUniqueness.B2.DG20Pt
