/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSquareRing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

def laneBBufferedSquareRing (R : ℝ) : Set ℂ :=
  {z | ((17 / 16 : ℝ) * R ≤ |z.re| ∨ (17 / 16 : ℝ) * R ≤ |z.im|) ∧
    |z.re| ≤ (5 / 4 : ℝ) * R ∧ |z.im| ≤ (5 / 4 : ℝ) * R}

 

theorem laneB_bufferedSquareRing_subset_open_annulus
    {R : ℝ} (hR : 0 < R) :
    laneBBufferedSquareRing R ⊆
      {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} := by
  intro z hz
  rcases hz with ⟨hinner, hre, him⟩
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnorm0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hcoords : z.re ^ 2 ≤ ((5 / 4 : ℝ) * R) ^ 2 ∧
      z.im ^ 2 ≤ ((5 / 4 : ℝ) * R) ^ 2 := by
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hre)
        (add_nonneg (abs_nonneg z.re) (by positivity : 0 ≤ (5 / 4 : ℝ) * R)), sq_abs z.re]
    · nlinarith [mul_nonneg (sub_nonneg.mpr him)
        (add_nonneg (abs_nonneg z.im) (by positivity : 0 ≤ (5 / 4 : ℝ) * R)), sq_abs z.im]
  have hlow : R < ‖z‖ := by
    rcases hinner with hr | hi
    · have hs : ((17 / 16 : ℝ) * R) ^ 2 ≤ z.re ^ 2 := by
        nlinarith [sq_nonneg (|z.re| - (17 / 16 : ℝ) * R), sq_abs z.re]
      nlinarith [sq_nonneg z.im]
    · have hs : ((17 / 16 : ℝ) * R) ^ 2 ≤ z.im ^ 2 := by
        nlinarith [sq_nonneg (|z.im| - (17 / 16 : ℝ) * R), sq_abs z.im]
      nlinarith [sq_nonneg z.re]
  have hupp : ‖z‖ < 2 * R := by
    nlinarith [hcoords.1, hcoords.2]
  simpa only [Set.mem_ofPred_eq, dist_zero_right] using And.intro hlow hupp

end SupercriticalLQGUniqueness.B2.DG20Conc
