/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusShiftCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TranslatedPointCost

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_translated_crossing_cost_compare
    (ξ : ℝ) (F G : ℂ → ℝ) (U A B : Set ℂ) (a : ℂ) (c : ℝ)
    (h : ∀ x, G x = F (x + a) - c) :
    crossLenIn ξ F ((· + a) '' U) ((· + a) '' A) ((· + a) '' B) ≤
        ENNReal.ofReal (Real.exp |ξ * c|) * crossLenIn ξ G U A B ∧
      crossLenIn ξ G U A B ≤
        ENNReal.ofReal (Real.exp |ξ * c|) *
          crossLenIn ξ F ((· + a) '' U) ((· + a) '' A) ((· + a) '' B) := by
  rw [crossLenIn_image_add ξ F U A B a]
  constructor
  · refine T20D.crossLenIn_le_of_le_add (fun x _ => ?_)
    have hx := h x
    have hle := le_abs_self (ξ * c)
    nlinarith [congrArg (fun v : ℝ => ξ * v) hx]
  · refine T20D.crossLenIn_le_of_le_add (fun x _ => ?_)
    have hx := h x
    have hle := neg_le_abs (ξ * c)
    nlinarith [congrArg (fun v : ℝ => ξ * v) hx]

theorem dg20_image_add_closedBall (c a : ℂ) (R : ℝ) :
    (fun x : ℂ => x + a) '' closedBall c R = closedBall (c + a) R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_add_right] using hx
  · intro hy
    refine ⟨y - a, ?_, by abel⟩
    change dist y (c + a) ≤ R at hy
    change dist (y - a) c ≤ R
    rw [← dist_add_right (y - a) c a]
    simpa only [sub_add_cancel] using hy

theorem dg20_image_add_sphere (c a : ℂ) (R : ℝ) :
    (fun x : ℂ => x + a) '' sphere c R = sphere (c + a) R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_sphere, dist_add_right] using hx
  · intro hy
    refine ⟨y - a, ?_, by abel⟩
    change dist y (c + a) = R at hy
    change dist (y - a) c = R
    rw [← dist_add_right (y - a) c a]
    simpa only [sub_add_cancel] using hy

end SupercriticalLQGUniqueness.B2.DG20Pt
