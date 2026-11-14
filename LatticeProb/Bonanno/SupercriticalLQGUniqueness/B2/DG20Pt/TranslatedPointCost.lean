/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.TranslatedPointCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

 

set_option autoImplicit false
noncomputable section

open LQGMetric LQGMetric.DDDF
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_translated_point_cost_compare
    (ξ : ℝ) (F G : ℂ → ℝ) (U : Set ℂ) (z w a : ℂ) (c : ℝ)
    (h : ∀ x, G x = F (x + a) - c) :
    crossLenIn ξ F ((· + a) '' U) {z + a} {w + a} ≤
        ENNReal.ofReal (Real.exp |ξ * c|) * crossLenIn ξ G U {z} {w} ∧
      crossLenIn ξ G U {z} {w} ≤
        ENNReal.ofReal (Real.exp |ξ * c|) *
          crossLenIn ξ F ((· + a) '' U) {z + a} {w + a} := by
  have htr : crossLenIn ξ F ((· + a) '' U) {z + a} {w + a} =
      crossLenIn ξ (fun x => F (x + a)) U {z} {w} := by
    simpa only [Set.image_singleton] using
      crossLenIn_image_add ξ F U {z} {w} a
  rw [htr]
  constructor
  · refine T20D.crossLenIn_le_of_le_add (fun x _ => ?_)
    have hx := h x
    have hle := le_abs_self (ξ * c)
    nlinarith [congrArg (fun v : ℝ => ξ * v) hx]
  · refine T20D.crossLenIn_le_of_le_add (fun x _ => ?_)
    have hx := h x
    have hle := neg_le_abs (ξ * c)
    nlinarith [congrArg (fun v : ℝ => ξ * v) hx]

end SupercriticalLQGUniqueness.B2.DG20Pt
