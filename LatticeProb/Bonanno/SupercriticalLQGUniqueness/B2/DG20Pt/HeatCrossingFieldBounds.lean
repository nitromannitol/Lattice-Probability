/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingFieldBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAdapter
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_crossing_bounds_of_square_field
    (ξ : ℝ) (φ : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ x ∈ closedUnitSquare, |φ x| ≤ M) :
    ENNReal.ofReal (Real.exp (-(|ξ| * M))) ≤
      lfppCrossingLength ξ φ ∧
    lfppCrossingLength ξ φ ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) := by
  have h := LQGMetric.DDDF.exp_neg_le_lenObs
    (ξ := ξ) (Y := fun x (_ : Unit) => φ x)
    (fun _ => φ.continuous) (rectAB 1 1)
    zero_le_one zero_le_one (ω := ())
    (fun x hx => hM x (LQGMetric.DFGPS.rectAB_one_toSet ▸ hx))
  have h' := LQGMetric.DDDF.lenObs_le_exp
    (ξ := ξ) (Y := fun x (_ : Unit) => φ x)
    (rectAB 1 1) zero_le_one zero_le_one (ω := ())
    (fun x hx => hM x (LQGMetric.DFGPS.rectAB_one_toSet ▸ hx))
  have heq := dg20_lfppCrossingLength_eq_ofReal_lenObs
    ξ (fun _ : Unit => φ) ()
  constructor
  · rw [heq]
    exact ENNReal.ofReal_le_ofReal (by simpa [LQGMetric.DDDF.lenObs,
      MarkedRect.crossWidth, rectAB] using h)
  · rw [heq]
    exact ENNReal.ofReal_le_ofReal (by simpa [LQGMetric.DDDF.lenObs,
      MarkedRect.crossWidth, rectAB] using h')

end SupercriticalLQGUniqueness.B2.DG20Pt
