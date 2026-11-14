/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefYCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefYGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric
open scoped ComplexConjugate

def laneCRefYMetric (D : ContMetric) : ContMetric :=
  laneCConjMetric (D.affine 1 one_ne_zero Complex.I)

theorem laneC_refYMetric_len (D : ContMetric) (ρ : ℝ → ℂ) (a b : ℝ) :
    (laneCRefYMetric D).len ρ a b =
      D.len (fun t => laneCRefY (ρ t)) a b := by
  rw [laneCRefYMetric, laneC_conjMetric_len, laneC_affineMetric_len]
  congr 1
  funext t
  simp [laneCRefY]

theorem laneC_refYMetric_len_reflected (D : ContMetric) (ρ : ℝ → ℂ)
    (a b : ℝ) :
    (laneCRefYMetric D).len (fun t => laneCRefY (ρ t)) a b =
      D.len ρ a b := by
  rw [laneC_refYMetric_len]
  have heq : (fun t => laneCRefY (laneCRefY (ρ t))) = ρ := by
    funext t
    exact laneC_refY_involutive (ρ t)
  rw [heq]

end SupercriticalLQGUniqueness.B2.DG20Conc
