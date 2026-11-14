/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefXCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefXGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefYCost

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

def laneCRefXMetric (D : ContMetric) : ContMetric :=
  laneCConjMetric (D.affine (-1) (by norm_num) 1)

theorem laneC_refXMetric_len (D : ContMetric) (ρ : ℝ → ℂ) (a b : ℝ) :
    (laneCRefXMetric D).len ρ a b =
      D.len (fun t => laneCRefX (ρ t)) a b := by
  rw [laneCRefXMetric, laneC_conjMetric_len, laneC_affineMetric_len]
  congr 1
  funext t
  simp [laneCRefX]
  ring

theorem laneC_refXMetric_len_reflected (D : ContMetric) (ρ : ℝ → ℂ)
    (a b : ℝ) :
    (laneCRefXMetric D).len (fun t => laneCRefX (ρ t)) a b =
      D.len ρ a b := by
  rw [laneC_refXMetric_len]
  have heq : (fun t => laneCRefX (laneCRefX (ρ t))) = ρ := by
    funext t
    exact laneC_refX_involutive (ρ t)
  rw [heq]

end SupercriticalLQGUniqueness.B2.DG20Conc
