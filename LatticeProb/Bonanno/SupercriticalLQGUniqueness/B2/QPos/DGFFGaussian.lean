/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFGaussian at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBox

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 

def algebraicGreen : Matrix V V ℝ :=
  (fun i j => (2 / Real.pi) * (G.precision⁻¹) i j)

 

def gaussianOfPrecision (_hK : G.precision.PosDef) :
    Measure (EuclideanSpace ℝ V) := multivariateGaussian 0 G.precision⁻¹

theorem covariance_gaussianOfPrecision (hK : G.precision.PosDef) (i j : V) :
    cov[fun x : EuclideanSpace ℝ V => x i,
      fun x : EuclideanSpace ℝ V => x j; G.gaussianOfPrecision hK] =
      (Real.pi / 2) * G.algebraicGreen i j := by
  rw [gaussianOfPrecision,
    covariance_eval_multivariateGaussian hK.inv.posSemidef]
  simp only [algebraicGreen]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
