/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Assembly.AStar
import LatticeProb.Bonanno.LQGDimension.Assembly.Reductions

/-!
# Assembly: Theorem 1.1

The final assembly step: combine the first assertion (`theorem11_aStar_of`) with the reduction
steps (`lambdaAsymptotics_of`, `theorem11_lambda_of`, `theorem11_dimension_of`) into the full
statement `Theorem11`.
-/

noncomputable section

namespace LQGDimension

/-- Theorem 1.1, assembled from the `Section2` and `LFPP` blueprint obligations. -/
theorem theorem11_of (h1 : Blueprint.AOneFinite) (h2 : Blueprint.ASubadditiveE)
    (h3 : Blueprint.ALinearLowerBound) (hU : Blueprint.Prop12Upper) (hL : Blueprint.Prop12Lower) :
    Theorem11 := by
  have hA : Theorem11_AStar := theorem11_aStar_of h1 h2 h3
  have hLA : Blueprint.LambdaAsymptotics := lambdaAsymptotics_of hA hU hL
  exact ⟨hA, theorem11_lambda_of hLA, theorem11_dimension_of hLA⟩

end LQGDimension
