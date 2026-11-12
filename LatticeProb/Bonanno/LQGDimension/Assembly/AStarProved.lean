/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Assembly.AStarProved at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Assembly.AStar
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Section2.ZCovPSD
import LatticeProb.Bonanno.LQGDimension.Section2.Finite
import LatticeProb.Bonanno.LQGDimension.Section2.Subadditive
import LatticeProb.Bonanno.LQGDimension.Section2.LowerBound

/-!
# The first assertion of Theorem 1.1, unconditionally

`a_n` is finite and subadditive, and `0 < a* = lim a_n / n = inf_{n ≥ 1} a_n / n`.
-/

namespace LQGDimension

theorem aOneFinite : Blueprint.AOneFinite :=
  aOneFinite_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

theorem aSubadditiveE : Blueprint.ASubadditiveE :=
  aSubadditiveE_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

theorem aLinearLowerBound : Blueprint.ALinearLowerBound :=
  aLinearLowerBound_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

end LQGDimension
