import LatticeProb.Prob.Percolation.LSS.Basic
import LatticeProb.Prob.Percolation.LSS.Defs
import LatticeProb.Prob.Percolation.LSS.DependencyGraph
import LatticeProb.Prob.Percolation.LSS.LocalLemma
import LatticeProb.Prob.Percolation.LSS.Thin
import LatticeProb.Prob.Percolation.LSS.Domination
import LatticeProb.Prob.Percolation.LSS.DominationCouple
import LatticeProb.Prob.Percolation.LSS.DominationFinite
import LatticeProb.Prob.Percolation.LSS.Cylinder
import LatticeProb.Prob.Percolation.LSS.UpHull
import LatticeProb.Prob.Percolation.LSS.General
import LatticeProb.Prob.Percolation.LSS.Countable

/-!
# Domination by product measures of Liggett, Schonmann and Stacey

Entry module for the domination theorems of T. M. Liggett, R. H. Schonmann and A. M. Stacey,
*Domination by product measures*, Ann. Probab. 25 (1997). It imports the vocabulary, the
statements and the proofs under `LatticeProb.Percolation.LSS.*`.

Ported from the Exploding-Sandpiles formalization, `Exploding/External/LSSBoundedDegreeProved.lean`.
-/

namespace LatticeProb.Percolation.LSS

/-- The bounded-degree domination of Liggett, Schonmann and Stacey, with no remaining
hypothesis: the statement `LiggettSchonmannStaceyBoundedDegree` is proved. -/
theorem lssBoundedDegree : LiggettSchonmannStaceyBoundedDegree :=
  xlse_lss_bounded_degree

end LatticeProb.Percolation.LSS
