import Mathlib
import LatticeProb.Graph.Basic
import LatticeProbAudit.GFF.SolutionBasic

/-!
# Comparator bridge: `LatticeProbAudit.GFF` vocabulary to the library

The vocabulary of `LatticeProbAudit/GFF/SolutionBasic.lean` (namespace `LatticeProbAudit`), a
verbatim copy of the vocabulary block of `LatticeProbAudit/GFF/Challenge.lean`, copies four
definitions of `LatticeProb/Graph/Basic.lean`.  The copies are new constants, so this file
proves that each agrees with its library counterpart: the averaging operator by unfolding, the
killed transition kernel by induction on time, and the two Green functions from the kernel.

**It is imported by `LatticeProbAudit/GFF/Solution.lean` only.**  The `Challenge` and
`SolutionBasic` files must stay Mathlib-only: a library import inside the vocabulary changes
instance elaboration there and breaks the comparator's constant-by-constant closure check.
-/

namespace LatticeProbAudit.Bridge

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

theorem walkOp_eq : LatticeProbAudit.walkOp G = LatticeProb.Graph.walkOp G := rfl

theorem killedHeat_eq (C : Set V) :
    LatticeProbAudit.killedHeat G C = LatticeProb.Graph.killedHeat G C := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x y
    simp only [LatticeProbAudit.killedHeat, LatticeProb.Graph.killedHeat, ih, walkOp_eq]

theorem killedGreen_eq (C : Set V) :
    LatticeProbAudit.killedGreen G C = LatticeProb.Graph.killedGreen G C := by
  funext y v
  simp only [LatticeProbAudit.killedGreen, LatticeProb.Graph.killedGreen, killedHeat_eq]

theorem killedGreenReal_eq (C : Set V) :
    LatticeProbAudit.killedGreenReal G C = LatticeProb.Graph.killedGreenReal G C := by
  funext y v
  simp only [LatticeProbAudit.killedGreenReal, LatticeProb.Graph.killedGreenReal, killedGreen_eq]

end LatticeProbAudit.Bridge
