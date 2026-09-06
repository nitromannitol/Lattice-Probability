/-
The random-walk representation of the odometer on a graph.

The odometer after `n` rounds is the least upper bound of the expected payoffs
over the stopping times bounded by `n`, and the bound is attained at the first
time the remaining value vanishes.  Stating the first half as `IsLUB` means no
junk value of an unattained supremum can satisfy it: it says both that the
odometer is an upper bound for every bounded stopping rule and that it is the
least one.  The scenery is the excess mass, so the payoff is the sum of the
scenery along the walk.
-/
import LatticeProb.Graph.Representation

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem LatticeProb.Graph.randomWalkRepresentation [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    IsLUB (LatticeProb.Graph.stopValues G (LatticeProb.Graph.excess σ) n x) (LatticeProb.Graph.odometer G σ n x) ∧
      LatticeProb.Graph.odometer G σ n x =
        LatticeProb.Graph.walkExp G n x (fun X =>
          LatticeProb.Graph.payoff G (LatticeProb.Graph.excess σ) (LatticeProb.Graph.optimalStop G (LatticeProb.Graph.excess σ) n X) X)
:= ⟨LatticeProb.Graph.isLUB_odometer hG σ n x, (LatticeProb.Graph.walkExp_optimalStop hG σ n x).symm⟩
