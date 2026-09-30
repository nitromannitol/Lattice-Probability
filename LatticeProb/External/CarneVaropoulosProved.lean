import LatticeProb.External.CarneVaropoulos
import LatticeProb.Graph.CarneVaropoulos

/-!
# The Carne–Varopoulos bound, proved

The proposition `LatticeProb.External.CarneVaropoulos G` holds for every locally finite graph `G`,
by `LatticeProb.Graph.walkLaw_eval_le_carneVaropoulos`. A formalization that carries the
proposition as a hypothesis can discharge it with `carneVaropoulos_holds`.
-/

namespace LatticeProb.External

/-- **The Carne–Varopoulos bound holds** for the simple random walk on every connected,
nontrivial, locally finite graph. -/
theorem carneVaropoulos_holds {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace V] : CarneVaropoulos G :=
  fun _ _ hG x y n hn => LatticeProb.Graph.walkLaw_eval_le_carneVaropoulos G hG x y n hn

end LatticeProb.External
