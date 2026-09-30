import LatticeProb.Graph.Walk

/-!
# The Carne–Varopoulos bound

The pointwise Carne–Varopoulos bound for the simple random walk on a connected, nontrivial,
locally finite graph (T. K. Carne, 1985; N. Varopoulos, 1985; Lyons–Peres, *Probability on Trees
and Networks*, Theorem 13.4): `P_x(X_n = y) ≤ 2 √(deg y / deg x) e^{-dist(x, y)²/(2n)}` for
`n ≥ 1`.

The statement is recorded here as a proposition so that a formalization citing the bound can
carry it as an explicit hypothesis; it is proved in `LatticeProb.External.CarneVaropoulosProved`.
-/

namespace LatticeProb.External

/-- **The Carne–Varopoulos bound** for the simple random walk `LatticeProb.Graph.walkLaw` on a
connected, nontrivial, locally finite graph with measurable singletons:
`P_x(X_n = y) ≤ 2 √(deg y / deg x) exp(-dist(x, y)² / (2n))` for `n ≥ 1`. -/
def CarneVaropoulos {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace V] : Prop :=
  MeasurableSingletonClass V → Nontrivial V → G.Connected →
    ∀ (x y : V) (n : ℕ), 1 ≤ n →
      LatticeProb.Graph.walkLaw G x {X : ℕ → V | X n = y} ≤
        ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
          Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)))

end LatticeProb.External
