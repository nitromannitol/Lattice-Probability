/-
The odometer recursion: the odometer after `n + 1` rounds is the positive part
of the average of the odometer after `n` rounds over the neighbours, plus the
scenery.  The graph is infinite, locally finite and connected throughout.
-/
import LatticeProb.Graph.Odometer

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem LatticeProb.Graph.odometerRecursion [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    LatticeProb.Graph.odometer G σ (n + 1) x =
      max (LatticeProb.Graph.walkOp G (LatticeProb.Graph.odometer G σ n) x + LatticeProb.Graph.scenery G σ x) 0
:= by
  rw [odometer_succ_max hG]
  have hle := odometer_le_bellman (G := G) hG σ n x
  have hnn := odometer_nonneg (G := G) σ n x
  rcases le_total (0 : ℝ) (walkOp G (odometer G σ n) x + scenery G σ x) with hA | hA
  · rw [max_eq_left hA, max_eq_left (by rw [max_eq_left hA] at hle; exact hle)]
  · rw [max_eq_right hA] at hle
    rw [max_eq_right hA, max_eq_right (by linarith)]
    linarith
