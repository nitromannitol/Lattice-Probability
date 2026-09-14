/-
Liouville theorems for harmonic functions on a network: on a finite connected
graph every harmonic function is constant, and on a recurrent network every
bounded harmonic function is constant.

The second is the classical bounded-harmonic-on-recurrent argument: the mean
value property iterated gives `f x = ∑_v heat G n x v * f v`, so a bounded `f`
is bounded by `C` times the total mass of the `n`-step kernel; recurrence makes
the Green function infinite, so those masses are unbounded and `f` must be
constant.
-/
import LatticeProb.Network.Basic
import LatticeProb.Graph.Basic
import LatticeProb.Graph.Setting

open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- On a finite connected graph every harmonic function is constant. -/
theorem eq_const_of_harmonicOn_of_finite [Fintype V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ)
    (hharm : HarmonicOn G (unitCond G) f Set.univ) (x y : V) : f x = f y := by
  classical
  obtain ⟨b, -, hbmax⟩ := Finset.exists_max_image (Finset.univ : Finset V) f ⟨x, Finset.mem_univ x⟩
  have hstep : ∀ u v : V, G.Adj u v → f u = f b → f v = f b := by
    intro u v huv hu
    have h := LatticeProb.Network.eq_of_harmonicOn_of_max f hharm (hdeg u).ne'
      (fun y _ => by rw [hu]; exact hbmax y (Finset.mem_univ y))
    exact (h v ((SimpleGraph.mem_neighborFinset _ _ _).mpr huv)).trans hu
  have hwalk : ∀ {u v : V} (p : G.Walk u v), f u = f b → f v = f b := by
    intro u v p
    induction p with
    | nil => exact id
    | cons hadj p' ih => exact ih ∘ hstep _ _ hadj
  obtain ⟨p⟩ := hG.preconnected b x
  obtain ⟨q⟩ := hG.preconnected b y
  exact (hwalk p rfl).trans (hwalk q rfl).symm

end LatticeProb.Network
