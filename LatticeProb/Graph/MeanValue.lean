/-
The mean value property iterated: a function that is its own one-step average at
every vertex equals its `n`-step kernel average, summed over the vertices
reachable in `n` steps.

This is the identity behind the Liouville theorem for bounded harmonic functions
on a recurrent network: it writes `f x` as the `n`-step kernel average of `f`,
so a bounded `f` is controlled by the total mass of the kernel, which is
unbounded exactly when the network is recurrent.
-/
import LatticeProb.Graph.Basic
import LatticeProb.Graph.Green
import LatticeProb.Graph.Reach

open scoped Classical

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The mean value property iterated: a function equal to its own one-step
average at every vertex equals its `n`-step kernel average. -/
theorem eq_sum_heat_mul_of_harmonic (_hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ)
    (hharm : ∀ x, walkOp G f x = f x) :
    ∀ (n : ℕ) (x : V), f x = ∑ v ∈ reach G n x, heat G n x v * f v := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    simp [reach_zero, heat]
  | succ n ih =>
    intro x
    rw [← hharm x, walkOp]
    have hsub : ∀ y ∈ G.neighborFinset x,
        reach G n y ⊆ reach G (n + 1) x := by
      intro y hy v hv
      rw [reach_succ]
      exact Finset.mem_biUnion.mpr ⟨y, hy, hv⟩
    have hstep : ∀ y ∈ G.neighborFinset x,
        f y = ∑ v ∈ reach G (n + 1) x, heat G n y v * f v := by
      intro y hy
      rw [ih y]
      exact Finset.sum_subset (hsub y hy) (fun v _ hv => by
        rw [heat_eq_zero_of_notMem_reach n y v hv, zero_mul])
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [heat_succ, walkOp, div_mul_eq_mul_div, Finset.sum_mul]

end LatticeProb.Graph
