import LatticeProb.Prob.Percolation.LatticeLinearGrowth
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# Pointwise growth on an infinite actual component

Nonzero constants on the fully open positive-dimensional lattice satisfy the literal
cofinite pointwise growth condition. The selected actual component is infinite, and
the pointwise-to-A₁ bridge applies to its actual harmonic equation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- Constants satisfy true radial pointwise growth on every actual component. -/
theorem componentPointwiseLinearGrowth_const (C : OpenComponent ω) (c : ℝ) :
    componentPointwiseLinearGrowth C (fun _ => c) := by
  rw [componentPointwiseLinearGrowth_iff_tail]
  refine ⟨|c| + 1, by positivity, 1, fun x hx => ?_⟩
  have hc := abs_nonneg c
  norm_num only [Nat.cast_one] at hx
  nlinarith

/-- Nonzero constants give an infinite all-open consumer of the pointwise-to-A₁ bridge. -/
theorem allOpen_nonzero_pointwise_linear_growth (d : ℕ) [NeZero d] :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)
    C.supp.Infinite ∧ ∃ u : C → ℝ, u ≠ 0 ∧
      componentPointwiseLinearGrowth C u ∧
      (∀ x, componentLaplacian C u x = 0) ∧ u ∈ harmonicGrowthSpace C 1 := by
  dsimp only
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent d)
  have hg := componentPointwiseLinearGrowth_const C 1
  have hh : ∀ x, componentLaplacian C (fun _ => 1) x = 0 := by
    intro x
    rw [componentLaplacian_eq_netLaplacian]
    exact Network.netLaplacian_const _ 1 x
  refine ⟨uniqueInfiniteComponent_infinite _, fun _ => 1, ?_, hg, hh,
    mem_harmonicGrowthSpace_one_of_pointwise_linear_growth C _ hh hg⟩
  intro he
  obtain ⟨x, hx⟩ := C.nonempty_supp
  have hv := congrFun he (⟨x, hx⟩ : C)
  norm_num only [Pi.zero_apply, one_ne_zero] at hv

/-- The singleton all-closed component also obeys the finite-component convention. -/
theorem allClosed_pointwise_linear_growth (z : Vertex d)
    (u : (openGraph (allClosed d)).connectedComponentMk z → ℝ) :
    componentPointwiseLinearGrowth ((openGraph (allClosed d)).connectedComponentMk z) u := by
  have he : u = fun _ => u ⟨z, rfl⟩ := by
    funext x
    exact congrArg u (Subtype.ext (allClosed_component_vertex_eq z x))
  rw [he]
  exact componentPointwiseLinearGrowth_const _ _

end

end LatticeProb.Percolation
