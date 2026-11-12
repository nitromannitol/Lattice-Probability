/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TreeInequality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux

/-!
# Node `J42`: the deterministic tree inequality (4.2)–(4.3)

For a well-formed partition tree `T` of an admissible path `γ`, a continuous field `φ` and
`ξ = δ^{3/2}`:

* the leaves' time intervals partition `[0,1]`, so the LFPP length is the sum of the leaf
  lengths (`Lnode_sum`);
* each leaf length is at least `R_v e^{ξ (H_v - osc φ (8ε))}` (chord ≤ arclength and the
  oscillation bound, `Lnode_leaf`);
* Jensen's inequality for `log`, applied node by node with the weights `q_{uv} = R_v / S_u`,
  gives `log L ≥ ξ H_root - ξ osc + Σ_v θ(v) Σ_{u ≺ v} (A_u + ξ Δ_u)` (`tree_jensen_root`);
* (4.3): `-(A_u + ξ Δ_u) ≤ δ² (δ^{-1/2} G_u - k_u)` (`local_bound`).
-/

noncomputable section

open MeasureTheory Set

namespace LQGDimension

open Blueprint.Draft TreeIneqJ42

/-- **Node `J42`** ((4.2) + (4.3) + flow averaging). -/
theorem treeInequality : Blueprint.Draft.TreeInequality := by
  intro γ hγ M hM ε hε T hT φ hφ δ hδ
  have hH : TreeHyp T γ M ε := ⟨hT, hγ.source, hγ.target, by omega⟩
  have hξ : 0 ≤ δ ^ (3 / 2 : ℝ) := (Real.rpow_pos_of_pos hδ _).le
  obtain ⟨hs, hLpos, hineq⟩ := tree_jensen_root hH
    (L := Lnode T (δ ^ (3 / 2 : ℝ)) φ γ)
    (F := fun w => δ ^ (3 / 2 : ℝ) * T.H γ φ w - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε))
    (Y := fun w => -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ w - T.kbin γ δ w)))
    (fun u hu hn => Lnode_sum hT hγ hφ _ hu hn)
    (fun v hv => Lnode_leaf hT hγ hφ hε.1 hξ hv)
    (fun u hu hn => local_bound hH hδ hu hn _)
  rw [Lnode_root hT] at hLpos hineq
  refine ⟨hLpos, ?_, fun v hv => (flow_pos hH (Finset.mem_filter.1 hv).1).le, hs⟩
  have hineq' : (δ ^ (3 / 2 : ℝ) * T.H γ φ [] - δ ^ (3 / 2 : ℝ) * osc φ (8 * ε)) +
      ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j))) ≤
      Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) := hineq
  have e : ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j))) =
      -(δ ^ 2 * ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  rw [e] at hineq'
  linarith

end LQGDimension
