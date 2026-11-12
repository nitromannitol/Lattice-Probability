/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanLC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBdy

/-!
# Toward node J1b (local connectivity of `∂𝓑^•_s`): boundary bumping

Miller–Sheffield arXiv:1506.03806, proof of Prop 2.1 (`mapmaking_final.tex` l. 572): "since `Γ`
is connected the closure of every component of `Γ ∩ B(z, s)` has non-empty intersection with
`∂B(z, s)`". `jl_boundary_bumping` is this (boundary bumping theorem for continua; proof via
`connectedComponent_eq_iInter_isClopen` in the compact space `Γ ∩ cl B(x, ρ)`, as in mathlib's
proof of that lemma). It is applied to `Γ = ∂𝓑^•_s`, which is connected by J1c
(`jb_isPreconnected_frontier_diff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.GM

/-- The frontier of a component of the complement of a closed plane set `F` lies in `F`. -/
theorem jl_frontier_cc_subset {F : Set ℂ} (hF : IsClosed F) (y : ℂ) :
    frontier (connectedComponentIn Fᶜ y) ⊆ F := by
  intro p hp
  by_contra hpF
  have hpo : IsOpen (connectedComponentIn Fᶜ p) := hF.isOpen_compl.connectedComponentIn
  obtain ⟨c, hcp, hcC⟩ := mem_closure_iff.1 hp.1 _ hpo (mem_connectedComponentIn hpF)
  have hpC : p ∈ connectedComponentIn Fᶜ y := by
    rw [connectedComponentIn_eq hcC, ← connectedComponentIn_eq hcp]
    exact mem_connectedComponentIn hpF
  exact hp.2 ((hF.isOpen_compl.connectedComponentIn).interior_eq.symm ▸ hpC)

variable {D : ContMetric} {z : ℂ} {s : ℝ}

end LQGMetric.GM
