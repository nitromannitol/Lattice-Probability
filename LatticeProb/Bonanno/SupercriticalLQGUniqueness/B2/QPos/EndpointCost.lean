/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.EndpointCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBox

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
def inclusivePathCost {V : Type*} (weight : V → ℝ) (path : List V) : ℝ :=
  (path.map weight).sum

theorem inclusivePathCost_nonneg {V : Type*} (weight : V → ℝ)
    (hw : ∀ v, 0 ≤ weight v) (path : List V) :
    0 ≤ inclusivePathCost weight path := by
  unfold inclusivePathCost
  apply List.sum_nonneg
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact hw v

 

theorem inclusivePathCost_subpath_le {V : Type*} (weight : V → ℝ)
    (hw : ∀ v, 0 ≤ weight v) (before middle after : List V) :
    inclusivePathCost weight middle ≤
      inclusivePathCost weight (before ++ middle ++ after) := by
  have hb := inclusivePathCost_nonneg weight hw before
  have ha := inclusivePathCost_nonneg weight hw after
  simp only [inclusivePathCost, List.map_append, List.sum_append] at *
  linarith

 

theorem dgff_inclusive_subpath_le {V : Type*} (ξ : ℝ) (h : V → ℝ)
    (before middle after : List V) :
    inclusivePathCost (fun v => Real.exp (ξ * h v)) middle ≤
      inclusivePathCost (fun v => Real.exp (ξ * h v))
        (before ++ middle ++ after) :=
  inclusivePathCost_subpath_le _ (fun v => (Real.exp_pos _).le) _ _ _

end SupercriticalLQGUniqueness.B2.QPos
