import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkStopping
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable
import LatticeProb.Walk.AdjacentPrefixExtension

/-! # Stopped polygonal curves under prefix replacement -/

set_option autoImplicit false

noncomputable section

open BouRabeeGwynne

namespace LatticeProb

/-- Replacing a path after a finite first exit preserves its stopped curve. -/
theorem stoppedPolygonalCurve_eq_of_prefix {d : ℕ} {V : Type*}
    (pos : V → Euc d) (A : Set V) {x y : ℕ → V} {M : ℕ}
    (hprefix : ∀ n ≤ M, y n = x n)
    (hexit : FiniteConductanceNetwork.exitTime A x ≤ (M : WithTop ℕ)) :
    stoppedPolygonalCurve pos A y = stoppedPolygonalCurve pos A x := by
  have heq := FiniteConductanceNetwork.exitTime_congr_prefix_of_le A hprefix hexit
  have hfin : FiniteConductanceNetwork.exitTime A x ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hexit
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmM : m ≤ M := WithTop.coe_le_coe.mp (hm.trans_le hexit)
  unfold stoppedPolygonalCurve
  rw [heq, ← hm, WithTop.untopD_coe]
  apply congrArg CurveSpace.project
  exact polygonalCurve_congr_prefix pos (fun n hn => hprefix n (hn.trans hmM))

/-- Alternating the last edge after a finite first exit preserves the stopped curve. -/
theorem stoppedPolygonalCurve_alternateLastEdge {d : ℕ} {V : Type*}
    (pos : V → Euc d) (A : Set V) (x : ℕ → V) (k : ℕ)
    (hexit : FiniteConductanceNetwork.exitTime A x ≤ ((k + 1 : ℕ) : WithTop ℕ)) :
    stoppedPolygonalCurve pos A (alternateLastEdge x k) = stoppedPolygonalCurve pos A x := by
  exact stoppedPolygonalCurve_eq_of_prefix pos A
    (fun n hn => alternateLastEdge_eq x k n hn) hexit

end LatticeProb
end
