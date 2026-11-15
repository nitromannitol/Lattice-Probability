import LatticeProb.Walk.SelectedParentBlockCellCollar
import LatticeProb.Walk.WalkSelectedStageActive

/-! # Physical selected-stage parent-block collars -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- A strictly advancing physical stage has a parent-block collar in complex
coordinates, centered at a square containing its starting point. -/
theorem physical_selected_parentBlock_collar_of_clock_lt
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ C, p C ∈ (C.1 : Set Plane)) (cell : V → H.cells)
    (centres : J → ℂ) (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ C, 0 < H.holding C) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (a : ℂ) (S s r R δ : ℝ)
    (hS : 0 ≤ S) (hs : 0 < s) (hδ : 0 ≤ δ) (hr : 4 * S < r)
    (hmargin : r + 4 * s + (ε : ℝ) * δ ≤ R)
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        closedSquare (centres j) s)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (C.1 : Set Plane) ≤ δ)
    (n k l : ℕ)
    (hk : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select n ω).1 = k)
    (hl : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select (n + 1) ω).1 = l)
    (hadvance : scaledJumpTime H (cell ∘ ω) hpos ε k <
      scaledJumpTime H (cell ∘ ω) hpos ε l) :
    ∃ j, select n (ω k) = some j ∧
      Complex.orthonormalBasisOneI.repr.symm
        (H.interpolatedWalk p ε (cell ∘ ω) (scaledJumpTime H (cell ∘ ω) hpos ε k)) ∈
        closedSquare (centres j) s ∧
      ∀ t ∈ Icc (scaledJumpTime H (cell ∘ ω) hpos ε k)
          (scaledJumpTime H (cell ∘ ω) hpos ε l),
        Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t) ∈
          Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock (centres j) s) := by
  let f := Complex.orthonormalBasisOneI.repr
  let pos : V → Plane := fun v => (ε : ℝ) • p (cell v)
  let B : J → Set V := fun j => {v | f.symm (pos v) ∈ parentBlock (centres j) s}
  have hactive := actualWalkStage_active_of_physical_clock_lt H cell pos B initial select ω
    n k l hpos hε hk hl hadvance
  obtain ⟨j, hj, hjcollar⟩ := active_cellWalk_parentBlock_collar H hH p hp cell centres
    initial select ω hpos hunb hadj hε a S s r R δ hS hs hδ hr hmargin hselect hmesh
    n k l hk hl hactive
  refine ⟨j, hj, ?_, ?_⟩
  · have hknot := interpolatedWalk_at_jumpTime H p (cell ∘ ω) hpos hunb k hε
    change H.interpolatedWalk p ε (cell ∘ ω) (scaledJumpTime H (cell ∘ ω) hpos ε k) = _ at hknot
    rw [hknot]
    exact (hselect n (ω k) j hj).2
  · intro t ht
    have hc := hjcollar t (show (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) k ≤ (t : ℝ) from ht.1)
      (show (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l from ht.2)
    change H.interpolatedWalk p ε (cell ∘ ω) t ∈
      Metric.cthickening ((ε : ℝ) * (2 * δ)) (f '' (parentBlock (centres j) s)) at hc
    change f.symm (H.interpolatedWalk p ε (cell ∘ ω) t) ∈
      Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock (centres j) s)
    rw [Metric.mem_cthickening_iff] at hc ⊢
    rw [← Metric.infEDist_image f.isometry]
    simpa only [f.apply_symm_apply] using hc

end BouRabeeGwynne.FiniteConductanceNetwork
end
