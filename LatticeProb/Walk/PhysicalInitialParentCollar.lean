import LatticeProb.Walk.SelectedParentBlockCellCollar
import LatticeProb.Walk.CellConfigKnotComparison
import LatticeProb.Walk.CellConfigFiniteExit

/-! # Initial parent-block collar in physical time -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- The initial physical stage stays in a parent-block collar, and starts in
its selected square. -/
theorem physical_initial_parentBlock_collar
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
    (houter : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      parentBlock a S)
    (hinit : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      closedSquare (centres initial) s)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (C.1 : Set Plane) ≤ δ)
    (l : ℕ)
    (hl : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select 0 ω).1 = l) :
    Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) 0) ∈
        closedSquare (centres initial) s ∧
      ∀ t ∈ Icc 0 (scaledJumpTime H (cell ∘ ω) hpos ε l),
        Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t) ∈
          Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock (centres initial) s) := by
  let f := Complex.orthonormalBasisOneI.repr
  have hzero : scaledJumpTime H (cell ∘ ω) hpos ε 0 = 0 := by
    apply NNReal.coe_injective
    change (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) 0 = 0
    rw [H.jumpTime_zero, mul_zero]
  have hknot := interpolatedWalk_at_jumpTime H p (cell ∘ ω) hpos hunb 0 hε
  change H.interpolatedWalk p ε (cell ∘ ω)
    (scaledJumpTime H (cell ∘ ω) hpos ε 0) = _ at hknot
  rw [hzero] at hknot
  constructor
  · rw [hknot]
    exact hinit
  · intro t ht
    have hc := initial_cellWalk_parentBlock_collar H hH p hp cell centres initial select ω
      hpos hunb hadj hε a S s r R δ hS hs hδ hr hmargin houter hinit hmesh l hl t
      (show (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l from ht.2)
    change H.interpolatedWalk p ε (cell ∘ ω) t ∈
      Metric.cthickening ((ε : ℝ) * (2 * δ)) (f '' parentBlock (centres initial) s) at hc
    change f.symm (H.interpolatedWalk p ε (cell ∘ ω) t) ∈
      Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock (centres initial) s)
    rw [Metric.mem_cthickening_iff] at hc ⊢
    rw [← Metric.infEDist_image f.isometry]
    simpa only [f.apply_symm_apply] using hc

end BouRabeeGwynne.FiniteConductanceNetwork
end
