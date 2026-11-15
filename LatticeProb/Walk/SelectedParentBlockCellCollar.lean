import LatticeProb.Walk.SelectedCellLocalBuffer
import LatticeProb.Euclidean.SelectedParentBlockBuffer
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Cell-walk collars for selected parent blocks -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS Preorder
open scoped NNReal
open LatticeProb.ParentBlock

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- The initial parent-block stage has a physical-time collar under a local mesh bound. -/
theorem initial_cellWalk_parentBlock_collar
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (cell : V → H.cells)
    (centres : J → ℂ) (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (a : ℂ) (S s r R δ : ℝ)
    (hS : 0 ≤ S) (hs : 0 < s) (hδ : 0 ≤ δ) (hr : 4 * S < r)
    (hmargin : r + 4 * s + (ε : ℝ) * δ ≤ R)
    (houter : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      parentBlock a S)
    (hinit : Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell (ω 0))) ∈
      closedSquare (centres initial) s)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (l : ℕ)
    (hl : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select 0 ω).1 = l)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l) :
    H.interpolatedWalk p ε (cell ∘ ω) t ∈ Metric.cthickening ((ε : ℝ) * (2 * δ))
      (Complex.orthonormalBasisOneI.repr '' parentBlock (centres initial) s) := by
  let f := Complex.orthonormalBasisOneI.repr
  let pos : V → Plane := fun v => (ε : ℝ) • p (cell v)
  let B : J → Set V := fun j => {v | f.symm (pos v) ∈ parentBlock (centres j) s}
  let U : J → Set Plane := fun j => f '' parentBlock (centres j) s
  have hU : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ U j := by
    intro j v hv
    exact ⟨f.symm (pos v), hv, f.apply_symm_apply (pos v)⟩
  have hA : U initial ⊆ Metric.ball (f a) (r + 4 * s) := by
    apply image_parentBlock_subset_ball_of_anchor f hs.le hinit
    exact lt_of_le_of_lt (dist_center_le_of_mem_parentBlock hS houter) hr
  apply initial_cellWalk_mem_cthickening_of_local_buffer H hH p hp cell pos B initial select ω
    hpos hunb hadj hε U hU (Metric.ball (f a) (r + 4 * s)) (Metric.ball (f a) R)
    δ hδ hA
  · intro x hx
    exact closedBall_subset_ball_of_mem_ball hx hmargin
  · exact hmesh
  · exact hl
  · change f.symm (pos (ω 0)) ∈ parentBlock (centres initial) s
    have hb := ball_subset_interior_parentBlock hs.le hinit
    exact interior_subset (hb (show f.symm (pos (ω 0)) ∈ Metric.ball (f.symm (pos (ω 0))) s from by
      simpa only [Metric.mem_ball, dist_self] using hs))
  · exact ht


/-- An active selected parent-block stage has a physical-time collar under a local mesh bound. -/
theorem active_cellWalk_parentBlock_collar
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (cell : V → H.cells)
    (centres : J → ℂ) (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (a : ℂ) (S s r R δ : ℝ)
    (hS : 0 ≤ S) (hs : 0 < s) (hδ : 0 ≤ δ) (hr : 4 * S < r)
    (hmargin : r + 4 * s + (ε : ℝ) * δ ≤ R)
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        closedSquare (centres j) s)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (n k l : ℕ)
    (hk : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select n ω).1 = k)
    (hl : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select (n + 1) ω).1 = l)
    (hactive : (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select (n + 1) ω).2.1 = false) :
    ∃ j, select n (ω k) = some j ∧ ∀ t : ℝ≥0,
      (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) k ≤ (t : ℝ) →
      (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l →
      H.interpolatedWalk p ε (cell ∘ ω) t ∈ Metric.cthickening ((ε : ℝ) * (2 * δ))
        (Complex.orthonormalBasisOneI.repr '' parentBlock (centres j) s) := by
  let f := Complex.orthonormalBasisOneI.repr
  let pos : V → Plane := fun v => (ε : ℝ) • p (cell v)
  let B : J → Set V := fun j => {v | f.symm (pos v) ∈ parentBlock (centres j) s}
  let U : J → Set Plane := fun j => f '' parentBlock (centres j) s
  have hU : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ U j := by
    intro j v hv
    exact ⟨f.symm (pos v), hv, f.apply_symm_apply (pos v)⟩
  have hsel : ∀ n v j, select n v = some j → v ∈ B j := by
    intro n v j hj
    change f.symm (pos v) ∈ parentBlock (centres j) s
    have hx := (hselect n v j hj).2
    have hb := ball_subset_interior_parentBlock hs.le hx
    exact interior_subset (hb (show f.symm (pos v) ∈ Metric.ball (f.symm (pos v)) s from by
      simpa only [Metric.mem_ball, dist_self] using hs))
  apply active_cellWalk_mem_cthickening_of_local_buffer H hH p hp cell pos B initial select ω
    hpos hunb hadj hε U hU (Metric.ball (f a) (r + 4 * s)) (Metric.ball (f a) R)
    δ hδ
  · intro x hx
    exact closedBall_subset_ball_of_mem_ball hx hmargin
  · exact hmesh
  · exact hsel
  · exact hk
  · exact hl
  · exact hactive
  · intro j hj
    obtain ⟨hout, hin⟩ := hselect n (ω k) j hj
    apply image_parentBlock_subset_ball_of_anchor f hs.le hin
    exact lt_of_le_of_lt (dist_center_le_of_mem_parentBlock hS hout) hr

end BouRabeeGwynne.FiniteConductanceNetwork
end
