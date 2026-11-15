import LatticeProb.Walk.SelectedCellStageCollar
import LatticeProb.Walk.CellConfigLocalDiameter

/-! # Local-mesh collars for selected cell-walk stages -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS Preorder
open scoped NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- A local cell-mesh bound and a buffer control the initial stage, including
its final edge. -/
theorem initial_cellWalk_mem_cthickening_of_local_mesh
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (cell : V → H.cells)
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (U : J → Set Plane)
    (hU : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ U j)
    (A W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ A)
    (hbuffer : ∀ x ∈ A, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (l : ℕ) (hl : (actualWalkStage pos B initial select 0 ω).1 = l)
    (hinit : ω 0 ∈ B initial) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l) :
    H.interpolatedWalk p ε (cell ∘ ω) t ∈
      Metric.cthickening ((ε : ℝ) * (2 * δ)) (U initial) := by
  apply initial_cellWalk_mem_cthickening H hH p hp cell pos B initial select ω
    hpos hunb hadj hε U hU l hl hinit (2 * δ)
  · intro m hm
    apply LatticeProb.CellConfigInterpolation.diam_add_le_of_adj_of_scaled_local_bound
      H hH p hp A W (ε : ℝ) δ ε.coe_nonneg hδ hbuffer hmesh
    · exact hA initial (ω m)
        (actualWalkStage_zero_mem_before_clock pos B initial select ω l m hl hm)
    · exact hadj m
  · exact ht

/-- A local cell-mesh bound and a buffer control each active selected stage,
including its final edge. -/
theorem active_cellWalk_mem_cthickening_of_local_mesh
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (cell : V → H.cells)
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    (hadj : ∀ n, H.Adj (cell (ω n)) (cell (ω (n + 1))))
    {ε : ℝ≥0} (hε : 0 < ε) (U : J → Set Plane)
    (hU : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ U j)
    (A W : Set Plane) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ j v, v ∈ B j → (ε : ℝ) • p (cell v) ∈ A)
    (hbuffer : ∀ x ∈ A, Metric.closedBall x ((ε : ℝ) * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), (ε : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (hselect : ∀ n v j, select n v = some j → v ∈ B j)
    (n k l : ℕ) (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l)
    (hactive : (actualWalkStage pos B initial select (n + 1) ω).2.1 = false) :
    ∃ j, select n (ω k) = some j ∧ ∀ t : ℝ≥0,
      (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) k ≤ (t : ℝ) →
      (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l →
      H.interpolatedWalk p ε (cell ∘ ω) t ∈
        Metric.cthickening ((ε : ℝ) * (2 * δ)) (U j) := by
  obtain ⟨j, _, hin⟩ := actualWalkStage_active_pre_exit pos B initial select ω n k l hk hl hactive
  apply active_cellWalk_mem_cthickening H hH p hp cell pos B initial select ω
    hpos hunb hadj hε U hU hselect n k l hk hl hactive (2 * δ)
  intro m hkm hml
  apply LatticeProb.CellConfigInterpolation.diam_add_le_of_adj_of_scaled_local_bound
    H hH p hp A W (ε : ℝ) δ ε.coe_nonneg hδ hbuffer hmesh
  · exact hA j (ω m) (hin m hkm hml)
  · exact hadj m

end BouRabeeGwynne.FiniteConductanceNetwork
end
