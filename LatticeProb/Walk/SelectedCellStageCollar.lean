import LatticeProb.Walk.CellConfigStageCollar
import LatticeProb.Walk.ActualWalkStagePreExit
import LatticeProb.Walk.WalkSelectedClockStrict

/-! # Cell-walk collars for selected finite stages -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS Preorder
open scoped NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- The interpolated cell walk stays in a collar of the initial selected set
up to its finite exit clock, including the final edge. -/
theorem initial_cellWalk_mem_cthickening
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
    (l : ℕ) (hl : (actualWalkStage pos B initial select 0 ω).1 = l)
    (hinit : ω 0 ∈ B initial) (d : ℝ)
    (hd : ∀ m, m < l → Metric.diam ((cell (ω m)).1 : Set Plane) +
      Metric.diam ((cell (ω (m + 1))).1 : Set Plane) ≤ d)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l) :
    H.interpolatedWalk p ε (cell ∘ ω) t ∈ Metric.cthickening ((ε : ℝ) * d) (U initial) := by
  have hlpos : 0 < l := by
    have h := exitTime_pos_of_mem hinit
    change 0 < (actualWalkStage pos B initial select 0 ω).1 at h
    rw [hl] at h
    exact WithTop.coe_lt_coe.mp h
  apply LatticeProb.CellConfigInterpolation.interpolatedWalk_mem_cthickening_between_jumps
    H hH p hp (cell ∘ ω) hpos hunb hadj hε (U initial) 0 l hlpos d
  · intro m _ hm
    exact hU initial (ω m) (actualWalkStage_zero_mem_before_clock pos B initial select ω l m hl hm)
  · intro m _ hm
    exact hd m hm
  · rw [H.jumpTime_zero, mul_zero]
    exact t.coe_nonneg
  · exact ht

/-- A finite active selected stage stays in a collar of its selected set,
including the final edge, when the selector contains its starting vertex. -/
theorem active_cellWalk_mem_cthickening
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
    (hselect : ∀ n v j, select n v = some j → v ∈ B j)
    (n k l : ℕ) (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l)
    (hactive : (actualWalkStage pos B initial select (n + 1) ω).2.1 = false)
    (d : ℝ) (hd : ∀ m, k ≤ m → m < l →
      Metric.diam ((cell (ω m)).1 : Set Plane) +
      Metric.diam ((cell (ω (m + 1))).1 : Set Plane) ≤ d) :
    ∃ j, select n (ω k) = some j ∧ ∀ t : ℝ≥0,
      (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) k ≤ (t : ℝ) →
      (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime (cell ∘ ω) l →
      H.interpolatedWalk p ε (cell ∘ ω) t ∈ Metric.cthickening ((ε : ℝ) * d) (U j) := by
  obtain ⟨j, hj, hin⟩ := actualWalkStage_active_pre_exit pos B initial select ω n k l hk hl hactive
  have hkl := actualWalkStage_active_clock_lt_of_select_mem pos B initial select ω n k l
    hselect hk hl hactive
  refine ⟨j, hj, ?_⟩
  intro t htlo hthi
  apply LatticeProb.CellConfigInterpolation.interpolatedWalk_mem_cthickening_between_jumps
    H hH p hp (cell ∘ ω) hpos hunb hadj hε (U j) k l hkl d
  · intro m hkm hml
    exact hU j (ω m) (hin m hkm hml)
  · exact hd
  · exact htlo
  · exact hthi

end BouRabeeGwynne.FiniteConductanceNetwork
end
