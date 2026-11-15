import LatticeProb.Walk.PhysicalInitialParentCollar
import LatticeProb.Walk.PhysicalSelectedParentCollar
import LatticeProb.Walk.CellWalkAbsorbedClock
import LatticeProb.Euclidean.ParentBlockPlateauCollars

/-! # Parent-block collars for absorbed physical walk clocks -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Every stage of a finite physical walk skeleton has a parent-block collar,
including stages on which its clock is constant. -/
theorem physical_absorbed_parentBlock_collars
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
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        closedSquare (centres j) s)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane),
      (ε : ℝ) • z ∈ Metric.ball (Complex.orthonormalBasisOneI.repr a) R) →
      Metric.diam (C.1 : Set Plane) ≤ δ)
    (K : ℕ) (k : ℕ → ℕ)
    (hclock : ∀ i ≤ K, (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      (fun j => {v | Complex.orthonormalBasisOneI.repr.symm ((ε : ℝ) • p (cell v)) ∈
        parentBlock (centres j) s}) initial select i ω).1 = k i) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
    let f : ℝ≥0 → ℂ := fun t =>
      Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t)
    T 0 = 0 ∧ Monotone T ∧
      (∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1)) ∧
      ∃ c : ℕ → ℂ, (∀ n < K + 1, f (T n) ∈ closedSquare (c n) s) ∧
        ∀ n < K + 1, ∀ t ∈ Icc (T n) (T (n + 1)),
          f t ∈ Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock (c n) s) := by
  let pos : V → Plane := fun v => (ε : ℝ) • p (cell v)
  let B : J → Set V := fun j => {v |
    Complex.orthonormalBasisOneI.repr.symm (pos v) ∈ parentBlock (centres j) s}
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
    (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
  let f : ℝ≥0 → ℂ := fun t =>
    Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t)
  have square_mem {j : J} {v : V}
      (hv : Complex.orthonormalBasisOneI.repr.symm (pos v) ∈ closedSquare (centres j) s) :
      v ∈ B j := by
    apply interior_subset (ball_subset_interior_parentBlock hs.le hv (Metric.mem_ball_self hs))
  have hb0 : ω 0 ∈ B initial := square_mem hinit
  have hbsel : ∀ n v j, select n v = some j → v ∈ B j := by
    intro n v j hj
    exact square_mem (hselect n v j hj).2
  obtain ⟨hT0, hmono, hmatch, hstrict, _, _⟩ :=
    actualWalkStage_physical_absorbed_clock H p cell pos B initial select ω K k
      hpos hunb hε hclock hb0 hbsel
  have hstages : ∀ n < K + 1, T n < T (n + 1) → ∃ c : ℂ,
      f (T n) ∈ closedSquare c s ∧ ∀ t ∈ Icc (T n) (T (n + 1)),
        f t ∈ Metric.cthickening ((ε : ℝ) * (2 * δ)) (parentBlock c s) := by
    intro n hn ht
    cases n with
    | zero =>
      refine ⟨centres initial, ?_⟩
      have h := physical_initial_parentBlock_collar H hH p hp cell centres initial select ω
        hpos hunb hadj hε a S s r R δ hS hs hδ hr hmargin houter hinit hmesh
        (k 0) (hclock 0 (Nat.zero_le K))
      constructor
      · change Complex.orthonormalBasisOneI.repr.symm
          (H.interpolatedWalk p ε (cell ∘ ω) 0) ∈ closedSquare (centres initial) s
        exact h.1
      · change ∀ t ∈ Icc 0 (scaledJumpTime H (cell ∘ ω) hpos ε (k (min 0 K))),
          Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t) ∈ _
        simpa only [Nat.zero_min] using h.2
    | succ i =>
      have hi : i < K := by omega
      have hTi : T (i + 1) = scaledJumpTime H (cell ∘ ω) hpos ε (k i) := hmatch i (by omega)
      have hTi' : T (i + 1 + 1) = scaledJumpTime H (cell ∘ ω) hpos ε (k (i + 1)) :=
        hmatch (i + 1) (by omega)
      rw [hTi, hTi'] at ht
      obtain ⟨j, _, hj, hc⟩ := physical_selected_parentBlock_collar_of_clock_lt
        H hH p hp cell centres initial select ω hpos hunb hadj hε a S s r R δ
        hS hs hδ hr hmargin hselect hmesh i (k i) (k (i + 1))
        (hclock i (by omega)) (hclock (i + 1) (by omega)) ht
      refine ⟨centres j, ?_, ?_⟩
      · simpa only [Nat.succ_eq_add_one, hTi] using hj
      · simpa only [Nat.succ_eq_add_one, hTi, hTi'] using hc
  have hrad : 0 ≤ (ε : ℝ) * (2 * δ) := mul_nonneg ε.coe_nonneg (by linarith)
  exact ⟨hT0, hmono, hstrict,
    exists_parentBlock_collars_of_strict_stages f T (K + 1) s _ hs.le hrad hmono hstages⟩

end BouRabeeGwynne.FiniteConductanceNetwork
end
