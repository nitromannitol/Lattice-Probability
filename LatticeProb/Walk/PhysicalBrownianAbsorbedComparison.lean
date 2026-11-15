import LatticeProb.Walk.PhysicalAbsorbedParentCollars
import LatticeProb.Prob.BrownianAbsorbedCollars
import LatticeProb.Euclidean.ParentBlockAbsorbedComparison

/-! # Comparison of absorbed physical walk and Brownian skeletons -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal ENNReal
open LatticeProb.ParentBlock LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Matching anchors control the paths up to their finite absorbed skeleton
endpoints, including stages where either clock is constant. -/
theorem physical_brownian_absorbed_comparison
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
        parentBlock (centres j) s}) initial select i ω).1 = k i)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J) (β : BrownianPath 2)
    (hbselect : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock a S ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈ closedSquare (centres j) s)
    (hbstart : Complex.orthonormalBasisOneI.repr.symm (z + β 0) ∈ closedSquare (centres j₀) s)
    (hbStop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock (centres j) s))
      z j₀ selector K β).1 = true)
    (hbFinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹' interior (parentBlock (centres j) s))
      z j₀ selector K β).2 ≠ ∞)
    (η : ℝ)
    (hanchors :
      let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
        (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
      let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (parentBlock (centres j) s)
      let Q : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
        (fun i => (brownianSkeletonClock U z j₀ selector (min i K) β).2.toNNReal)
      ∀ n ≤ K + 1, dist
        (Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) (T n)))
        (Complex.orthonormalBasisOneI.repr.symm (z + β (Q n))) ≤ η) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (centres j) s)
    let Q : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => (brownianSkeletonClock U z j₀ selector (min i K) β).2.toNNReal)
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (Complex.orthonormalBasisOneI.repr.symm
        (H.interpolatedWalk p ε (cell ∘ ω) (min t (T (K + 1)))))
        (Complex.orthonormalBasisOneI.repr.symm (z + β (min (φ t) (Q (K + 1))))) ≤
        max ((ε : ℝ) * (2 * δ) + 4 * s) (4 * s + 4 * s) + η +
          max ((ε : ℝ) * (2 * δ) + 4 * s) (4 * s + 4 * s) := by
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
    (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (parentBlock (centres j) s)
  let Q : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
    (fun i => (brownianSkeletonClock U z j₀ selector (min i K) β).2.toNNReal)
  let f : ℝ≥0 → ℂ := fun t =>
    Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) t)
  let g : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + β t)
  obtain ⟨hT0, hTmono, hTstrict, c, hc, hfc⟩ :=
    physical_absorbed_parentBlock_collars H hH p hp cell centres initial select ω
      hpos hunb hadj hε a S s r R δ hS hs hδ hr hmargin houter hinit hselect hmesh K k hclock
  obtain ⟨d, hd, hgc⟩ := brownianSkeletonClock_absorbed_parentBlock_collars
    centres s hs (parentBlock a S) z j₀ selector hbselect K β hbstart hbStop hbFinite
  have hU : ∀ j, IsOpen (U j) := fun _ => isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hstartU : z + β 0 ∈ U j₀ := by
    apply ball_subset_interior_parentBlock hs.le hbstart
    exact Metric.mem_ball_self hs
  have hball : ∀ n x j, selector n x = some j → Metric.ball x s ⊆ U j := by
    intro n x j hj y hy
    apply ball_subset_interior_parentBlock hs.le (hbselect n x j hj).2
    simpa only [Metric.mem_ball, Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq] using hy
  obtain ⟨Q', hQ0', hQmono', hQmatch, hQstrict'⟩ :=
    brownianSkeletonClock_exists_absorbed_comparison_clock U hU z j₀ selector hs hball
      K β hstartU hbStop hbFinite
  have hQeq : ∀ n ≤ K + 1, Q n = Q' n := by
    intro n hn
    cases n with
    | zero => simpa [Q] using hQ0'.symm
    | succ n =>
      have hnK : n ≤ K := by omega
      simpa [Q, min_eq_left hnK] using (hQmatch n hnK).symm
  have hQmono : Monotone Q := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact zero_le
    | succ n =>
      change (brownianSkeletonClock U z j₀ selector (min n K) β).2.toNNReal ≤
        (brownianSkeletonClock U z j₀ selector (min (n + 1) K) β).2.toNNReal
      exact ENNReal.toNNReal_mono
        (brownianSkeletonClock_finite_of_le U z j₀ selector β (min_le_right _ _) hbFinite)
        (brownianSkeletonClock_time_monotone U z j₀ selector β
          (min_le_min_right K (Nat.le_succ n)))
  have hQstrict : ∀ n < K + 1, Q n < Q (K + 1) → Q n < Q (n + 1) := by
    intro n hn hbefore
    rw [hQeq n (by omega), hQeq (K + 1) le_rfl] at hbefore
    rw [hQeq n (by omega), hQeq (n + 1) (by omega)]
    exact hQstrict' n hn hbefore
  have hrad : 0 ≤ (ε : ℝ) * (2 * δ) := mul_nonneg ε.coe_nonneg (by linarith)
  exact exists_orderIso_dist_le_of_parentBlock_collars_terminal_clocks
    f g T Q (K + 1) c d s ((ε : ℝ) * (2 * δ)) s (4 * s) η
    hs.le hrad hs.le (by linarith) hT0 rfl hTmono hQmono hTstrict hQstrict
    hc hd hfc hgc hanchors

end BouRabeeGwynne.FiniteConductanceNetwork
end
