import LatticeProb.Prob.BrownianAbsorbedComparisonClock
import LatticeProb.Prob.BrownianParentBlockStoppedKnots

/-! # Parent-block collars for absorbed Brownian skeletons -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Every segment of a finite absorbed parent-block skeleton stays in a
collar centered at its initial point, including the constant-clock segments. -/
theorem brownianSkeletonClock_absorbed_parentBlock_collars {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      LatticeProb.ParentBlock.closedSquare (centres j₀) s)
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector (min m K) ω).2.toNNReal)
    let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    ∃ c : ℕ → ℂ, (∀ n < K + 1, f (T n) ∈ LatticeProb.ParentBlock.closedSquare (c n) s) ∧
      ∀ n < K + 1, ∀ t ∈ Icc (T n) (T (n + 1)),
        f t ∈ Metric.cthickening (4 * s) (LatticeProb.ParentBlock.parentBlock (c n) s) := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
    (fun m => (brownianSkeletonClock U z j₀ selector (min m K) ω).2.toNNReal)
  let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
  have hU : ∀ j, IsOpen (U j) := fun j => isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hstartU : z + ω 0 ∈ U j₀ := by
    apply LatticeProb.ParentBlock.ball_subset_interior_parentBlock hs.le hstart
    exact mem_ball_self hs
  have hmargin : ∀ n x j, selector n x = some j → Metric.ball x s ⊆ U j := by
    intro n x j hj y hy
    apply LatticeProb.ParentBlock.ball_subset_interior_parentBlock hs.le (hselector n x j hj).2
    simpa only [Metric.mem_ball, Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq] using hy
  obtain ⟨T', hT0, hmono, hmatch, hstrict⟩ :=
    brownianSkeletonClock_exists_absorbed_comparison_clock U hU z j₀ selector hs hmargin
      K ω hstartU hstop hfinite
  have hT : ∀ n ≤ K + 1, T n = T' n := by
    intro n hn
    cases n with
    | zero => simpa [T] using hT0.symm
    | succ n =>
      have hnK : n ≤ K := by omega
      simpa [T, min_eq_left hnK] using (hmatch n hnK).symm
  obtain ⟨m, hm, ha, _, heq, htime⟩ :=
    brownianSkeletonClock_exists_last_active U z j₀ selector ω K hstop
  have hterminal : T (m + 1) = T (K + 1) := by
    simp only [T, min_eq_left hm.le, min_self]
    rw [heq, htime]
  have hosc : ∀ n < K + 1, ∀ t ∈ Icc (T n) (T (n + 1)),
      dist (f t) (f (T n)) ≤ 4 * s := by
    intro n hn t ht
    by_cases hnm : n < m + 1
    · cases n with
      | zero =>
        have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω (Nat.zero_le K) hfinite
        have hg := initial_parentBlock_exit_geometry (centres j₀) s hs z ω hstart hf
        simpa [T, f, dist_eq_norm, U] using hg.2 t ht
      | succ n =>
        have hn' : n < m := by omega
        have hactive := brownianSkeletonClock_active_of_le U z j₀ selector ω (Nat.succ_le_of_lt hn') ha
        have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω (Nat.succ_le_of_lt hn')
          (brownianSkeletonClock_finite_of_le U z j₀ selector ω hm.le hfinite)
        obtain ⟨j, hj, ho, hsq, he, hg⟩ :=
          brownianSkeletonClock_active_parentBlock_step centres s hs outer z j₀ selector hselector n ω hactive hf
        have hnK : n ≤ K := by omega
        have hnK' : n + 1 ≤ K := by omega
        have ht' : t ∈ Icc
            (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal
            (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal := by
          simpa [T, min_eq_left hnK, min_eq_left hnK', Nat.succ_eq_add_one] using ht
        simpa [T, f, dist_eq_norm, U, min_eq_left hnK, Nat.succ_eq_add_one] using hg t ht'
    · have hnm' : m + 1 ≤ n := Nat.le_of_not_gt hnm
      have hnk : n + 1 ≤ K + 1 := by omega
      have h1 : T (m + 1) ≤ T n := by
        simpa only [← hT (m + 1) (by omega), ← hT n (by omega)] using hmono hnm'
      have h2 : T (n + 1) ≤ T (K + 1) := by
        simpa only [← hT (n + 1) hnk, ← hT (K + 1) le_rfl] using hmono hnk
      have he : T n = T (n + 1) := le_antisymm
        (by simpa only [← hT n (by omega), ← hT (n + 1) hnk] using hmono (Nat.le_succ n))
        (by rw [hterminal] at h1; exact h2.trans h1)
      have ht' : t = T n := le_antisymm (he ▸ ht.2) ht.1
      rw [ht', dist_self]
      positivity
  refine ⟨fun n => f (T n), ?_, ?_⟩
  · intro n hn
    change f (T n) ∈ LatticeProb.ParentBlock.closedSquare (f (T n)) s
    simp only [LatticeProb.ParentBlock.closedSquare, mem_ofPred_eq, sub_self, abs_zero]
    constructor <;> positivity
  · intro n hn t ht
    apply Metric.mem_cthickening_of_dist_le _ (f (T n)) _ _ ?_ (hosc n hn t ht)
    rw [LatticeProb.ParentBlock.parentBlock_eq hs.le]
    simp only [LatticeProb.ParentBlock.closedSquare, mem_ofPred_eq, sub_self, abs_zero]
    constructor <;> positivity

end BouRabeeGwynne
