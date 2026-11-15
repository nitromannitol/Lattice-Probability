import LatticeProb.Prob.BrownianInteriorClockStrict
import LatticeProb.Prob.BrownianParentBlockInteriorGeometry
import LatticeProb.Prob.BrownianParentBlockInteriorActiveStep
import LatticeProb.Topology.StoppedKnotPackage

/-!
# Stopped knots for parent-block excursions

Finite active parent-block excursions give strictly increasing knots up to any
reached cutoff, with controlled oscillation of the stopped path.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Clip the initial and subsequent active parent-block excursions at a reached cutoff. -/
theorem brownianSkeletonClock_interior_parentBlock_stopped_knots {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      interior (LatticeProb.ParentBlock.parentBlock (centres j₀) s))
    (hactive : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞)
    (a : ℝ≥0)
    (hreach : a ≤ (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2.toNNReal) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
    let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    ∃ N ≤ K + 1, min (T 0) a = 0 ∧ min (T N) a = a ∧
      (∀ n < N, min (T n) a < min (T (n + 1)) a) ∧
      (∀ n < N, ∀ t ∈ Ico (min (T n) a) (min (T (n + 1)) a),
        dist (f (min t a)) (f (min (T n) a)) ≤ 6 * s) ∧
      (∀ t, min (T N) a ≤ t → f (min t a) = f a) := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
    (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
  let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
  have hU : ∀ j, IsOpen (U j) := fun j => isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hstartU : z + ω 0 ∈ U j₀ := hstart
  have hselect : ∀ n x j, selector n x = some j → x ∈ U j := by
    intro n x j hj
    exact (hselector n x j hj).2
  have hstrict : ∀ n < K + 1, T n < a → T n < T (n + 1) := by
    intro n hn _
    exact brownianSkeletonClock_prepend_zero_lt_succ_of_mem U hU z j₀ selector hselect
      K ω hstartU hactive hfinite n hn
  have hosc : ∀ n < K + 1, ∀ t ∈ Icc (T n) (T (n + 1)),
      dist (f t) (f (T n)) ≤ 6 * s := by
    intro n hn t ht
    cases n with
    | zero =>
      have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω (Nat.zero_le K) hfinite
      have hg := interior_parentBlock_exit_geometry (centres j₀) s hs z ω hstart hf
      simpa [T, f, dist_eq_norm, U] using hg.2 t ht
    | succ n =>
      have hn' : n < K := by omega
      have ha := brownianSkeletonClock_active_of_le U z j₀ selector ω (Nat.succ_le_of_lt hn') hactive
      have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω (Nat.succ_le_of_lt hn') hfinite
      obtain ⟨j, hj, ho, hsq, he, hg⟩ :=
        brownianSkeletonClock_active_parentBlock_interior_step centres s hs outer z j₀ selector hselector n ω ha hf
      simpa [T, f, dist_eq_norm, U, Nat.succ_eq_add_one] using hg t ht
  exact LatticeProb.KnotReparam.exists_stopped_knot_package f T a (K + 1) (6 * s)
    rfl hreach hstrict hosc

end BouRabeeGwynne
