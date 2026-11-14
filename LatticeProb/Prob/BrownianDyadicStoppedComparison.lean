import LatticeProb.Prob.BrownianDyadicOuterExitKnots
import LatticeProb.Topology.AsymmetricKnotComparison

/-!
# Comparison with a stopped dyadic Brownian skeleton

The comparison uses explicit bounds on the anchors after either skeleton has
stopped. The two stopping indices may differ.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Compare a stopped dyadic Brownian path with a second stopped path whose
finite skeleton has uniformly close padded anchors. -/
theorem brownianSkeletonClock_dyadic_outerExit_compare
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
    (f : Euc 2 → Option (LatticeProb.ParentBlock.ParentDyadicIndex n))
    (hsome : ∀ x j, f x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
    (hnone : ∀ x, f x = none →
      Complex.orthonormalBasisOneI.repr.symm x ∉ LatticeProb.ParentBlock.parentBlock c S)
    (z : Euc 2) (j₀ : LatticeProb.ParentBlock.ParentDyadicIndex n)
    (hz : f z = some j₀) (K : ℕ) (ω : BrownianPath 2) (hzero : ω 0 = 0)
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
      z j₀ (fun _ => f) K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
      z j₀ (fun _ => f) K ω).2 ≠ ∞)
    (g : ℝ≥0 → ℂ) (σ : ℕ → ℝ≥0) (M : ℕ) (δ : ℝ)
    (hσ0 : σ 0 = 0) (hσ : ∀ k < M, σ k < σ (k + 1))
    (hg : ∀ k < M, ∀ t ∈ Ico (σ k) (σ (k + 1)),
      dist (g t) (g (σ k)) ≤ 4 * (2 * S / (2 : ℝ) ^ n))
    (hgtail : ∀ t, σ M ≤ t → g t = g (σ M))
    (hanchors :
      let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
      let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
        (fun m => (brownianSkeletonClock U z j₀ (fun _ => f) m ω).2.toNNReal)
      let b : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
      let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        LatticeProb.ParentBlock.parentBlock c S) z ω).toNNReal
      ∀ N ≤ K, min (T N) τ = τ →
        (∀ k < N, min (T k) τ < min (T (k + 1)) τ) → ∀ k ≤ max K M,
        dist (b (min (T (min k N)) τ)) (g (σ (min k M))) ≤ δ) :
    let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock c S) z ω).toNNReal
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (Complex.orthonormalBasisOneI.repr.symm (z + ω (min t τ))) (g (φ t)) ≤
        4 * (2 * S / (2 : ℝ) ^ n) + δ + 4 * (2 * S / (2 : ℝ) ^ n) := by
  dsimp only at hanchors ⊢
  obtain ⟨N, hNK, h0, hN, hstrict, hosc, htail⟩ :=
    brownianSkeletonClock_dyadic_outerExit_stopped_knots c hS n f hsome hnone
      z j₀ hz K ω hzero hstop hfinite
  let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock
      (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
  let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
    (fun m => (brownianSkeletonClock U z j₀ (fun _ => f) m ω).2.toNNReal)
  let b : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
  let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    LatticeProb.ParentBlock.parentBlock c S) z ω).toNNReal
  let a : ℝ := 4 * (2 * S / (2 : ℝ) ^ n)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨φ, _, hφ⟩ := LatticeProb.KnotReparam.exists_orderIso_dist_le_of_asymmetric_finite_knots
    (N := N) (M := M) (K := max K M) (Nat.le_trans hNK (le_max_left _ _))
    (le_max_right _ _) hstrict hσ h0 hσ0
    (p := fun k => b (min (T k) τ)) (q := fun k => g (σ k))
    (hanchors N hNK hN hstrict) hosc hg
    (fun t ht => by rw [htail t ht, ← hN, dist_self]; exact ha)
    (fun t ht => by rw [hgtail t ht, dist_self]; exact ha)
  exact ⟨φ, hφ⟩

end BouRabeeGwynne
