import LatticeProb.Prob.BrownianFiniteDomainSkeleton
import LatticeProb.Prob.ParentBlockDyadicFiniteSelector

/-! # Active Brownian skeletons for dyadic selectors -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne

namespace LatticeProb.ParentBlock

private theorem bounded_closedSquare (c : ℂ) (s : ℝ) :
    Bornology.IsBounded (closedSquare c s) := by
  refine ((Metric.isBounded_Icc (c.re - s / 2) (c.re + s / 2)).reProdIm
    (Metric.isBounded_Icc (c.im - s / 2) (c.im + s / 2))).subset ?_
  intro z hz
  change |z.re - c.re| ≤ s / 2 ∧ |z.im - c.im| ≤ s / 2 at hz
  change z.re ∈ Icc _ _ ∧ z.im ∈ Icc _ _
  obtain ⟨h1, h2⟩ := abs_le.mp hz.1
  obtain ⟨h3, h4⟩ := abs_le.mp hz.2
  constructor <;> constructor <;> linarith

/-- A uniform active-skeleton tail holds for every measurable dyadic selector
with a common positive interior-ball margin. The selector may vary with time. -/
theorem dyadic_selector_activeSkeleton_tail
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentDyadicIndex n))]
    {μ : Measure (BrownianPath 2)} (hμ : IsStandardBrownianLaw μ)
    {Z : Set (Euc 2)} (hZ : Bornology.IsBounded Z)
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : ParentDyadicIndex n,
      ∀ selector : ℕ → Euc 2 → Option (ParentDyadicIndex n),
        (∀ k, Measurable (selector k)) →
        (∀ k x j, selector k x = some j → ball x r ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))) →
        μ {ω | (brownianSkeletonClock
          (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
          z j₀ selector K ω).1 = false} ≤ ENNReal.ofReal η := by
  let U : ParentDyadicIndex n → Set (Euc 2) := fun j =>
    Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
  have hside : 0 ≤ 2 * S / (2 : ℝ) ^ n := by positivity
  have hU : ∀ j, IsOpen (U j) := fun _ =>
    isOpen_interior.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hUb : ∀ j, Bornology.IsBounded (U j) := by
    intro j
    apply (Complex.orthonormalBasisOneI.repr.symm.isometry.antilipschitzWith.isBounded_preimage
      (s := parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)) ?_).subset
      (preimage_mono interior_subset)
    rw [parentBlock_eq hside]
    exact bounded_closedSquare _ _
  exact brownian_finiteDomain_activeSkeleton_tail (by decide) hμ U hU hUb hZ hr hη

end LatticeProb.ParentBlock
