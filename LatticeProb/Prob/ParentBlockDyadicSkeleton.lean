import LatticeProb.Prob.BrownianFiniteDomainSkeleton
import LatticeProb.Prob.ParentBlockDyadicFiniteSelector

/-!
# Brownian skeletons on dyadic parent blocks

A finite dyadic selector yields a uniform active-skeleton tail at a fixed scale.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

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

private theorem bounded_parentBlock_preimage (c : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    Bornology.IsBounded (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c s) := by
  apply Complex.orthonormalBasisOneI.repr.symm.isometry.antilipschitzWith.isBounded_preimage
  rw [parentBlock_eq hs]
  exact bounded_closedSquare c (3 * s)

/-- At a fixed scale the active-skeleton tail is uniform over starts in the outer parent block
and initial dyadic indices, for a measurable selector with a positive ball margin. -/
theorem exists_dyadic_selector_activeSkeleton_tail
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentDyadicIndex n))]
    {μ : Measure (BouRabeeGwynne.BrownianPath 2)}
    (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ) {η : ℝ} (hη : 0 < η) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → Option (ParentDyadicIndex n)) (K : ℕ),
      Measurable f ∧
      (∀ x p, f x = some p →
        Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          closedSquare (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n) ∧
        ball x (2 * S / (2 : ℝ) ^ n) ⊆
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n)))) ∧
      (∀ x, f x = none ↔ Complex.orthonormalBasisOneI.repr.symm x ∉ parentBlock c S) ∧
      ∀ z, Complex.orthonormalBasisOneI.repr.symm z ∈ parentBlock c S →
        ∀ p : ParentDyadicIndex n,
          μ {ω | (BouRabeeGwynne.brownianSkeletonClock
            (fun q => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
              interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n)))
            z p (fun _ => f) K ω).1 = false} ≤ ENNReal.ofReal η := by
  let U : ParentDyadicIndex n → Set (BouRabeeGwynne.Euc 2) := fun p =>
    Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n))
  have hside : 0 < 2 * S / (2 : ℝ) ^ n := by positivity
  have hU : ∀ p, IsOpen (U p) := fun _ =>
    isOpen_interior.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hUb : ∀ p, Bornology.IsBounded (U p) := fun p =>
    (bounded_parentBlock_preimage _ hside.le).subset (preimage_mono interior_subset)
  obtain ⟨f, hf, hsome, hnone⟩ := exists_measurable_finite_dyadic_selector_margin c hS n
  obtain ⟨K, hK⟩ := brownian_finiteDomain_activeSkeleton_tail (by decide) hμ U hU hUb
    (bounded_parentBlock_preimage c hS.le) hside hη
  refine ⟨f, K, hf, hsome, hnone, ?_⟩
  intro z hz p
  exact hK z hz p (fun _ => f) (fun _ => hf) (fun _ x q h => (hsome x q h).2.2)

end LatticeProb.ParentBlock
