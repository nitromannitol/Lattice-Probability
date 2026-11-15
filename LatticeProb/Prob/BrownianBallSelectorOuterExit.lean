import LatticeProb.Prob.BrownianBallSelectorNeighborhood
import LatticeProb.Prob.BrownianSkeletonOuterExitTail

/-! # Brownian ball selector couplings -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- One dyadic selector controls endpoint coupling failure and the time needed
for the Brownian skeleton to reach the first exit of any smaller outer set. -/
theorem exists_brownian_ball_dyadic_selector_coupling_and_outerExit
    {J : Type*} [Fintype J]
    (center : J → Euc 2) (radius : J → ℝ)
    (c : ℂ) {S : ℝ} (hS : 0 < S)
    (hcenter : ∀ j, Complex.orthonormalBasisOneI.repr.symm (center j) ∈ closedSquare c S)
    (hradius : ∀ j, radius j ≤ S)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (x : ∀ j, P j → Euc 2) (hx : ∀ j z, x j z ∈ ball (center j) (radius j))
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc 2))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc 2))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc 2)) =
      (stoppedBrownianLaw (ball (center j) (radius j)) (x j z) ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (ν j (p j n v) : Measure (Euc 2)) < ε)
    {Z : Set (Euc 2)} (hZ : Bornology.IsBounded Z)
    (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentDyadicIndex n))] :
    ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S) ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < (2 * S / (2 : ℝ) ^ n) / 2) ∧
      (∀ j i z, (ν j z : Measure (Euc 2)) (frontier (E i)) = 0) ∧
      (∀ j z q, (ν j z : Measure (Euc 2))
        (frontier (cellSelector E choice ⁻¹' {q})) = 0) ∧
      Measurable (cellSelector E choice) ∧
      (∀ y ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S),
        cellSelector E choice y ≠ none) ∧
      (∀ y q, cellSelector E choice y = some q →
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n))) ∧
      (∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : ParentDyadicIndex n,
        ∀ outer : Set (Euc 2),
        outer ⊆ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S) →
        ρ {ω | (brownianSkeletonClock
          (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
          z j₀ (fun _ => cellSelector E choice) K ω).2 <
            continuousExitTime outer z ω} ≤ ENNReal.ofReal η) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ →
          ∃ π : Measure (Euc 2 × Euc 2), IsProbabilityMeasure π ∧
            π.fst = (μ j k v : Measure (Euc 2)) ∧
            π.snd = (ν j z : Measure (Euc 2)) ∧
            π {q | ¬ ∃ i, cellSelector E choice q.1 = some i ∧
              cellSelector E choice q.2 = some i ∧
              q.1 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
                interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n))) ∧
              q.2 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
                interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n)))} ≤
              ENNReal.ofReal ε := by
  obtain ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, hcoupling⟩ :=
    exists_brownian_ball_dyadic_selector_common_neighborhood_coupling center radius c hS
      hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n
  refine ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, ?_, hcoupling⟩
  intro η hη
  let U : ParentDyadicIndex n → Set (Euc 2) := fun j =>
    Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
  have hU : ∀ j, IsOpen (U j) := fun _ =>
    isOpen_interior.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hUb : ∀ j, Bornology.IsBounded (U j) := by
    intro j
    apply (Complex.orthonormalBasisOneI.repr.symm.isometry.antilipschitzWith.isBounded_preimage
      (s := parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)) ?_).subset
      (preimage_mono interior_subset)
    rw [parentBlock_eq (by positivity)]
    let a := parentDyadicCentre c S n j
    let t := 3 * (2 * S / (2 : ℝ) ^ n)
    refine ((Metric.isBounded_Icc (a.re - t / 2) (a.re + t / 2)).reProdIm
      (Metric.isBounded_Icc (a.im - t / 2) (a.im + t / 2))).subset ?_
    intro w hw
    change |w.re - a.re| ≤ t / 2 ∧ |w.im - a.im| ≤ t / 2 at hw
    change w.re ∈ Icc _ _ ∧ w.im ∈ Icc _ _
    obtain ⟨h1, h2⟩ := abs_le.mp hw.1
    obtain ⟨h3, h4⟩ := abs_le.mp hw.2
    constructor <;> constructor <;> linarith
  have hr : 0 < (2 * S / (2 : ℝ) ^ n) / 2 := by positivity
  obtain ⟨K, hK⟩ := brownian_finiteDomain_outerExit_skeleton_tail
    (by decide) hρ U hU hUb hZ hr hη
  refine ⟨K, ?_⟩
  intro z hz j₀ outer houter
  exact hK z hz j₀ (fun _ => cellSelector E choice) (fun _ => hmeas)
    (fun _ => hmargin) outer (fun _ x hx => hactive x (houter hx))

end LatticeProb.ParentBlock
