import LatticeProb.Walk.CollarReferenceBallEndpoint
import LatticeProb.Prob.NetworkBackwardCellErrors

/-! # Backward endpoint cells from collar estimates -/

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Collar reference estimates and exit oscillation yield uniform backward-cell
endpoint bounds for the same sequence of finite networks. -/
theorem exists_network_backward_cells_of_collar_reference
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J]
    (U I K : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (hK : ∀ j, IsCompact (K j)) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (hcollar : ∀ j x, x ∈ I j → ∀ y, dist y x < r j → y ∈ K j)
    (center : J → Euc d) (R : J → ℝ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (p q : ∀ n, V n → Euc d)
    (hp : ∀ n, Measurable (p n))
    (A : ∀ n, Set (V n)) (hA : ∀ n v, v ∈ A n → 0 < (N n).totalConductance v)
    (hpA : ∀ n j, p n ⁻¹' ball (center j) (R j) ⊆ A n)
    (hqA : ∀ n j, q n ⁻¹' ball (center j) (R j) ⊆ A n)
    (ν : ∀ j, K j → ProbabilityMeasure (Euc d)) (hν : ∀ j, Continuous (ν j))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v, dist (p n v) (q n v) < δ)
    (href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : p n v ∈ K j,
      levyProkhorovDist
        (((N n).discreteHarmonicMeasure (p n ⁻¹' ball (center j) (R j))
          (fun w hw => hA n w (hpA n j hw)) v).map (p n))
        (ν j ⟨p n v, hv⟩ : Measure (Euc d)) < ε)
    (hosc : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      q n v ∈ I j → ∃ (δ η : ℝ) (E : Set (ℕ → V n)),
        (∀ w, dist (p n w) (q n w) ≤ δ) ∧ η + δ < ε / 4 ∧
        (N n).trajectoryLaw (A n) (hA n) v E ≤ (ENNReal.ofReal (ε / 4)) ∧
        (∀ᵐ ω ∂(N n).trajectoryLaw (A n) (hA n) v, ω ∉ E →
          exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω ≠ ⊤ ∧
          ∀ i ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (R j - δ)) ω).untopD 0)
              ((exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω).untopD 0),
            ∀ k ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (R j - δ)) ω).untopD 0)
                ((exitTime (p n ⁻¹' ball (center j) (R j + δ)) ω).untopD 0),
              dist (p n (ω i)) (p n (ω k)) ≤ η))
    (C : Set (Euc d)) (hC : IsCompact C) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, C ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, Bornology.IsBounded (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i : Fin L, ∀ k, ∀ x ∈ E i.castSucc k, ∀ y ∈ E i.castSucc k,
        dist x y ≤ δ i.succ) ∧
      (∀ i j k z, z ∈ I j →
        ((stoppedBrownianLaw (U j) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (frontier (E i k)) = 0) ∧
      ∀ᶠ n in atTop, ∀ (choice : ∀ i, Fin (m i) → Option J),
        (∀ i k j, choice i k = some j → E i k ⊆ I j) →
        ∀ (initial : J) (v₀ : V n) (z : Euc d),
        q n v₀ ∈ I initial → z ∈ I initial →
        dist (q n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun t => m (ix t)
        let E' : ∀ t, Fin (m' t) → Set (Euc d) := fun t => E (ix t)
        let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
        (∀ t < L, ∀ k j, choice' t k = some j →
          ∀ v : V n, q n v ∈ E' t k → ∀ y ∈ E' t k, ∀ l,
            |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center j) (R j)) (fun w hw => hA n w (hqA n j hw)) v).map (q n) (E' (t + 1) l)).toReal -
              (((stoppedBrownianLaw (U j) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (t + 1) l)).toReal| ≤
                b / (m' (t + 1) + 1)) ∧
        (∀ k, |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center initial) (R initial)) (fun w hw => hA n w (hqA n initial hw)) v₀).map (q n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (U initial) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) := by
  let νI : ∀ j, I j → ProbabilityMeasure (Euc d) := fun j x =>
    ν j ⟨x.1, hcollar j _ x.2 _ (by simpa using hr j)⟩
  have hνI : ∀ j, Continuous (νI j) := by
    intro j
    apply (hν j).comp
    exact continuous_subtype_val.subtype_mk _
  have hνIlaw : ∀ j x, (νI j x : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) x.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint := by
    intro j x
    exact hνlaw j _
  have hLP := uniform_ball_exit_law_of_collar_reference I K hK r hr hcollar center R
    V N p q hp A hA hpA hqA ν hν hclose href hosc
  exact exists_network_backward_cells_with_errors hd U I hU hUb hI hIU ρ hρ V N q
    (fun n => (measurable_of_countable _)) (fun n j => q n ⁻¹' ball (center j) (R j))
    (fun n j w hw => hA n w (hqA n j hw)) νI hνIlaw hνI hLP C hC a b ha hb L

end LatticeProb
end
