import LatticeProb.Walk.CollarReferenceBackwardCells
import LatticeProb.Prob.NetworkBallSelectorDiameter

/-! # Ball selectors from collar reference estimates -/

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal Topology

namespace LatticeProb

local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

/-- On a fixed network sequence, collar reference estimates provide selectors
and initial and successive endpoint-cell errors on a common eventual tail. -/
theorem exists_collar_reference_ball_selectors
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J] (center : J → Euc d)
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U I K : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (hK : ∀ j, IsCompact (K j)) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (hcollar : ∀ j x, x ∈ I j → ∀ y, dist y x < r j → y ∈ K j)
    (R : J → ℝ)
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
    (C D : Set (Euc d)) (hC : IsCompact C) (hDC : D ⊆ C)
    (s : ℝ) (hs : 0 < s)
    (hcover : ∀ x ∈ D, ∃ j : J, x ∈ ball (center j) (s / 4))
    (hinner : ∀ j : J, ball (center j) (s / 2) ⊆ I j)
    (hR : ∀ j : J, s ≤ R j)
    (hUball : ∀ j : J, U j = ball (center j) (R j))
    (hIball : ∀ j : J, I j ⊆ ball (center j) (R j))
    (hballC : ∀ j : J, closure (ball (center j) (R j)) ⊆ C)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ) (choice : ∀ i, Fin (m i) → Option J),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, C ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ I j) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ ball (center j) (R j)) ∧
      (∀ i j, closure (ball (center j) (R j)) ⊆ ⋃ k, E i k) ∧
      (∀ i, Measurable (cellSelector (E i) (choice i))) ∧
      (∀ i x, x ∈ D → cellSelector (E i) (choice i) x ≠ none) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (s / 2) ⊆ ball (center j) (R j)) ∧
      ∀ᶠ n in atTop, ∀ (initial : J) (v₀ : V n) (z : Euc d),
        q n v₀ ∈ I initial → z ∈ I initial →
        dist (q n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun t => m (ix t)
        let E' : ∀ t, Fin (m' t) → Set (Euc d) := fun t => E (ix t)
        let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
        (∀ t < L, ∀ k j, choice' t k = some j →
          ∀ v : V n, q n v ∈ E' t k → ∀ y ∈ E' t k, ∀ l,
            |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center j) (R j)) (fun w hw => hA n w (hqA n j hw)) v).map (q n) (E' (t + 1) l)).toReal -
              (((stoppedBrownianLaw (ball (center j) (R j)) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (t + 1) l)).toReal| ≤
                b / (m' (t + 1) + 1)) ∧
        (∀ k, |(((N n).discreteHarmonicMeasure (q n ⁻¹' ball (center initial) (R initial)) (fun w hw => hA n w (hqA n initial hw)) v₀).map (q n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (ball (center initial) (R initial)) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) := by
  have hmin : 0 < min a (s / 4) := lt_min ha (by positivity)
  obtain ⟨m, E, δ, hδ, hdisj, hcov, hmeas, hbounded, hdiam, hback, hnull, herror⟩ :=
    exists_network_backward_cells_of_collar_reference hd U I K hU hUb hI hIU ρ hρ hK r hr hcollar
      center R V N p q hp A hA hpA hqA ν hν hνlaw hclose href hosc
      C hC (min a (s / 4)) b hmin hb L
  have hex (i : Fin (L + 1)) : ∃ ch : Fin (m i) → Option J,
      (∀ k, ch k = none ↔ E i k ∩ D = ∅) ∧
      ∀ k j, ch k = some j → E i k ⊆ ball (center j) (s / 2) := by
    classical
    have he (k : Fin (m i)) (hk : (E i k ∩ D).Nonempty) :
        ∃ j : J, E i k ⊆ ball (center j) (s / 2) := by
      obtain ⟨x, hx, hxD⟩ := hk
      obtain ⟨j, hj⟩ := hcover x hxD
      refine ⟨j, ?_⟩
      intro y hy
      change dist y (center j) < s / 2
      have hxy := (hdiam i k y hy x hx).trans (min_le_right _ _)
      calc
        dist y (center j) ≤ dist y x + dist x (center j) := dist_triangle _ _ _
        _ < s / 4 + s / 4 := add_lt_add_of_le_of_lt hxy hj
        _ = s / 2 := by ring
    let ch : Fin (m i) → Option J := fun k =>
      if hk : (E i k ∩ D).Nonempty then some (Classical.choose (he k hk)) else none
    refine ⟨ch, ?_, ?_⟩
    · intro k
      by_cases hk : (E i k ∩ D).Nonempty
      · simp [ch, hk, Set.nonempty_iff_ne_empty.mp hk]
      · simp [ch, Set.not_nonempty_iff_eq_empty.mp hk]
    · intro k j hj
      by_cases hk : (E i k ∩ D).Nonempty
      · have hj' : Classical.choose (he k hk) = j := by simpa [ch, hk] using hj
        rw [← hj']
        exact Classical.choose_spec (he k hk)
      · simp [ch, hk] at hj
  choose choice hnone hchoice using hex
  have hchoiceI : ∀ i k j, choice i k = some j → E i k ⊆ I j :=
    fun i k j h => (hchoice i k j h).trans (hinner j)
  refine ⟨m, E, δ, choice, hδ, hdisj, hcov, hmeas, ?_, hchoiceI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i k x hx y hy => (hdiam i k x hx y hy).trans (min_le_left _ _)
  · exact fun i k j h => (hchoiceI i k j h).trans (hIball j)
  · exact fun i j => (hballC j).trans (hcov i)
  · exact fun i => measurable_cellSelector (E i) (choice i) (hdisj i) (hmeas i)
  · intro i x hx hn
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov i (hDC hx))
    have hlabel := (cellLabel_eq_some_iff (E i) (hdisj i) x k).mpr hk
    have hch : choice i k = none := (cellSelector_of_label (E i) (choice i) hlabel).symm.trans hn
    exact (Set.notMem_empty x) ((hnone i k).mp hch ▸ (show x ∈ E i k ∩ D from ⟨hk, hx⟩))
  · intro i x j hj y hy
    obtain ⟨k, hx, hc⟩ := cellSelector_some_mem (E i) (choice i) hj
    have hxj := hchoice i k j hc hx
    change dist y (center j) < R j
    calc
      dist y (center j) ≤ dist y x + dist x (center j) := dist_triangle _ _ _
      _ < s / 2 + s / 2 := add_lt_add hy hxj
      _ = s := by ring
      _ ≤ R j := hR j
  · filter_upwards [herror] with n hn
    have h := hn choice hchoiceI
    simp only [hUball] at h
    exact h

end LatticeProb
