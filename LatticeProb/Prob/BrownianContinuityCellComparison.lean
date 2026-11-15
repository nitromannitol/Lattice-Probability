import LatticeProb.Bonanno.BouRabeeGwynne.BrownianContinuityCells
import LatticeProb.Prob.FiniteDomainCellComparison

/-! # Common Brownian exit continuity cells and uniform mass comparison -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace LatticeProb

/-- For finitely many bounded open domains, choose one family of small Brownian
exit continuity cells and compare their masses uniformly at nearby starts.
Continuity of the reference kernels and uniform convergence of the approximating
laws are explicit hypotheses. -/
theorem exists_common_brownian_cells_uniform_mass_comparison
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (x : ∀ j, P j → Euc d) (hx : ∀ j z, x j z ∈ U j)
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) (x j z) ρ).map CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    {K : Set (Euc d)} (hK : IsCompact K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (m : ℕ) (E : Fin m → Set (Euc d)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧ K ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < a) ∧
      (∀ j i z, (ν j z : Measure (Euc d)) (frontier (E i)) = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
        dist (p j n v) z ≤ δ → ∀ i,
          |((μ j n v : Measure (Euc d)) (E i)).toReal -
            ((ν j z : Measure (Euc d)) (E i)).toReal| ≤ b := by
  obtain ⟨m, E, hdisj, hcover, hmeas, hbounded, hdiam, hnull⟩ :=
    exists_common_brownian_exit_continuity_cells hd hρ U hU hUb hK ha
  have hn : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (E i)) = 0 := by
    intro j i z
    rw [hνlaw]
    exact hnull j (x j z) (hx j z) i
  exact ⟨m, E, hdisj, hcover, hmeas, hbounded, hdiam, hn,
    finite_uniform_nearby_cell_mass_error P V p μ ν hν hLP E hn hb⟩

end LatticeProb
