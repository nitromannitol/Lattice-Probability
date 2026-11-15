import LatticeProb.Bonanno.BouRabeeGwynne.Section4UniformExitCells

/-! # Uniform continuity-cell comparison for finitely many domains -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology Classical

namespace LatticeProb

/-- A finite family of compact starting spaces admits a common nearby-start
modulus and a common eventual index. Uniform convergence and null frontiers
are required separately for each reference law. -/
theorem finite_uniform_nearby_cell_mass_error
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (BouRabeeGwynne.Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (BouRabeeGwynne.Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (BouRabeeGwynne.Euc d))
        (ν j (p j n v) : Measure (BouRabeeGwynne.Euc d)) < ε)
    {ι : Type*} [Fintype ι] (S : ι → Set (BouRabeeGwynne.Euc d))
    (hnull : ∀ j i z, (ν j z : Measure (BouRabeeGwynne.Euc d)) (frontier (S i)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ i,
        |((μ j n v : Measure (BouRabeeGwynne.Euc d)) (S i)).toReal -
          ((ν j z : Measure (BouRabeeGwynne.Euc d)) (S i)).toReal| ≤ ε := by
  classical
  have hs : ∀ j, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ i,
        |((μ j n v : Measure (BouRabeeGwynne.Euc d)) (S i)).toReal -
          ((ν j z : Measure (BouRabeeGwynne.Euc d)) (S i)).toReal| ≤ ε := by
    intro j
    exact BouRabeeGwynne.uniform_nearby_cell_mass_error_of_uniform_levyProkhorov_error
      (V j) (p j) (μ j) (ν j) (hν j) (hLP j) S (hnull j) ε hε
  choose δ hδ hcompare using hs
  let f : Option J → ℝ := fun j => Option.elim j 1 δ
  let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty f
  have hδ₀ : 0 < δ₀ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j hj
    cases j with
    | none => exact zero_lt_one
    | some j => exact hδ j
  have hδle (j : J) : δ₀ ≤ δ j :=
    Finset.inf'_le f (Finset.mem_univ (some j))
  refine ⟨δ₀, hδ₀, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hcompare] with n hn
  intro j v z hz i
  exact hn j v z (hz.trans (hδle j)) i

end LatticeProb
