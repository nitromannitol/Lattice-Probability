import LatticeProb.Prob.UniformCellCoupling

/-! # Prescribed error bounds for finite partition couplings -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace LatticeProb

/-- A finite partition coupling makes every event disjoint from the diagonal
cells arbitrarily small, uniformly for nearby starting points. -/
theorem finite_uniform_nearby_partition_coupling_bad_le_budget
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc d))
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (S i)) = 0)
    (hcover : ∀ j z, (ν j z : Measure (Euc d)) (⋃ i, S i) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ B : Set (Euc d × Euc d),
        (∀ i, Disjoint B (S i ×ˢ S i)) →
        finitePartitionCoupling (μ j n v : Measure (Euc d))
          (ν j z : Measure (Euc d)) S S B ≤ ENNReal.ofReal ε := by
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hsmall : 0 < ε / ((Fintype.card ι : ℝ) + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hbound⟩ :=
    finite_uniform_nearby_partition_coupling_bad_le P V p μ ν hν hLP S hS
      hdisj hnull hcover hsmall
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j v z hz B hB
  refine (hn j v z hz B hB).trans (ENNReal.ofReal_le_ofReal ?_)
  have : (Fintype.card ι : ℝ) * ε ≤ ε * ((Fintype.card ι : ℝ) + 1) := by
    nlinarith
  simpa only [mul_div_assoc] using (div_le_iff₀ hden).2 this

end LatticeProb
