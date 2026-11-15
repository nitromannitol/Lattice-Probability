import LatticeProb.MeasureTheory.FiniteIntervalAlignment

/-! # Endpoints of equal-length interval covers -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Two finite equal-length interval covers with the same left boundary have
matching endpoints for intervals containing a common interior point. -/
theorem interval_endpoints_eq_of_common_interior_point
    {ι κ : Type*} [Finite ι] [Finite κ] (c d ℓ : ℝ)
    (A B : ι → ℝ) (C D : κ → ℝ)
    (hℓ : 0 < ℓ)
    (hboundAB : ∀ i, c ≤ A i) (hboundCD : ∀ j, c ≤ C j)
    (hlenAB : ∀ i, B i - A i = ℓ) (hlenCD : ∀ j, D j - C j = ℓ)
    (hdisAB : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hdisCD : Pairwise fun i j => Disjoint (Ioo (C i) (D i)) (Ioo (C j) (D j)))
    (hcoverAB : Icc c d ⊆ ⋃ i, Icc (A i) (B i))
    (hcoverCD : Icc c d ⊆ ⋃ j, Icc (C j) (D j))
    (i : ι) (j : κ) (hi : B i ≤ d) (hj : D j ≤ d) (u : ℝ)
    (hui : u ∈ Ioo (A i) (B i)) (huj : u ∈ Ioo (C j) (D j)) :
    A i = C j ∧ B i = D j := by
  obtain ⟨n, hn⟩ := interval_left_endpoint_eq_grid_point c d ℓ A B hℓ hboundAB
    hlenAB hdisAB hcoverAB i hi
  obtain ⟨m, hm⟩ := interval_left_endpoint_eq_grid_point c d ℓ C D hℓ hboundCD
    hlenCD hdisCD hcoverCD j hj
  have hu₁ : u ∈ Ico (c + (n : ℝ) * ℓ) (c + ((n : ℝ) + 1) * ℓ) := by
    simp only [mem_Ico]
    constructor <;> nlinarith [hui.1, hui.2, hlenAB i]
  have hu₂ : u ∈ Ico (c + (m : ℝ) * ℓ) (c + ((m : ℝ) + 1) * ℓ) := by
    simp only [mem_Ico]
    constructor <;> nlinarith [huj.1, huj.2, hlenCD j]
  have hnm : n = m := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (Set.disjoint_left.mp (disjoint_Ico_cells c ℓ hℓ.le h)) hu₁ hu₂
    · exact (Set.disjoint_left.mp (disjoint_Ico_cells c ℓ hℓ.le h)) hu₂ hu₁
  rw [← hnm] at hm
  have hleft : A i = C j := hn.trans hm.symm
  exact ⟨hleft, by linarith [hlenAB i, hlenCD j]⟩

end LatticeProb
