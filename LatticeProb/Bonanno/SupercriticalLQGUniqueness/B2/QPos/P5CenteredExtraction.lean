/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5CenteredExtraction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointExtraction

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem latticeAdjacent_sub_center (z w c : ℤ × ℤ)
    (h : latticeAdjacent z w) :
    latticeAdjacent (z - c) (w - c) := by
  rcases h with h | h | h | h
  · left
    dsimp at *
    constructor <;> omega
  · right; left
    dsimp at *
    constructor <;> omega
  · right; right; left
    dsimp at *
    constructor <;> omega
  · right; right; right
    dsimp at *
    constructor <;> omega

 

theorem centered_lattice_annular_indices
    (p : ℕ → ℤ × ℤ) (N : ℕ) (c : ℤ × ℤ) (r R : ℤ)
    (hrR : r + 1 < R)
    (hstart : latticeSupRadius (p 0 - c) ≤ r)
    (hend : R ≤ latticeSupRadius (p N - c))
    (hpath : ∀ i < N, latticeAdjacent (p i) (p (i + 1))) :
    ∃ s t : ℕ, 0 < s ∧ s ≤ t ∧ t ≤ N ∧
      latticeSupRadius (p s - c) = r + 1 ∧
      latticeSupRadius (p t - c) = R ∧
      (∀ i, s ≤ i → i ≤ t →
        r + 1 ≤ latticeSupRadius (p i - c) ∧
        latticeSupRadius (p i - c) ≤ R) := by
  exact lattice_annular_indices (fun i => p i - c) N r R hrR
    hstart hend (fun i hi => latticeAdjacent_sub_center _ _ _ (hpath i hi))

end SupercriticalLQGUniqueness.B2.QPos
