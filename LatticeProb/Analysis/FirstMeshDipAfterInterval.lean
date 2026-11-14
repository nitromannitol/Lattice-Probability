import LatticeProb.Analysis.FirstMeshDip

/-!
# Locating the first mesh interval below a level

A protected interval on which a function stays above a level forces its first
strict-dip mesh interval to lie beyond any point one mesh width earlier.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The first mesh interval with a strict dip lies beyond a point separated
from the protected interval's endpoint by at least one mesh width. -/
theorem exists_first_mesh_dip_after_of_forall_ge {X : ℝ → ℝ} {a b c s ε : ℝ}
    (hε : 0 < ε) (has : a ≤ s) (hgap : b + ε ≤ s)
    (hprotected : ∀ u ∈ Icc a s, c ≤ X u)
    (hdip : ∃ t ≥ a, X t < c) :
    ∃ n : ℕ, ∃ t ∈ Icc (a + (n : ℝ) * ε) (a + ((n : ℝ) + 1) * ε),
      X t < c ∧ (∀ u ∈ Icc a (a + (n : ℝ) * ε), c ≤ X u) ∧
        b < a + (n : ℝ) * ε := by
  obtain ⟨n, t, ht, hlt, hbefore⟩ :=
    exists_first_mesh_dip hε (hprotected a ⟨le_rfl, has⟩) hdip
  have hta : a ≤ t := by
    have hn : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε.le
    linarith [ht.1]
  have hst : s < t := by
    by_contra h
    exact (not_lt_of_ge (hprotected t ⟨hta, le_of_not_gt h⟩)) hlt
  refine ⟨n, t, ht, hlt, hbefore, ?_⟩
  nlinarith [ht.2]

end LatticeProb
