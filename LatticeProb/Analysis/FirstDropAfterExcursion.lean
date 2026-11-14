import Mathlib

/-!
# First drop after an excursion

If a real function returns to its starting level after a strictly positive excursion,
and the endpoint is not a local minimum, that endpoint is the first strict drop
below the starting level in the sense of an infimum.
-/

open Set Filter
open scoped Topology

namespace LatticeProb

/-- An excursion endpoint which is not a local minimum is the infimum of the
subsequent strict-drop times. Continuity is not needed. -/
theorem firstDrop_eq_of_excursion {X : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (heq : X s = X t)
    (hpos : ∀ u ∈ Ioo s t, X s < X u) (hmin : ¬ IsLocalMin X t) :
    sInf {u : ℝ | s < u ∧ X u < X s} = t := by
  have hnear : ∀ r : ℝ, t < r → ∃ u ∈ Ioo s r, X u < X s := by
    intro r htr
    by_contra hn
    have hm : IsMinOn X (Ioo s r) t := by
      intro u hu
      by_contra hbad
      have hlt : X u < X s := by
        rw [heq]
        exact lt_of_not_ge hbad
      exact hn ⟨u, hu, hlt⟩
    exact hmin (hm.isLocalMin (Ioo_mem_nhds hst htr))
  have hlower : ∀ u ∈ {u : ℝ | s < u ∧ X u < X s}, t ≤ u := by
    intro u hu
    by_contra h
    have hut : u < t := lt_of_not_ge h
    exact (not_lt_of_ge (hpos u ⟨hu.1, hut⟩).le) hu.2
  have hnonempty : {u : ℝ | s < u ∧ X u < X s}.Nonempty := by
    obtain ⟨u, hu, hv⟩ := hnear (t + 1) (by linarith)
    exact ⟨u, hu.1, hv⟩
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt hnonempty hlower
  intro r htr
  obtain ⟨u, hu, hv⟩ := hnear r htr
  exact ⟨u, ⟨hu.1, hv⟩, hu.2⟩

end LatticeProb
