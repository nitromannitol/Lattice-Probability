import Mathlib

/-! # Endpoints and adjacent interval minima -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- If two adjacent intervals have a common minimum, then that value occurs at
an outer endpoint or their common endpoint is a local minimum, provided distinct
local minima have distinct values. -/
theorem adjacent_minimizer_endpoint_or_localMin (f : ℝ → ℝ) {a b c s t : ℝ}
    (hab : a < b) (hbc : b < c)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc b c)
    (hmin : IsMinOn f (Icc a c) s) (heq : f t = f s) :
    f a = f s ∨ f c = f s ∨ IsLocalMin f b := by
  by_cases ha : f a = f s
  · exact Or.inl ha
  by_cases hc : f c = f s
  · exact Or.inr (Or.inl hc)
  · right
    right
    have hsa : a < s := by
      have hne : s ≠ a := by
        intro h
        exact ha (congrArg f h.symm)
      exact lt_of_le_of_ne hs.1 (Ne.symm hne)
    have htc : t < c := by
      have hne : t ≠ c := by
        intro h
        apply hc
        simpa [h] using heq
      exact lt_of_le_of_ne ht.2 hne
    have hslt : s < c := lt_of_le_of_lt hs.2 hbc
    have hat : a < t := lt_of_lt_of_le hab ht.1
    have hmins : IsLocalMin f s := hmin.isLocalMin (Icc_mem_nhds hsa hslt)
    have hmint : IsMinOn f (Icc a c) t := by
      intro x hx
      rw [heq]
      exact hmin hx
    have hminloc : IsLocalMin f t := hmint.isLocalMin (Icc_mem_nhds hat htc)
    have hst : s = t := by
      by_contra hne
      exact hdist s t hne hmins hminloc heq.symm
    have hsb : s = b := le_antisymm hs.2 (hst ▸ ht.1)
    simpa [hsb] using hmins

end LatticeProb
