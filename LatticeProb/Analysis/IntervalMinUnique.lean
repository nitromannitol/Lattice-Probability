import Mathlib

/-! # Uniqueness of interval minima -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Distinct local-minimum values and distinct endpoint values, with endpoints
avoiding local-minimum values, force uniqueness of a minimum on an interval. -/
theorem isMinOn_Icc_unique_of_localMin_values (f : ℝ → ℝ) {a b : ℝ}
    (hdist : ∀ s t, s ≠ t → IsLocalMin f s → IsLocalMin f t → f s ≠ f t)
    (hend : f a ≠ f b)
    (ha : ∀ t, IsLocalMin f t → f a ≠ f t)
    (hb : ∀ t, IsLocalMin f t → f b ≠ f t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hms : IsMinOn f (Icc a b) s) (hmt : IsMinOn f (Icc a b) t) : s = t := by
  have heq : f s = f t := le_antisymm (hms ht) (hmt hs)
  have classify (u : ℝ) (hu : u ∈ Icc a b) (hm : IsMinOn f (Icc a b) u) :
      u = a ∨ u = b ∨ IsLocalMin f u := by
    by_cases hua : u = a
    · exact Or.inl hua
    by_cases hub : u = b
    · exact Or.inr (Or.inl hub)
    · exact Or.inr (Or.inr (hm.isLocalMin
        (Icc_mem_nhds (lt_of_le_of_ne hu.1 (Ne.symm hua))
          (lt_of_le_of_ne hu.2 hub))))
  rcases classify s hs hms with hsa | hsb | hsl
  · subst s
    rcases classify t ht hmt with hta | htb | htl
    · exact hta.symm
    · subst t; exact (hend heq).elim
    · exact (ha t htl heq).elim
  · subst s
    rcases classify t ht hmt with hta | htb | htl
    · subst t; exact (hend heq.symm).elim
    · exact htb.symm
    · exact (hb t htl heq).elim
  · rcases classify t ht hmt with hta | htb | htl
    · subst t; exact (ha s hsl heq.symm).elim
    · subst t; exact (hb s hsl heq.symm).elim
    · by_contra hst
      exact hdist s t hst hsl htl heq

end LatticeProb
