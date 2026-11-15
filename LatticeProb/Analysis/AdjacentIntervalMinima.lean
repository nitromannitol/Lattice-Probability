import Mathlib

/-! # Minima on adjacent intervals -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- If the minimum on a union of adjacent intervals is unique and their
common endpoint is not a local minimum, their minimum values are distinct. -/
theorem IsMinOn.ne_of_adjacent_Icc {f : ℝ → ℝ} {a b c s t : ℝ}
    (hab : a < b) (hbc : b < c)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc b c)
    (hms : IsMinOn f (Icc a b) s) (hmt : IsMinOn f (Icc b c) t)
    (hunique : ∀ u ∈ Icc a c, ∀ v ∈ Icc a c,
      IsMinOn f (Icc a c) u → IsMinOn f (Icc a c) v → u = v)
    (hb : ¬ IsLocalMin f b) : f s ≠ f t := by
  intro heq
  have hs' : s ∈ Icc a c := ⟨hs.1, hs.2.trans hbc.le⟩
  have ht' : t ∈ Icc a c := ⟨hab.le.trans ht.1, ht.2⟩
  have hms' : IsMinOn f (Icc a c) s := by
    intro z hz
    rcases le_total z b with hzb | hbz
    · exact hms ⟨hz.1, hzb⟩
    · rw [heq]
      exact hmt ⟨hbz, hz.2⟩
  have hmt' : IsMinOn f (Icc a c) t := by
    intro z hz
    rcases le_total z b with hzb | hbz
    · rw [← heq]
      exact hms ⟨hz.1, hzb⟩
    · exact hmt ⟨hbz, hz.2⟩
  have hst : s = t := hunique s hs' t ht' hms' hmt'
  have hsb : s = b := le_antisymm hs.2 (hst ▸ ht.1)
  have hmb : IsMinOn f (Icc a c) b := hsb ▸ hms'
  exact hb (hmb.isLocalMin (Icc_mem_nhds hab hbc))

end LatticeProb
