import LatticeProb.Topology.ParameterLoopExcision

/-! # Loop-free minimal parameter sets -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- In a minimal closed set with equal-image gaps, two equal-image points have
no retained point strictly between them. -/
theorem no_mem_between_of_minimal_equal_gap {Y : Type*} (f : ℝ → Y)
    {a b : ℝ} {K : Set ℝ} (hsub : K ⊆ Icc a b) (hclosed : IsClosed K)
    (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hmin : ∀ L : Set ℝ, L ⊆ K → IsClosed L → a ∈ L → b ∈ L →
      (∀ u ∈ L, ∀ v ∈ L, u < v →
        (∀ w ∈ L, ¬ (u < w ∧ w < v)) → f u = f v) → L = K)
    {s t : ℝ} (hs : s ∈ K) (ht : t ∈ K) (heq : f s = f t) :
    ∀ w ∈ K, ¬ (s < w ∧ w < t) := by
  have hsa : a ≤ s := (hsub hs).1
  have htb : t ≤ b := (hsub ht).2
  have ha' : a ∈ K \ Ioo s t := ⟨ha, by
    intro h
    exact (not_lt_of_ge hsa) h.1⟩
  have hb' : b ∈ K \ Ioo s t := ⟨hb, by
    intro h
    exact (not_lt_of_ge htb) h.2⟩
  have hcut : K \ Ioo s t = K :=
    hmin (K \ Ioo s t) sdiff_subset (hclosed.sdiff isOpen_Ioo) ha' hb'
      (equal_of_gap_after_loop_excision f K hs ht heq hgap)
  intro w hw hbetween
  have hw' : w ∈ K \ Ioo s t := hcut.symm ▸ hw
  exact hw'.2 hbetween

end LatticeProb
