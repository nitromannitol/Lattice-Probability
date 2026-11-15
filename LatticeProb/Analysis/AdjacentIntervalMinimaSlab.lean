import Mathlib
import LatticeProb.Analysis.OverlappingIntervalMinima

/-! # Adjacent interval minima on short slabs -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- If the minima on adjacent intervals agree at every point of a short
slab, then these minima have one common value throughout the slab. -/
theorem adjacent_interval_minima_eq_on_slab (f : ℝ → ℝ) (hf : Continuous f)
    (δ D : ℝ) (hδ : 0 ≤ δ) (hδD : δ ≤ D) (S : Set ℝ)
    (hshort : ∀ t ∈ S, ∀ u ∈ S, t ≤ u → u ≤ t + δ ∧ u + δ ≤ t + D)
    (heq : ∀ t ∈ S,
      sInf (f '' Icc t (t + δ)) = sInf (f '' Icc (t + δ) (t + D))) :
    ∀ t ∈ S, ∀ u ∈ S, sInf (f '' Icc t (t + δ)) =
      sInf (f '' Icc u (u + δ)) := by
  have hmin (t : ℝ) (ht : t ∈ S) :
      ∃ x ∈ Icc t (t + δ), ∃ y ∈ Icc (t + δ) (t + D),
        IsMinOn f (Icc t (t + D)) x ∧ f y = f x ∧
        sInf (f '' Icc t (t + δ)) = f x := by
    obtain ⟨x, hx, hxMin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith : t ≤ t + δ)) hf.continuousOn
    obtain ⟨y, hy, hyMin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith : t + δ ≤ t + D)) hf.continuousOn
    have hxInf : sInf (f '' Icc t (t + δ)) = f x := by
      exact IsLeast.csInf_eq ⟨mem_image_of_mem f hx, by
        rintro _ ⟨z, hz, rfl⟩
        exact hxMin hz⟩
    have hyInf : sInf (f '' Icc (t + δ) (t + D)) = f y := by
      exact IsLeast.csInf_eq ⟨mem_image_of_mem f hy, by
        rintro _ ⟨z, hz, rfl⟩
        exact hyMin hz⟩
    have hxy : f y = f x := by rw [← hyInf, ← hxInf, heq t ht]
    refine ⟨x, hx, y, hy, ?_, hxy, hxInf⟩
    intro z hz
    by_cases hz' : z ≤ t + δ
    · exact hxMin ⟨hz.1, hz'⟩
    · rw [← hxy]
      exact hyMin ⟨le_of_not_ge hz', hz.2⟩
  have hordered (t u : ℝ) (ht : t ∈ S) (hu : u ∈ S) (htu : t ≤ u) :
      sInf (f '' Icc t (t + δ)) = sInf (f '' Icc u (u + δ)) := by
    obtain ⟨x, hx, y, hy, hxm, hxy, hxInf⟩ := hmin t ht
    obtain ⟨x', hx', y', hy', hx'm, hx'y', hx'Inf⟩ := hmin u hu
    have hs := hshort t ht u hu htu
    rw [hxInf, hx'Inf]
    exact overlapping_interval_minima_eq f htu hs.1 hs.2 (by linarith)
      hy hx' hxm hx'm hxy
  intro t ht u hu
  rcases le_total t u with h | h
  · exact hordered t u ht hu h
  · exact (hordered u t hu ht h).symm

end LatticeProb
