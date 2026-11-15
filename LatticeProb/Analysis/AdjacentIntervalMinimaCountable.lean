import LatticeProb.Analysis.AdjacentIntervalMinimaSlab
import LatticeProb.Analysis.AdjacentMinimizerEndpoints
import LatticeProb.Analysis.ForwardLevelVisits

/-! # Countability of matching adjacent minima on a short slab -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Matching adjacent minima occur at countably many points in a short slab,
when distinct local minima have distinct values. -/
theorem countable_adjacent_interval_minima_on_slab (f : ℝ → ℝ) (hf : Continuous f)
    (δ D : ℝ) (hδ : 0 < δ) (hδD : δ < D) (S : Set ℝ)
    (hdist : ∀ x y, x ≠ y → IsLocalMin f x → IsLocalMin f y → f x ≠ f y)
    (hshort : ∀ t ∈ S, ∀ u ∈ S, t ≤ u → u ≤ t + δ ∧ u + δ ≤ t + D)
    (heq : ∀ t ∈ S,
      sInf (f '' Icc t (t + δ)) = sInf (f '' Icc (t + δ) (t + D))) :
    S.Countable := by
  by_cases hempty : S.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hempty
    let v := sInf (f '' Icc t₀ (t₀ + δ))
    have hconstant : ∀ t ∈ S, sInf (f '' Icc t (t + δ)) = v := by
      intro t ht
      exact adjacent_interval_minima_eq_on_slab f hf δ D hδ.le hδD.le S hshort heq
        t ht t₀ ht₀
    have hforward := countable_forward_level_visits f v D (by linarith) hdist
    have hbackward := countable_backward_level_visits f v D (by linarith) hdist
    have hlocal := countable_localMin_of_distinct_values f hdist
    have hback := hbackward.preimage (show Function.Injective (fun t : ℝ => t + D) by
      intro x y h
      linarith)
    have hloc := hlocal.preimage (show Function.Injective (fun t : ℝ => t + δ) by
      intro x y h
      linarith)
    apply (hforward.union (hback.union hloc)).mono
    intro t ht
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
    have hxv : f x = v := hxInf.symm.trans (hconstant t ht)
    have hm : IsMinOn f (Icc t (t + D)) x := by
      intro z hz
      by_cases hz' : z ≤ t + δ
      · exact hxMin ⟨hz.1, hz'⟩
      · rw [← hxy]
        exact hyMin ⟨le_of_not_ge hz', hz.2⟩
    rcases adjacent_minimizer_endpoint_or_localMin f (by linarith : t < t + δ)
        (by linarith : t + δ < t + D) hdist hx hy hm hxy with ha | hc | hb
    · left
      refine ⟨ha.trans hxv, ?_⟩
      intro z hz
      rw [← hxv]
      exact hm hz
    · right
      left
      refine ⟨hc.trans hxv, ?_⟩
      intro z hz
      rw [← hxv]
      apply hm
      constructor <;> linarith [hz.1, hz.2]
    · exact Or.inr (Or.inr hb)
  · exact (not_nonempty_iff_eq_empty.mp hempty) ▸ countable_empty

end LatticeProb
