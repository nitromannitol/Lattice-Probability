import LatticeProb.Analysis.StraddlingLevelPairs

/-! # Excursion contacts in separated intervals -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous function below a level in two separated intervals and strictly
above it between them has an excursion with one endpoint in each interval. -/
theorem exists_separated_excursion_contacts {f : ℝ → ℝ} {a b c d r : ℝ}
    (hf : Continuous f) (hbc : b ≤ c)
    (hleft : ∃ x ∈ Icc a b, f x < r) (hright : ∃ y ∈ Icc c d, f y < r)
    (hmiddle : ∀ z ∈ Icc b c, r < f z) :
    ∃ s ∈ Ioo a b, ∃ t ∈ Ioo c d,
      f s = r ∧ f t = r ∧ ∀ z ∈ Ioo s t, r < f z := by
  obtain ⟨x, hx, hfx⟩ := hleft
  obtain ⟨y, hy, hfy⟩ := hright
  have hl : r < f b := hmiddle b ⟨le_rfl, hbc⟩
  have ha : ∃ x ≤ b, f x ≤ r := ⟨x, hx.2, hfx.le⟩
  have hb : ∃ y, b ≤ y ∧ f y ≤ r := ⟨y, hbc.trans hy.1, hfy.le⟩
  have hs := apply_lastBelow hf hl ha
  have ht := apply_firstBelow hf hl hb
  have hxs : x < lastBelow f b r := by
    refine lt_of_le_of_ne (le_lastBelow hx.2 hfx.le) ?_
    intro h
    rw [← h] at hs
    exact hfx.ne hs
  have hty : firstBelow f b r < y := by
    refine lt_of_le_of_ne (firstBelow_le (hbc.trans hy.1) hfy.le) ?_
    intro h
    rw [h] at ht
    exact hfy.ne ht
  have hct : c < firstBelow f b r := by
    by_contra h
    have htc : firstBelow f b r ≤ c := le_of_not_gt h
    have hbt : b ≤ firstBelow f b r := (firstBelow_mem hf hb).1
    exact (hmiddle _ ⟨hbt, htc⟩).ne' ht
  refine ⟨lastBelow f b r, ⟨hx.1.trans_lt hxs, lastBelow_lt hf hl ha⟩,
    firstBelow f b r, ⟨hct, hty.trans_le hy.2⟩, hs, ht, ?_⟩
  intro z hz
  have h := (straddle_pair hf hl ha hb).2.2 z hz
  rwa [hs] at h

end LatticeProb
