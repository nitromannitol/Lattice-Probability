import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! # Almost everywhere constant profiles on overlapping intervals -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

/-- Almost everywhere constants on two sets coincide when the sets have
positive common measure and the functions agree almost everywhere there. -/
theorem ae_constants_eq_of_overlap
    {α β : Type*} [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (f g : α → β) (p q : β) (hst : μ (s ∩ t) ≠ 0)
    (hf : ∀ᵐ x ∂(μ.restrict s), f x = p)
    (hg : ∀ᵐ x ∂(μ.restrict t), g x = q)
    (hfg : ∀ᵐ x ∂(μ.restrict (s ∩ t)), f x = g x) : p = q := by
  have : (ae (μ.restrict (s ∩ t))).NeBot := ae_restrict_neBot.mpr hst
  have hf' : ∀ᵐ x ∂(μ.restrict (s ∩ t)), f x = p :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hf
  have hg' : ∀ᵐ x ∂(μ.restrict (s ∩ t)), g x = q :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hg
  have h : ∀ᵐ x ∂(μ.restrict (s ∩ t)), p = q := by
    filter_upwards [hf', hg', hfg] with x hx hy hxy
    exact hx.symm.trans (hxy.trans hy)
  exact h.exists.choose_spec

/-- If two open intervals overlap and a common almost everywhere profile
records their lengths, those lengths are equal. -/
theorem interval_lengths_eq_of_ae_profile_overlap
    (a b c d u : ℝ) (f g : ℝ → ℝ)
    (hu : u ∈ Ioo a b ∩ Ioo c d)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), f x = b - a)
    (hg : ∀ᵐ x ∂(volume.restrict (Ioo c d)), g x = d - c)
    (hfg : ∀ᵐ x ∂(volume.restrict (Ioo a b ∩ Ioo c d)), f x = g x) :
    b - a = d - c := by
  apply ae_constants_eq_of_overlap volume (Ioo a b) (Ioo c d) f g _ _ ?_ hf hg hfg
  rw [Ioo_inter_Ioo, Real.volume_Ioo]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  have ha : max a c < u := max_lt hu.1.1 hu.2.1
  have hb : u < min b d := lt_min hu.1.2 hu.2.2
  linarith

/-- With equal left endpoints, overlapping intervals carrying the same
length profile also have equal right endpoints. -/
theorem interval_right_eq_of_ae_profile_overlap
    (a b d u : ℝ) (f g : ℝ → ℝ)
    (hu : u ∈ Ioo a b ∩ Ioo a d)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), f x = b - a)
    (hg : ∀ᵐ x ∂(volume.restrict (Ioo a d)), g x = d - a)
    (hfg : ∀ᵐ x ∂(volume.restrict (Ioo a b ∩ Ioo a d)), f x = g x) : b = d := by
  have h := interval_lengths_eq_of_ae_profile_overlap a b a d u f g hu hf hg hfg
  linarith

end LatticeProb
