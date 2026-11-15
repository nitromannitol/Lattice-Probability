import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith

/-! # Measurable local values of profiles -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal

namespace LatticeProb

open scoped Classical in
/-- A jointly measurable real profile has a measurable selector that recovers
any nonnegative almost-everywhere constant value on a neighborhood of an anchor. -/
theorem exists_measurable_local_profile_value
    {Θ : Type*} [MeasurableSpace Θ] (u : ℝ)
    (F : Θ × ℝ → ℝ) (hF : Measurable F) :
    ∃ V : Θ → ℝ, Measurable V ∧
      ∀ (θ : Θ) (l r c : ℝ), l < u → u < r → 0 ≤ c →
        (∀ᵐ t ∂(volume.restrict (Ioo l r)), F (θ, t) = c) → V θ = c := by
  classical
  let W : Θ → (ℚ × ℚ × ℚ) → Prop := fun θ z =>
    0 ≤ (z.1 : ℝ) ∧ (z.2.1 : ℝ) < u ∧ u < (z.2.2 : ℝ) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))),
        (z.1 : ℝ) ≤ F (θ, t)
  let V : Θ → ℝ := fun θ => ⨆ z, if W θ z then (z.1 : ℝ) else 0
  have hW (z : ℚ × ℚ × ℚ) : MeasurableSet {θ | W θ z} := by
    have hs : MeasurableSet {x : Θ × ℝ | F x < (z.1 : ℝ)} :=
      measurableSet_lt hF measurable_const
    have hm : Measurable (fun θ : Θ =>
        (volume.restrict (Ioo (z.2.1 : ℝ) (z.2.2 : ℝ)))
          {t | F (θ, t) < (z.1 : ℝ)}) :=
      measurable_measure_prodMk_left hs
    have he : MeasurableSet {θ : Θ | ∀ᵐ t ∂(volume.restrict
        (Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))), (z.1 : ℝ) ≤ F (θ, t)} := by
      have hzero := measurableSet_eq_fun hm
        (measurable_const : Measurable (fun _ : Θ => (0 : ℝ≥0∞)))
      convert hzero using 1
      ext θ
      simp only [mem_ofPred_eq, ae_iff, not_le]
    by_cases h : 0 ≤ (z.1 : ℝ) ∧ (z.2.1 : ℝ) < u ∧ u < (z.2.2 : ℝ)
    · have hw_eq : {θ : Θ | W θ z} = {θ : Θ | ∀ᵐ t ∂(volume.restrict
          (Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))), (z.1 : ℝ) ≤ F (θ, t)} := by
        ext θ
        exact ⟨fun ht => ht.2.2.2, fun ht => ⟨h.1, h.2.1, h.2.2, ht⟩⟩
      rw [hw_eq]
      exact he
    · have hw_eq : {θ : Θ | W θ z} = ∅ := by
        ext θ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro ht
        exact h ⟨ht.1, ht.2.1, ht.2.2.1⟩
      rw [hw_eq]
      exact MeasurableSet.empty
  refine ⟨V, Measurable.iSup (fun z => measurable_const.ite (hW z) measurable_const), ?_⟩
  intro θ l r c hlu hur hc hrun
  have hbound (z : ℚ × ℚ × ℚ) : (if W θ z then (z.1 : ℝ) else 0) ≤ c := by
    by_cases hw : W θ z
    · simp only [hw, ↓reduceIte]
      obtain ⟨hq, hp, hr, hqae⟩ := hw
      have hpos : volume (Ioo l r ∩ Ioo (z.2.1 : ℝ) (z.2.2 : ℝ)) ≠ 0 := by
        rw [Ioo_inter_Ioo, Real.volume_Ioo]
        apply ne_of_gt
        apply ENNReal.ofReal_pos.mpr
        have hleft : max l (z.2.1 : ℝ) < u := max_lt hlu hp
        have hright : u < min r (z.2.2 : ℝ) := lt_min hur hr
        linarith
      have : (ae (volume.restrict (Ioo l r ∩ Ioo (z.2.1 : ℝ) (z.2.2 : ℝ)))).NeBot :=
        ae_restrict_neBot.mpr hpos
      have ha : ∀ᵐ t ∂(volume.restrict (Ioo l r ∩ Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))),
          F (θ, t) = c := ae_restrict_of_ae_restrict_of_subset inter_subset_left hrun
      have hb : ∀ᵐ t ∂(volume.restrict (Ioo l r ∩ Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))),
          (z.1 : ℝ) ≤ F (θ, t) := ae_restrict_of_ae_restrict_of_subset inter_subset_right hqae
      have hh : ∀ᵐ t ∂(volume.restrict (Ioo l r ∩ Ioo (z.2.1 : ℝ) (z.2.2 : ℝ))),
          (z.1 : ℝ) ≤ c := by
        filter_upwards [ha, hb] with t ht hqt
        simpa [ht] using hqt
      exact hh.exists.choose_spec
    · simp [hw, hc]
  have hB : BddAbove (range (fun z => if W θ z then (z.1 : ℝ) else 0)) :=
    ⟨c, by rintro _ ⟨z, rfl⟩; exact hbound z⟩
  have hV : 0 ≤ V θ := by
    have h := le_ciSup hB ((0, 0, 0) : ℚ × ℚ × ℚ)
    by_cases hz : W θ ((0, 0, 0) : ℚ × ℚ × ℚ) <;> simpa [V, hz] using h
  apply le_antisymm
  · exact ciSup_le hbound
  · by_contra h
    have hv : V θ < c := lt_of_not_ge h
    obtain ⟨q, hq0, hqc⟩ := exists_rat_btwn (show max (V θ) 0 < c from max_lt hv (lt_of_le_of_lt hV hv))
    obtain ⟨p, hlp, hpu⟩ := exists_rat_btwn hlu
    obtain ⟨r', hur', hr'r⟩ := exists_rat_btwn hur
    have hw : W θ (q, p, r') := by
      refine ⟨(lt_of_le_of_lt (le_max_right _ _) hq0).le, hpu, hur', ?_⟩
      have ha := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hlp.le hr'r.le) hrun
      filter_upwards [ha] with t ht
      linarith
    have hqle := le_ciSup hB (q, p, r')
    simp only [hw, ↓reduceIte] at hqle
    exact (not_lt_of_ge hqle) (lt_of_le_of_lt (le_max_left _ _) hq0)

end LatticeProb
