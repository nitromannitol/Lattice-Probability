/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.PushArea at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# An area-parametrized surjective curve pushes Lebesgue measure to the area

Source: [18], §1.2: the space-filling SLE `η` is parametrized by
LQG area, `μ_h(η([s, t])) = t − s`. Deterministic fact used to encode the local GMC area of [18] Lemma 4.3 by the
curve alone: if a continuous surjective `e : ℝ → ℂ` satisfies `μ(e([s, t])) = t − s` for all `s ≤ t`, then
`μ = e_* Leb`.

* `measure_image_le_volume`: `μ(e(S)) ≤ Leb(S)` for **every** `S ⊆ ℝ` (outer measures; Lebesgue outer measure is
  the infimum over countable covers by intervals `(a, b]`);
* `volume_le_measure_image`: `Leb(A) ≤ μ(e(A))` for measurable `A ⊆ [s, t]`;
* `eq_map_volume`: `μ = volume.map e`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cM

variable {μ : Measure ℂ} {e : ℝ → ℂ}

/-- **The image mass of any time set is at most its Lebesgue outer measure.** -/
theorem measure_image_le_volume
    (harea : ∀ s t : ℝ, s ≤ t → μ (e '' Icc s t) = ENNReal.ofReal (t - s)) (S : Set ℝ) :
    μ (e '' S) ≤ volume S := by
  have key : OuterMeasure.comap e μ.toOuterMeasure ≤ StieltjesFunction.id.outer := by
    refine OuterMeasure.le_ofFunction.2 fun s => ?_
    unfold StieltjesFunction.length
    simp only [not_isEmpty_of_nonempty, ite_false]
    refine le_iInf fun a => le_iInf fun b => le_iInf fun hs' => ?_
    have hs : s ⊆ Ioc a b := fun x hx => hs' ⟨hx, fun hb => not_isBot x hb⟩
    rw [OuterMeasure.comap_apply]
    rcases le_or_gt a b with hab | hab
    · calc μ.toOuterMeasure (e '' s) = μ (e '' s) := rfl
        _ ≤ μ (e '' Icc a b) := measure_mono (image_mono (hs.trans Ioc_subset_Icc_self))
        _ = ENNReal.ofReal (b - a) := harea a b hab
        _ = ENNReal.ofReal (StieltjesFunction.id b - StieltjesFunction.id a) := rfl
    · have hs0 : s = ∅ := by
        rw [Ioc_eq_empty (not_lt.2 hab.le)] at hs
        exact subset_empty_iff.1 hs
      subst hs0
      simp
  have hvol : volume S = StieltjesFunction.id.outer S := by
    rw [Real.volume_eq_stieltjes_id, StieltjesFunction.measure]
    rfl
  calc μ (e '' S) = OuterMeasure.comap e μ.toOuterMeasure S := (OuterMeasure.comap_apply _ _ _).symm
    _ ≤ StieltjesFunction.id.outer S := key S
    _ = volume S := hvol.symm

/-- **The image mass of a measurable time set is at least its Lebesgue measure.** -/
theorem volume_le_measure_image
    (harea : ∀ s t : ℝ, s ≤ t → μ (e '' Icc s t) = ENNReal.ofReal (t - s)) {s t : ℝ} (hst : s ≤ t)
    {A : Set ℝ} (hA : MeasurableSet A) (hAst : A ⊆ Icc s t) :
    volume A ≤ μ (e '' A) := by
  have hAfin : volume A ≤ ENNReal.ofReal (t - s) :=
    (measure_mono hAst).trans (Real.volume_Icc).le
  have h1 : ENNReal.ofReal (t - s) ≤ μ (e '' A) + volume (Icc s t \ A) := by
    calc ENNReal.ofReal (t - s) = μ (e '' Icc s t) := (harea s t hst).symm
      _ = μ (e '' A ∪ e '' (Icc s t \ A)) := by rw [← image_union, union_sdiff_cancel hAst]
      _ ≤ μ (e '' A) + μ (e '' (Icc s t \ A)) := measure_union_le _ _
      _ ≤ μ (e '' A) + volume (Icc s t \ A) :=
        add_le_add le_rfl (measure_image_le_volume harea _)
  have h2 : volume (Icc s t \ A) = ENNReal.ofReal (t - s) - volume A := by
    rw [measure_sdiff hAst hA.nullMeasurableSet (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAfin),
      Real.volume_Icc]
  rw [h2] at h1
  have h3 := tsub_le_iff_right.2 h1
  rwa [ENNReal.sub_sub_cancel ENNReal.ofReal_ne_top hAfin] at h3

/-- **An area-parametrized surjective continuous curve pushes Lebesgue measure to the area.** -/
theorem eq_map_volume (he : Continuous e) (hsurj : Function.Surjective e)
    (harea : ∀ s t : ℝ, s ≤ t → μ (e '' Icc s t) = ENNReal.ofReal (t - s)) :
    μ = volume.map e := by
  ext C hC
  rw [Measure.map_apply he.measurable hC]
  apply le_antisymm
  · calc μ C = μ (e '' (e ⁻¹' C)) := by rw [image_preimage_eq C hsurj]
      _ ≤ volume (e ⁻¹' C) := measure_image_le_volume harea _
  · have hmeas : MeasurableSet (e ⁻¹' C) := he.measurable hC
    have hU : e ⁻¹' C = ⋃ n : ℕ, (e ⁻¹' C ∩ Icc (-(n : ℝ)) n) := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_Icc]
      constructor
      · intro hu
        obtain ⟨n, hn⟩ := exists_nat_ge |u|
        exact ⟨n, hu, by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
      · rintro ⟨n, hu, -⟩
        exact hu
    have hmono : Monotone fun n : ℕ => e ⁻¹' C ∩ Icc (-(n : ℝ)) n := by
      intro m n hmn
      refine inter_subset_inter_right _ (Icc_subset_Icc ?_ ?_)
      · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith
      · exact_mod_cast hmn
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hn : -(n : ℝ) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    calc volume (e ⁻¹' C ∩ Icc (-(n : ℝ)) n)
        ≤ μ (e '' (e ⁻¹' C ∩ Icc (-(n : ℝ)) n)) :=
          volume_le_measure_image harea hn (hmeas.inter measurableSet_Icc) inter_subset_right
      _ ≤ μ C := measure_mono ((image_mono inter_subset_left).trans (image_preimage_subset e C))

end MatedCRTHarmonic.GMS4cM
