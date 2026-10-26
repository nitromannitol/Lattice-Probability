import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation

/-!
# A translated coordinate plane with its actual normalization

On the translated fully open two-dimensional component the inverse-composition plane
is y₀ minus one. Its shifted root has value zero, while the actual origin has value minus
one, displaying both the constant slope displacement and nonconstancy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

/-- The coordinate plane translates to y₀ minus one, with distinct values at the shifted
root and the actual origin, and retains the original corrected slope. -/
theorem allOpen_two_translated_coordinate_correctedPlane :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    let z := unit (0 : Fin 2)
    let D := openComponentTranslation z (allOpen 2) C
    ∃ v : D → ℝ, (∀ y, v y = (y.val 0 : ℝ) - 1) ∧
      IsCorrectedPlane D (Pi.single 0 1) v ∧
      ∃ a b : D, a.val = z ∧ b.val = 0 ∧ v a = 0 ∧ v b = -1 ∧ v a ≠ v b := by
  dsimp only
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
  let z := unit (0 : Fin 2)
  let D := openComponentTranslation z (allOpen 2) C
  let u : C → ℝ := fun x => (x.val 0 : ℝ)
  let v : D → ℝ := fun y => u ((openComponentTranslationIso z C).symm y)
  have hv (y : D) : v y = (y.val 0 : ℝ) - 1 := by
    change (((openComponentTranslationIso z C).symm y).val 0 : ℝ) = _
    rw [openComponentTranslationIso_symm_val]
    norm_num [Pi.sub_apply, z, unit, Pi.single_apply]
  have ha : z ∈ D.supp := by
    rw [mem_openComponentTranslation_supp]
    change z - z ∈ C.supp
    rw [sub_self, uniqueInfiniteComponent_allOpen_supp]
    trivial
  have hb : (0 : Vertex 2) ∈ D.supp := by
    rw [mem_openComponentTranslation_supp]
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  refine ⟨v, hv, (isCorrectedPlane_translation_iff z C (Pi.single 0 1) u).mpr
    (allOpen_isCorrectedPlane_coordinate 2 0), ⟨z, ha⟩, ⟨0, hb⟩, rfl, rfl, ?_⟩
  have hva : v ⟨z, ha⟩ = 0 := by
    rw [hv]
    norm_num [z, unit, Pi.single_apply]
  have hvb : v ⟨0, hb⟩ = -1 := by
    rw [hv]
    norm_num
  exact ⟨hva, hvb, by rw [hva, hvb]; norm_num⟩

end

end LatticeProb.Percolation
