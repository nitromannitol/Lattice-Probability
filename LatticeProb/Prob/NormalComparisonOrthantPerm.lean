/-
# Li--Shao normal comparison: permuting the coordinates of an orthant integral (route item 4)

Continuing `LatticeProb/Prob/NormalComparisonOrthantDeriv.lean`: the orthant box-Fubini
`lintegral_Iic_cons₂` only peels the coordinates `0` and `1` of `Set.Iic b ⊆ (Fin n → ℝ)`.
Route item 4 needs the mixed derivative `∂_i ∂_j` in an *arbitrary* pair of coordinates
`i ≠ j`, so we move `(i, j)` to the positions `(0, 1)` by a coordinate permutation.  This file
supplies the two ingredients:

* **`lintegral_Iic_perm`, `integral_Iic_perm`, `integrableOn_Iic_perm`** — the orthant integral
  is invariant under permuting the coordinates.  With the measurable equivalence
  `e y = fun l => y (σ.symm l)` (that is `MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ`, which is
  volume preserving by `MeasureTheory.volume_measurePreserving_piCongrLeft`) one has
  `x = e y`, and `x ∈ Iic b ⇔ ∀ l, x l ≤ b l ⇔ ∀ k, y k ≤ b (σ k)` (substitute `l = σ k`), so
  `e ⁻¹' Iic b = Iic (b ∘ σ)`.  The change of variables is then
  `MeasurePreserving.setLIntegral_comp_preimage_emb` (lintegral form),
  `MeasurePreserving.setIntegral_preimage_emb` (Bochner form, no integrability hypothesis) and
  `MeasurePreserving.integrableOn_comp_preimage` (integrability).
* **`exists_perm_zero_one`** — any ordered pair of distinct coordinates `i ≠ j` of
  `Fin (m + 2)` is the image of `(0, 1)` under some permutation, built from two transpositions.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- The measurable equivalence `piCongrLeft` for the constant family `ℝ` is the coordinate
permutation `y ↦ fun l => y (σ.symm l)`. -/
theorem piCongrLeft_const_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ) y = fun l => y (σ.symm l) := by
  funext l
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

/-- The preimage of the orthant `Iic b` under the coordinate permutation
`y ↦ fun l => y (σ.symm l)` is the orthant `Iic (b ∘ σ)`. -/
theorem preimage_perm_Iic {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : Fin n → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ) ⁻¹' Set.Iic b
      = Set.Iic (fun k => b (σ k)) := by
  ext y
  rw [Set.mem_preimage, piCongrLeft_const_apply, Set.mem_Iic, Set.mem_Iic, Pi.le_def, Pi.le_def]
  constructor
  · intro h k
    simpa using h (σ k)
  · intro h l
    simpa using h (σ.symm l)

/-- **Permuting coordinates preserves the orthant lintegral.**  For `σ` a permutation of
`Fin n`, the integral of `f` over the orthant `Iic b` equals the integral of
`y ↦ f (fun l => y (σ.symm l))` over the permuted orthant `Iic (fun k => b (σ k))`. -/
theorem lintegral_Iic_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ x in Set.Iic b, f x
      = ∫⁻ y in Set.Iic (fun k => b (σ k)), f (fun l => y (σ.symm l)) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ
  have h := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).measurableEmbedding f (Set.Iic b)
  rw [preimage_perm_Iic] at h
  simp_rw [piCongrLeft_const_apply] at h
  exact h.symm

/-- **Signed form of `lintegral_Iic_perm`; no integrability hypothesis is needed.** -/
theorem integral_Iic_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x in Set.Iic b, f x
      = ∫ y in Set.Iic (fun k => b (σ k)), f (fun l => y (σ.symm l)) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).measurableEmbedding f (Set.Iic b)
  rw [preimage_perm_Iic] at h
  simp_rw [piCongrLeft_const_apply] at h
  exact h.symm

/-- **Integrability transports along the coordinate permutation.** -/
theorem integrableOn_Iic_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (b : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    IntegrableOn f (Set.Iic b) volume
      ↔ IntegrableOn (fun y => f (fun l => y (σ.symm l))) (Set.Iic (fun k => b (σ k))) volume := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ
  have h := hmp.integrableOn_comp_preimage
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).measurableEmbedding (f := f)
    (s := Set.Iic b)
  rw [preimage_perm_Iic] at h
  have hfun : (f ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ))
      = fun y => f (fun l => y (σ.symm l)) := by
    funext y
    simp only [Function.comp_apply, piCongrLeft_const_apply]
  rw [hfun] at h
  exact h.symm

/-- **Any ordered pair of distinct coordinates can be moved to positions `0, 1`.**  Take
`σ₁ = swap 0 i`, which sends `0` to `i`, and `k = σ₁.symm j ≠ 0`; then
`σ = σ₁ * swap 1 k` sends `0 ↦ i` and `1 ↦ j`. -/
theorem exists_perm_zero_one {m : ℕ} (i j : Fin (m + 2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j := by
  set σ₁ : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 i with hσ₁
  set k : Fin (m + 2) := σ₁.symm j with hk
  have hσ₁k : σ₁ k = j := by rw [hk]; exact σ₁.apply_symm_apply j
  have hσ₁0 : σ₁ 0 = i := by rw [hσ₁]; exact Equiv.swap_apply_left 0 i
  have hk0 : k ≠ 0 := by
    intro h
    apply hij
    rw [← hσ₁0, ← hσ₁k, h]
  refine ⟨σ₁ * Equiv.swap 1 k, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Ne.symm hk0)]
    exact hσ₁0
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact hσ₁k

end LatticeProb
