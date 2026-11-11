import Mathlib
import LatticeProb.Prob.PhaseTorus

/-!
# Ergodicity of the product of a multiplication map on the circle with an ergodic map

Let `n ≥ 2`, let `(Y, ν)` be an s-finite measure space and `S : Y → Y` an ergodic map. Then the skew-free product
`(θ, y) ↦ (n • θ, S y)` on `AddCircle T × Y` is ergodic for the product of the Haar measure with `ν`
(`ergodic_prodMap_nsmul`). Applying this twice gives the ergodicity of the doubling map of the two-dimensional torus
times an ergodic map (`phaseTorusDoublingProductErgodic`), which is the statement
`PhaseTorusDoublingProductErgodic` of `LatticeProb.Prob.PhaseTorus`.

In the literature this is the fact that the product of a (weakly) mixing map with an ergodic map is ergodic: Walters,
*An Introduction to Ergodic Theory* (GTM 79), Section 1.6 and Theorem 1.27; Einsiedler and Ward, *Ergodic Theory with a
View towards Number Theory*, Theorem 2.36.

Route. Let `A` be an invariant measurable set, with sections `A_y = {θ | (θ, y) ∈ A}`. Invariance gives
`A_y = (n ^ k • ·) ⁻¹' A_{S^[k] y}` for every `k`, so each section is invariant under the translations by the points of
order `n ^ k`. A null-measurable subset of the circle which is invariant under translations by points of unbounded
order is null or conull (`AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`, a consequence of the Lebesgue density
theorem). Hence the measure of the section `y ↦ |A_y|` takes for every `y` the value zero or the full value; it is
`S`-invariant because multiplication by `n` preserves the Haar measure. By the ergodicity of `S`, almost every section
is null or almost every section is conull, and Tonelli's theorem concludes.
-/

open MeasureTheory Filter Set
open scoped Pointwise ENNReal

namespace LatticeProb.Prob

universe u

section AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- A null-measurable subset of the circle which is, for every `k`, a preimage under multiplication by `n ^ k`
(`n ≥ 2`) is null or conull. -/
theorem ae_empty_or_univ_of_forall_eq_preimage_pow_nsmul {n : ℕ} (hn : 1 < n) {s : Set (AddCircle T)}
    (hs : NullMeasurableSet s volume)
    (h : ∀ k : ℕ, ∃ t : Set (AddCircle T), s = (fun θ : AddCircle T => n ^ k • θ) ⁻¹' t) :
    s =ᵐ[volume] (∅ : Set (AddCircle T)) ∨ s =ᵐ[volume] univ := by
  have hn0 : ∀ k : ℕ, 0 < n ^ k := fun k => pow_pos (by omega) k
  have hord : ∀ k : ℕ, addOrderOf ((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T) = n ^ k :=
    fun k => AddCircle.addOrderOf_period_div (hn0 k)
  refine AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self hs (l := atTop)
    (u := fun k : ℕ => ((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T)) (fun k => ?_) ?_
  · obtain ⟨t, ht⟩ := h k
    have hz : n ^ k • ((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T) = 0 := by
      have h0 := addOrderOf_nsmul_eq_zero ((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T)
      rwa [hord k] at h0
    have hEq : (((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T) +ᵥ s : Set (AddCircle T)) = s := by
      ext θ
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, ht]
      simp only [Set.mem_preimage, vadd_eq_add, smul_add, smul_neg, hz, neg_zero, zero_add]
    rw [hEq]
  · have hfun : (addOrderOf ∘ fun k : ℕ => ((T / ((n ^ k : ℕ) : ℝ) : ℝ) : AddCircle T)) = fun k => n ^ k :=
      funext hord
    rw [hfun]
    exact tendsto_atTop_mono (fun k => (Nat.lt_pow_self hn).le) tendsto_id

/-- **Product of a multiplication map on the circle with an ergodic map.** For `n ≥ 2` and an ergodic map `S` of an
s-finite measure space `(Y, ν)`, the map `(θ, y) ↦ (n • θ, S y)` is ergodic for the product of the Haar measure of
the circle with `ν`. -/
theorem ergodic_prodMap_nsmul {Y : Type*} [MeasurableSpace Y] {n : ℕ} (hn : 1 < n) {ν : Measure Y} [SFinite ν]
    {S : Y → Y} (hS : Ergodic S ν) :
    Ergodic (Prod.map (fun θ : AddCircle T => n • θ) S) ((volume : Measure (AddCircle T)).prod ν) := by
  have hD : Ergodic (fun θ : AddCircle T => n • θ) volume := AddCircle.ergodic_nsmul hn
  refine ⟨hD.toMeasurePreserving.prod hS.toMeasurePreserving, ⟨fun A hA hinv => ?_⟩⟩
  -- invariance of `A`, pointwise and iterated
  have h1 : ∀ (θ : AddCircle T) (y : Y), (θ, y) ∈ A ↔ (n • θ, S y) ∈ A := by
    intro θ y
    have h : (θ, y) ∈ Prod.map (fun θ : AddCircle T => n • θ) S ⁻¹' A ↔ (θ, y) ∈ A := by rw [hinv]
    exact h.symm
  have hmem : ∀ (k : ℕ) (θ : AddCircle T) (y : Y), (θ, y) ∈ A ↔ (n ^ k • θ, S^[k] y) ∈ A := by
    intro k
    induction k with
    | zero => intro θ y; simp
    | succ k ih =>
      intro θ y
      rw [h1 θ y, ih (n • θ) (S y), pow_succ, mul_smul, Function.iterate_succ_apply]
  have hsecMeas : ∀ y : Y, MeasurableSet ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) :=
    fun y => measurable_prodMk_right hA
  -- every section is null or conull
  have hdich : ∀ y : Y, volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0 ∨
      volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A)ᶜ = 0 := by
    intro y
    have h := ae_empty_or_univ_of_forall_eq_preimage_pow_nsmul hn (hsecMeas y).nullMeasurableSet
      (fun k => ⟨(fun θ : AddCircle T => (θ, S^[k] y)) ⁻¹' A, by ext θ; exact hmem k θ y⟩)
    rwa [ae_eq_empty, ae_eq_univ] at h
  -- the measure of the section is invariant
  have hmS : ∀ y : Y, volume ((fun θ : AddCircle T => (θ, S y)) ⁻¹' A)
      = volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) := by
    intro y
    have hsec : (fun θ : AddCircle T => (θ, y)) ⁻¹' A
        = (fun θ : AddCircle T => n • θ) ⁻¹' ((fun θ : AddCircle T => (θ, S y)) ⁻¹' A) := by
      ext θ; exact h1 θ y
    rw [hsec]
    exact (hD.toMeasurePreserving.measure_preimage (hsecMeas (S y)).nullMeasurableSet).symm
  have hmMeas : Measurable fun y : Y => volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) :=
    measurable_measure_prodMk_right hA
  -- the set of null sections is invariant
  have hBmeas : MeasurableSet {y : Y | volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0} :=
    hmMeas (measurableSet_singleton 0)
  have hBinv : S ⁻¹' {y : Y | volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0}
      = {y : Y | volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0} := by
    ext y
    show volume ((fun θ : AddCircle T => (θ, S y)) ⁻¹' A) = 0 ↔ volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0
    rw [hmS y]
  suffices key : (volume : Measure (AddCircle T)).prod ν A = 0 ∨ (volume : Measure (AddCircle T)).prod ν Aᶜ = 0 from
    eventuallyEmptyOrUniv_iff'.2 (key.imp ae_eq_empty.2 ae_eq_univ.2)
  rcases hS.toPreErgodic.measure_self_or_compl_eq_zero hBmeas hBinv with hB | hB
  · -- almost every section is conull
    right
    rw [Measure.prod_apply_symm hA.compl, lintegral_eq_zero_iff
      (measurable_measure_prodMk_right hA.compl)]
    have hB' : ∀ᵐ y ∂ν, ¬ volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0 :=
      measure_eq_zero_iff_ae_notMem.1 hB
    filter_upwards [hB'] with y hy
    exact (hdich y).resolve_left hy
  · -- almost every section is null
    left
    rw [Measure.prod_apply_symm hA, lintegral_eq_zero_iff hmMeas]
    have hB' : ∀ᵐ y ∂ν, volume ((fun θ : AddCircle T => (θ, y)) ⁻¹' A) = 0 := by
      have h := measure_eq_zero_iff_ae_notMem.1 hB
      filter_upwards [h] with y hy
      exact not_not.1 hy
    filter_upwards [hB'] with y hy
    exact hy

end AddCircle

/-- **Ergodicity of the doubling map of the torus times an ergodic map.** For every probability space `(Y, ν)` and
every measure-preserving ergodic map `R : Y → Y`, the map `(θ, θ', y) ↦ (2θ, 2θ', R y)` is ergodic for the product
of the Haar measure of the two-dimensional torus with `ν`. -/
theorem phaseTorusDoublingProductErgodic : PhaseTorusDoublingProductErgodic.{u} := by
  intro Y _ ν _ R _ hR
  have h1 : Ergodic (Prod.map (fun θ : PhaseCircle => 2 • θ) R) ((volume : Measure PhaseCircle).prod ν) :=
    ergodic_prodMap_nsmul one_lt_two hR
  have h2 : Ergodic (Prod.map (fun θ : PhaseCircle => 2 • θ) (Prod.map (fun θ : PhaseCircle => 2 • θ) R))
      ((volume : Measure PhaseCircle).prod ((volume : Measure PhaseCircle).prod ν)) :=
    ergodic_prodMap_nsmul one_lt_two h1
  have he : MeasurePreserving (MeasurableEquiv.prodAssoc : (PhaseCircle × PhaseCircle) × Y ≃ᵐ _)
      (phaseTorusFieldMeasure ν) ((volume : Measure PhaseCircle).prod ((volume : Measure PhaseCircle).prod ν)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hconj : (MeasurableEquiv.prodAssoc : (PhaseCircle × PhaseCircle) × Y ≃ᵐ _) ∘
      (fun p : PhaseTorus × Y => (phaseTorusDouble p.1, R p.2)) ∘
        (MeasurableEquiv.prodAssoc : (PhaseCircle × PhaseCircle) × Y ≃ᵐ _).symm
      = Prod.map (fun θ : PhaseCircle => 2 • θ) (Prod.map (fun θ : PhaseCircle => 2 • θ) R) := by
    funext p
    rfl
  exact he.ergodic_conjugate_iff.1 (hconj ▸ h2)

end LatticeProb.Prob
