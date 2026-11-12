import Mathlib.Probability.IdentDistrib

/-!
# Joint laws through the events of one coordinate

Let `Z, W` be random elements under `P` and `Z', W'` under `Q`, with `Z, Z'` measurable. The pairs `(Z, W)` and
`(Z', W')` have the same law if and only if, for every measurable set `A`, the random element `W` under `P` restricted
to `{Z ∈ A}` has the same law as `W'` under `Q` restricted to `{Z' ∈ A}`
(`identDistrib_prodMk_iff_forall_restrict`).

The proof compares the two laws on measurable boxes `A ×ˢ B`, a π-system generating the product σ-algebra
(`generateFrom_prod`, `isPiSystem_prod`, `MeasureTheory.ext_of_generate_finite`).

Use: a statement "`W` has the same law in two realizations", proved for arbitrary finite measures, upgrades to the
joint law of `W` with an extra coordinate `Z` whose joint law with the inputs of the statement is known, by applying
the statement to the restricted measures.
-/

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

variable {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β] [MeasurableSpace γ]
  {P : Measure Ω} {Q : Measure Ω'} {Z : Ω → β} {W : Ω → γ} {Z' : Ω' → β} {W' : Ω' → γ}

/-- The law of `(Z, W)` on a box is the law of `W` on the event `{Z ∈ A}`. -/
theorem map_prodMk_apply_prod_eq_restrict (hZ : Measurable Z) (hW : AEMeasurable W P) {A : Set β}
    (hA : MeasurableSet A) {B : Set γ} (hB : MeasurableSet B) :
    P.map (fun ω => (Z ω, W ω)) (A ×ˢ B) = (P.restrict (Z ⁻¹' A)).map W B := by
  rw [Measure.map_apply_of_aemeasurable (hZ.aemeasurable.prodMk hW) (hA.prod hB),
    Measure.map_apply_of_aemeasurable hW.restrict hB, Measure.restrict_apply' (hZ hA), mk_preimage_prod,
    inter_comm]

/-- **Restricted laws from a joint law.** If `(Z, W)` and `(Z', W')` have the same law, then for every measurable
`A`, `W` on `{Z ∈ A}` and `W'` on `{Z' ∈ A}` have the same law. -/
theorem identDistrib_restrict_preimage_of_prodMk (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (Z ω, W ω)) (fun ω => (Z' ω, W' ω)) P Q) {A : Set β} (hA : MeasurableSet A) :
    IdentDistrib W W' (P.restrict (Z ⁻¹' A)) (Q.restrict (Z' ⁻¹' A)) := by
  have hW : AEMeasurable W P := measurable_snd.comp_aemeasurable h.aemeasurable_fst
  have hW' : AEMeasurable W' Q := measurable_snd.comp_aemeasurable h.aemeasurable_snd
  refine ⟨hW.restrict, hW'.restrict, Measure.ext fun B hB => ?_⟩
  rw [← map_prodMk_apply_prod_eq_restrict hZ hW hA hB, ← map_prodMk_apply_prod_eq_restrict hZ' hW' hA hB,
    h.map_eq]

/-- **Joint law from restricted laws.** For a finite measure `P`, if for every measurable `A` the random element `W`
on `{Z ∈ A}` has the same law as `W'` on `{Z' ∈ A}`, then `(Z, W)` and `(Z', W')` have the same law. -/
theorem identDistrib_prodMk_of_forall_restrict [IsFiniteMeasure P] (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : ∀ A : Set β, MeasurableSet A → IdentDistrib W W' (P.restrict (Z ⁻¹' A)) (Q.restrict (Z' ⁻¹' A))) :
    IdentDistrib (fun ω => (Z ω, W ω)) (fun ω => (Z' ω, W' ω)) P Q := by
  have hW : AEMeasurable W P := by
    simpa using (h univ MeasurableSet.univ).aemeasurable_fst
  have hW' : AEMeasurable W' Q := by
    simpa using (h univ MeasurableSet.univ).aemeasurable_snd
  refine ⟨hZ.aemeasurable.prodMk hW, hZ'.aemeasurable.prodMk hW', ?_⟩
  have hbox : ∀ A : Set β, MeasurableSet A → ∀ B : Set γ, MeasurableSet B →
      P.map (fun ω => (Z ω, W ω)) (A ×ˢ B) = Q.map (fun ω => (Z' ω, W' ω)) (A ×ˢ B) := by
    intro A hA B hB
    rw [map_prodMk_apply_prod_eq_restrict hZ hW hA hB, map_prodMk_apply_prod_eq_restrict hZ' hW' hA hB,
      (h A hA).map_eq]
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hbox A hA B hB
  · rw [← univ_prod_univ]
    exact hbox univ MeasurableSet.univ univ MeasurableSet.univ

/-- **Joint laws through the events of one coordinate.** For a finite measure `P` and measurable `Z, Z'`, the pairs
`(Z, W)` and `(Z', W')` have the same law if and only if `W` on `{Z ∈ A}` and `W'` on `{Z' ∈ A}` have the same law for
every measurable `A`. -/
theorem identDistrib_prodMk_iff_forall_restrict [IsFiniteMeasure P] (hZ : Measurable Z) (hZ' : Measurable Z') :
    IdentDistrib (fun ω => (Z ω, W ω)) (fun ω => (Z' ω, W' ω)) P Q ↔
      ∀ A : Set β, MeasurableSet A → IdentDistrib W W' (P.restrict (Z ⁻¹' A)) (Q.restrict (Z' ⁻¹' A)) :=
  ⟨fun h _ hA => identDistrib_restrict_preimage_of_prodMk hZ hZ' h hA, identDistrib_prodMk_of_forall_restrict hZ hZ'⟩

end LatticeProb
