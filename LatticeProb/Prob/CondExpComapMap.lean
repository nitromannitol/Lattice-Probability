import Mathlib

/-!
# Conditional expectation given a pulled-back σ-algebra, computed on the image space

If `π : Ω → Ω'` is measurable, `G` is a σ-algebra on `Ω'` and `F` is a bounded measurable function on
`Ω'`, then the conditional expectation of `F ∘ π` given `σ(π⁻¹ G)` (the comap σ-algebra) is the
conditional expectation of `F` on the image space `(Ω', π_* μ)` given `G`, composed with `π`.  This lets
one compute the conditional expectation of a function of one coordinate of a product space, given a
σ-algebra of that coordinate, from the law of the coordinate alone.
-/

open MeasureTheory

namespace LatticeProb

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {G m' : MeasurableSpace Ω'}

/-- **Conditional expectation of a function of a coordinate, given a σ-algebra of the coordinate.**
For measurable `π : Ω → Ω'`, a sub-σ-algebra `G ≤ m'` and a bounded measurable `F : Ω' → ℝ`,
`E_μ[F ∘ π | π⁻¹ G] = E_{π_* μ}[F | G] ∘ π` almost everywhere. -/
theorem condExp_comp_comap_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] {π : Ω → Ω'}
    (hπ : Measurable π) (hG : G ≤ m') {F : Ω' → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    μ[fun ω => F (π ω) | G.comap π] =ᵐ[μ] fun ω => ((μ.map π)[F | G]) (π ω) := by
  have hGle : G.comap π ≤ m := (MeasurableSpace.comap_mono hG).trans hπ.comap_le
  have hFm : Measurable fun ω => F (π ω) := hF.comp hπ
  have hFint' : Integrable F (μ.map π) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hint : Integrable (fun ω => F (π ω)) μ :=
    (integrable_map_measure hF.aestronglyMeasurable hπ.aemeasurable).1 hFint'
  set g : Ω' → ℝ := (μ.map π)[F | G] with hg
  have hgG : Measurable[G] g := stronglyMeasurable_condExp.measurable
  have hgm : Measurable g := hgG.mono hG le_rfl
  have hgint' : Integrable g (μ.map π) := integrable_condExp
  have hgint : Integrable (fun ω => g (π ω)) μ :=
    (integrable_map_measure hgm.aestronglyMeasurable hπ.aemeasurable).1 hgint'
  have hgcomap : Measurable[G.comap π] fun ω => g (π ω) := hgG.comp (comap_measurable π)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hGle hint (fun s _ _ => hgint.integrableOn) ?_
    hgcomap.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨A, hA, rfl⟩ := hs
  have hAm : MeasurableSet A := hG _ hA
  calc ∫ ω in π ⁻¹' A, g (π ω) ∂μ = ∫ y in A, g y ∂(μ.map π) :=
        (setIntegral_map hAm hgm.aestronglyMeasurable hπ.aemeasurable).symm
    _ = ∫ y in A, F y ∂(μ.map π) := setIntegral_condExp hG hFint' hA
    _ = ∫ ω in π ⁻¹' A, F (π ω) ∂μ := setIntegral_map hAm hF.aestronglyMeasurable hπ.aemeasurable

end LatticeProb
