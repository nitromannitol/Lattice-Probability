import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Independent random null sections -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

/-- A measurable random section that is null for a reference measure is also
null for an independent finite random measure when every fixed null section is
almost surely null for that measure. -/
theorem ae_kernel_section_eq_zero_of_indepFun
    {Ω A B E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun Y X P) (κ : Kernel A E) (hκ : ∀ a, IsFiniteMeasure (κ a))
    (ν : Measure E) [SFinite ν] {S : Set (B × E)} (hS : MeasurableSet S)
    (hfixed : ∀ b, ν (Prod.mk b ⁻¹' S) = 0 →
      ∀ᵐ ω ∂P, κ (X ω) (Prod.mk b ⁻¹' S) = 0)
    (hnull : ∀ᵐ ω ∂P, ν (Prod.mk (Y ω) ⁻¹' S) = 0) :
    ∀ᵐ ω ∂P, κ (X ω) (Prod.mk (Y ω) ⁻¹' S) = 0 := by
  let K : Kernel (B × A) E := ⟨fun p => κ p.2, κ.measurable.comp measurable_snd⟩
  let T : Set ((B × A) × E) := {p | (p.1.1, p.2) ∈ S}
  have hT : MeasurableSet T := (measurable_fst.fst.prodMk measurable_snd) hS
  have hm : Measurable (fun p : B × A => κ p.2 (Prod.mk p.1 ⁻¹' S)) := by
    change Measurable (fun p : B × A => K p (Prod.mk p ⁻¹' T))
    exact Kernel.measurable_kernel_prodMk_left_of_finite hT (fun p => hκ p.2)
  have hb : Measurable (fun b : B => ν (Prod.mk b ⁻¹' S)) :=
    measurable_measure_prodMk_left hS
  have hn : ∀ᵐ b ∂P.map Y, ν (Prod.mk b ⁻¹' S) = 0 :=
    (ae_map_iff hY.aemeasurable (hb (measurableSet_singleton 0))).2 hnull
  have hp : ∀ᵐ p ∂(P.map Y).prod (P.map X), κ p.2 (Prod.mk p.1 ⁻¹' S) = 0 := by
    apply (Measure.ae_prod_iff_ae_ae (hm (measurableSet_singleton 0))).2
    filter_upwards [hn] with b hb0
    exact (ae_map_iff hX.aemeasurable
      ((κ.measurable_coe (measurable_prodMk_left hS)) (measurableSet_singleton 0))).2
      (hfixed b hb0)
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).1 hind
  rw [← hlaw] at hp
  exact ae_of_ae_map (hY.prodMk hX).aemeasurable hp

end LatticeProb
