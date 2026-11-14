/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RFreeze at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

variable {Ω β γ : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]

 
theorem laneA3R_kernel_rect (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → β} {Y : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {A : Set β} {B : Set γ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, condExpKernel P (mβ.comap X) ω (X ⁻¹' A ∩ Y ⁻¹' B) =
      (A.indicator (fun _ => P (Y ⁻¹' B)) (X ω)) := by
  have hm : mβ.comap X ≤ mΩ := hX.comap_le
  have hXA : MeasurableSet[mβ.comap X] (X ⁻¹' A) := ⟨A, hA, rfl⟩
  have hYB : MeasurableSet (Y ⁻¹' B) := hY hB
  have hs : MeasurableSet (X ⁻¹' A ∩ Y ⁻¹' B) := (hm _ hXA).inter hYB
  have h1 := condExpKernel_ae_eq_condExp (μ := P) hm hs
  have hprod : (X ⁻¹' A ∩ Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) =
      (X ⁻¹' A).indicator (fun _ => (1 : ℝ)) * (Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases ha : ω ∈ X ⁻¹' A <;> by_cases hb : ω ∈ Y ⁻¹' B <;>
      simp [Set.indicator, ha, hb]
  have hSm : StronglyMeasurable[mβ.comap X] ((X ⁻¹' A).indicator (fun _ => (1 : ℝ))) :=
    (stronglyMeasurable_const.indicator hXA)
  have hint1 : Integrable ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hYB
  have hint2 : Integrable ((X ⁻¹' A).indicator (fun _ => (1 : ℝ)) *
      (Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) P := by
    rw [← hprod]; exact (integrable_const (1 : ℝ)).indicator hs
  have h2 := condExp_mul_of_stronglyMeasurable_left hSm hint2 hint1
  have hInd : Indep (mγ.comap Y) (mβ.comap X) P := hXY.symm
  have hfm : StronglyMeasurable[mγ.comap Y] ((Y ⁻¹' B).indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator (show MeasurableSet[mγ.comap Y] (Y ⁻¹' B) from
      ⟨B, hB, rfl⟩)
  have h3 := condExp_indep_eq (μ := P) hY.comap_le hm hfm hInd
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  have hreal : (condExpKernel P (mβ.comap X) ω).real (X ⁻¹' A ∩ Y ⁻¹' B) =
      (X ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω * P.real (Y ⁻¹' B) := by
    rw [e1, hprod, e2]
    simp only [Pi.mul_apply]
    rw [e3, integral_indicator_const _ hYB, smul_eq_mul, mul_one]
  have hfin : condExpKernel P (mβ.comap X) ω (X ⁻¹' A ∩ Y ⁻¹' B) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  change ENNReal.ofReal ((condExpKernel P (mβ.comap X) ω).real (X ⁻¹' A ∩ Y ⁻¹' B)) = _
  rw [hreal]
  by_cases ha : X ω ∈ A
  · have : ω ∈ X ⁻¹' A := ha
    simp [Set.indicator, this, ha, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · have : ω ∉ X ⁻¹' A := ha
    simp [Set.indicator, this, ha]

 
theorem laneA3R_kernel_freeze_set (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → β}
    {Y : Ω → γ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    ∀ C : Set (β × γ), MeasurableSet C →
      ∀ᵐ ω ∂P, condExpKernel P (mβ.comap X) ω ((fun x => (X x, Y x)) ⁻¹' C) =
        (P.map Y) (Prod.mk (X ω) ⁻¹' C) := by
  have hm : mβ.comap X ≤ mΩ := hX.comap_le
  have hXYm : Measurable fun x => (X x, Y x) := hX.prodMk hY
  have : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ω => by simp
  · rintro t ⟨A, hA, B, hB, rfl⟩
    filter_upwards [laneA3R_kernel_rect P hX hY hXY hA hB] with ω hω
    have e1 : (fun x => (X x, Y x)) ⁻¹' (A ×ˢ B) = X ⁻¹' A ∩ Y ⁻¹' B := by
      ext x; simp
    rw [e1, hω]
    by_cases ha : X ω ∈ A
    · have e2 : Prod.mk (X ω) ⁻¹' (A ×ˢ B) = B := by ext y; simp [ha]
      rw [e2, Measure.map_apply hY hB]
      simp [Set.indicator, ha]
    · have e2 : Prod.mk (X ω) ⁻¹' (A ×ˢ B) = ∅ := by ext y; simp [ha]
      rw [e2]
      simp [Set.indicator, ha]
  · intro t htm ht
    filter_upwards [ht] with ω hω
    rw [preimage_compl, preimage_compl, prob_compl_eq_one_sub (hXYm htm),
      prob_compl_eq_one_sub (measurable_prodMk_left htm), hω]
  · intro f hdisj hfm hf
    filter_upwards [ae_all_iff.mpr hf] with ω hω
    rw [preimage_iUnion, preimage_iUnion,
      measure_iUnion (fun i j hij => (hdisj hij).preimage _) (fun i => hXYm (hfm i)),
      measure_iUnion (fun i j hij => (hdisj hij).preimage _)
        (fun i => measurable_prodMk_left (hfm i))]
    exact tsum_congr hω

 
theorem laneA3R_kernel_freeze (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → β}
    {Y : Ω → γ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {φ : β × γ → ℝ≥0∞} (hφ : Measurable φ) :
    ∀ᵐ ω ∂P, ∫⁻ x, φ (X x, Y x) ∂(condExpKernel P (mβ.comap X) ω) =
      ∫⁻ y, φ (X ω, y) ∂(P.map Y) := by
  have hXYm : Measurable fun x => (X x, Y x) := hX.prodMk hY
  refine Measurable.ennreal_induction (motive := fun φ => ∀ᵐ ω ∂P,
      ∫⁻ x, φ (X x, Y x) ∂(condExpKernel P (mβ.comap X) ω) =
        ∫⁻ y, φ (X ω, y) ∂(P.map Y)) ?_ ?_ ?_ hφ
  · intro c s hs
    filter_upwards [laneA3R_kernel_freeze_set P hX hY hXY s hs] with ω hω
    have e1 : (fun x => s.indicator (fun _ => c) (X x, Y x)) =
        ((fun x => (X x, Y x)) ⁻¹' s).indicator (fun _ => c) := by
      funext x; rfl
    have e2 : (fun y => s.indicator (fun _ => c) (X ω, y)) =
        (Prod.mk (X ω) ⁻¹' s).indicator (fun _ => c) := by
      funext y; rfl
    rw [e1, e2, lintegral_indicator_const (hXYm hs), lintegral_indicator_const
      (measurable_prodMk_left hs), hω]
  · intro f g _ hf hg hfP hgP
    filter_upwards [hfP, hgP] with ω h1 h2
    simp only [Pi.add_apply]
    rw [lintegral_add_left (show Measurable fun x => f (X x, Y x) from hf.comp hXYm),
      lintegral_add_left (show Measurable fun y => f (X ω, y) from hf.comp measurable_prodMk_left),
      h1, h2]
  · intro f hf hmono hfP
    filter_upwards [ae_all_iff.mpr hfP] with ω hω
    rw [lintegral_iSup (f := fun n x => f n (X x, Y x))
        (fun n => (hf n).comp hXYm) (fun i j hij x => hmono hij _),
      lintegral_iSup (f := fun n y => f n (X ω, y))
        (fun n => (hf n).comp measurable_prodMk_left) (fun i j hij x => hmono hij _)]
    exact iSup_congr hω

end SupercriticalLQGUniqueness.B2.DG20Conc
