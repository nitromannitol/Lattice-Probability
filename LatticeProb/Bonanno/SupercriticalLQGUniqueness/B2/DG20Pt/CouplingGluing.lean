/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.CouplingGluing at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.CondDistrib

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Pt

variable {Ω₁ Ω₂ α β : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

 

def dg20GlueMeasure (P : Measure Ω₁) (Q : Measure Ω₂) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (X : Ω₁ → α) (Y : Ω₂ → α) (Z : Ω₂ → β)
    (hX : Measurable X) : Measure (Ω₁ × β) :=
  P ⊗ₘ (condDistrib Z Y Q).comap X hX

instance (P : Measure Ω₁) (Q : Measure Ω₂) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (X : Ω₁ → α) (Y : Ω₂ → α) (Z : Ω₂ → β)
    (hX : Measurable X) : IsProbabilityMeasure (dg20GlueMeasure P Q X Y Z hX) := by
  unfold dg20GlueMeasure
  infer_instance

theorem dg20GlueMeasure_fst (P : Measure Ω₁) (Q : Measure Ω₂)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω₁ → α) (Y : Ω₂ → α) (Z : Ω₂ → β) (hX : Measurable X) :
    (dg20GlueMeasure P Q X Y Z hX).map Prod.fst = P := by
  exact Measure.fst_compProd P _

 
theorem dg20GlueMeasure_joint (P : Measure Ω₁) (Q : Measure Ω₂)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω₁ → α) (Y : Ω₂ → α) (Z : Ω₂ → β)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hlaw : P.map X = Q.map Y) :
    (dg20GlueMeasure P Q X Y Z hX).map (fun p => (X p.1, p.2)) =
      Q.map (fun ω => (Y ω, Z ω)) := by
  have hm : Measurable (fun p : Ω₁ × β => (X p.1, p.2)) :=
    (hX.comp measurable_fst).prodMk measurable_snd
  refine Measure.ext_prod (fun {s t} hs ht => ?_)
  rw [Measure.map_apply hm (hs.prod ht), Measure.map_apply (hY.prodMk hZ) (hs.prod ht)]
  have h1 : (fun p : Ω₁ × β => (X p.1, p.2)) ⁻¹' (s ×ˢ t) =
      (X ⁻¹' s) ×ˢ t := by ext; simp
  have h2 : (fun ω : Ω₂ => (Y ω, Z ω)) ⁻¹' (s ×ˢ t) =
      Y ⁻¹' s ∩ Z ⁻¹' t := by ext; simp
  rw [h1, h2, dg20GlueMeasure, Measure.compProd_apply_prod (hX hs) ht]
  simp only [Kernel.comap_apply]
  have hKt : Measurable (fun x => condDistrib Z Y Q x t) :=
    (condDistrib Z Y Q).measurable_coe ht
  rw [← setLIntegral_map hs hKt hX, hlaw]
  rw [setLIntegral_map hs hKt hY]
  exact setLIntegral_preimage_condDistrib (μ := Q) hY hZ.aemeasurable ht hs

end SupercriticalLQGUniqueness.B2.DG20Pt
