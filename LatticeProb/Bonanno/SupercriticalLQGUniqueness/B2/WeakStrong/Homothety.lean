/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.WeakStrong.Homothety at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInstMeasurableSpace
import LatticeProb.Bonanno.SLUMetricAPI

 













set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 

theorem eVariationOn_comp_isometry {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {ψ : X → Y} (hψ : Isometry ψ) (f : ℝ → X) (s : Set ℝ) :
    eVariationOn (ψ ∘ f) s = eVariationOn f s := by
  simp only [eVariationOn, Function.comp_apply, hψ.edist_eq]

def dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : LSCMetric :=
  ⟨fun p => M (c • p.1, c • p.2),
    ⟨fun x => M.isExtMetric.1 _,
      fun x y h => smul_right_injective ℂ hc (M.isExtMetric.2.1 _ _ h),
      fun x y => M.isExtMetric.2.2.1 _ _,
      fun x y z => M.isExtMetric.2.2.2 _ _ _⟩,
    M.lowerSemicontinuous.comp
      (show Continuous fun p : ℂ × ℂ => (c • p.1, c • p.2) by fun_prop)⟩

theorem dilateM_apply (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (p : ℂ × ℂ) :
    dilateM M c hc p = M (c • p.1, c • p.2) := rfl

def homPt (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : (dilateM M c hc).Space → M.Space :=
  fun z => M.pt (c • (show ℂ from z))

theorem isometry_homPt (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : Isometry (homPt M c hc) :=
  fun _ _ => rfl

theorem homPt_comp (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) :
    homPt M c hc ∘ ((dilateM M c hc).pt ∘ P) = M.pt ∘ fun t => c • P t := rfl

theorem isCurve_dilateM_iff (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) (a b : ℝ) :
    (dilateM M c hc).IsCurve P a b ↔ M.IsCurve (fun t => c • P t) a b := by
  refine and_congr_right fun _ => ?_
  rw [(isometry_homPt M c hc).isEmbedding.continuousOn_iff, homPt_comp]

theorem len_dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) (a b : ℝ) :
    (dilateM M c hc).len P a b = M.len (fun t => c • P t) a b := by
  change eVariationOn _ _ = eVariationOn _ _
  rw [← homPt_comp, eVariationOn_comp_isometry (isometry_homPt M c hc)]

theorem smul_inv_smul_fun {c : ℝ} (hc : c ≠ 0) (Q : ℝ → ℂ) :
    (fun t => c • (fun t => c⁻¹ • Q t) t) = Q :=
  funext fun t => smul_inv_smul₀ hc (Q t)

 
theorem internal_dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (Y Y' : Set ℂ)
    (hY : ∀ z, c • z ∈ Y' ↔ z ∈ Y) (p : Y × Y) :
    (dilateM M c hc).internal Y p =
      M.internal Y' (⟨c • p.1.1, (hY _).2 p.1.2⟩, ⟨c • p.2.1, (hY _).2 p.2.2⟩) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQY => le_iInf fun hQa => le_iInf fun hQb => ?_
    have h1 : (dilateM M c hc).IsCurve (fun t => c⁻¹ • Q t) a b := by
      rw [isCurve_dilateM_iff, smul_inv_smul_fun hc]; exact hQ
    have h2 : ∀ t ∈ Icc a b, (fun t => c⁻¹ • Q t) t ∈ Y := by
      intro t ht
      rw [← hY, smul_inv_smul₀ hc]
      exact hQY t ht
    have h3 : (fun t => c⁻¹ • Q t) a = (p.1 : ℂ) := by simp only [hQa, inv_smul_smul₀ hc]
    have h4 : (fun t => c⁻¹ • Q t) b = (p.2 : ℂ) := by simp only [hQb, inv_smul_smul₀ hc]
    calc (dilateM M c hc).internal Y p ≤ (dilateM M c hc).len (fun t => c⁻¹ • Q t) a b :=
          iInf_le_of_le (fun t => c⁻¹ • Q t) <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = M.len Q a b := by rw [len_dilateM, smul_inv_smul_fun hc]
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPY => le_iInf fun hPa => le_iInf fun hPb => ?_
    have h1 : M.IsCurve (fun t => c • P t) a b := (isCurve_dilateM_iff M c hc P a b).1 hP
    have h2 : ∀ t ∈ Icc a b, (fun t => c • P t) t ∈ Y' := fun t ht => (hY _).2 (hPY t ht)
    have h3 : (fun t => c • P t) a = c • (p.1 : ℂ) := by simp only [hPa]
    have h4 : (fun t => c • P t) b = c • (p.2 : ℂ) := by simp only [hPb]
    calc M.internal Y' (⟨c • p.1.1, (hY _).2 p.1.2⟩, ⟨c • p.2.1, (hY _).2 p.2.2⟩)
          ≤ M.len (fun t => c • P t) a b :=
          iInf_le_of_le (fun t => c • P t) <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = (dilateM M c hc).len P a b := by rw [len_dilateM]

 

instance instBorelSpaceLSCMetric : BorelSpace LSCMetric := ⟨rfl⟩

 
end SupercriticalLQGUniqueness.B2.WeakStrong
