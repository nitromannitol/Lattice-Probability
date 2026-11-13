/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.GeneralPairBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.GeneralFieldBridge

/-!
# The local cone versus zero-cone pair comparison

The source pair is the frozen γ-cone and IG field, both pulled back by
`z ↦ z+t`. The target is a measurable normalized whole-plane GFF version
of the frozen zero-cone restriction, paired with the original IG field.
Independence makes each joint law a product of its marginals.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric LQGMetric
open LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- The affine comparison in the orientation of [18] (4.16), on an arbitrary
observation region satisfying the cone and Markov circle-separation conditions.
The target is a measurable version of the frozen zero-cone restriction. Both
source fields use the explicit pullback `h ↦ affineComp 1 t h`. -/
theorem IsMatingOfTreesCoupling.exists_affineZeroConeComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (W V : Opens ℂ) (t : ℂ)
    (hK : IsCompact (closure ((affOpens 1 t W : Opens ℂ) : Set ℂ)))
    (hCone : closure ((affOpens 1 t W : Opens ℂ) : Set ℂ) ⊆
      ball (0 : ℂ) 1 \ {0})
    (hWV : W ≤ V) (hKW : IsCompact (closure (W : Set ℂ)))
    (hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ))
    (hadm : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere (-t) 1))
    (hWunit : (W : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    ∃ (hγm h₀m : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF h₀m P ∧
      (fun ω => restrictTo W (coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) =ᵐ[P]
        (fun ω => restrictTo W (h₀m ω)) ∧
      ∃ p q : ℝ, 1 < p ∧
        Nonempty (GMS4c.LocalFieldLawComparison W P P
          (fun ω => affineComp 1 t (hγm ω))
          (fun ω => affineComp 1 t (hIG₀ ω))
          h₀m hIG₀ p q) := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨hγm, Xt, hγmeas, hγae, hXt, pF, hpF, DF, hDF, hLawF, hMomF⟩ :=
    IsMatingOfTreesCoupling.exists_affineFieldComparison hC hγ W V t hK hCone
      hWV hKW hKV hadm hne hV₁ hVR
  obtain ⟨h₀m, h₀norm, h₀ae⟩ :=
    IsMatingOfTreesCoupling.exists_zeroCone_localField_eq hC hγ W hWunit
  obtain ⟨pI, hpI, -, DI, hDI, hLawI, hMomI⟩ :=
    rawTranslate_recentered_local_reverse hC.igField.1 t
      hWV hKW hKV hadm hne hV₁ hVR
  let νF := P.map (fun ω => restrictTo W (affineComp 1 t (hγm ω)))
  let νI := P.map (fun ω => restrictTo W (affineComp 1 t (hIG₀ ω)))
  let μF := P.map (fun ω => restrictTo W (h₀m ω))
  let μI := P.map (fun ω => restrictTo W (hIG₀ ω))
  have hνFmeas : Measurable (fun ω => restrictTo W (affineComp 1 t (hγm ω))) :=
    (measurable_restrictTo W).comp ((measurable_affineComp 1 t).comp hγmeas)
  have hνImeas : Measurable (fun ω => restrictTo W (affineComp 1 t (hIG₀ ω))) :=
    (measurable_restrictTo W).comp ((measurable_affineComp 1 t).comp hC.igField.1.1.measurable)
  have hμFmeas : Measurable (fun ω => restrictTo W (h₀m ω)) :=
    (measurable_restrictTo W).comp h₀norm.1.measurable
  have hμImeas : Measurable (fun ω => restrictTo W (hIG₀ ω)) :=
    (measurable_restrictTo W).comp hC.igField.1.1.measurable
  have hνFprob : IsProbabilityMeasure νF :=
    (Measure.isProbabilityMeasure_map_iff hνFmeas.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure νF := hνFprob
  have hνIprob : IsProbabilityMeasure νI :=
    (Measure.isProbabilityMeasure_map_iff hνImeas.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure νI := hνIprob
  have hXtLaw : P.map (fun ω => restrictTo W (Xt ω)) = μF := by
    have hWhole : P.map Xt = P.map h₀m :=
      CircleAvg.map_eq_of_isNormalizedWPGFF hXt h₀norm
    calc
      P.map (fun ω => restrictTo W (Xt ω)) = (P.map Xt).map (restrictTo W) := by
        rw [Measure.map_map (measurable_restrictTo W) hXt.1.measurable]
        rfl
      _ = (P.map h₀m).map (restrictTo W) := by rw [hWhole]
      _ = μF := by
        rw [Measure.map_map (measurable_restrictTo W) h₀norm.1.measurable]
        rfl
  have hLawF' : μF = νF.withDensity DF := by
    rw [← hXtLaw]
    exact hLawF
  have hIGLaw : P.map (fun ω => restrictTo W (recenteredTranslate hIG₀ t ω)) = μI := by
    have ht := recenteredTranslate_normalized hC.igField.1 t
    calc
      P.map (fun ω => restrictTo W (recenteredTranslate hIG₀ t ω)) =
          (P.map (recenteredTranslate hIG₀ t)).map (restrictTo W) := by
            rw [Measure.map_map (measurable_restrictTo W) ht.1.1.measurable]
            rfl
      _ = (P.map hIG₀).map (restrictTo W) := by rw [ht.2]
      _ = μI := by
        rw [Measure.map_map (measurable_restrictTo W) hC.igField.1.1.measurable]
        rfl
  have hLawI' : μI = νI.withDensity DI := by
    rw [← hIGLaw]
    exact hLawI
  obtain ⟨p, hp, hLawProd, hMomProd⟩ :=
    prod_withDensity_moment νF νI DF DI hDF hDI hpF hpI hMomF hMomI
  have hindγ : IndepFun hγm hIG₀ P :=
    (IsMatingOfTreesCoupling.indepFun_coneField_hIG hC hγ).congr
      hγae (ae_eq_refl _)
  have hindSource : IndepFun
      (fun ω => restrictTo W (affineComp 1 t (hγm ω)))
      (fun ω => restrictTo W (affineComp 1 t (hIG₀ ω))) P :=
    hindγ.comp ((measurable_restrictTo W).comp (measurable_affineComp 1 t))
      ((measurable_restrictTo W).comp (measurable_affineComp 1 t))
  have hsource : P.map (GMS4c.localFieldPair W
      (fun ω => affineComp 1 t (hγm ω))
      (fun ω => affineComp 1 t (hIG₀ ω))) = νF.prod νI :=
    (indepFun_iff_map_prod_eq_prod_map_map hνFmeas.aemeasurable
      hνImeas.aemeasurable).1 hindSource
  have hindZero : IndepFun (fun ω => restrictTo W (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))))
      (fun ω => restrictTo W (hIG₀ ω)) P :=
    (IsMatingOfTreesCoupling.indepFun_zeroConeField_hIG hC hγ).comp
      (measurable_restrictTo W) (measurable_restrictTo W)
  have hindTarget : IndepFun (fun ω => restrictTo W (h₀m ω))
      (fun ω => restrictTo W (hIG₀ ω)) P :=
    hindZero.congr h₀ae (ae_eq_refl _)
  have htarget : P.map (GMS4c.localFieldPair W h₀m hIG₀) = μF.prod μI :=
    (indepFun_iff_map_prod_eq_prod_map_map hμFmeas.aemeasurable
      hμImeas.aemeasurable).1 hindTarget
  refine ⟨hγm, h₀m, hγmeas, hγae, h₀norm, h₀ae,
    p, p.conjExponent, hp, ⟨?_, ?_, (fun z => DF z.1 * DI z.2),
      (hDF.comp measurable_fst).mul (hDI.comp measurable_snd), ?_, ?_,
      Real.HolderConjugate.conjExponent hp⟩⟩
  · exact GMS4c.measurable_localFieldPair W
      ((measurable_affineComp 1 t).comp hγmeas)
      ((measurable_affineComp 1 t).comp hC.igField.1.1.measurable)
  · exact GMS4c.measurable_localFieldPair W h₀norm.1.measurable
      hC.igField.1.1.measurable
  · calc
      P.map (GMS4c.localFieldPair W h₀m hIG₀) = μF.prod μI := htarget
      _ = (νF.withDensity DF).prod (νI.withDensity DI) := by rw [hLawF', hLawI']
      _ = (νF.prod νI).withDensity (fun z => DF z.1 * DI z.2) := hLawProd
      _ = (P.map (GMS4c.localFieldPair W
        (fun ω => affineComp 1 t (hγm ω))
        (fun ω => affineComp 1 t (hIG₀ ω)))).withDensity
          (fun z => DF z.1 * DI z.2) := by rw [hsource]
  · rw [hsource]
    exact hMomProd

end MatedCRTHarmonic.GMSCM
