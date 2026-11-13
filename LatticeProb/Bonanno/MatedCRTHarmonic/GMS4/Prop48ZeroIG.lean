/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48ZeroIG at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ConeDisk
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.BundleIG

/-! The 0-cone field is independent of the imaginary-geometry data. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set Metric LQGMetric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.MatedCRT LQGMetric.Blueprint

/-- The actual 0-cone field in the frozen coupling is independent of its IG
field. This is the 0-cone counterpart of `GMSCM.IsMatingOfTreesCoupling.indepFun_coneField_hIG`. -/
theorem prop48_zeroCone_indepFun_IGdata
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))
      (fun ω => (hIG₀ ω, U ω)) P := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B₀'
  have hIGcones : IndepFun (fun ω => (hIG₀ ω, U ω))
      (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω))) P :=
    D.indep_curve
  let coneXBB : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
    fun q => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2))
  have hconeXBB : Measurable coneXBB :=
    (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
       (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  have hIGXBB : IndepFun (fun ω => (hIG₀ ω, U ω)) (fun ω =>
      (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    hIGcones.comp measurable_id hconeXBB
  have hpath : (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) =ᵐ[P]
      fun ω => (X₀ ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hIGXBc : IndepFun (fun ω => (hIG₀ ω, U ω))
      (fun ω => (X₀ ω, (Bc ω, Bc' ω))) P :=
    IGLaw.indepFun_triple_continuousMap_of_coe
      (hIGXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ 0 (Bc ω, Bc' ω)
  have hIGXW : IndepFun (fun ω => (hIG₀ ω, U ω))
      (fun ω => (X₀ ω, W ω)) P :=
    hIGXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ 0).comp measurable_snd))
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B₀.eval_zero_ae_eq_zero,
      D.bm_B₀'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B₀'
        (show 0 < CellScaling.lqgQ γ - 0 by simpa using IGLaw.lqgQ_pos' hγ.1)]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B₀ s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B₀' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ 0 (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun (fun ω =>
      ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω))
      (fun ω => (hIG₀ ω, U ω)) P :=
    (hIGXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  unfold CellScaling.coneField ConeScaling.fieldOf
  congr 2
  funext z
  simpa only [ConeScaling.radialOf] using hω (-Real.log ‖z‖)

/-- The joint restriction of the actual 0-cone field and its IG input has
The same law as a normalized whole-plane GFF sampled independently of that
IG input. This is the field-law transfer used in [18] immediately after
Proposition 4.8. -/
theorem prop48_zeroCone_disk_IGdata_law_eq_wholePlaneGFF
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    (hind : IndepFun h (fun ω => (hIG₀ ω, U ω)) P) :
    P.map (fun ω => (restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω))), (hIG₀ ω, U ω))) =
      P.map (fun ω => (restrictTo (ballO 0 1) (h ω),
        (hIG₀ ω, U ω))) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hraw : AEMeasurable (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) P :=
    aemeasurable_prop48ZeroConeField D
  have hfield₀ : AEMeasurable (fun ω => restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hraw
  have hfield₁ : AEMeasurable (fun ω => restrictTo (ballO 0 1) (h ω)) P :=
    ((measurable_restrictTo _).comp hh.1.measurable).aemeasurable
  have hU : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif
      (IGLaw.period_pos_of_uniform D.igField.2.1) D.igField.2.1
  have hIGdata : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P :=
    D.igField.1.1.measurable.aemeasurable.prodMk hU
  have hind₀ : IndepFun (fun ω => restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω))))
      (fun ω => (hIG₀ ω, U ω)) P :=
    (prop48_zeroCone_indepFun_IGdata D hγ).comp (measurable_restrictTo _) measurable_id
  have hind₁ : IndepFun (fun ω => restrictTo (ballO 0 1) (h ω))
      (fun ω => (hIG₀ ω, U ω)) P :=
    hind.comp (measurable_restrictTo _) measurable_id
  exact prop48_jointLocalLaw_of_indep_ae hfield₀ hfield₁ hIGdata hIGdata
    (prop48_zeroCone_disk_law_eq_wholePlaneGFF D hγ hh) rfl hind₀ hind₁

end MatedCRTHarmonic.GMS4

