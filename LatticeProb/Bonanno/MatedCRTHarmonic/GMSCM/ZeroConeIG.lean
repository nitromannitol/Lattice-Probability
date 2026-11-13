/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.ZeroConeIG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ZeroConeLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.BundleIG

/-!
# Independence of the frozen zero-cone and imaginary-geometry fields

The frozen `indep_curve` clause makes the IG field independent of all cone
data. The zero-cone field is a measurable function of the continuous versions
of its GFF and radial Brownian pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LQGMetric
open scoped NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- The actual frozen zero-cone field is independent of the frozen IG field. -/
theorem IsMatingOfTreesCoupling.indepFun_zeroConeField_hIG
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) hIG₀ P := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version hC.bm_B₀
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version hC.bm_B₀'
  have hIGcones : IndepFun hIG₀
      (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω))) P :=
    hC.indep_curve.comp measurable_fst measurable_id
  let zeroData : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
    fun q => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2))
  have hzeroData : Measurable zeroData := by fun_prop
  have hIGXBB : IndepFun hIG₀ (fun ω =>
      (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    hIGcones.comp measurable_id hzeroData
  have hpath : (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) =ᵐ[P]
      fun ω => (X₀ ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hIGXBc : IndepFun hIG₀ (fun ω => (X₀ ω, (Bc ω, Bc' ω))) P :=
    IGLaw.indepFun_triple_continuousMap_of_coe
      (hIGXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ 0 (Bc ω, Bc' ω)
  have hIGXW : IndepFun hIG₀ (fun ω => (X₀ ω, W ω)) P :=
    hIGXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ 0).comp measurable_snd))
  have hQ0 : 0 < CellScaling.lqgQ γ - 0 := by
    have hq := CellScaling.lqgQ_sub_pos hγ.1 hγ.2
    linarith [hγ.1]
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t := by
    filter_upwards [hBc, hBc', hC.bm_B₀.eval_zero_ae_eq_zero,
      hC.bm_B₀'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hC.bm_B₀' hQ0]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B₀ s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B₀' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ 0 (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ 0 (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun (fun ω =>
      ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)) hIG₀ P :=
    (hIGXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  simp only [CellScaling.coneField, ConeScaling.fieldOf]
  have he : ConeScaling.radialOf (W ω) =
      (fun z : ℂ => CellScaling.coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω) (-Real.log ‖z‖)) := by
    funext z
    exact hω (-Real.log ‖z‖)
  rw [he]

end MatedCRTHarmonic.GMSCM
