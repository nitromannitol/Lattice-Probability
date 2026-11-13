/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.BundleIG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ConeLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.Normalized
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OG4Adapter

/-!
# Independence of the frozen cone field and its IG field

The bundle's `indep_curve` factorizes the IG field and all cone data. Passing
through continuous Brownian path versions makes the cone field a measurable
function of that data and preserves independence.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LQGMetric
open scoped NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The actual frozen γ-cone field is independent of the frozen IG field. -/
theorem IsMatingOfTreesCoupling.indepFun_coneField_hIG
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X ω)
      (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) hIG₀ P := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version hC.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version hC.bm_B'
  have hIGcones : IndepFun hIG₀
      (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
        (fun t => B₀ t ω), (fun t => B₀' t ω))) P :=
    hC.indep_curve.comp measurable_fst measurable_id
  let coneXBB : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun q => (q.1, (q.2.1, q.2.2.1))
  have hconeXBB : Measurable coneXBB :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hIGXBB : IndepFun hIG₀ (fun ω =>
      (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P :=
    hIGcones.comp measurable_id hconeXBB
  have hpath : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hIGXBc : IndepFun hIG₀ (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    IGLaw.indepFun_triple_continuousMap_of_coe
      (hIGXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hIGXW : IndepFun hIG₀ (fun ω => (X ω, W ω)) P :=
    hIGXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ γ).comp measurable_snd))
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', hC.bm_B.eval_zero_ae_eq_zero,
      hC.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hC.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)]
        with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ γ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ γ (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ γ (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun (fun ω =>
      ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω)) hIG₀ P :=
    (hIGXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling,
    MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

end MatedCRTHarmonic.GMSCM
