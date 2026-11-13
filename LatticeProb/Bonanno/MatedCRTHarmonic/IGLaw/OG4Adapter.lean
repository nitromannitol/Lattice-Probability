/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OG4Adapter at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import Mathlib.Probability.Independence.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath

/-!
# SLE similarity interface from the bundle and the amended `igMap` clause

G4's `GMS4..SpaceFillingSLEScaleRotationRecenterInput M` (consumed by [18] Proposition 4.10, Cases 3/4) asks,
over a cell model `M`, for the independently sampled Lebesgue-parametrized space-filling SLE with its LQG-area time
change and the Borel law invariance under every similarity `w ↦ z + s e^{iθ} w` (forward pushforward, area time
`s⁻²`, re-rooted at the first visit to the preimage of `0`).

* `affineSLEPathC_eq_affineReroot`: G4's forward transform is the bundle's `affineReroot` with the inverse
  similarity, `affineSLEPathC z s θ = affineReroot (−(s e^{iθ})⁻¹ z) s⁻¹ (−θ)`;
* `IsMatingOfTreesCoupling.map_affineSLEPathC_rotation`: rotations about `0` (`z = 0`, `s = 1`) from the frozen
  bundle alone;
* `IsMatingOfTreesCoupling.sleScaleRotationRecenterInput hC hγ hpos`: the full structure on the bundle's cell model
  `MoTInput.cellModelOfCoupling hC hγ`, from the frozen bundle and `IGMapPositiveRadii` (scale and recentering need
  the amended clause, `OCounter`). The field/curve independence uses the measurable continuous radial path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.IGLaw

open LQGMetric MatedCRTHarmonic.MatedCRT

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- Under the amended clause the similarity transforms of `ηL` are a.e. measurable. -/
theorem IsMatingOfTreesCoupling.aemeasurable_affineReroot_of_igMapPositiveRadii
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hpos : IGMapPositiveRadii γ P hIG₀ U ηL) (z₀ : ℂ) {s : ℝ} (hs : 0 < s) (φ : ℝ) :
    AEMeasurable (fun ω => affineReroot z₀ s φ (ηL ω)) P := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨Φ, hΦ, -, hcc⟩ := igMapPos_of_igMapPositiveRadii hpos
  have hrpos : 0 < 2 * Real.pi * igChi γ := period_pos_of_uniform hC.igField.2.1
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hrpos hC.igField.2.1
  have hp : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P :=
    hC.igField.1.1.measurable.aemeasurable.prodMk hUm
  have hK : AEMeasurable (fun ω => Φ (restrictCircles univ
      (igPullback γ z₀ s φ (igCircleAvgInput (hIG₀ ω, U ω))))) P :=
    (hΦ.comp (measurable_posIn.comp (measurable_igPullback γ z₀ s φ))).comp_aemeasurable
      (measurable_igCircleAvgInput.comp_aemeasurable hp)
  refine hK.congr ?_
  filter_upwards [hcc z₀ s φ hs] with ω hω
  exact hω

/-- The γ-cone field of the bundle is independent of `ηL`. -/
theorem IsMatingOfTreesCoupling.indepFun_coneField_ηL
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))
      ηL P := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version hC.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version hC.bm_B'
  -- `ηL ⟂ (X, (B, B'))`, then through the continuous versions
  have hηcones := IsMatingOfTreesCoupling.indepFun_ηL_coneData hC
  let coneXBB : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun q => (q.1, (q.2.1, q.2.2.1))
  have hconeXBB : Measurable coneXBB :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hηXBB : IndepFun ηL (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P :=
    hηcones.comp measurable_id hconeXBB
  have hpath : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hηXBc : IndepFun ηL (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    indepFun_triple_continuousMap_of_coe (hηXBB.congr (ae_eq_refl _) hpath)
  -- the measurable radial path `W` and the measurable field
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hηXW : IndepFun ηL (fun ω => (X ω, W ω)) P :=
    hηXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ γ).comp measurable_snd))
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', hC.bm_B.eval_zero_ae_eq_zero, hC.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift hC.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)] with ω h1 h2 h3 h4 hdrift t
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
  have hind : IndepFun (fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω)) ηL P :=
    (hηXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

end Bundle

end MatedCRTHarmonic.IGLaw
