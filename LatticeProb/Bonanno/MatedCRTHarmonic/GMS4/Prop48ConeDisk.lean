/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48ConeDisk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48LocalTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw

/-!
# The zero-cone field on the unit disk

The γ-cone decomposition from GMCFacts has drift `γ(-log|z|)` on the unit
disk. Removing that drift gives the zero-cone field there, under the same
Brownian and lateral data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.CellScaling MatedCRTHarmonic.MoTPort

/-- Deterministic restriction identity behind the 0-cone/whole-plane field
comparison; the local-integrability premises avoid the junk value of
`Distribution.ofFun` outside its natural domain. -/
theorem prop48_zeroCone_restrict_eq_of_gamma_decomposition
    (γ : ℝ) (X Xt : DistC) (b b' : ℝ≥0 → ℝ) (g : ℂ → ℝ)
    (hgLI : LocallyIntegrable g volume)
    (h0LI : LocallyIntegrable
      (fun z : ℂ => coneRadial γ 0 b b' (-Real.log ‖z‖)) volume)
    (hγLI : LocallyIntegrable
      (fun z : ℂ => coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hdec : coneFieldOf γ X b b' = Xt + MoTPort.ofFunC g)
    (hg : ∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖)) :
    restrictTo (ballO 0 1) (coneField X (coneRadial γ 0 b b')) =
      restrictTo (ballO 0 1) Xt := by
  let V := ballO (0 : ℂ) 1
  let f₀ : ℂ → ℝ := fun z => coneRadial γ 0 b b' (-Real.log ‖z‖)
  let fγ : ℂ → ℝ := fun z => coneRadial γ γ b b' (-Real.log ‖z‖)
  have hfg : fγ =ᵐ[volume.restrict V] fun z => f₀ z + g z := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have : dist z 0 < 1 := hz
      simpa only [dist_zero_right] using this.le
    have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.mpr
      (Real.log_nonpos (norm_nonneg _) hz1)
    simp only [fγ, f₀, GMCFacts.coneRadial_of_nonneg γ γ b b' ht,
      GMCFacts.coneRadial_of_nonneg γ 0 b b' ht, hg z hz1]
    ring
  have hOf : restrictTo V (CellScaling.ofFunC fγ) =
      restrictTo V (CellScaling.ofFunC f₀) + restrictTo V (MoTPort.ofFunC g) := by
    rw [show CellScaling.ofFunC fγ = MoTPort.ofFunC fγ by rfl,
      show CellScaling.ofFunC f₀ = MoTPort.ofFunC f₀ by rfl,
      MoTPort.GFFBdry.restrictTo_ofFunC V hγLI,
      MoTPort.GFFBdry.restrictTo_ofFunC V h0LI,
      MoTPort.GFFBdry.restrictTo_ofFunC V hgLI]
    change Distribution.ofFun V fγ volume ⊤ =
      Distribution.ofFun V f₀ volume ⊤ + Distribution.ofFun V g volume ⊤
    rw [Distribution.ofFun_congr_ae hfg]
    exact Distribution.ofFun_add (h0LI.locallyIntegrableOn _) (hgLI.locallyIntegrableOn _)
  have hresDec : restrictTo V (coneFieldOf γ X b b') =
      restrictTo V Xt + restrictTo V (MoTPort.ofFunC g) := by
    rw [hdec, MoTPort.GFFBdry.restrictTo_add]
  change restrictTo V (coneField X (coneRadial γ 0 b b')) = restrictTo V Xt
  change restrictTo V (lateralPart X + CellScaling.ofFunC f₀) = restrictTo V Xt
  have hγres : restrictTo V (lateralPart X + CellScaling.ofFunC fγ) =
      restrictTo V Xt + restrictTo V (MoTPort.ofFunC g) := hresDec
  rw [MoTPort.GFFBdry.restrictTo_add] at hγres ⊢
  rw [hOf] at hγres
  rw [← add_assoc] at hγres
  exact add_right_cancel hγres

/-- The bundle's zero-cone field agrees on the unit disk, almost surely, with
some normalized whole-plane GFF on the same probability space. -/
theorem prop48_exists_zeroCone_disk_wholePlaneGFF
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧
      ∀ᵐ ω ∂P, restrictTo (ballO 0 1)
        (coneField (X₀ ω) (coneRadial γ 0
          (fun t => B₀ t ω) (fun t => B₀' t ω))) =
          restrictTo (ballO 0 1) (Xt ω) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := rfl
  have hA₀ : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ 0
        (fun s => B₀ s ω) (fun s => B₀' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hAγ : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ γ
        (fun s => B₀ s ω) (fun s => B₀' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hLI₀ : ∀ᵐ ω ∂P, LocallyIntegrable
      (fun z : ℂ => coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)
        (-Real.log ‖z‖)) volume := by
    filter_upwards [MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA₀] with ω hω
    refine hω.congr (Filter.Eventually.of_forall fun z => ?_)
    have he := LQGCone.coneRadial_eq_Q_add_motConeRadial γ 0
      (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)
    rw [hQ] at he
    exact he.symm
  have hLIγ : ∀ᵐ ω ∂P, LocallyIntegrable
      (fun z : ℂ => coneRadial γ γ (fun s => B₀ s ω) (fun s => B₀' s ω)
        (-Real.log ‖z‖)) volume := by
    filter_upwards [MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hAγ] with ω hω
    refine hω.congr (Filter.Eventually.of_forall fun z => ?_)
    have he := LQGCone.coneRadial_eq_Q_add_motConeRadial γ γ
      (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)
    rw [hQ] at he
    exact he.symm
  obtain ⟨Xt, hXt, hdecomp⟩ := GMCFacts.exists_cone_decomposition hγ.1 D.gff₀
    D.bm_B₀ D.bm_B₀' D.indep_cone₀ hγ.2
  refine ⟨Xt, hXt, ?_⟩
  filter_upwards [hdecomp, hLI₀, hLIγ] with ω hdec h0 hγLI
  obtain ⟨g, hfield, _, hgLI, _, hg⟩ := hdec
  exact prop48_zeroCone_restrict_eq_of_gamma_decomposition γ (X₀ ω) (Xt ω)
    (fun t => B₀ t ω) (fun t => B₀' t ω) g hgLI h0 hγLI hfield hg

/-- [18, §4] The 0-cone and a unit-circle-normalized whole-plane GFF have the
same distribution when restricted to the unit disk. This applies to any
normalized whole-plane GFF, including one on a different probability space. -/
theorem prop48_zeroCone_disk_law_eq_wholePlaneGFF
    {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {h : Ω' → DistC} (hh : IsNormalizedWPGFF h P') :
    P.map (fun ω => restrictTo (ballO 0 1)
      (coneField (X₀ ω) (coneRadial γ 0
        (fun t => B₀ t ω) (fun t => B₀' t ω)))) =
      P'.map (fun ω => restrictTo (ballO 0 1) (h ω)) := by
  obtain ⟨Xt, hXt, he⟩ := prop48_exists_zeroCone_disk_wholePlaneGFF D hγ
  calc
    _ = P.map (fun ω => restrictTo (ballO 0 1) (Xt ω)) := Measure.map_congr he
    _ = P'.map (fun ω => restrictTo (ballO 0 1) (h ω)) := by
      change P.map (restrictTo (ballO 0 1) ∘ Xt) =
        P'.map (restrictTo (ballO 0 1) ∘ h)
      rw [← Measure.map_map (measurable_restrictTo _) hXt.1.measurable,
        ← Measure.map_map (measurable_restrictTo _) hh.1.measurable,
        LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF hXt hh]

end MatedCRTHarmonic.GMS4

