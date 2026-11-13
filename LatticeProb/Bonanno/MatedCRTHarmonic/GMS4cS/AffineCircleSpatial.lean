/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cS.AffineCircleSpatial at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ConeCircleSpatial
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Rescale
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.AffineAreaCertificate
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-! Spatial continuity of the recentered zero-cone circle averages. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cS

open MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling
open LQGMetric

theorem continuousAt_circleAvg_affineCone_off_resonance
    {γ α : ℝ} {X : DistC} {b b' : ℝ≥0 → ℝ}
    (hg : RadialGood γ α X b b')
    (hs : ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      Tendsto (fun s => mollAvgS X s w ρ) (𝓝[>] 0) (𝓝 (circleAvg X ρ w)))
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z : ℂ) (C : ℝ) {w : ℂ}
    (hne : ‖(r : ℂ) * w + z‖ ≠ r * ρ) :
    ContinuousAt (fun x : ℂ =>
      circleAvg (addConst (affineComp r z (coneField X (coneRadial γ α b b'))) C) ρ x) w := by
  have hli₁ : LocallyIntegrable (radialAvg X) volume := by
    obtain ⟨K, hK⟩ := abs_radialAvg_le hg one_pos
    exact locallyIntegrable_of_logBound (measurable_radialAvg X)
      (continuousOn_radialAvg hg.good) hK
  have hli₂ : LocallyIntegrable (coneProfile γ α b b') volume := by
    obtain ⟨K, hK⟩ := abs_coneProfile_le hg one_pos
    exact locallyIntegrable_of_logBound (measurable_coneProfile hg)
      (continuousOn_coneProfile hg) (fun x hx hx' => (hK x hx hx').1)
  have hcont₁ := continuousOn_radialAvg hg.good
  have hcont₂ := continuousOn_coneProfile hg
  have ho : IsOpen {x : ℂ | ‖(r : ℂ) * x + z‖ ≠ r * ρ} :=
    isOpen_ne_fun (continuous_const.mul continuous_id |>.add continuous_const |>.norm)
      continuous_const
  have heq : (fun x : ℂ =>
      circleAvg (addConst (affineComp r z (coneField X (coneRadial γ α b b'))) C) ρ x) =ᶠ[𝓝 w]
      fun x => circleAvg (coneField X (coneRadial γ α b b')) (r * ρ) ((r : ℂ) * x + z) + C := by
    filter_upwards [ho.mem_nhds hne] with x hx
    apply circleAvg_addConst_affineComp_of_tendsto hr C
    rw [coneField_eq_cone]
    have ht := tendsto_mollAvgS_cone hli₁ hli₂ hcont₁ hcont₂
      (mul_pos hr hρ) hx (hs (r * ρ) (mul_pos hr hρ) ((r : ℂ) * x + z))
    have hv := circleAvg_cone hli₁ hli₂ hcont₁ hcont₂
      (mul_pos hr hρ) hx (hs (r * ρ) (mul_pos hr hρ) ((r : ℂ) * x + z))
    simpa only [coneField_eq_cone, hv] using ht
  have hc := GMS4c.continuousAt_circleAvg_coneField_off_resonance hg hs
    (mul_pos hr hρ) hne
  have ha : ContinuousAt (fun x : ℂ => (r : ℂ) * x + z) w := by fun_prop
  have hcomp : ContinuousAt (fun x : ℂ =>
      circleAvg (coneField X (coneRadial γ α b b')) (r * ρ) ((r : ℂ) * x + z)) w :=
    ContinuousAt.comp (f := fun x : ℂ => (r : ℂ) * x + z) (x := w)
      (g := fun y => circleAvg (coneField X (coneRadial γ α b b')) (r * ρ) y) hc ha
  exact (hcomp.add_const C).congr_of_eventuallyEq heq

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.L43O

theorem ae_affine_zeroCone_localCircle_continuous_eventually
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂(volume.restrict V),
      ContinuousAt (fun v => GMS4c.localCircleProcess (GMS4c.thickOpen V δ)
        (restrictTo (GMS4c.thickOpen V δ)
          (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)))
        (CellScaling.dyadicScale k) v) w := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨K, hK⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  filter_upwards [ae_radialGood D.gff₀ D.bm_B₀ D.bm_B₀'
      (LQGCoord.lqgQ_pos hγ.1), ae_tendsto_mollAvgS_circleAvg D.gff₀]
    with ω hrad hscale
  filter_upwards [eventually_ge_atTop K] with k hk
  have hρ : 0 < CellScaling.dyadicScale k := by unfold CellScaling.dyadicScale; positivity
  have hsmall : CellScaling.dyadicScale k < δ := by
    rw [LQGCone.dyadicScale_eq_radius]
    exact hK k hk
  have hne : ∀ᵐ w : ℂ, ‖(r : ℂ) * w + z‖ ≠ r * CellScaling.dyadicScale k := by
    simpa only [LQGCoord.affT_apply] using
      (LQGCoord.quasiMeasurePreserving_affT hr z).ae
        (LQGCoord.ae_norm_ne (r * CellScaling.dyadicScale k))
  filter_upwards [ae_restrict_of_ae hne,
    ae_restrict_mem V.isOpen.measurableSet] with w hwr hwV
  apply GMS4c.continuousAt_localCircleProcess_restrictTo V hρ hsmall _ hwV
  rw [IGLaw.affField, L43O.rotateField_zero]
  change ContinuousAt (fun v => circleAvg
    (addConst (affineComp r z (zeroConeField γ X₀ B₀ B₀' ω))
      (-(circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z))) (CellScaling.dyadicScale k) v) w
  exact continuousAt_circleAvg_affineCone_off_resonance hrad hscale.2 hr hρ z
    (-(circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z)) hwr

end MatedCRTHarmonic.GMS4cS

