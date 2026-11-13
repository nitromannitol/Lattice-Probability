/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OCurveScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock

/-!
# `CurveScaleInvariant` for the `0`-cone curve of the mating-of-trees bundle ([18] Theorem 4.4 input)

G4b's named input `GMS4b.CurveScaleInvariant P η₀`: for every `ε > 0` there is a measurable
positive scale `R` with `law(t ↦ R⁻¹ η₀(εt)) = law(η₀)` on `C(ℝ, ℂ)`, where `η₀` is the bundle's space-filling SLE
parametrized by the γ-LQG area of the `0`-quantum cone `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')`.

`IsMatingOfTreesCoupling.curveScaleInvariant hC hγ` proves it from the mating-of-trees bundle alone (no hypothesis
beyond `γ ∈ (0, 2)`), with `R = R_ε` the `0`-cone mass scale in lateral/radial coordinates. The proof is [18]'s, written as
proof of the cone scaling identity (`CellScaling/JointScalingOMain.lean`) at `α = 0`:

* **field** (DMS Prop 4.13(i) at `α = 0`): `h₀ = fieldOf (lateralPart X₀) W` and
  `h₀^ε = fieldOf (lateralPart X₀ (R_ε ·)) (radShift W)` have the same law (`map_radShift_coneRadial_alpha`,
  `map_fieldOf_shift_eq`);
* **curve**: `ηL` is independent of `(X₀, W)` and its law is invariant under every fixed dilation
  (`IsMatingOfTreesCoupling.map_affineReroot_ηL`, from the `igMap` clause), so the random dilation at `R_ε` keeps the
  joint law (`measure_dilCurve_indep_eq`);
* **area clock**: the covariance `μ_{h₀^ε}(A) = ε⁻¹ μ_{h₀}(R_ε A)` (`ae_lqgArea_coneRescaleField_alpha`), area
  existence and open-set positivity for the `0`-cone, and the bundle's `areaParam₀` give, pathwise,
  `η₀ = parEval(h₀, ηL)` and `R_ε⁻¹ η₀(ε ·) = parEval(h₀^ε, R_ε⁻¹ ηL(R_ε² ·))` (the measurable functional
  `parEval` and its identities `coe_eq_parEval_of_areaParam`, `coe_coneRescaleCurve_eq_parEval`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.IGLaw

open LQGMetric

lemma lqgQ_pos' {γ : ℝ} (hγ : 0 < γ) : 0 < CellScaling.lqgQ γ := by
  unfold CellScaling.lqgQ
  positivity

lemma curveRescale_eq_coneRescaleCurve (R ε : ℝ) (c : C(ℝ, ℂ)) :
    (⇑(GMS4b.curveRescale R ε c) : ℝ → ℂ) = ⇑(CellScaling.coneRescaleCurve R ε c) := by
  funext t
  rw [GMS4b.curveRescale_apply]
  rfl

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- **[18] Theorem 4.4's scale invariance of the `0`-cone curve** (`GMS4b.CurveScaleInvariant`, exact statement), from
the frozen v4 mating-of-trees bundle. -/
theorem IsMatingOfTreesCoupling.curveScaleInvariant
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : GMS4b.CurveScaleInvariant P η₀ := by
  intro ε hε
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨hγ0, hγ2⟩ := hγ
  have hQ0 : (0 : ℝ) < CellScaling.lqgQ γ := lqgQ_pos' hγ0
  have hQ0' : 0 < CellScaling.lqgQ γ - 0 := by rw [sub_zero]; exact hQ0
  have hQc : (0 : ℝ) < QuantumZipper.Qc γ := by
    have : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
    rw [← this]; exact hQ0
  -- `ηL ⟂ (X₀, B₀, B₀')`
  have hηcones := IsMatingOfTreesCoupling.indepFun_ηL_coneData hC
  have hproj : Measurable fun q : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2)) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        measurable_snd)))).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
          measurable_snd)))))
  have hηX₀BB : IndepFun ηL (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    hηcones.comp measurable_id hproj
  -- the radial path of the `0`-cone
  obtain ⟨W, hWm, hXW, hVη, hW⟩ := exists_radialPath_alpha (γ := γ) (α := 0) hQ0' hC.bm_B₀
    hC.bm_B₀' hC.indep_cone₀.1 hηX₀BB
  let V : Ω → DistC × C(ℝ, ℝ) := fun ω => (X₀ ω, W ω)
  have hV : Measurable V := hC.gff₀.measurable.prodMk hWm
  -- the measurable fields `h₀^ε`, `h₀` and scale `R_ε` as functions of `V`
  let y : ℝ := γ⁻¹ * Real.log ε
  let Rv : DistC × C(ℝ, ℝ) → ℝ := fun v => Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y v.2)
  let F₁ : DistC × C(ℝ, ℝ) → DistC := fun v =>
    ConeScaling.fieldOf (affineComp (Rv v) 0 (CellScaling.lateralPart v.1))
      (ConeScaling.radShift (CellScaling.lqgQ γ) y v.2)
  let F₂ : DistC × C(ℝ, ℝ) → DistC := fun v => ConeScaling.fieldOf (CellScaling.lateralPart v.1) v.2
  have hRv : Measurable Rv :=
    Real.measurable_exp.comp
      ((ConeScaling.measurable_lastLevel (CellScaling.lqgQ γ) y).comp measurable_snd)
  have hF₁ : Measurable F₁ :=
    ConeScaling.measurable_fieldOf.comp (Measurable.prodMk
      (MoTPort.ConeMeas.measurable_affineComp_joint.comp
        (hRv.prodMk (ConeScaling.measurable_lateralPart.comp measurable_fst)))
      ((ConeScaling.measurable_radShift (CellScaling.lqgQ γ) y).comp measurable_snd))
  have hF₂ : Measurable F₂ :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  -- the field law `h₀^ε =d h₀` (DMS Prop 4.13(i) at `α = 0`)
  have hrad := map_radShift_coneRadial_alpha (γ := γ) (α := 0) hQ0 hC.bm_B₀ hC.bm_B₀'
    hC.indep_cone₀.2 hWm hW y
  have hlaw : P.map (fun ω => F₁ (V ω)) = P.map (fun ω => F₂ (V ω)) :=
    ConeScaling.map_fieldOf_shift_eq hC.gff₀ hWm hXW.symm hrad
  -- the fixed-scale curve law
  have hdil : ∀ r : ℝ, 0 < r →
      P.map (fun ω => CellScaling.JointScalingO.dilCurve r (ηL ω)) = P.map ηL := by
    intro r hr
    rw [← IsMatingOfTreesCoupling.map_affineReroot_ηL hC 0 hr 0]
    refine Measure.map_congr ?_
    filter_upwards [IsMatingOfTreesCoupling.ae_rootTime_zero hC] with ω hω
    exact CellScaling.JointScalingO.dilCurve_eq_affineReroot r (ηL ω) hω
  -- almost sure inputs for the `0`-cone
  have hXA := indepFun_motConeRadial_alpha (γ := γ) (α := 0) hXW hW
  have hvague := LQGCone.ae_isVagueLimitC_coneField hγ0 hγ2 hQc hC.gff₀ hC.bm_B₀ hC.bm_B₀'
    hC.indep_cone₀.2 hXA
  have hpos := LQGCone.ae_lqgArea_coneField_open_pos hγ0 hγ2 hQc hC.gff₀ hC.bm_B₀ hC.bm_B₀'
    hC.indep_cone₀.2 hXA
  have hLR1 := ae_lqgArea_coneRescaleField_alpha (α := 0) hγ0 hγ2 hQ0 hC.gff₀ hC.bm_B₀ hC.bm_B₀'
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hA : MoTPort.IsConeProcess 0 (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [ConeScaling.radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  -- the pathwise identification
  have key : ∀ᵐ ω ∂P,
      (⇑(GMS4b.curveRescale (Rv (V ω)) ε (η₀ ω)) : ℝ → ℂ) =
          (fun t => CellScaling.JointScalingO.parEval γ (F₁ (V ω))
            (CellScaling.JointScalingO.dilCurve (Rv (V ω)) (ηL ω)) t) ∧
        (⇑(η₀ ω) : ℝ → ℂ) = fun t => CellScaling.JointScalingO.parEval γ (F₂ (V ω)) (ηL ω) t := by
    filter_upwards [hW, hli, hC.areaParam₀, hvague, hpos, hLR1] with
      ω hWω hliω hparω hvω hposω hLRω
    obtain ⟨⟨φ, hφ0, hφ⟩, hareaμ⟩ := hparω
    let hf : DistC :=
      CellScaling.coneField (X₀ ω) (CellScaling.coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω))
    have hv : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ hf) μ := hvω
    have harea : ∀ s t : ℝ, s ≤ t →
        CellScaling.lqgArea γ hf (η₀ ω '' Icc s t) = ENNReal.ofReal (t - s) :=
      hareaμ (CellScaling.lqgArea γ hf) (CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hv)
    have hR0 : 0 < Rv (V ω) := Real.exp_pos _
    have hh : hf = F₂ (V ω) := coneField_eq_fieldOf_alpha γ 0 (X₀ ω) hWω
    have hhb : CellScaling.coneRescaleField γ (Rv (V ω)) ε hf = F₁ (V ω) := by
      rw [hh]
      exact ConeScaling.coneRescaleField_fieldOf γ ε _ hliω
    have hcov : ∀ A : Set ℂ, CellScaling.lqgArea γ (CellScaling.coneRescaleField γ (Rv (V ω)) ε hf) A =
        ENNReal.ofReal ε⁻¹ * CellScaling.lqgArea γ hf ((fun w => ((Rv (V ω) : ℝ) : ℂ) * w) '' A) :=
      fun A => hLRω (Rv (V ω)) hR0 ε hε A
    have hposR : 0 < CellScaling.lqgArea γ hf (ball 0 (Rv (V ω))) :=
      hposω _ isOpen_ball (nonempty_ball.2 hR0)
    have hlhs := CellScaling.JointScalingO.coe_coneRescaleCurve_eq_parEval hR0 hε hφ0 hφ harea hcov
      hposR
    have hrhs := CellScaling.JointScalingO.coe_eq_parEval_of_areaParam hv hφ0 hφ harea
    refine ⟨?_, ?_⟩
    · rw [curveRescale_eq_coneRescaleCurve, hlhs, hhb]
    · rw [hrhs, hh]
  -- the law transfer, set by set
  refine ⟨fun ω => Rv (V ω), hRv.comp hV, fun ω => Real.exp_pos _, ?_⟩
  have hη₀m : Measurable η₀ := hC.measurable_curves.2.2.1
  have hcm : Measurable fun ω => GMS4b.curveRescale (Rv (V ω)) ε (η₀ ω) :=
    (GMS4b.measurable_curveRescale ε).comp ((hRv.comp hV).prodMk hη₀m)
  have hΨ : Measurable fun p : DistC × C(ℝ, ℂ) =>
      (fun t => CellScaling.JointScalingO.parEval γ p.1 p.2 t : ℝ → ℂ) :=
    measurable_pi_iff.2 fun t => CellScaling.JointScalingO.measurable_parEval γ t
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap (fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ))
      MeasurableSpace.pi] A := by
    rw [← CellScaling.JointScalingO.measurableSpace_continuousMap_complex_eq_comap]
    exact hA
  obtain ⟨T, hT, rfl⟩ := hA'
  rw [Measure.map_apply hcm hA, Measure.map_apply hη₀m hA]
  have hkey1 : (fun ω => (⇑(GMS4b.curveRescale (Rv (V ω)) ε (η₀ ω)) : ℝ → ℂ)) =ᵐ[P]
      fun ω => (fun t => CellScaling.JointScalingO.parEval γ (F₁ (V ω))
        (CellScaling.JointScalingO.dilCurve (Rv (V ω)) (ηL ω)) t) := key.mono fun ω hω => hω.1
  have hkey2 : (fun ω => (⇑(η₀ ω) : ℝ → ℂ)) =ᵐ[P]
      fun ω => (fun t => CellScaling.JointScalingO.parEval γ (F₂ (V ω)) (ηL ω) t) :=
    key.mono fun ω hω => hω.2
  calc P ((fun ω => GMS4b.curveRescale (Rv (V ω)) ε (η₀ ω)) ⁻¹'
        ((fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ)) ⁻¹' T))
      = P {ω | (⇑(GMS4b.curveRescale (Rv (V ω)) ε (η₀ ω)) : ℝ → ℂ) ∈ T} := rfl
    _ = P {ω | (fun t => CellScaling.JointScalingO.parEval γ (F₁ (V ω))
          (CellScaling.JointScalingO.dilCurve (Rv (V ω)) (ηL ω)) t) ∈ T} :=
        ConeScaling.measure_setOf_mem_congr hkey1 T
    _ = P {ω | (fun t => CellScaling.JointScalingO.parEval γ (F₂ (V ω)) (ηL ω) t) ∈ T} :=
        CellScaling.JointScalingO.measure_dilCurve_indep_eq hV hC.measurable_curves.1 hVη hdil hF₁ hF₂
          hlaw hRv (fun v => Real.exp_pos _) hΨ hT
    _ = P {ω | (⇑(η₀ ω) : ℝ → ℂ) ∈ T} := (ConeScaling.measure_setOf_mem_congr hkey2 T).symm
    _ = P (η₀ ⁻¹' ((fun f : C(ℝ, ℂ) => (⇑f : ℝ → ℂ)) ⁻¹' T)) := rfl

end Bundle

end MatedCRTHarmonic.IGLaw
