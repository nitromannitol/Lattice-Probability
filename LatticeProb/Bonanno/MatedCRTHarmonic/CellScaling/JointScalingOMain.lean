/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.JointScalingOMain and JointScalingOClock at commit fdb5cad;
   imports adapted and some documentation omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CurveLaws
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.ConeRealization
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ScalingLawTransfer

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

open LQGMetric

theorem measurable_parMap (γ : ℝ) : Measurable (parMap γ) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun t => measurable_parEval γ t)


/-- The σ-algebra of (field, curve) pairs is the trace of that of (field, function) pairs. -/
theorem prod_measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace (DistC × C(ℝ, ℂ))) =
      MeasurableSpace.comap (Prod.map id fun c : C(ℝ, ℂ) => (⇑c : ℝ → ℂ)) inferInstance := by
  apply le_antisymm
  · -- `fst` and `snd` are measurable for the trace σ-algebra
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      intro s hs
      exact ⟨Prod.fst ⁻¹' s, measurable_fst hs, rfl⟩
    · rw [measurableSpace_continuousMap_complex_eq_comap, MeasurableSpace.comap_comp]
      rw [MeasurableSpace.comap_le_iff_le_map]
      intro s hs
      exact ⟨Prod.snd ⁻¹' s, measurable_snd hs, rfl⟩
  · exact (measurable_id.prodMap measurable_coe_continuousMap_complex).comap_le

/-- Every Borel set of (field, curve) pairs is the preimage under `c ↦ ⇑c` of a measurable set of
(field, function) pairs. -/
theorem exists_measurableSet_preimage_coe {S : Set (DistC × C(ℝ, ℂ))} (hS : MeasurableSet S) :
    ∃ T : Set (DistC × (ℝ → ℂ)), MeasurableSet T ∧
      S = Prod.map id (fun c : C(ℝ, ℂ) => (⇑c : ℝ → ℂ)) ⁻¹' T := by
  have hS' : MeasurableSet[MeasurableSpace.comap
      (Prod.map id fun c : C(ℝ, ℂ) => (⇑c : ℝ → ℂ)) inferInstance] S := by
    rw [← prod_measurableSpace_eq_comap]
    exact hS
  obtain ⟨T, hT, hTS⟩ := hS'
  exact ⟨T, hT, hTS.symm⟩



def CurveDilationLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ηL : Ω → C(ℝ, ℂ)) : Prop :=
  ∀ s : ℝ, 0 < s → P.map (fun ω => MatedCRT.affineReroot 0 s 0 (ηL ω)) = P.map ηL

/-! ### Independence through continuous versions, with an extra component -/

/-- Independence from `(Z, U, V)` with `U, V` continuous paths is independence from
`(Z, ⇑U, ⇑V)`. (Three-component form of `ConeScaling.indepFun_pair_continuousMap_of_coe`.) -/
theorem indepFun_triple_continuousMap_of_coe {Ω β δ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace δ] {P : Measure Ω} {f : Ω → β} {Z : Ω → δ}
    {U V : Ω → C(ℝ≥0, ℝ)}
    (h : IndepFun f (fun ω => (Z ω, (⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))) P) :
    IndepFun f (fun ω => (Z ω, U ω, V ω)) P := by
  have hc : Measurable fun g : C(ℝ≥0, ℝ) => (⇑g : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval t
  have hσ : MeasurableSpace.comap (fun ω => (Z ω, U ω, V ω))
        (inferInstance : MeasurableSpace (δ × C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ))) =
      MeasurableSpace.comap (fun ω => (Z ω, (⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)))
        (inferInstance : MeasurableSpace (δ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) := by
    apply le_antisymm
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap
        (fun ω => (Z ω, (⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ))) inferInstance
      have hm : Measurable fun ω => (Z ω, (⇑(U ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)) :=
        comap_measurable _
      refine (measurable_fst.comp hm).prodMk (Measurable.prodMk ?_ ?_)
      · exact ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_fst.comp (measurable_snd.comp hm))
      · exact ContinuousMap.measurable_iff_eval.2 fun t =>
          (measurable_pi_apply t).comp (measurable_snd.comp (measurable_snd.comp hm))
    · rw [← measurable_iff_comap_le]
      let _ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (Z ω, U ω, V ω)) inferInstance
      have hm : Measurable fun ω => (Z ω, U ω, V ω) := comap_measurable _
      exact (measurable_fst.comp hm).prodMk ((hc.comp (measurable_fst.comp (measurable_snd.comp hm))).prodMk
        (hc.comp (measurable_snd.comp (measurable_snd.comp hm))))
  unfold IndepFun Kernel.IndepFun at h ⊢
  rw [hσ]
  exact h

/-- A transient continuous curve invariant under a fixed time shift has zero shift (local copy of
IGC's `IGLaw.shift_eq_zero_of_transient`). -/
theorem shift_eq_zero_of_transient (c : C(ℝ, ℂ)) (τ : ℝ)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hshift : ∀ t, c t = c (τ + t)) : τ = 0 := by
  by_contra hτ
  have hn : ∀ n : ℕ, c (n * τ) = c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have h := hshift (k * τ)
      have hk : τ + (k : ℝ) * τ = ((k + 1 : ℕ) : ℝ) * τ := by
        push_cast
        ring
      rw [hk] at h
      rw [← h, ih]
  have hK : ({c 0}ᶜ : Set ℂ) ∈ cocompact ℂ := isCompact_singleton.compl_mem_cocompact
  obtain ⟨C, hC, hCsub⟩ := Filter.mem_cocompact.1 (htr hK)
  obtain ⟨M, hM⟩ := hC.isBounded.exists_norm_le
  have hτpos : 0 < |τ| := abs_pos.2 hτ
  obtain ⟨n, hn'⟩ := exists_nat_gt (M / |τ|)
  have hmem : (n : ℝ) * τ ∈ C := by
    by_contra hnot
    have h1 := hCsub hnot
    simp [hn n] at h1
  have h2 := hM _ hmem
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast] at h2
  rw [div_lt_iff₀ hτpos] at hn'
  linarith

/-! ### The coupling -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The Lebesgue-parametrized curve is rooted at time `0`: `firstHit ηL 0 = 0` a.s. (the identity
coordinate clause of `igMap` and transience; local copy of IGC's `IGLaw.ae_firstHit_zero`). -/
theorem ae_firstHit_zero_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, MatedCRT.firstHit (ηL ω) 0 = 0 := by
  obtain ⟨Φ, -, -, hroot, hcc, -⟩ := D.igMap
  filter_upwards [hroot, hcc 0 1 0 one_pos, D.spaceFilling] with ω hr hc hs
  have hid : MatedCRT.igPullback γ 0 1 0 (fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) =
      fun ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω := by
    funext ρ w
    simp [MatedCRT.igPullback]
  rw [hid] at hc
  have hfix : ∀ t, ηL ω t = ηL ω (MatedCRT.firstHit (ηL ω) 0 + t) := by
    intro t
    have h := congrArg (fun c : C(ℝ, ℂ) => c t) (hr.trans hc)
    simpa [MatedCRT.affineReroot] using h
  exact shift_eq_zero_of_transient (ηL ω) _ hs.2.1 hfix

/-- The Lebesgue-parametrized curve is independent of the γ-cone data `(X, B, B')` (the `igMap`
factorization through the IG field and `indep_curve`; local form of IGC's
`IGLaw.IsMatingOfTreesCoupling.indepFun_ηL_cones`). -/
theorem indepFun_curve_cone
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun ηL (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) P := by
  obtain ⟨Φ, hΦ, -, hfactor, -⟩ := D.igMap
  have h := IGLaw.indepFun_igCurve_of_draft_factor D.indep_curve hΦ hfactor
  have hproj : Measurable fun p : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (p.1, p.2.1, p.2.2.1) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact h.comp measurable_id hproj

/-- **The cone's radial path as a measurable continuous version**, independent of the GFF `X`, and
jointly with `X` independent of the Lebesgue-parametrized curve `η_L`. -/
theorem exists_radialPath_indepFun_curve
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧ IndepFun X W P ∧ IndepFun (fun ω => (X ω, W ω)) ηL P ∧
      ∀ᵐ ω ∂P, ∀ t, W ω t = coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  have hpath : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hXC : IndepFun X (fun ω => (Bc ω, Bc' ω)) P :=
    ConeScaling.indepFun_pair_continuousMap_of_coe (D.indep_cone.1.congr (ae_eq_refl _) hpath)
  have hηXBB := indepFun_curve_cone D
  have hpath3 : (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => (X ω, (⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hpath] with ω hω
    exact congrArg (fun p => (X ω, p)) hω
  have hηC : IndepFun ηL (fun ω => (X ω, Bc ω, Bc' ω)) P :=
    indepFun_triple_continuousMap_of_coe (hηXBB.congr (ae_eq_refl _) hpath3)
  have hrm := ConeScaling.measurable_radMap γ γ
  refine ⟨fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω), hrm.comp (hBcm.prodMk hBc'm),
    hXC.comp measurable_id hrm, ?_, ?_⟩
  · have hG : Measurable fun p : MatedCRT.Field × C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        (p.1, ConeScaling.radMap γ γ p.2) := measurable_fst.prodMk (hrm.comp measurable_snd)
    exact (hηC.comp measurable_id hG).symm
  · filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero, D.bm_B'.eval_zero_ae_eq_zero,
      ae_goodDrift D.bm_B' (lqgQ_sub_pos hγ0 hγ2)] with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ γ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ coneDrift γ γ (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ γ (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]


theorem coneJointScaling_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) (hdil : CurveDilationLaw P ηL) :
    ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ) := by
  intro b hb S hS
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hγ0, hγ2⟩ := hγ
  let hf : Ω → DistC := fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)
  let Rb : Ω → ℝ := fun ω => coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b
  let coeC : C(ℝ, ℂ) → (ℝ → ℂ) := fun c => ⇑c
  change P {ω | (coneRescaleField γ (Rb ω) b (hf ω),
      coneRescaleCurve (Rb ω) b (MoTInput.bundleCurve D ω)) ∈ S} =
    P {ω | (hf ω, MoTInput.bundleCurve D ω) ∈ S}
  -- the radial path, independence
  obtain ⟨W, hWm, hXW, hVη, hW⟩ := exists_radialPath_indepFun_curve D hγ0 hγ2
  let V : Ω → DistC × C(ℝ, ℝ) := fun ω => (X ω, W ω)
  have hV : Measurable V := D.gff.measurable.prodMk hWm
  -- the measurable fields `h_b`, `h` and scale `R_b` as functions of `V`
  let y : ℝ := γ⁻¹ * Real.log b
  let Rv : DistC × C(ℝ, ℝ) → ℝ := fun v => Real.exp (ConeScaling.lastLevel (lqgQ γ) y v.2)
  let F₁ : DistC × C(ℝ, ℝ) → DistC := fun v =>
    ConeScaling.fieldOf (affineComp (Rv v) 0 (lateralPart v.1)) (ConeScaling.radShift (lqgQ γ) y v.2)
  let F₂ : DistC × C(ℝ, ℝ) → DistC := fun v => ConeScaling.fieldOf (lateralPart v.1) v.2
  have hRv : Measurable Rv :=
    Real.measurable_exp.comp ((ConeScaling.measurable_lastLevel (lqgQ γ) y).comp measurable_snd)
  have hF₁ : Measurable F₁ :=
    ConeScaling.measurable_fieldOf.comp (Measurable.prodMk
      (MoTPort.ConeMeas.measurable_affineComp_joint.comp
        (hRv.prodMk (ConeScaling.measurable_lateralPart.comp measurable_fst)))
      ((ConeScaling.measurable_radShift (lqgQ γ) y).comp measurable_snd))
  have hF₂ : Measurable F₂ :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  -- the field law `h_b =d h` (DMS Prop 4.13(i))
  have hrad := ConeScaling.map_radShift_coneRadial hγ0 hγ2 D.bm_B D.bm_B' D.indep_cone.2 hWm hW y
  have hlaw : P.map (fun ω => F₁ (V ω)) = P.map (fun ω => F₂ (V ω)) :=
    ConeScaling.map_fieldOf_shift_eq D.gff hWm hXW.symm hrad
  -- the fixed-scale curve law, in the form `dilCurve`
  have hdil' : ∀ r : ℝ, 0 < r → P.map (fun ω => dilCurve r (ηL ω)) = P.map ηL := by
    intro r hr
    rw [← hdil r hr]
    refine Measure.map_congr ?_
    filter_upwards [ae_firstHit_zero_of_coupling D] with ω hω
    exact dilCurve_eq_affineReroot r (ηL ω) hω
  -- almost sure inputs
  have hXA := ConeScaling.indepFun_motConeRadial hγ0 hγ2 D.bm_B D.bm_B' D.indep_cone.1
  have hα := ConeScaling.lt_Qc hγ0 hγ2
  have hvague := LQGCone.ae_isVagueLimitC_coneField hγ0 hγ2 hα D.gff D.bm_B D.bm_B'
    D.indep_cone.2 hXA
  have hpos := LQGCone.ae_lqgArea_coneField_open_pos hγ0 hγ2 hα D.gff D.bm_B D.bm_B'
    D.indep_cone.2 hXA
  have hLR1 := LQGCoord.ae_lqgArea_coneRescaleField_holds hγ0 hγ2 D.gff D.bm_B D.bm_B'
  have hQ : lqgQ γ = QuantumZipper.Qc γ := by dsimp [lqgQ, QuantumZipper.Qc]
  have hA : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial D.bm_B D.bm_B' D.indep_cone.2
  have hli : ∀ᵐ ω ∂P, LocallyIntegrable (ConeScaling.radialOf (W ω)) volume := by
    filter_upwards [hW, MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω hl
    refine hl.congr (Eventually.of_forall fun z => ?_)
    simp only [ConeScaling.radialOf, hω, LQGCone.coneRadial_eq_Q_add_motConeRadial, hQ]
  -- the pathwise identification
  have key : ∀ᵐ ω ∂P,
      Prod.map id coeC (coneRescaleField γ (Rb ω) b (hf ω),
          coneRescaleCurve (Rb ω) b (MoTInput.bundleCurve D ω)) =
        parMap γ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) ∧
      Prod.map id coeC (hf ω, MoTInput.bundleCurve D ω) = parMap γ (F₂ (V ω), ηL ω) := by
    filter_upwards [hW, hli, MoTInput.ae_bundleCurve_eq D, D.areaParam, hvague, hpos, hLR1]
      with ω hWω hliω hcω hparω hvω hposω hLRω
    obtain ⟨⟨φ, hφ0, hφ⟩, hareaμ⟩ := hparω
    have hc : MoTInput.bundleCurve D ω = η ω := hcω
    have hv : ∃ μ, IsVagueLimitC (lqgAreaApprox γ (hf ω)) μ := hvω
    have harea : ∀ s t : ℝ, s ≤ t → lqgArea γ (hf ω) (η ω '' Icc s t) = ENNReal.ofReal (t - s) :=
      hareaμ (lqgArea γ (hf ω)) (isVagueLimitC_lqgArea_of_exists hv)
    have hR : Rb ω = Rv (V ω) := ConeScaling.coneScale_eq_exp_lastLevel γ b hWω
    have hR0 : 0 < Rb ω := Real.exp_pos _
    have hh : hf ω = F₂ (V ω) := ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hWω
    have hhb : coneRescaleField γ (Rb ω) b (hf ω) = F₁ (V ω) := by
      rw [hR, hh]
      exact ConeScaling.coneRescaleField_fieldOf γ b _ hliω
    have hcov : ∀ A : Set ℂ, lqgArea γ (coneRescaleField γ (Rb ω) b (hf ω)) A =
        ENNReal.ofReal b⁻¹ * lqgArea γ (hf ω) ((fun w => ((Rb ω : ℝ) : ℂ) * w) '' A) :=
      fun A => hLRω (Rb ω) hR0 b hb A
    have hposR : 0 < lqgArea γ (hf ω) (ball 0 (Rb ω)) :=
      hposω _ isOpen_ball (nonempty_ball.2 hR0)
    have hlhs := coe_coneRescaleCurve_eq_parEval hR0 hb hφ0 hφ harea hcov hposR
    have hrhs := coe_eq_parEval_of_areaParam hv hφ0 hφ harea
    refine ⟨?_, ?_⟩
    · rw [hc]
      change (coneRescaleField γ (Rb ω) b (hf ω), (⇑(coneRescaleCurve (Rb ω) b (η ω)) : ℝ → ℂ)) =
        (F₁ (V ω), fun t => parEval γ (F₁ (V ω)) (dilCurve (Rv (V ω)) (ηL ω)) t)
      rw [hlhs, ← hhb, ← hR]
    · rw [hc]
      change (hf ω, (⇑(η ω) : ℝ → ℂ)) = (F₂ (V ω), fun t => parEval γ (F₂ (V ω)) (ηL ω) t)
      rw [hrhs, ← hh]
  -- the law transfer
  obtain ⟨T, hT, rfl⟩ := exists_measurableSet_preimage_coe hS
  have hkey1 : (fun ω => Prod.map id coeC (coneRescaleField γ (Rb ω) b (hf ω),
        coneRescaleCurve (Rb ω) b (MoTInput.bundleCurve D ω))) =ᵐ[P]
      fun ω => parMap γ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) := key.mono fun ω hω => hω.1
  have hkey2 : (fun ω => Prod.map id coeC (hf ω, MoTInput.bundleCurve D ω)) =ᵐ[P]
      fun ω => parMap γ (F₂ (V ω), ηL ω) := key.mono fun ω hω => hω.2
  calc P {ω | (coneRescaleField γ (Rb ω) b (hf ω),
          coneRescaleCurve (Rb ω) b (MoTInput.bundleCurve D ω)) ∈ Prod.map id coeC ⁻¹' T}
      = P {ω | Prod.map id coeC (coneRescaleField γ (Rb ω) b (hf ω),
          coneRescaleCurve (Rb ω) b (MoTInput.bundleCurve D ω)) ∈ T} := rfl
    _ = P {ω | parMap γ (F₁ (V ω), dilCurve (Rv (V ω)) (ηL ω)) ∈ T} :=
        ConeScaling.measure_setOf_mem_congr hkey1 T
    _ = P {ω | parMap γ (F₂ (V ω), ηL ω) ∈ T} :=
        measure_dilCurve_indep_eq hV D.measurable_curves.1 hVη hdil' hF₁ hF₂ hlaw hRv
          (fun v => Real.exp_pos _) (measurable_parMap γ) hT
    _ = P {ω | Prod.map id coeC (hf ω, MoTInput.bundleCurve D ω) ∈ T} :=
        (ConeScaling.measure_setOf_mem_congr hkey2 T).symm
    _ = P {ω | (hf ω, MoTInput.bundleCurve D ω) ∈ Prod.map id coeC ⁻¹' T} := rfl

/-- **Boundary-length covariance at the coupling** (`BoundaryLengthCovariance` for the
realization): the bundle field `boundaryLength`, transported to MTC's repaired curve and Brownian
path (same argument as `MesoModel.final_boundaryLengthCovariance_of_coupling`). -/
theorem boundaryLengthCovariance_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    BoundaryLengthCovariance (MoTInput.coneRealizationOfCoupling D hstd hγ) := by
  rcases D.boundaryLength with ⟨BL, hBLmeas, hBLbase, hBLscale⟩
  refine ⟨BL, hBLmeas, ?_, ?_⟩
  · filter_upwards [hBLbase, MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D]
      with ω hbase hbm hcurve
    have hbm' : MoTInput.bundleBM D ω = bm ω := hbm
    have hcurve' : MoTInput.bundleCurve D ω = η ω := hcurve
    change MoTInput.bundleBM D ω =
      BL (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), MoTInput.bundleCurve D ω)
    rw [hbm', hcurve']
    exact hbase
  · intro b hb
    filter_upwards [hBLscale b hb, MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D]
      with ω hscale hbm hcurve
    have hbm' : MoTInput.bundleBM D ω = bm ω := hbm
    have hcurve' : MoTInput.bundleCurve D ω = η ω := hcurve
    change BL (coneRescaleField γ (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        coneRescaleCurve (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (MoTInput.bundleCurve D ω)) =
      brownRescale b (MoTInput.bundleBM D ω)
    rw [hbm', hcurve']
    exact hscale


theorem matedCRTProposition23GridScalingInput_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) (hdil : CurveDilationLaw P ηL) :
    MesoModel.MatedCRTProposition23GridScalingInput (MoTInput.unitMesoModelOfCoupling D hstd hγ) :=
  matedCRTProposition23GridScalingInput_of_cone (MoTInput.coneRealizationOfCoupling D hstd hγ)
    (coneJointScaling_of_coupling D hstd hγ hdil) (boundaryLengthCovariance_of_coupling D hstd hγ)
    MeshGridEventMeasurable_holds

end Coupling

end JointScalingO

end MatedCRTHarmonic.CellScaling

