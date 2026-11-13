/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.ZeroConeMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.WholePlaneMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-! Local GMC identification for the zero-quantum cone and the whole-plane upper-mass bound. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

private theorem zeroCone_local_field_eq
    (γ : ℝ) (X Xt : DistC) (b b' : ℝ≥0 → ℝ) (g : ℂ → ℝ)
    (hdec : MatedCRTHarmonic.CellScaling.coneFieldOf γ X b b' = Xt + ofFunC g)
    (hg : ∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖))
    (hgli : LocallyIntegrable g volume)
    (hliγ : LocallyIntegrable
      (fun z : ℂ => MatedCRTHarmonic.CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hli0 : LocallyIntegrable
      (fun z : ℂ => MatedCRTHarmonic.CellScaling.coneRadial γ 0 b b' (-Real.log ‖z‖)) volume)
    (V : TopologicalSpace.Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1) :
    restrictTo V (MatedCRTHarmonic.CellScaling.coneField X
      (MatedCRTHarmonic.CellScaling.coneRadial γ 0 b b')) = restrictTo V Xt := by
  let fγ : ℂ → ℝ := fun z =>
    MatedCRTHarmonic.CellScaling.coneRadial γ γ b b' (-Real.log ‖z‖)
  let f0 : ℂ → ℝ := fun z =>
    MatedCRTHarmonic.CellScaling.coneRadial γ 0 b b' (-Real.log ‖z‖)
  have hfγ : LocallyIntegrable fγ volume := hliγ
  have hf0 : LocallyIntegrable f0 volume := hli0
  have hfun : ∀ z ∈ (V : Set ℂ), fγ z = f0 z + g z := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 (hV hz)).le
    have ht : 0 ≤ -Real.log ‖z‖ :=
      neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hz1)
    simp only [fγ, f0]
    rw [MatedCRTHarmonic.GMCFacts.coneRadial_of_nonneg γ γ b b' ht,
      MatedCRTHarmonic.GMCFacts.coneRadial_of_nonneg γ 0 b b' ht,
      hg z hz1]
    ring
  have hsum : ofFunOn V fγ = ofFunOn V f0 + ofFunOn V g := by
    calc
      ofFunOn V fγ = ofFunOn V (fun z => f0 z + g z) := by
        ext φ
        have hfg : LocallyIntegrable (fun z => f0 z + g z) volume := hf0.add hgli
        change (ofFunOn V fγ) φ = (ofFunOn V (fun z => f0 z + g z)) φ
        rw [ofFunOn_apply (hfγ.locallyIntegrableOn _)]
        rw [ofFunOn_apply (hfg.locallyIntegrableOn _)]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ (V : Set ℂ)
        · rw [← hfun z hz]
        · have hφ : φ z = 0 :=
            image_eq_zero_of_notMem_tsupport fun hs => hz (φ.tsupport_subset hs)
          simp [hφ]
      _ = ofFunOn V f0 + ofFunOn V g := by
        exact Distribution.ofFun_add (hf0.locallyIntegrableOn _)
          (hgli.locallyIntegrableOn _)
  have hdecV : restrictTo V (MatedCRTHarmonic.CellScaling.lateralPart X) +
      ofFunOn V fγ = restrictTo V Xt + ofFunOn V g := by
    have h := congrArg (restrictTo V) hdec
    change restrictTo V (MatedCRTHarmonic.CellScaling.lateralPart X + ofFunC fγ) =
      restrictTo V (Xt + ofFunC g) at h
    simpa only [restrictTo_add, restrictTo_ofFunC V hfγ,
      restrictTo_ofFunC V hgli] using h
  change restrictTo V (MatedCRTHarmonic.CellScaling.lateralPart X +
    MatedCRTHarmonic.CellScaling.ofFunC f0) = restrictTo V Xt
  change restrictTo V (MatedCRTHarmonic.CellScaling.lateralPart X + ofFunC f0) = _
  rw [restrictTo_add, restrictTo_ofFunC V hf0]
  rw [hsum] at hdecV
  exact add_right_cancel (by simpa only [add_assoc] using hdecV)

/-- On every disk strictly inside the unit disk, the 0-cone GMC is the GMC of
the normalized whole-plane GFF obtained by replacing the radial Brownian path. -/
theorem exists_zeroConeArea_local_wholePlane
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling
      γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧
      ∀ r ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
        (zeroConeArea γ X₀ B₀ B₀' ω).restrict (ball 0 r) =
          (wholePlaneArea γ Xt ω).restrict (ball 0 r) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Xt, hXt, hdec⟩ :=
    MatedCRTHarmonic.GMCFacts.exists_cone_decomposition hγ.1
      D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀ hγ.2
  refine ⟨Xt, hXt, ?_⟩
  intro r hr
  let V : TopologicalSpace.Opens ℂ := ⟨ball 0 r, isOpen_ball⟩
  let d : ℝ := (1 - r) / 2
  have hd : 0 < d := by dsimp [d]; linarith [hr.2]
  have hthick : (MatedCRTHarmonic.GMS4c.thickOpen V d : Set ℂ) ⊆
      ball (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 hz
    have hwr : ‖w‖ < r := mem_ball_zero_iff.1 hw
    have hdist : ‖z - w‖ < d := by simpa [dist_eq_norm] using hzw
    have hnorm : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      have he : z = (z - w) + w := by abel
      calc
        ‖z‖ = ‖(z - w) + w‖ := congrArg norm he
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le (z - w) w
    exact mem_ball_zero_iff.2 (by dsimp [d] at *; linarith)
  let Aγ : ℝ → Ω → ℝ := fun t ω =>
    MatedCRTHarmonic.LQGCone.motConeRadial γ γ
      (fun s => B₀ s ω) (fun s => B₀' s ω) t
  let A0 : ℝ → Ω → ℝ := fun t ω =>
    MatedCRTHarmonic.LQGCone.motConeRadial γ 0
      (fun s => B₀ s ω) (fun s => B₀' s ω) t
  have hAγ : IsConeProcess γ (QuantumZipper.Qc γ) Aγ P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial
      D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hA0 : IsConeProcess 0 (QuantumZipper.Qc γ) A0 P :=
    MatedCRTHarmonic.LQGCone.isConeProcess_motConeRadial
      D.bm_B₀ D.bm_B₀' D.indep_cone₀.2
  have hliγ := MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hAγ
  have hli0 := MatedCRTHarmonic.MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA0
  have hv0 := MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ
  have hvXt := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp
    hXt.1 hγ.1 hγ.2
  filter_upwards [hdec, hliγ, hli0, hv0, hvXt] with ω hωdec hωγ hω0 hωv0 hωvXt
  obtain ⟨g, hfield, -, hgli, -, hg⟩ := hωdec
  have hprofγ : LocallyIntegrable
      (fun z : ℂ => MatedCRTHarmonic.CellScaling.coneRadial γ γ
        (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)) volume := by
    simpa only [MatedCRTHarmonic.LQGCone.coneRadial_eq_Q_add_motConeRadial,
      MatedCRTHarmonic.CellScaling.lqgQ, QuantumZipper.Qc] using hωγ
  have hprof0 : LocallyIntegrable
      (fun z : ℂ => MatedCRTHarmonic.CellScaling.coneRadial γ 0
        (fun s => B₀ s ω) (fun s => B₀' s ω) (-Real.log ‖z‖)) volume := by
    simpa only [MatedCRTHarmonic.LQGCone.coneRadial_eq_Q_add_motConeRadial,
      MatedCRTHarmonic.CellScaling.lqgQ, QuantumZipper.Qc] using hω0
  have hlocal := zeroCone_local_field_eq γ (X₀ ω) (Xt ω)
    (fun s => B₀ s ω) (fun s => B₀' s ω) g hfield hg hgli hprofγ hprof0
    (MatedCRTHarmonic.GMS4c.thickOpen V d) hthick
  exact MatedCRTHarmonic.GMS4c.lqgArea_restrict_eq_of_localField_eq
    γ V hd hlocal hωv0 hωvXt

/-- The actual zero-cone GMC satisfies the same compact-disk upper-mass
estimate as normalized whole-plane GMC. -/
theorem upperMassBoundZeroConeModel_holds
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling
      γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    UpperMassBoundZeroConeModel hγ D := by
  obtain ⟨Xt, hXt, harea⟩ := exists_zeroConeArea_local_wholePlane hγ D
  obtain ⟨ξ, β, hξ, hβ, hwhole⟩ := upperMassBoundWholePlaneModel_holds hγ hXt
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  obtain ⟨C₀, hC₀⟩ := hwhole ρ hρ
  let r : ℝ := (1 + ρ) / 2
  have hr : r ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> dsimp [r] <;> linarith [hρ.1, hρ.2]
  let δ₀ : ℝ := (1 - ρ) / 4
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith [hρ.2]
  let C : ℝ := max C₀ (δ₀ ^ (-β))
  refine ⟨C, fun δ hδ => ?_⟩
  by_cases hsmall : δ ≤ δ₀
  · have hball : ∀ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆ ball (0 : ℂ) r := by
      intro z hz w hw
      have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
      have hδw : ‖w - z‖ < δ := by simpa [dist_eq_norm] using hw
      have hnorm : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := congrArg norm (by abel : w = (w - z) + z)
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      exact mem_ball_zero_iff.2 (by dsimp [r, δ₀] at *; linarith)
    have hevent : {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δ ^ ξ) < zeroConeArea γ X₀ B₀ B₀' ω (ball z δ)} =ᵐ[P]
        {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Xt ω (ball z δ)} := by
      filter_upwards [harea r hr] with ω hω
      have hmass : ∀ z ∈ ball (0 : ℂ) ρ,
          zeroConeArea γ X₀ B₀ B₀' ω (ball z δ) =
          wholePlaneArea γ Xt ω (ball z δ) := by
        intro z hz
        have hh := congrArg (fun μ : Measure ℂ => μ (ball z δ)) hω
        rw [Measure.restrict_apply measurableSet_ball,
          Measure.restrict_apply measurableSet_ball] at hh
        simpa only [inter_eq_self_of_subset_left (hball z hz)] using hh
      apply propext
      constructor
      · rintro ⟨z, hz, hbad⟩
        exact ⟨z, hz, by rwa [← hmass z hz]⟩
      · rintro ⟨z, hz, hbad⟩
        exact ⟨z, hz, by rwa [hmass z hz]⟩
    have hpow : 0 ≤ δ ^ β := Real.rpow_nonneg hδ.1.le _
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < zeroConeArea γ X₀ B₀ B₀' ω (ball z δ)} =
          P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
            ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Xt ω (ball z δ)} :=
        measure_congr hevent
      _ ≤ ENNReal.ofReal (C₀ * δ ^ β) := hC₀ δ hδ
      _ ≤ ENNReal.ofReal (C * δ ^ β) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · letI : IsProbabilityMeasure P := D.isProbabilityMeasure
    have hδ₀δ : δ₀ ≤ δ := le_of_not_ge hsmall
    have hδpow : δ₀ ^ β ≤ δ ^ β :=
      Real.rpow_le_rpow hδ₀.le hδ₀δ hβ.le
    have hδ₀pow : 0 ≤ δ₀ ^ (-β) := Real.rpow_nonneg hδ₀.le _
    have hδpow0 : 0 ≤ δ ^ β := Real.rpow_nonneg hδ.1.le _
    have hid : δ₀ ^ (-β) * δ₀ ^ β = 1 := by
      rw [← Real.rpow_add hδ₀]
      simp
    have hCδ : 1 ≤ C * δ ^ β := by
      have h1 := mul_le_mul_of_nonneg_left hδpow hδ₀pow
      have h2 := mul_le_mul_of_nonneg_right
        (le_max_right C₀ (δ₀ ^ (-β))) hδpow0
      nlinarith
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
        ENNReal.ofReal (δ ^ ξ) < zeroConeArea γ X₀ B₀ B₀' ω (ball z δ)} ≤
          P Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C * δ ^ β) := by
        simpa using ENNReal.ofReal_le_ofReal hCδ

end MatedCRTHarmonic.GMCUpper
