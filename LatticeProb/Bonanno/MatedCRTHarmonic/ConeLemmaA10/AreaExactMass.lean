/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.AreaExactMass at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.NoAtom
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.UniformIntegrability
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaTestL1

/-!
# Exact first moment inside the normalization circle

This file records exact first moments of the whole-plane GMC approximations away from the
normalization boundary, together with the analytic cutoff step that recovers disk masses from
compactly supported test expectations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeLemmaA10
/-- For a circle contained in the unit disk, the correction term `betaAvg` vanishes. -/
lemma betaAvg_eq_zero_of_inside_circle {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) : LQGDimension.Osc37.betaAvg r z = 0 := by
  unfold LQGDimension.Osc37.betaAvg
  apply Real.circleAverage_const_on_circle
  intro y hy
  rw [mem_sphere_iff_norm, abs_of_pos hr] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    calc
      ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 := by rw [hy]; linarith
  rw [max_eq_right hy1, Real.log_one]

/-- The circle-average variance is exactly `-log r` when the averaging circle is inside
the normalization disk. -/
lemma gffCircleCov_self_eq_neg_log {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) : LQGDimension.gffCircleCov r z r z = -Real.log r := by
  rw [LQGDimension.Osc37.gffCircleCov_formula hr,
    LQGDimension.Osc37.aAvg_self hr]
  rw [betaAvg_eq_zero_of_inside_circle hr hz]
  ring

/-- The expected density of the circle-average GMC approximation is exactly one in the
interior of the normalization disk. -/
lemma lintegral_dens_eq_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ + r ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) ∂P = 1 := by
  have hm : ∀ ω, ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)) =
      ENNReal.ofReal (r ^ (γ ^ 2 / 2)) * ENNReal.ofReal (Real.exp (γ * H r z ω)) := fun ω =>
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)
  simp_rw [hm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    LQGMetric.DG.lintegral_exp_circleAvg hH hr z γ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  rw [ENNReal.ofReal_eq_one]
  rw [gffCircleCov_self_eq_neg_log hr hz, Real.rpow_def_of_pos hr, ← Real.exp_add]
  rw [Real.exp_eq_one_iff]
  ring


/-- An open set's measure is the supremum of the integrals of its continuous ramp cutoffs. -/
lemma measure_eq_iSup_ramp_lintegral (ν : Measure ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    ν U = ⨆ n, ∫⁻ z, ENNReal.ofReal (QuantumZipper.FinArea.ramp U n z) ∂ν := by
  have hmono : Monotone fun n =>
      ∫⁻ z, ENNReal.ofReal (QuantumZipper.FinArea.ramp U n z) ∂ν := fun n m hnm =>
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal
      (QuantumZipper.FinArea.ramp_mono U z hnm)
  have hsup : (⨆ n, ∫⁻ z, ENNReal.ofReal (QuantumZipper.FinArea.ramp U n z) ∂ν) = ν U := by
    rw [← lintegral_iSup
      (f := fun n z => ENNReal.ofReal (QuantumZipper.FinArea.ramp U n z))
      (fun n => ENNReal.measurable_ofReal.comp
        (QuantumZipper.FinArea.continuous_ramp U n).measurable)
      (fun n m hnm z => ENNReal.ofReal_le_ofReal
        (QuantumZipper.FinArea.ramp_mono U z hnm)),
      ← lintegral_indicator_one hU.measurableSet]
    congr 1
    funext z
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz, Pi.one_apply]
      obtain ⟨n, hn⟩ := QuantumZipper.FinArea.exists_ramp_eq_one hU hUc hz
      refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_one.2
        (QuantumZipper.FinArea.ramp_le_one U m z)) ?_
      exact (le_iSup (fun m => ENNReal.ofReal
        (QuantumZipper.FinArea.ramp U m z)) n).trans' (by simp [hn])
    · rw [indicator_of_notMem hz]
      have hzero : ∀ m, QuantumZipper.FinArea.ramp U m z = 0 := fun m =>
        QuantumZipper.FinArea.ramp_eq_zero m hz
      simp [hzero]
  exact hsup.symm

/-- Exact expected mass of an interior open ball from exact expectations of nonnegative
compactly-supported continuous tests. This is the analytic ramp and monotone-convergence step. -/
theorem lintegral_openBall_eq_of_test_expectations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {R : ℝ} (hRpos : 0 < R) (hRlt : R < 1)
    (hLoc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => ∫ z, f z ∂(μ ω)) P ∧
        ∫ ω, ∫ z, f z ∂(μ ω) ∂P = ∫ z, f z) :
    AEMeasurable (fun ω => μ ω (ball (0 : ℂ) R)) P ∧
      ∫⁻ ω, μ ω (ball (0 : ℂ) R) ∂P = volume (ball (0 : ℂ) R) := by
  let U : Set ℂ := ball (0 : ℂ) R
  let f : ℕ → ℂ → ℝ := fun n => QuantumZipper.FinArea.ramp U n
  let g : ℕ → Ω → ℝ := fun n ω => ∫ z, f n z ∂(μ ω)
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ∫⁻ z, ENNReal.ofReal (f n z) ∂(μ ω)
  have hUc : Uᶜ.Nonempty := by
    refine ⟨(2 : ℂ), ?_⟩
    change (2 : ℂ) ∉ ball (0 : ℂ) R
    rw [mem_ball, dist_zero_right]
    norm_num
    linarith
  have hclosed : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hclosedSub : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hRlt
  have hts : ∀ n, tsupport (f n) ⊆ closedBall (0 : ℂ) R := by
    intro n
    apply closure_minimal
    · intro z hz
      have hzU : z ∈ U := by
        by_contra hzu
        exact hz (QuantumZipper.FinArea.ramp_eq_zero n hzu)
      change dist z 0 < R at hzU
      exact mem_closedBall.mpr hzU.le
    · exact isClosed_closedBall
  have hcs : ∀ n, HasCompactSupport (f n) := by
    intro n
    refine HasCompactSupport.intro hclosed fun z hz => ?_
    apply QuantumZipper.FinArea.ramp_eq_zero n
    intro hzu
    apply hz
    rw [mem_closedBall, dist_zero_right]
    rw [mem_ball, dist_zero_right] at hzu
    exact le_of_lt hzu
  have hsupport : ∀ n, tsupport (f n) ⊆ ball (0 : ℂ) 1 := fun n =>
    (hts n).trans hclosedSub
  have hnonneg : ∀ n z, 0 ≤ f n z := fun n z =>
    QuantumZipper.FinArea.ramp_nonneg U n z
  have hTI : ∀ n, Integrable (g n) P := fun n =>
    (hTest (f n) (QuantumZipper.FinArea.continuous_ramp U n) (hcs n)
      (hsupport n) (hnonneg n)).1
  have hTE : ∀ n, ∫ ω, g n ω ∂P = ∫ z, f n z := fun n =>
    (hTest (f n) (QuantumZipper.FinArea.continuous_ramp U n) (hcs n)
      (hsupport n) (hnonneg n)).2
  have hFae : ∀ n, ∀ᵐ ω ∂P, F n ω = ENNReal.ofReal (g n ω) := by
    intro n
    filter_upwards [hLoc] with ω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hi : Integrable (f n) (μ ω) :=
      (QuantumZipper.FinArea.continuous_ramp U n).integrable_of_hasCompactSupport (hcs n)
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (hnonneg n))).symm
  have hFaemeas : ∀ n, AEMeasurable (F n) P := by
    intro n
    have hEq : ENNReal.ofReal ∘ g n =ᵐ[P] F n :=
      (hFae n).mono fun ω hω => hω.symm
    exact (ENNReal.measurable_ofReal.comp_aemeasurable (hTI n).aemeasurable).congr hEq
  have hFmono : ∀ ω, Monotone fun n => F n ω := by
    intro ω n m hnm
    exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal
      (QuantumZipper.FinArea.ramp_mono U z hnm)
  have htestLin : ∀ n,
      ∫⁻ ω, F n ω ∂P = ∫⁻ z, ENNReal.ofReal (f n z) ∂volume := by
    intro n
    have hgNonneg : 0 ≤ᵐ[P] g n := by
      filter_upwards with ω
      exact integral_nonneg_of_ae (ae_of_all _ (fun z => hnonneg n z))
    have hfInt : Integrable (f n) volume :=
      (QuantumZipper.FinArea.continuous_ramp U n).integrable_of_hasCompactSupport (hcs n)
    calc
      ∫⁻ ω, F n ω ∂P = ∫⁻ ω, ENNReal.ofReal (g n ω) ∂P :=
        lintegral_congr_ae (hFae n)
      _ = ENNReal.ofReal (∫ ω, g n ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hTI n) hgNonneg).symm
      _ = ENNReal.ofReal (∫ z, f n z ∂volume) := by rw [hTE n]
      _ = ∫⁻ z, ENNReal.ofReal (f n z) ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hfInt (ae_of_all _ (hnonneg n))
  have hmass : (fun ω => μ ω U) = fun ω => ⨆ n, F n ω := by
    funext ω
    exact measure_eq_iSup_ramp_lintegral (μ ω) isOpen_ball hUc
  have hmassAemeas : AEMeasurable (fun ω => μ ω U) P := by
    rw [hmass]
    exact AEMeasurable.iSup hFaemeas
  have hball : ∫⁻ ω, μ ω U ∂P = ⨆ n, ∫⁻ ω, F n ω ∂P := by
    rw [hmass, lintegral_iSup' hFaemeas (ae_of_all _ hFmono)]
  have hvolume : (⨆ n, ∫⁻ z, ENNReal.ofReal (f n z) ∂volume) = volume U := by
    exact (measure_eq_iSup_ramp_lintegral volume isOpen_ball hUc).symm
  refine ⟨hmassAemeas, ?_⟩
  rw [hball]
  calc
    (⨆ n, ∫⁻ ω, F n ω ∂P) = ⨆ n, ∫⁻ z, ENNReal.ofReal (f n z) ∂volume := by
      congr with n
      exact htestLin n
    _ = volume U := hvolume

/-- Exact expected mass of the open unit disk, obtained by exhausting it with compactly
supported tests whose supports remain strictly inside the normalization disk. -/
theorem lintegral_unitDisk_eq_of_test_expectations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    (hLoc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => ∫ z, f z ∂(μ ω)) P ∧
        ∫ ω, ∫ z, f z ∂(μ ω) ∂P = ∫ z, f z) :
    AEMeasurable (fun ω => μ ω (ball (0 : ℂ) 1)) P ∧
      ∫⁻ ω, μ ω (ball (0 : ℂ) 1) ∂P = volume (ball (0 : ℂ) 1) := by
  let R : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hRpos : ∀ n, 0 < R n := by
    intro n
    dsimp [R]
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hfrac : (1 : ℝ) / ((n : ℝ) + 2) < 1 :=
      (div_lt_one hden).2 (by nlinarith)
    linarith
  have hRlt : ∀ n, R n < 1 := by
    intro n
    dsimp [R]
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hfrac : 0 < (1 : ℝ) / ((n : ℝ) + 2) := div_pos zero_lt_one hden
    linarith
  have hRmono : Monotone R := by
    intro n m hnm
    dsimp [R]
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hnmCast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hnm' : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by linarith
    have hinv : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le hn hnm'
    linarith
  have hSetMono : Monotone fun n => ball (0 : ℂ) (R n) := by
    intro n m hnm
    exact Metric.ball_subset_ball (hRmono hnm)
  have hUnion : (⋃ n, ball (0 : ℂ) (R n)) = ball (0 : ℂ) 1 := by
    ext z
    constructor
    · intro hz
      rcases mem_iUnion.1 hz with ⟨n, hn⟩
      rw [mem_ball, dist_zero_right] at hn ⊢
      exact lt_trans hn (hRlt n)
    · intro hz
      rw [mem_ball, dist_zero_right] at hz
      apply mem_iUnion.mpr
      have hd : 0 < 1 - ‖z‖ := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ‖z‖))
      refine ⟨n, ?_⟩
      rw [mem_ball, dist_zero_right]
      dsimp [R]
      have hden : 0 < (n : ℝ) + 2 := by positivity
      have hlarge : 1 / (1 - ‖z‖) < (n : ℝ) + 2 :=
        lt_trans hn (by norm_num)
      have hlarge' : 1 < ((n : ℝ) + 2) * (1 - ‖z‖) :=
        (div_lt_iff₀ hd).mp hlarge
      have hrecip : 1 / ((n : ℝ) + 2) < 1 - ‖z‖ := by
        rw [div_lt_iff₀ hden]
        nlinarith [hlarge']
      linarith
  have hBall : ∀ n,
      AEMeasurable (fun ω => μ ω (ball (0 : ℂ) (R n))) P ∧
        ∫⁻ ω, μ ω (ball (0 : ℂ) (R n)) ∂P = volume (ball (0 : ℂ) (R n)) := by
    intro n
    exact lintegral_openBall_eq_of_test_expectations (hRpos n) (hRlt n) hLoc hTest
  have hmass : ∀ ω, μ ω (ball (0 : ℂ) 1) = ⨆ n, μ ω (ball (0 : ℂ) (R n)) := by
    intro ω
    calc
      μ ω (ball (0 : ℂ) 1) = μ ω (⋃ n, ball (0 : ℂ) (R n)) := by rw [hUnion]
      _ = ⨆ n, μ ω (ball (0 : ℂ) (R n)) := hSetMono.measure_iUnion
  have hmassMono : ∀ ω, Monotone fun n => μ ω (ball (0 : ℂ) (R n)) := by
    intro ω n m hnm
    exact measure_mono (hSetMono hnm)
  have hMassAemeas : AEMeasurable (fun ω => μ ω (ball (0 : ℂ) 1)) P := by
    rw [show (fun ω => μ ω (ball (0 : ℂ) 1)) =
      fun ω => ⨆ n, μ ω (ball (0 : ℂ) (R n)) from funext hmass]
    exact AEMeasurable.iSup (fun n => (hBall n).1)
  refine ⟨hMassAemeas, ?_⟩
  calc
    ∫⁻ ω, μ ω (ball (0 : ℂ) 1) ∂P =
        ⨆ n, ∫⁻ ω, μ ω (ball (0 : ℂ) (R n)) ∂P := by
          rw [show (fun ω => μ ω (ball (0 : ℂ) 1)) =
            fun ω => ⨆ n, μ ω (ball (0 : ℂ) (R n)) from funext hmass]
          exact lintegral_iSup' (fun n => (hBall n).1)
            (ae_of_all _ hmassMono)
    _ = ⨆ n, volume (ball (0 : ℂ) (R n)) := by
      congr with n
      exact (hBall n).2
    _ = volume (ball (0 : ℂ) 1) := by
      calc
        (⨆ n, volume (ball (0 : ℂ) (R n))) = volume (⋃ n, ball (0 : ℂ) (R n)) :=
          hSetMono.measure_iUnion.symm
        _ = volume (ball (0 : ℂ) 1) := by rw [hUnion]

/-- Exact expected mass of the open unit disk for an `IsLQGAreaOf` limit. The exact
compact-test expectations come from L¹ convergence, with uniform integrability supplied by the
proved `exists_unitDisk_approx_moment` bound. -/
theorem lintegral_areaMeasure_unitDisk_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    AEMeasurable (fun ω => μ ω (ball (0 : ℂ) 1)) P ∧
      ∫⁻ ω, μ ω (ball (0 : ℂ) 1) ∂P = volume (ball (0 : ℂ) 1) := by
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hLoc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.1
  have hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => ∫ z, f z ∂(μ ω)) P ∧
        ∫ ω, ∫ z, f z ∂(μ ω) ∂P = ∫ z, f z := by
    intro f hf _hfc hfs hfn
    have h := integral_areaTestIntegral_eq_volume hH hHm hγ hγ2 hμ hf hfs hfn
    refine ⟨?_, ?_⟩
    · exact h.1
    · exact h.2
  exact lintegral_unitDisk_eq_of_test_expectations hLoc hTest
  

end MatedCRTHarmonic.ConeLemmaA10

