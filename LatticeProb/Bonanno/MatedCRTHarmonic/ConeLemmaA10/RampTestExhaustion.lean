/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RampTestExhaustion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaExactMass

/-!
# Weighted ramp exhaustion for the whole-plane area bias

Compactly-supported Palm identities determine the mass-weighted identity on an interior disk
by ramp cutoffs. An increasing family of interior disks then gives the identity on the open unit
disk. The bounded field observable is carried through both limits by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

/-- Weighted compact-test expectations determine the mass-weighted identity on every fixed
interior disk. The ramp supports stay inside the normalization disk. -/
theorem integral_openBall_mul_of_test_expectations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {F : Ω → ℝ} {G : ℂ → ℝ} {B R : ℝ}
    (hRpos : 0 < R) (hRlt : R < 1)
    (hLoc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hMassInt : Integrable (fun ω => (μ ω (ball (0 : ℂ) 1)).toReal) P)
    (_hFmeas : AEStronglyMeasurable F P) (hB : 0 ≤ B)
    (hFbound : ∀ᵐ ω ∂P, ‖F ω‖ ≤ B)
    (hGmeas : AEStronglyMeasurable G volume)
    (hGbound : ∀ᵐ z ∂volume, ‖G z‖ ≤ B)
    (hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => F ω * ∫ z, f z ∂(μ ω)) P ∧
        ∫ ω, F ω * ∫ z, f z ∂(μ ω) ∂P = ∫ z, f z * G z) :
    Integrable (fun ω => F ω * (μ ω (ball (0 : ℂ) R)).toReal) P ∧
      ∫ ω, F ω * (μ ω (ball (0 : ℂ) R)).toReal ∂P =
        ∫ z in ball (0 : ℂ) R, G z := by
  let U : Set ℂ := ball (0 : ℂ) R
  let f : ℕ → ℂ → ℝ := fun n => QuantumZipper.FinArea.ramp U n
  let g : ℕ → Ω → ℝ := fun n ω => ∫ z, f n z ∂(μ ω)
  let q : ℕ → Ω → ℝ := fun n ω => F ω * g n ω
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
  have htestInt : ∀ n, Integrable (q n) P := by
    intro n
    exact (hTest (f n) (QuantumZipper.FinArea.continuous_ramp U n)
      (hcs n) (hsupport n) (hnonneg n)).1.congr
        (ae_of_all _ fun ω => by rfl)
  have htestEq : ∀ n, ∫ ω, q n ω ∂P = ∫ z, f n z * G z := by
    intro n
    exact (hTest (f n) (QuantumZipper.FinArea.continuous_ramp U n)
      (hcs n) (hsupport n) (hnonneg n)).2
  have hmassPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n => g n ω) atTop (𝓝 ((μ ω U).toReal)) := by
    filter_upwards [hLoc] with ω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hUfinite : μ ω U < ⊤ :=
      (measure_mono (ball_subset_closedBall : U ⊆ closedBall (0 : ℂ) R)).trans_lt
        hclosed.measure_lt_top
    have hindInt : Integrable (U.indicator (fun _ : ℂ => (1 : ℝ))) (μ ω) := by
      rw [integrable_indicator_iff isOpen_ball.measurableSet]
      exact integrableOn_const hUfinite.ne
    have hfnInt : ∀ n, Integrable (f n) (μ ω) := fun n =>
      (QuantumZipper.FinArea.continuous_ramp U n).integrable_of_hasCompactSupport
        (hcs n)
    have hbound : ∀ n z, ‖f n z‖ ≤ U.indicator (fun _ : ℂ => (1 : ℝ)) z := by
      intro n z
      by_cases hz : z ∈ U
      · rw [indicator_of_mem hz]
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n z)]
        exact QuantumZipper.FinArea.ramp_le_one U n z
      · rw [indicator_of_notMem hz, Real.norm_eq_abs, abs_of_nonneg (hnonneg n z)]
        change QuantumZipper.FinArea.ramp U n z ≤ 0
        rw [QuantumZipper.FinArea.ramp_eq_zero n hz]
    have hpoint : ∀ z, Tendsto (fun n => f n z) atTop
        (𝓝 (U.indicator (fun _ : ℂ => (1 : ℝ)) z)) := by
      intro z
      by_cases hz : z ∈ U
      · obtain ⟨N, hN⟩ := QuantumZipper.FinArea.exists_ramp_eq_one isOpen_ball hUc hz
        have hev : ∀ᶠ n : ℕ in atTop, f n z = 1 := by
          filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
          dsimp [f]
          exact le_antisymm (QuantumZipper.FinArea.ramp_le_one U n z)
            (hN ▸ QuantumZipper.FinArea.ramp_mono U z hn)
        simpa [indicator_of_mem hz] using
          (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
      · have hzero : ∀ n, f n z = 0 := fun n => QuantumZipper.FinArea.ramp_eq_zero n hz
        simpa [indicator_of_notMem hz, hzero] using tendsto_const_nhds
    have hconv := tendsto_integral_of_dominated_convergence
      (fun z => U.indicator (fun _ : ℂ => (1 : ℝ)) z)
      (fun n => (hfnInt n).aestronglyMeasurable) hindInt
      (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hpoint)
    have hconv' : Tendsto (fun n => ∫ z, f n z ∂(μ ω)) atTop
        (𝓝 (∫ z, U.indicator (fun _ : ℂ => (1 : ℝ)) z ∂(μ ω))) := by
      simpa [g] using hconv
    have hmassEq :
        (∫ z, U.indicator (fun _ : ℂ => (1 : ℝ)) z ∂(μ ω)) = (μ ω U).toReal := by
      change (∫ z, (ball (0 : ℂ) R).indicator (fun _ : ℂ => (1 : ℝ)) z ∂(μ ω)) = _
      change (∫ z, (ball (0 : ℂ) R).indicator 1 z ∂(μ ω)) = _
      rw [integral_indicator_one (μ := μ ω) (s := ball (0 : ℂ) R) measurableSet_ball,
        measureReal_def]
    rw [← hmassEq]
    exact hconv'
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun n => q n ω) atTop
      (𝓝 (F ω * (μ ω U).toReal)) := by
    filter_upwards [hmassPoint] with ω hω
    exact tendsto_const_nhds.mul hω
  have hdom : Integrable (fun ω => B * (μ ω (ball (0 : ℂ) 1)).toReal) P :=
    hMassInt.const_mul B
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖q n ω‖ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := by
    intro n
    filter_upwards [hFbound, hLoc] with ω hFω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hfull : (μ ω (ball (0 : ℂ) 1)).toReal ≥ 0 := ENNReal.toReal_nonneg
    have hfinite : μ ω (ball (0 : ℂ) 1) ≠ ⊤ := by
      exact ne_of_lt ((measure_mono (ball_subset_closedBall :
        ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)).trans_lt
          (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_lt_top)
    have hle : g n ω ≤ (μ ω (ball (0 : ℂ) 1)).toReal := by
      have hindInt : Integrable ((ball (0 : ℂ) 1).indicator
          (fun _ : ℂ => (1 : ℝ))) (μ ω) := by
        rw [integrable_indicator_iff measurableSet_ball]
        exact integrableOn_const hfinite
      have hfInt : Integrable (f n) (μ ω) :=
        (QuantumZipper.FinArea.continuous_ramp U n).integrable_of_hasCompactSupport (hcs n)
      have hpointwise : ∀ᵐ z ∂(μ ω), f n z ≤
          (ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z := by
        filter_upwards with z
        by_cases hz : z ∈ ball (0 : ℂ) 1
        · rw [indicator_of_mem hz]
          change QuantumZipper.FinArea.ramp U n z ≤ 1
          exact QuantumZipper.FinArea.ramp_le_one U n z
        · rw [indicator_of_notMem hz]
          have hzu : z ∉ U := fun h => hz (hclosedSub (ball_subset_closedBall h))
          have : f n z = 0 := QuantumZipper.FinArea.ramp_eq_zero n hzu
          simp [this]
      calc
        g n ω = ∫ z, f n z ∂(μ ω) := rfl
        _ ≤ ∫ z, (ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z ∂(μ ω) :=
          integral_mono_ae hfInt hindInt hpointwise
        _ = (μ ω (ball (0 : ℂ) 1)).toReal := by
          change (∫ z, (ball (0 : ℂ) 1).indicator 1 z ∂(μ ω)) = _
          rw [integral_indicator_one (μ := μ ω) (s := ball (0 : ℂ) 1)
            measurableSet_ball, measureReal_def]
    have hgn : 0 ≤ g n ω := integral_nonneg_of_ae
      (ae_of_all _ (fun z => hnonneg n z))
    have hgNorm : ‖g n ω‖ = g n ω := by
      rw [Real.norm_eq_abs, abs_of_nonneg hgn]
    calc
      ‖q n ω‖ = ‖F ω‖ * ‖g n ω‖ := norm_mul _ _
      _ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := by
        rw [hgNorm]
        calc
          ‖F ω‖ * g n ω ≤ B * g n ω := mul_le_mul_of_nonneg_right hFω hgn
          _ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := mul_le_mul_of_nonneg_left hle hB
  have hqmeas : ∀ n, AEStronglyMeasurable (q n) P := fun n => (htestInt n).aestronglyMeasurable
  have hlimMeas : AEStronglyMeasurable (fun ω => F ω * (μ ω U).toReal) P := by
    exact aestronglyMeasurable_of_tendsto_ae atTop hqmeas hpoint
  have hlimBound : ∀ᵐ ω ∂P,
      ‖F ω * (μ ω U).toReal‖ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := by
    filter_upwards [hFbound, hLoc] with ω hFω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hfinite : μ ω (ball (0 : ℂ) 1) ≠ ⊤ := by
      exact ne_of_lt ((measure_mono (ball_subset_closedBall :
        ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)).trans_lt
          (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_lt_top)
    have hle : (μ ω U).toReal ≤ (μ ω (ball (0 : ℂ) 1)).toReal :=
      ENNReal.toReal_mono hfinite
        (measure_mono (ball_subset_closedBall.trans hclosedSub))
    have hnonneg : 0 ≤ (μ ω U).toReal := ENNReal.toReal_nonneg
    rw [norm_mul]
    have hnorm : ‖(μ ω U).toReal‖ = (μ ω U).toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [hnorm]
    calc
      ‖F ω‖ * (μ ω U).toReal ≤ B * (μ ω U).toReal :=
        mul_le_mul_of_nonneg_right hFω hnonneg
      _ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := mul_le_mul_of_nonneg_left hle hB
  have hlimInt : Integrable (fun ω => F ω * (μ ω U).toReal) P :=
    Integrable.mono' hdom hlimMeas hlimBound
  have hleft : Tendsto (fun n => ∫ ω, q n ω ∂P) atTop
      (𝓝 (∫ ω, F ω * (μ ω U).toReal ∂P)) := by
    convert tendsto_integral_of_dominated_convergence
      (fun ω => B * (μ ω (ball (0 : ℂ) 1)).toReal) hqmeas hdom hbound hpoint using 1
  have hvolFinite : volume U < ⊤ :=
    (measure_mono (ball_subset_closedBall : U ⊆ closedBall (0 : ℂ) R)).trans_lt
      hclosed.measure_lt_top
  have hindInt : Integrable (U.indicator (fun _ : ℂ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff isOpen_ball.measurableSet]
    exact integrableOn_const hvolFinite.ne
  have hvolBound : Integrable (fun z => B * U.indicator (fun _ : ℂ => (1 : ℝ)) z) volume := by
    have hEq : (fun z => B * U.indicator (fun _ : ℂ => (1 : ℝ)) z) =
        U.indicator (fun _ : ℂ => B) := by
      funext z
      by_cases hz : z ∈ U <;> simp [hz]
    rw [hEq, integrable_indicator_iff isOpen_ball.measurableSet]
    exact integrableOn_const hvolFinite.ne
  have hfGmeas : ∀ n, AEStronglyMeasurable (fun z => f n z * G z) volume := by
    intro n
    exact ((QuantumZipper.FinArea.continuous_ramp U n).aestronglyMeasurable.mul hGmeas)
  have hfGbound : ∀ n, ∀ᵐ z ∂volume,
      ‖f n z * G z‖ ≤ B * U.indicator (fun _ : ℂ => (1 : ℝ)) z := by
    intro n
    filter_upwards [hGbound] with z hz
    by_cases hzu : z ∈ U
    · rw [indicator_of_mem hzu]
      calc
        ‖f n z * G z‖ = ‖f n z‖ * ‖G z‖ := norm_mul _ _
        _ ≤ 1 * B := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n z)]
          calc
            f n z * ‖G z‖ ≤ 1 * ‖G z‖ :=
              mul_le_mul_of_nonneg_right (QuantumZipper.FinArea.ramp_le_one U n z)
                (norm_nonneg _)
            _ ≤ 1 * B := mul_le_mul_of_nonneg_left hz zero_le_one
        _ = B * 1 := by ring
    · rw [indicator_of_notMem hzu]
      change ‖QuantumZipper.FinArea.ramp U n z * G z‖ ≤ B * 0
      rw [QuantumZipper.FinArea.ramp_eq_zero n hzu]
      simp
  have hGpoint : ∀ z, Tendsto (fun n => f n z * G z) atTop
      (𝓝 (U.indicator G z)) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨N, hN⟩ := QuantumZipper.FinArea.exists_ramp_eq_one isOpen_ball hUc hz
      have hev : ∀ᶠ n : ℕ in atTop, f n z = 1 := by
        filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
        dsimp [f]
        exact le_antisymm (QuantumZipper.FinArea.ramp_le_one U n z)
          (hN ▸ QuantumZipper.FinArea.ramp_mono U z hn)
      have hftend : Tendsto (fun n => f n z) atTop (𝓝 (1 : ℝ)) := by
        exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
      simpa [indicator_of_mem hz] using hftend.mul_const (G z)
    · have hzero : ∀ n, f n z = 0 := fun n => QuantumZipper.FinArea.ramp_eq_zero n hz
      simpa [indicator_of_notMem hz, hzero] using tendsto_const_nhds
  have hright := tendsto_integral_of_dominated_convergence
    (fun z => B * U.indicator (fun _ : ℂ => (1 : ℝ)) z) hfGmeas hvolBound
    hfGbound (ae_of_all _ hGpoint)
  have hseq : ∀ n, (∫ ω, q n ω ∂P) = ∫ z, f n z * G z := htestEq
  have hleft' : Tendsto (fun n => ∫ z, f n z * G z) atTop
      (𝓝 (∫ ω, F ω * (μ ω U).toReal ∂P)) := by
    rw [← (funext hseq)]
    exact hleft
  have hright' : Tendsto (fun n => ∫ z, f n z * G z) atTop
      (𝓝 (∫ z, U.indicator G z ∂volume)) := hright
  have heq := tendsto_nhds_unique hleft' hright'
  refine ⟨hlimInt, ?_⟩
  calc
    ∫ ω, F ω * (μ ω U).toReal ∂P = ∫ z, U.indicator G z ∂volume := heq
    _ = ∫ z in U, G z := integral_indicator isOpen_ball.measurableSet

/-- Weighted compact-test expectations determine the mass-weighted identity on the full open
unit disk. The outer exhaustion also uses only interior balls, so every ramp test remains within
the normalization disk. -/
theorem integral_unitDisk_mul_of_test_expectations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {F : Ω → ℝ} {G : ℂ → ℝ} {B : ℝ}
    (hLoc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hMassInt : Integrable (fun ω => (μ ω (ball (0 : ℂ) 1)).toReal) P)
    (_hFmeas : AEStronglyMeasurable F P) (hB : 0 ≤ B)
    (hFbound : ∀ᵐ ω ∂P, ‖F ω‖ ≤ B)
    (hGmeas : AEStronglyMeasurable G volume)
    (hGbound : ∀ᵐ z ∂volume, ‖G z‖ ≤ B)
    (hTest : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ball (0 : ℂ) 1 → (∀ z, 0 ≤ f z) →
      Integrable (fun ω => F ω * ∫ z, f z ∂(μ ω)) P ∧
        ∫ ω, F ω * ∫ z, f z ∂(μ ω) ∂P = ∫ z, f z * G z) :
    Integrable (fun ω => F ω * (μ ω (ball (0 : ℂ) 1)).toReal) P ∧
      ∫ ω, F ω * (μ ω (ball (0 : ℂ) 1)).toReal ∂P =
        ∫ z in ball (0 : ℂ) 1, G z := by
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
  have hBall : ∀ n, Integrable
      (fun ω => F ω * (μ ω (ball (0 : ℂ) (R n))).toReal) P ∧
        ∫ ω, F ω * (μ ω (ball (0 : ℂ) (R n))).toReal ∂P =
          ∫ z in ball (0 : ℂ) (R n), G z := by
    intro n
    exact integral_openBall_mul_of_test_expectations (hRpos n) (hRlt n)
      hLoc hMassInt _hFmeas hB hFbound hGmeas hGbound hTest
  have hmassPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n => (μ ω (ball (0 : ℂ) (R n))).toReal) atTop
        (𝓝 ((μ ω (ball (0 : ℂ) 1)).toReal)) := by
    filter_upwards [hLoc] with ω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hfull : μ ω (ball (0 : ℂ) 1) ≠ ⊤ := by
      exact ne_of_lt ((measure_mono (ball_subset_closedBall :
        ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)).trans_lt
          (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_lt_top)
    have hmeasure := tendsto_measure_iUnion_atTop (μ := μ ω) hSetMono
    rw [hUnion] at hmeasure
    exact (ENNReal.tendsto_toReal hfull).comp hmeasure
  let q : ℕ → Ω → ℝ := fun n ω => F ω * (μ ω (ball (0 : ℂ) (R n))).toReal
  have hqmeas : ∀ n, AEStronglyMeasurable (q n) P := fun n => (hBall n).1.aestronglyMeasurable
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun n => q n ω) atTop
      (𝓝 (F ω * (μ ω (ball (0 : ℂ) 1)).toReal)) := by
    filter_upwards [hmassPoint] with ω hω
    exact tendsto_const_nhds.mul hω
  have hdom : Integrable (fun ω => B * (μ ω (ball (0 : ℂ) 1)).toReal) P :=
    hMassInt.const_mul B
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖q n ω‖ ≤
      B * (μ ω (ball (0 : ℂ) 1)).toReal := by
    intro n
    filter_upwards [hFbound, hLoc] with ω hFω hloc
    letI : IsLocallyFiniteMeasure (μ ω) := hloc
    have hfull : (μ ω (ball (0 : ℂ) 1)).toReal ≥ 0 := ENNReal.toReal_nonneg
    have hfullFinite : μ ω (ball (0 : ℂ) 1) ≠ ⊤ := by
      exact ne_of_lt ((measure_mono (ball_subset_closedBall :
        ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)).trans_lt
          (isCompact_closedBall (0 : ℂ) (1 : ℝ)).measure_lt_top)
    have hle : (μ ω (ball (0 : ℂ) (R n))).toReal ≤
        (μ ω (ball (0 : ℂ) 1)).toReal :=
      ENNReal.toReal_mono hfullFinite (measure_mono (Metric.ball_subset_ball (le_of_lt (hRlt n))))
    have hsmallNonneg : 0 ≤ (μ ω (ball (0 : ℂ) (R n))).toReal := ENNReal.toReal_nonneg
    have hnormSmall : ‖(μ ω (ball (0 : ℂ) (R n))).toReal‖ =
        (μ ω (ball (0 : ℂ) (R n))).toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg hsmallNonneg]
    have hnormq : ‖q n ω‖ = ‖F ω‖ * (μ ω (ball (0 : ℂ) (R n))).toReal := by
      dsimp [q]
      calc
        ‖F ω * (μ ω (ball (0 : ℂ) (R n))).toReal‖ =
            ‖F ω‖ * ‖(μ ω (ball (0 : ℂ) (R n))).toReal‖ := norm_mul _ _
        _ = ‖F ω‖ * (μ ω (ball (0 : ℂ) (R n))).toReal := by rw [hnormSmall]
    calc
      ‖q n ω‖ = ‖F ω‖ * (μ ω (ball (0 : ℂ) (R n))).toReal := hnormq
      _ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal :=
        calc
          ‖F ω‖ * (μ ω (ball (0 : ℂ) (R n))).toReal ≤
              B * (μ ω (ball (0 : ℂ) (R n))).toReal :=
            mul_le_mul_of_nonneg_right hFω hsmallNonneg
          _ ≤ B * (μ ω (ball (0 : ℂ) 1)).toReal := mul_le_mul_of_nonneg_left hle hB
  have hlimMeas : AEStronglyMeasurable
      (fun ω => F ω * (μ ω (ball (0 : ℂ) 1)).toReal) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hqmeas hpoint
  have hlimBound : ∀ᵐ ω ∂P, ‖F ω * (μ ω (ball (0 : ℂ) 1)).toReal‖ ≤
      B * (μ ω (ball (0 : ℂ) 1)).toReal := by
    filter_upwards [hFbound] with ω hFω
    rw [norm_mul]
    have hnonneg : 0 ≤ (μ ω (ball (0 : ℂ) 1)).toReal := ENNReal.toReal_nonneg
    have hnorm : ‖(μ ω (ball (0 : ℂ) 1)).toReal‖ =
        (μ ω (ball (0 : ℂ) 1)).toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hFω hnonneg
  have hlimInt : Integrable
      (fun ω => F ω * (μ ω (ball (0 : ℂ) 1)).toReal) P :=
    Integrable.mono' hdom hlimMeas hlimBound
  have hleft := tendsto_integral_of_dominated_convergence
    (fun ω => B * (μ ω (ball (0 : ℂ) 1)).toReal) hqmeas hdom hbound hpoint
  have hGseqbound : ∀ n, ∀ᵐ z ∂volume,
      ‖(ball (0 : ℂ) (R n)).indicator G z‖ ≤
        B * (ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z := by
    intro n
    filter_upwards [hGbound] with z hz
    by_cases hzn : z ∈ ball (0 : ℂ) (R n)
    · have hz1 : z ∈ ball (0 : ℂ) 1 :=
        Metric.ball_subset_ball (le_of_lt (hRlt n)) hzn
      rw [indicator_of_mem hzn, indicator_of_mem hz1]
      simpa [one_mul] using hz
    · rw [indicator_of_notMem hzn]
      by_cases hz1 : z ∈ ball (0 : ℂ) 1
      · rw [indicator_of_mem hz1]
        simp [hB]
      · rw [indicator_of_notMem hz1]
        simp
  have hvolBound : Integrable
      (fun z => B * (ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z) volume := by
    have hEq : (fun z => B * (ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z) =
        (ball (0 : ℂ) 1).indicator (fun _ : ℂ => B) := by
      funext z
      by_cases hz : z ∈ ball (0 : ℂ) 1 <;> simp [hz]
    rw [hEq, integrable_indicator_iff measurableSet_ball]
    exact integrableOn_const (measure_ball_ne_top : volume (ball (0 : ℂ) 1) ≠ ⊤)
  have hGseqmeas : ∀ n, AEStronglyMeasurable
      ((ball (0 : ℂ) (R n)).indicator G) volume := by
    intro n
    exact hGmeas.indicator measurableSet_ball
  have hGpoint : ∀ z, Tendsto (fun n => (ball (0 : ℂ) (R n)).indicator G z) atTop
      (𝓝 ((ball (0 : ℂ) 1).indicator G z)) := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (hUnion ▸ hz)
      have hevent : ∀ᶠ m : ℕ in atTop, z ∈ ball (0 : ℂ) (R m) :=
        (eventually_atTop.2 ⟨n, fun m hnm => hSetMono hnm hn⟩)
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with m hm
      rw [indicator_of_mem hm, indicator_of_mem hz]
    · have hzero : ∀ n, z ∉ ball (0 : ℂ) (R n) := by
        intro n hn
        exact hz (hUnion ▸ mem_iUnion.mpr ⟨n, hn⟩)
      simpa [indicator_of_notMem hz, hzero] using tendsto_const_nhds
  have hright := tendsto_integral_of_dominated_convergence
    (fun z => B * ((ball (0 : ℂ) 1).indicator (fun _ : ℂ => (1 : ℝ)) z))
    hGseqmeas hvolBound hGseqbound (ae_of_all _ hGpoint)
  have hBallEq : ∀ n, (∫ ω, q n ω ∂P) =
      ∫ z, (ball (0 : ℂ) (R n)).indicator G z ∂volume := by
    intro n
    rw [(hBall n).2, ← integral_indicator measurableSet_ball]
  have hleft' : Tendsto
      (fun n => ∫ z, (ball (0 : ℂ) (R n)).indicator G z ∂volume) atTop
      (𝓝 (∫ ω, F ω * (μ ω (ball (0 : ℂ) 1)).toReal ∂P)) := by
    rw [← funext hBallEq]
    exact hleft
  have heq := tendsto_nhds_unique hleft' hright
  refine ⟨hlimInt, ?_⟩
  calc
    ∫ ω, F ω * (μ ω (ball (0 : ℂ) 1)).toReal ∂P =
        ∫ z, (ball (0 : ℂ) 1).indicator G z ∂volume := heq
    _ = ∫ z in ball (0 : ℂ) 1, G z := integral_indicator measurableSet_ball

end MatedCRTHarmonic.ConeLemmaA10

