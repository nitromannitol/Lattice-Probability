/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.BallMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.ChiBound
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16MeasArea

/-!
# The ball-mass tail bound `BallMassTail` and its corollaries

`BallMassTail` (`ChiBound.lean`) is Markov's inequality applied to DZZ Lemma 2.10's first moment
`E μ_h(B(x,ρ)) ≤ C_γ π ρ²` (`LQGMetric.lintegral_qAreaMeasureOn_ball_le`,
`Dimension/GMCBall.lean`), as prescribed in `decisions/DEC-A.md` D-A1 (DIM.S-chi-le-2).

The missing input was the a.e.-measurability of `ω ↦ μ_{X ω}(B(x,ρ))`
(`aemeasurable_qAreaMeasureOn_ball`). Following QuantumZipper's
`Prop16Area.Meas` (`Proofs/Section5/Prop16MeasArea.lean`, own elementary argument there, after
`LQGMeas.measurable_qAreaMeasure_open`): on the full-measure event that the measure is a genuine
vague limit on `(0,1)²` (`ae_isVagueLimitOn_qAreaMeasureOn_openSquare`), the integral of a
continuous compactly supported test function is the measurable limit `Meas.Psi` of pre-limit
integrals, and the mass of the open ball is the monotone limit of the integrals of the cut-offs
`min 1 (n · dist(z, B(x,ρ)ᶜ))` (monotone convergence). Own elementary glue (AGENT_GUIDE cost rule).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG

/-- the cut-offs `min 1 (n · dist(z, B(x,ρ)ᶜ))` -/
def ballCut (x : ℂ) (ρ : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  min 1 ((n : ℝ) * Metric.infDist z (Metric.ball x ρ)ᶜ)

lemma continuous_ballCut (x : ℂ) (ρ : ℝ) (n : ℕ) : Continuous (ballCut x ρ n) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

lemma ballCut_of_notMem {x : ℂ} {ρ : ℝ} (n : ℕ) {z : ℂ} (hz : z ∉ Metric.ball x ρ) :
    ballCut x ρ n z = 0 := by
  unfold ballCut
  rw [Metric.infDist_zero_of_mem (mem_compl hz), mul_zero, min_eq_right zero_le_one]

lemma tsupport_ballCut_subset (x : ℂ) (ρ : ℝ) (n : ℕ) :
    tsupport (ballCut x ρ n) ⊆ Metric.closedBall x ρ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  by_contra h
  exact hz (ballCut_of_notMem n fun h' => h (Metric.ball_subset_closedBall h'))

lemma hasCompactSupport_ballCut (x : ℂ) (ρ : ℝ) (n : ℕ) : HasCompactSupport (ballCut x ρ n) :=
  (isCompact_closedBall x ρ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_ballCut_subset x ρ n)

lemma ballCut_nonneg (x : ℂ) (ρ : ℝ) (n : ℕ) (z : ℂ) : 0 ≤ ballCut x ρ n z :=
  le_min zero_le_one (mul_nonneg n.cast_nonneg Metric.infDist_nonneg)

lemma ballCut_mono (x : ℂ) (ρ : ℝ) (z : ℂ) : Monotone fun n => ballCut x ρ n z := by
  intro a b hab
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hab) Metric.infDist_nonneg)

lemma iSup_ofReal_ballCut (x : ℂ) {ρ : ℝ} (z : ℂ) :
    ⨆ n, ENNReal.ofReal (ballCut x ρ n z) = (Metric.ball x ρ).indicator 1 z := by
  by_cases hz : z ∈ Metric.ball x ρ
  · rw [indicator_of_mem hz, Pi.one_apply]
    have hne : ((Metric.ball x ρ)ᶜ).Nonempty := by
      refine ⟨x + (|ρ| + 1 : ℝ), fun h => ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)] at h
      linarith [le_abs_self ρ]
    have hd : 0 < Metric.infDist z (Metric.ball x ρ)ᶜ :=
      (Metric.isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hz)
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / Metric.infDist z (Metric.ball x ρ)ᶜ)
    refine le_antisymm (iSup_le fun m => ?_) (le_iSup_of_le n ?_)
    · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · have : ballCut x ρ n z = 1 := by
        unfold ballCut
        refine min_eq_left ?_
        rw [div_le_iff₀ hd] at hn; linarith
      rw [this, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    simp only [ballCut_of_notMem _ hz, ENNReal.ofReal_zero, iSup_const]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

/-- **a.e.-measurability of ball masses**: `ω ↦ μ_{X ω}(B(x,ρ))` for `B̄(x,ρ) ⊆ (0,1)²`. -/
theorem aemeasurable_qAreaMeasureOn_ball (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {x : ℂ} {ρ : ℝ}
    (hB : Metric.closedBall x ρ ⊆ openSquare) :
    AEMeasurable (fun ω => qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ)) P := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  let F : Ω → ℝ≥0∞ := fun ω =>
    ⨆ n, ENNReal.ofReal (Prop16Area.Meas.Psi γ X (fun _ z => ballCut x ρ n z) ω)
  have hF : Measurable F := Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (Prop16Area.Meas.measurable_Psi γ hXm
      ((continuous_ballCut x ρ n).measurable.comp measurable_snd))
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_isVagueLimitOn_qAreaMeasureOn_openSquare hX hγ hγ2] with ω hm
  set μ := qAreaMeasureOn γ (X ω) openSquare
  have hts : ∀ n, tsupport (ballCut x ρ n) ⊆ openSquare := fun n =>
    (tsupport_ballCut_subset x ρ n).trans hB
  have ePsi : ∀ n, Prop16Area.Meas.Psi γ X (fun _ z => ballCut x ρ n z) ω =
      ∫ z, ballCut x ρ n z ∂μ := fun n =>
    (hm.2.2 _ (continuous_ballCut x ρ n) (hasCompactSupport_ballCut x ρ n) (hts n)).limUnder_eq
  have eL : ∀ n, ENNReal.ofReal (∫ z, ballCut x ρ n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (ballCut x ρ n z) ∂μ := fun n =>
    ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (continuous_ballCut x ρ n)
        (hasCompactSupport_ballCut x ρ n) (hts n))
      (ae_of_all _ (ballCut_nonneg x ρ n))
  simp only [F, ePsi, eL]
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (ballCut x ρ n z)) (fun n => ENNReal.measurable_ofReal.comp
      (continuous_ballCut x ρ n).measurable)
    (fun a b hab z => ENNReal.ofReal_le_ofReal (ballCut_mono x ρ z hab))]
  simp_rw [iSup_ofReal_ballCut]
  exact lintegral_indicator_one Metric.isOpen_ball.measurableSet

/-- **`BallMassTail`**: Markov's inequality for DZZ Lemma 2.10's first moment. -/
theorem ballMassTail : BallMassTail := by
  intro γ hγ hγ2
  refine ⟨(3 ^ (γ ^ 2 / 2) + Real.exp (γ * junkR)) * Real.pi, by positivity, ?_⟩
  intro Ω _ P _ X hX x ρ t hρ ht hB
  have hK : gmcConst γ * (ENNReal.ofReal ρ ^ 2 * NNReal.pi) / ENNReal.ofReal t =
      ENNReal.ofReal ((3 ^ (γ ^ 2 / 2) + Real.exp (γ * junkR)) * Real.pi * ρ ^ 2 / t) := by
    unfold gmcConst
    rw [ENNReal.ofReal_div_of_pos ht, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  rw [← hK]
  calc P {ω | ENNReal.ofReal t < qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ)}
      ≤ P {ω | ENNReal.ofReal t ≤ qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ)} :=
        measure_mono fun _ hω => Set.mem_ofPred.2 (le_of_lt hω)
    _ ≤ (∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ∂P) / ENNReal.ofReal t :=
        meas_ge_le_lintegral_div (aemeasurable_qAreaMeasureOn_ball hX hγ hγ2 hB)
          (by simpa using ht) ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right (lintegral_qAreaMeasureOn_ball_le hX γ hB) _

/-- **DIM.S-chi-le-2**: `χ ≤ 2`. -/
theorem chiLeTwo : ChiLeTwo := chiLeTwo_of_ballMassTail ballMassTail

/-- **GM.S2.5** (`Blueprint.GMXiQBound`) from DG Thm 1.5 alone. -/
theorem gmXiQBound_of_dgThm1_5' (hDG : DGThm1_5) : Blueprint.GMXiQBound :=
  gmXiQBound_of_dgThm1_5_ballMassTail hDG ballMassTail

end DG
end LQGMetric
