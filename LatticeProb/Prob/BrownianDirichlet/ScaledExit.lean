import LatticeProb.Prob.BrownianPathSpace

/-!
# Exit times of spatially scaled Brownian paths

Spatial scaling transports exit from an open set to exit from its affine preimage.
This gives stopping, measurability, positivity and almost sure finiteness properties.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

/-- Multiply every value of a continuous path by a real scalar. -/
def scalePath (b : ℝ) (ω : BrownianPath d) : BrownianPath d :=
  ⟨fun t ↦ b • ω t, ω.continuous.const_smul b⟩

/-- Evaluation of a spatially scaled path. -/
@[simp] lemma scalePath_apply (b : ℝ) (ω : BrownianPath d) (t : ℝ≥0) :
    scalePath b ω t = b • ω t := rfl

/-- Spatial scaling is continuous in the compact-open topology. -/
lemma continuous_scalePath (b : ℝ) : Continuous (scalePath (d := d) b) := by
  change Continuous (fun ω : BrownianPath d ↦ b • ω)
  exact continuous_const_smul b

/-- Spatial scaling is measurable for the Borel path-space structure. -/
lemma measurable_scalePath (b : ℝ) : Measurable (scalePath (d := d) b) :=
  (continuous_scalePath b).measurable

/-- First exit of the spatially scaled path, started at `x`, from `B`. -/
noncomputable def scaledExit (B : Set (Euc d)) (σ : ℝ) (x : Euc d)
    (ω : BrownianPath d) : ℝ≥0∞ :=
  continuousExitTime B x (scalePath σ ω)

/-- Scaling the path is equivalent to taking the affine preimage of the exit domain. -/
lemma scaledExit_eq (B : Set (Euc d)) (σ : ℝ) (x : Euc d) (ω : BrownianPath d) :
    scaledExit B σ x ω = continuousExitTime {w | x + σ • w ∈ B} 0 ω := by
  change (⨅ t : {t : ℝ≥0 // x + σ • ω t ∉ B}, (t.val : ℝ≥0∞)) =
    ⨅ t : {t : ℝ≥0 // x + σ • (0 + ω t) ∉ B}, (t.val : ℝ≥0∞)
  have hpred : (fun t : ℝ≥0 ↦ x + σ • (0 + ω t) ∉ B) =
      (fun t : ℝ≥0 ↦ x + σ • ω t ∉ B) := by
    funext t
    rw [zero_add]
  rw [hpred]

/-- The affine preimage of an open exit domain is open. -/
lemma isOpen_scaledExit_domain {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) : IsOpen {w | x + σ • w ∈ B} :=
  hB.preimage (continuous_const.add (continuous_id.const_smul σ))

/-- Scaled exit from an open domain is a stopping time in the coordinate filtration. -/
theorem isStoppingTime_scaledExit {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) : IsStoppingTime (brownianNaturalFiltration d) (scaledExit B σ x) := by
  have heq : scaledExit B σ x = continuousExitTime {w | x + σ • w ∈ B} 0 :=
    funext (scaledExit_eq B σ x)
  exact heq.symm ▸
    isStoppingTime_continuousExitTime (isOpen_scaledExit_domain hB σ x) 0

/-- Scaled exit from an open domain is a measurable path functional. -/
theorem measurable_scaledExit {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    (x : Euc d) : Measurable (scaledExit B σ x) :=
  (measurable_continuousExitTime hB x).comp (measurable_scalePath σ)

/-- A positive spatial scaling preserves boundedness of the affine inverse domain. -/
lemma isBounded_scaledExit_domain {B : Set (Euc d)} (hB : Bornology.IsBounded B)
    {σ : ℝ} (hσ : 0 < σ) (x : Euc d) :
    Bornology.IsBounded {w | x + σ • w ∈ B} := by
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(R + ‖x‖) / σ, fun w hw ↦ ?_⟩
  apply (le_div_iff₀ hσ).mpr
  have hnorm : σ * ‖w‖ ≤ R + ‖x‖ := calc
    σ * ‖w‖ = ‖σ • w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    _ ≤ ‖x + σ • w‖ + ‖x‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (x + σ • w) x
    _ ≤ R + ‖x‖ := add_le_add (hR _ hw) le_rfl
  simpa only [mul_comm] using hnorm

/-- Standard Brownian paths in positive dimension exit bounded scaled domains almost surely. -/
theorem ae_scaledExit_ne_top (hd : 1 ≤ d) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {B : Set (Euc d)} (hB : Bornology.IsBounded B)
    {σ : ℝ} (hσ : 0 < σ) (x : Euc d) : ∀ᵐ ω ∂μ, scaledExit B σ x ω ≠ ∞ := by
  simp_rw [scaledExit_eq]
  exact standardBrownianLaw_ae_finiteExit hd hμ (isBounded_scaledExit_domain hB hσ x) 0

/-- A continuous zero-start path started inside an open domain has positive scaled exit. -/
theorem scaledExit_pos {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {x : Euc d} (hx : x ∈ B) {ω : BrownianPath d} (hω : ω 0 = 0) :
    0 < scaledExit B σ x ω := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hfinite : continuousExitTime B x (scalePath σ ω) ≠ ∞ := by
    change scaledExit B σ x ω ≠ ∞
    rw [hz]
    exact ENNReal.zero_ne_top
  have hout := continuousExitTime_not_mem hB hfinite
  change x + scalePath σ ω (scaledExit B σ x ω).toNNReal ∉ B at hout
  simp only [hz, ENNReal.toNNReal_zero, scalePath_apply, hω, smul_zero, add_zero] at hout
  exact hout hx

/-- Strictly before scaled exit, the shifted and scaled path remains in the domain. -/
lemma mem_of_lt_scaledExit {B : Set (Euc d)} {σ : ℝ} {x : Euc d}
    {ω : BrownianPath d} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < scaledExit B σ x ω) :
    x + σ • ω t ∈ B :=
  mem_of_lt_continuousExitTime ht

/-- The unit-speed ramp in dimension one has positive finite exit from the unit ball. -/
theorem scaledExit_ramp_unitBall :
    0 < scaledExit (Metric.ball (0 : Euc 1) 1) 1 0
      (BrownianPathSpaceExample.rampPath BrownianPathSpaceExample.unitVec) ∧
    scaledExit (Metric.ball (0 : Euc 1) 1) 1 0
      (BrownianPathSpaceExample.rampPath BrownianPathSpaceExample.unitVec) ≠ ∞ := by
  constructor
  · apply scaledExit_pos Metric.isOpen_ball
    · simp only [Metric.mem_ball, dist_self, zero_lt_one]
    · simp only [BrownianPathSpaceExample.rampPath_apply, NNReal.coe_zero, zero_smul]
  · simpa only [scaledExit_eq, one_smul, zero_add, setOf_mem_eq] using
      BrownianPathSpaceExample.rampPath_exitTime_ne_top

end LatticeProb
