/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.BallIndep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.PosMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.RadialProcess
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss

/-!
# Exact scaling of the GMC approximations at the origin

For a whole-plane GFF circle-average process `H` normalized by `h_1(0) = 0` and `ε ≤ 1`, the circle average `h_ε(0)` is
**independent** of the recentred field `(h_r(w) − h_ε(0))` on circles `∂B_r(w) ⊆ B_ε(0)` (`indepFun_recentred_origin`:
jointly Gaussian and uncorrelated, by Newton's theorem; it is the Markov property used in [16]'s proof of Lemma A.3,
: "`h̊_r|_𝔻` is independent from `h̊_r(0)`"). Hence the approximation on the square `Q` of
side `a ∈ (ε/8, ε/2]` centred at `0` factorizes in law,

  `E[μ_{2^{-(m+k)}}(Q)^q] ≤ ε^{q(2+γ²/2)} · ε^{−q²γ²/2} · E[S_k^q]`,

with `S_k = ε^{-2} ∫_Q (r/ε)^{γ²/2} e^{γ(h_r − h_ε(0))}` (`lintegral_approx_sq_rpow_le`), for every `q > 0`;
`E[S_k^q] ≤ 1` for `q ≤ 1` (Jensen, `E S_k ≤ 1/4`) and is bounded uniformly for `1 < q < 4/γ²` (`PosMoment.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open LQGMetric.DGMC LQGMetric.DGMC.Neg3 LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### A continuous retraction onto a closed ball -/

/-- The radial retraction `w ↦ min(1, R/|w|) w` of `ℂ` onto `B̄_R(0)`. -/
def ballRetract (R : ℝ) (w : ℂ) : ℂ := (min 1 (R / ‖w‖) : ℝ) • w

lemma ballRetract_of_le {R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) : ballRetract R w = w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [ballRetract]
  · have : 1 ≤ R / ‖w‖ := by rw [le_div_iff₀ (norm_pos_iff.2 hw0)]; linarith
    simp [ballRetract, min_eq_left this]

lemma norm_ballRetract_le {R : ℝ} (hR : 0 ≤ R) (w : ℂ) : ‖ballRetract R w‖ ≤ R := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [ballRetract, hR]
  · have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    rw [ballRetract, norm_smul, Real.norm_of_nonneg (le_min zero_le_one (by positivity))]
    calc min 1 (R / ‖w‖) * ‖w‖ ≤ R / ‖w‖ * ‖w‖ := by gcongr; exact min_le_right _ _
      _ = R := div_mul_cancel₀ R hn.ne'

lemma continuous_ballRetract {R : ℝ} (hR : 0 < R) : Continuous (ballRetract R) := by
  rw [continuous_iff_continuousAt]
  intro w
  rcases eq_or_ne w 0 with rfl | hw0
  · refine (continuousAt_id).congr ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hR] with v hv
    rw [mem_ball_zero_iff] at hv
    exact (ballRetract_of_le hv.le).symm
  · have hc : ContinuousAt (fun v : ℂ => R / ‖v‖) w :=
      continuousAt_const.div continuous_norm.continuousAt (norm_ne_zero_iff.2 hw0)
    exact (continuousAt_const.min hc).smul continuousAt_id

/-! ### Covariances at the origin -/

/-- For `ε ≤ 1`, `‖w‖ ≤ ε/2`, `0 < r ≤ ε/2`: `Cov(h_ε(0), h_r(w)) = −log ε`. -/
lemma gffCircleCov_origin {ε r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) (hrε : r ≤ ε / 2)
    {w : ℂ} (hw : ‖w‖ ≤ ε / 2) : LQGDimension.gffCircleCov ε 0 r w = -Real.log ε := by
  rw [gffCircleCov_eq_circCov hε hr, circCov_of_outside hr hε hrε (by rwa [sub_zero]),
    circCov_concentric hε one_pos, max_eq_right hε1, Real.log_one,
    circCov_of_outside hr one_pos (by linarith) (by rw [sub_zero]; linarith),
    circCov_concentric one_pos one_pos, max_self, Real.log_one]
  ring

/-- `Var h_ε(0) = −log ε` for `ε ≤ 1`. -/
lemma gffCircleCov_origin_self {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    LQGDimension.gffCircleCov ε 0 ε 0 = -Real.log ε := by
  rw [gffCircleCov_eq_circCov hε hε, circCov_concentric hε hε, max_self,
    circCov_concentric hε one_pos, max_eq_right hε1, Real.log_one,
    circCov_concentric one_pos hε, max_eq_left hε1, Real.log_one,
    circCov_concentric one_pos one_pos, max_self, Real.log_one]
  ring

/-- **Independence of `h_ε(0)` from the recentred field inside `B_ε(0)`** (`ε ≤ 1`), as a process indexed by `ℂ`
through the retraction onto `B̄_{ε/2}(0)`. -/
theorem indepFun_recentred_origin (hH : LQGDimension.IsGFFCircleAverage H P) {ε r : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hr : 0 < r) (hrε : r ≤ ε / 2) :
    IndepFun (H ε 0) (fun ω (w : ℂ) => H r (ballRetract (ε / 2) w) ω - H ε 0 ω) P := by
  classical
  set X : Unit → Ω → ℝ := fun _ => H ε 0
  set Y : ℂ → Ω → ℝ := fun w ω => H r (ballRetract (ε / 2) w) ω - H ε 0 ω
  have hXY : IsGaussianProcess (Sum.elim X Y) P := by
    refine hH.isGaussianProcess.of_isGaussianProcess fun s => ?_
    rcases s with _ | w
    · exact ⟨{((⟨ε, hε⟩ : Ioi (0 : ℝ)), (0 : ℂ))},
        { toFun := fun v => v ⟨(⟨ε, hε⟩, 0), by simp⟩
          map_add' := fun v w => rfl
          map_smul' := fun c v => rfl },
        fun ω => rfl⟩
    · exact ⟨{((⟨r, hr⟩ : Ioi (0 : ℝ)), ballRetract (ε / 2) w), ((⟨ε, hε⟩ : Ioi (0 : ℝ)), (0 : ℂ))},
        { toFun := fun v => v ⟨(⟨r, hr⟩, ballRetract (ε / 2) w), by simp⟩ - v ⟨(⟨ε, hε⟩, 0), by simp⟩
          map_add' := fun v w => by simp only [Pi.add_apply]; ring
          map_smul' := fun c v => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
        fun ω => by simp [Y]⟩
  have hmem : ∀ {ρ : ℝ}, 0 < ρ → ∀ z, MemLp (H ρ z) 2 P := fun hρ z => memLp_two_coord hH hρ z
  have h := hXY.indepFun_of_covariance_eq_zero (X := X) (Y := Y)
    (fun _ => (hmem hε 0).aestronglyMeasurable.aemeasurable)
    (fun w => ((hmem hr _).sub (hmem hε 0)).aestronglyMeasurable.aemeasurable)
    (fun _ w => by
      have hw : ‖ballRetract (ε / 2) w‖ ≤ ε / 2 := norm_ballRetract_le (by linarith) w
      have := hH.isProbabilityMeasure
      change cov[H ε 0, H r (ballRetract (ε / 2) w) - H ε 0; P] = 0
      rw [covariance_sub_right (hmem hε 0) (hmem hr _) (hmem hε 0), hH.covariance_eq ε hε r hr,
        hH.covariance_eq ε hε ε hε, gffCircleCov_origin hε hε1 hr hrε hw,
        gffCircleCov_origin_self hε hε1, sub_self])
  exact h.comp (measurable_pi_apply ()) measurable_id

/-! ### The factorization -/

/-- The normalized recentred mass `S_k = ε^{-2} ∫_Q (r/ε)^{γ²/2} e^{γ(h_r(w) − h_ε(0))} dw` on the square of side
`2^{-m}` centred at `0`, `r = 2^{-(m+k)}`. -/
def sMass (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (ε : ℝ) (m k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w in sqQ (sqCorner 0 (QuantumZipper.radius m)) m,
    nDens γ H 0 ε (QuantumZipper.radius (m + k)) w ω

lemma mem_sqQ_norm_le {a : ℝ} {m : ℕ} (ha : a = QuantumZipper.radius m) {w : ℂ}
    (hw : w ∈ sqQ (sqCorner 0 a) m) : ‖w‖ ≤ a := by
  obtain ⟨y, hy, rfl⟩ := eq_of_mem_sqQ hw
  have := norm_sqPoint_sub_le 0 (QuantumZipper.radius_pos m).le (cell0_subset_unitSq hy)
  rw [sub_zero] at this
  rw [ha]
  exact this

/-- The `σ`-algebra generated by a family of random variables indexed by `ℂ`. -/
@[instance_reducible] def famSigma (Y : ℂ → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (w : ℂ) => Y w ω) MeasurableSpace.pi

omit [MeasurableSpace Ω] in
lemma measurable_famSigma (Y : ℂ → Ω → ℝ) (w : ℂ) : Measurable[famSigma Y] (Y w) := by
  have hfam : Measurable[famSigma Y] (fun ω (w : ℂ) => Y w ω) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply w).comp hfam

/-- `S_k` is a function of the recentred field (`σ`-algebra form), hence independent of `h_ε(0)`. -/
theorem indepFun_sMass (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ} (ha : QuantumZipper.radius m ≤ ε / 2) (k : ℕ) :
    Measurable (sMass γ H ε m k) ∧ IndepFun (H ε 0) (sMass γ H ε m k) P := by
  set a := QuantumZipper.radius m with ha_def
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hra : r ≤ a := by
    simp only [r, a]
    rw [radius_add]
    exact mul_le_of_le_one_right (QuantumZipper.radius_pos m).le
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hrε : r ≤ ε / 2 := hra.trans ha
  set Y : ℂ → Ω → ℝ := fun w ω => H r (ballRetract (ε / 2) w) ω - H ε 0 ω
  have hYc : ∀ ω, Continuous fun w => Y w ω := fun ω =>
    ((hH.continuous r hr ω).comp (continuous_ballRetract (by linarith))).sub continuous_const
  have hY𝒢 : ∀ w, Measurable[famSigma Y] (Y w) := measurable_famSigma Y
  have h𝒢le : famSigma Y ≤ (inferInstance : MeasurableSpace Ω) :=
    (measurable_pi_iff.2 fun w => (hHm r _).sub (hHm ε 0)).comap_le
  -- `sMass` rewritten through the retraction
  set Q := sqQ (sqCorner 0 a) m
  have hQm : MeasurableSet Q := measurableSet_sqQ _ _
  set F : ℂ × Ω → ℝ≥0∞ := (Q ×ˢ univ).indicator
    (fun p => ENNReal.ofReal ((r / ε) ^ (γ ^ 2 / 2) * Real.exp (γ * Y p.1 p.2)))
  have hsM : ∀ ω, sMass γ H ε m k ω = ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w, F (w, ω) := fun ω => by
    rw [sMass, ← lintegral_indicator hQm]
    congr 1
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ Q
    · have hw' : (w, ω) ∈ Q ×ˢ (univ : Set Ω) := ⟨hw, mem_univ _⟩
      simp only [F, indicator_of_mem hw, indicator_of_mem hw', nDens, Y]
      rw [ballRetract_of_le ((mem_sqQ_norm_le ha_def hw).trans ha)]
    · have hw' : (w, ω) ∉ Q ×ˢ (univ : Set Ω) := fun h => hw h.1
      simp only [F, indicator_of_notMem hw, indicator_of_notMem hw']
  have hF𝒢 : Measurable[@Prod.instMeasurableSpace ℂ Ω _ (famSigma Y)] F := by
    have hu : Measurable[@Prod.instMeasurableSpace ℂ Ω _ (famSigma Y)] fun p : ℂ × Ω => Y p.1 p.2 :=
      measurable_uncurry_of_continuous_of_measurable (m := famSigma Y) (u := Y) hYc hY𝒢
    refine Measurable.indicator ?_ (hQm.prod (MeasurableSet.univ (α := Ω) (m := famSigma Y)))
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul ((hu.const_mul γ).exp))
  have hm𝒢 : Measurable[famSigma Y] (sMass γ H ε m k) := by
    have : Measurable[famSigma Y] fun ω => ENNReal.ofReal (ε⁻¹ ^ 2) * ∫⁻ w, F (w, ω) := by
      let _ : MeasurableSpace Ω := famSigma Y
      exact hF𝒢.lintegral_prod_left'.const_mul _
    exact (funext hsM ▸ this)
  refine ⟨hm𝒢.mono h𝒢le le_rfl, ?_⟩
  have hind := indepFun_recentred_origin hH hε hε1 hr hrε
  unfold IndepFun Kernel.IndepFun at hind ⊢
  exact indep_of_indep_of_le_right hind hm𝒢.comap_le

/-- **The factorization**: `E[μ_{2^{-(m+k)}}(Q)^q] = ε^{q(2+γ²/2) − q²γ²/2} E[S_k^q]` (`0 < ε ≤ 1`). -/
theorem lintegral_approx_sq_rpow_eq (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    (ha : QuantumZipper.radius m ≤ ε / 2) (k : ℕ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, GMSLemma27.lqgApprox γ H (m + k) ω (sqQ (sqCorner 0 (QuantumZipper.radius m)) m) ^ q ∂P =
      ENNReal.ofReal (ε ^ (q * (2 + γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2)) *
        ∫⁻ ω, sMass γ H ε m k ω ^ q ∂P := by
  have hP := hH.isProbabilityMeasure
  obtain ⟨hsm, hind⟩ := indepFun_sMass hH hHm γ hε hε1 ha k
  have hfact : ∀ ω, GMSLemma27.lqgApprox γ H (m + k) ω (sqQ (sqCorner 0 (QuantumZipper.radius m)) m) ^ q =
      ENNReal.ofReal (ε ^ (2 + γ ^ 2 / 2)) ^ q *
        (ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q * sMass γ H ε m k ω ^ q) := fun ω => by
    rw [lqgApprox_sq_eq γ 0 hε m k ω, ENNReal.ofReal_mul (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le, mul_assoc]
    rfl
  simp_rw [hfact]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)]
  have hf : Measurable fun ω => ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q :=
    (ENNReal.measurable_ofReal.comp (((hHm ε 0).const_mul γ).exp)).pow_const q
  have hg : Measurable fun ω => sMass γ H ε m k ω ^ q := hsm.pow_const q
  have hind' : IndepFun (fun ω => ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q)
      (fun ω => sMass γ H ε m k ω ^ q) P :=
    hind.comp (f := H ε 0) ((ENNReal.measurable_ofReal.comp
      (measurable_id.const_mul γ).exp).pow_const q) (measurable_id.pow_const q)
  rw [show (fun ω => ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q * sMass γ H ε m k ω ^ q) =
      (fun ω => ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q) * (fun ω => sMass γ H ε m k ω ^ q) from rfl,
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hf hg hind', ← mul_assoc]
  congr 1
  -- the Gaussian factor
  have e1 : ∀ ω, ENNReal.ofReal (Real.exp (γ * H ε 0 ω)) ^ q =
      ENNReal.ofReal (Real.exp ((q * γ) * H ε 0 ω)) := fun ω => by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2; ring
  simp_rw [e1]
  rw [LQGMetric.DG.lintegral_exp_circleAvg hH hε 0 (q * γ), gffCircleCov_origin_self hε hε1,
    ENNReal.ofReal_rpow_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_mul hε.le, Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 1
  ring

end MatedCRTHarmonic.GMCFacts
