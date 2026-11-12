/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ConeRadial at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeTight
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial

/-!
The circle-average embedding of the α-quantum cone (`CellScaling.coneField`) is
`X − ofFunC g₁ + ofFunC g₂` with `g₁ = radialAvg X = X_{|·|}(0)` and
`g₂ = A(−log|·|)`, `A = coneRadial γ α B B'` (DMS Def. 4.10 and Rem. 4.4). This file
proves, almost surely:

* `g₁`, `g₂` are measurable, continuous off `0` and locally integrable;
* the log-growth bounds `|g_i(w)| ≤ a(−log|w|) + C` near `0`, and
  `g₂ − g₁ ≤ (α + 2η)(−log|w|) + C` for every `η > 0`.

Ingredients: `t ↦ X_{e^{-t}}(0) − X_1(0)` is a Brownian motion (LQGMetric
`isPreBrownianReal_circleAvg`, continuous on the good event; Duplantier–Sheffield Prop. 3.3), the
Brownian law of large numbers `B_t/t → 0` (QuantumZipper `BMLLN.ae_tendsto_div_atTop`), and the
`GoodDrift` for the conditioned branch (`B'_u + (Q − α)u` has a last zero, at which it vanishes),
which makes `A` continuous. Local integrability: a log bound near `0` plus continuity elsewhere
(LQGMetric's integrable `logBallFun`). Own elementary glue (cf. MoTPort `ConeArea4E`–`4G`, `5B`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling QuantumZipper

/-! ## Deterministic lemmas -/

/-- **local integrability from a log bound at `0`** and continuity elsewhere -/
theorem locallyIntegrable_of_logBound {g : ℂ → ℝ} (hgm : Measurable g)
    (hgc : ContinuousOn g {0}ᶜ) {a C : ℝ}
    (hb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |g w| ≤ a * -Real.log ‖w‖ + C) :
    LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine IntegrableOn.mono_set ?_ hR
  set K₂ := closedBall (0 : ℂ) (max R 1) \ ball 0 (1 / 2) with hK₂
  have hK₂c : IsCompact K₂ := (isCompact_closedBall _ _).diff isOpen_ball
  have hK₂0 : K₂ ⊆ {0}ᶜ := fun w hw h0 => by
    rw [mem_singleton_iff] at h0
    exact hw.2 (by rw [h0]; exact mem_ball_self (by norm_num))
  obtain ⟨B, hB⟩ := hK₂c.exists_bound_of_continuousOn (hgc.mono hK₂0)
  set b : ℂ → ℝ := fun w => |a| * logBallFun w + (|C| + |B|) with hbdef
  have hbi : IntegrableOn b (closedBall 0 R) :=
    (integrable_logBallFun.const_mul |a|).integrableOn.add
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : ℂ)) (r := R)).ne)
  refine Integrable.mono' hbi hgm.aestronglyMeasurable.restrict ?_
  have h0 : ∀ᵐ w ∂(volume.restrict (closedBall (0 : ℂ) R)), w ≠ 0 :=
    ae_restrict_of_ae (by
      rw [ae_iff]; simp)
  filter_upwards [h0, ae_restrict_mem measurableSet_closedBall] with w hw0 hwR
  rw [Real.norm_eq_abs]
  have hlb : 0 ≤ logBallFun w := logBallFun_nonneg w
  by_cases hw : ‖w‖ < 1 / 2
  · have h1 := hb w hw0 (by linarith)
    have hlog : -Real.log ‖w‖ ≤ logBallFun w := by
      rw [logBallFun, indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; linarith)]
      exact neg_le_abs _
    have hlog0 : 0 ≤ -Real.log ‖w‖ := by
      have := Real.log_nonpos (norm_nonneg w) (by linarith)
      linarith
    calc |g w| ≤ a * -Real.log ‖w‖ + C := h1
      _ ≤ |a| * logBallFun w + |C| := by
          have : a * -Real.log ‖w‖ ≤ |a| * logBallFun w :=
            (mul_le_mul_of_nonneg_right (le_abs_self a) hlog0).trans
              (mul_le_mul_of_nonneg_left hlog (abs_nonneg a))
          linarith [le_abs_self C]
      _ ≤ b w := by simp only [hbdef]; linarith [abs_nonneg B]
  · have hwK : w ∈ K₂ := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right] at hwR ⊢
        exact hwR.trans (le_max_left _ _)
      · rw [mem_ball, dist_zero_right]; exact hw
    have h1 := hB w hwK
    rw [Real.norm_eq_abs] at h1
    calc |g w| ≤ B := h1
      _ ≤ b w := by
          simp only [hbdef]
          have : 0 ≤ |a| * logBallFun w := mul_nonneg (abs_nonneg _) hlb
          linarith [le_abs_self B, abs_nonneg C]

/-- `|f t| ≤ η t + C` from `f t / t → 0` and continuity -/
lemma exists_bound_of_tendsto_div {f : ℝ≥0 → ℝ} (hc : Continuous f)
    (hl : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * f t) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ C, ∀ t : ℝ≥0, |f t| ≤ η * t + C := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hl.eventually (gt_mem_nhds hη |>.and
    (lt_mem_nhds (neg_neg_of_pos hη))))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun t => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, bot_le⟩)
  have ht0 : (0 : ℝ) ≤ t := t.2
  by_cases ht : t ≤ T + 1
  · have := hM t ⟨bot_le, ht⟩
    rw [Real.norm_eq_abs] at this
    nlinarith
  · have hlt : T + 1 < t := lt_of_not_ge ht
    have htT : T ≤ t := le_self_add.trans hlt.le
    obtain ⟨h1, h2⟩ := hT t htT
    have htpos : (0 : ℝ) < t := by
      have : (1 : ℝ≥0) < t := lt_of_le_of_lt le_add_self hlt
      exact lt_trans one_pos (by exact_mod_cast this)
    have habs : |(t : ℝ)⁻¹ * f t| < η := abs_lt.2 ⟨h2, h1⟩
    rw [abs_mul, abs_inv, abs_of_pos htpos, inv_mul_lt_iff₀ htpos] at habs
    nlinarith

/-- **continuity of the cone's radial process** `A_t` (both branches meet at `0`) -/
lemma continuous_coneRadial {γ α μ : ℝ} {b b' : ℝ≥0 → ℝ} (hb : Continuous b) (hb0 : b 0 = 0)
    (hgd : GoodDrift (coneDrift γ α b') μ) : Continuous (coneRadial γ α b b') := by
  have e : coneRadial γ α b b' = fun t => if (0 : ℝ) ≤ t then b t.toNNReal + α * t else
      coneDrift γ α b' (lastZeroR (coneDrift γ α b') - t) + lqgQ γ * t := by
    funext t; rfl
  rw [e]
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact (hb.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
  · exact (hgd.cont.comp (continuous_const.sub continuous_id)).add
      (continuous_const.mul continuous_id)
  · intro t ht
    have ht0 : t = 0 := by simpa using ht.symm
    subst ht0
    simp [hb0, hgd.lastZeroR_mem.2]

/-! ## The radial Brownian motion of the GFF -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `β_t = X_{e^{-t}}(0) − X_1(0)` -/
def radBM (X : Ω → DistC) (t : ℝ≥0) (ω : Ω) : ℝ :=
  circleAvg (X ω) (Real.exp (-(t : ℝ))) 0 - circleAvg (X ω) 1 0

/-- `t ↦ X_{e^{-t}}(0) − X_1(0)` is a Brownian motion (Duplantier–Sheffield Prop. 3.3) -/
theorem isBrownianReal_radBM {X : Ω → DistC} (hX : IsWholePlaneGFF X P) :
    IsBrownianReal (radBM X) P := by
  obtain ⟨B, hBpre, -, hBae⟩ := CircleAvg.isPreBrownianReal_circleAvg hX 0
  refine ⟨hBpre.congr (C := radBM X) fun t => ?_, ?_⟩
  · filter_upwards [hBae t] with ω h
    unfold radBM
    exact h
  · filter_upwards [ae_goodCirc hX] with ω hg
    have hc : Continuous fun t : ℝ≥0 => ((Real.exp (-(t : ℝ)), (0 : ℂ)) : ℝ × ℂ) := by
      fun_prop
    have h1 : Continuous ((fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2) ∘
        fun t : ℝ≥0 => ((Real.exp (-(t : ℝ)), (0 : ℂ)) : ℝ × ℂ)) :=
      hg.comp_continuous hc fun t => ⟨Real.exp_pos _, mem_univ _⟩
    have h2 := h1.sub (continuous_const (y := circleAvg (X ω) 1 0))
    unfold radBM
    exact h2

/-- The almost sure regularity of the cone data used below. -/
structure RadialGood (γ α : ℝ) (X : DistC) (b b' : ℝ≥0 → ℝ) : Prop where
  good : GoodCirc X
  contA : Continuous (coneRadial γ α b b')
  boundB : ∀ η : ℝ, 0 < η → ∃ C, ∀ t : ℝ≥0, |b t| ≤ η * t + C
  boundβ : ∀ η : ℝ, 0 < η → ∃ C, ∀ t : ℝ≥0,
    |circleAvg X (Real.exp (-(t : ℝ))) 0 - circleAvg X 1 0| ≤ η * t + C

theorem ae_radialGood {X : Ω → DistC} (hX : IsWholePlaneGFF X P) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) {γ α : ℝ} (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, RadialGood γ α (X ω) (fun t => B t ω) (fun t => B' t ω) := by
  have hβ := isBrownianReal_radBM hX
  filter_upwards [ae_goodCirc hX, hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    BMLLN.ae_tendsto_div_atTop hB, BMLLN.ae_tendsto_div_atTop hβ, hβ.cont,
    CellScaling.ae_goodDrift hB' (sub_pos.2 hαQ)] with ω hg hBc hB0 hBl hβl hβc hgd
  refine ⟨hg, continuous_coneRadial hBc hB0 hgd,
    fun η hη => exists_bound_of_tendsto_div hBc hBl hη, fun η hη => ?_⟩
  obtain ⟨C, hC⟩ := exists_bound_of_tendsto_div hβc hβl hη
  exact ⟨C, fun t => hC t⟩

/-! ## The profiles -/

/-- the radial profile of the cone: `z ↦ A(−log|z|)` -/
def coneProfile (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (z : ℂ) : ℝ := coneRadial γ α b b' (-Real.log ‖z‖)

lemma coneField_eq_cone (γ α : ℝ) (X : DistC) (b b' : ℝ≥0 → ℝ) :
    coneField X (coneRadial γ α b b') =
      X - ofFunC (radialAvg X) + ofFunC (coneProfile γ α b b') := by
  unfold coneField CellScaling.lateralPart coneProfile
  rfl

variable {γ α : ℝ} {X : DistC} {b b' : ℝ≥0 → ℝ}

lemma measurable_radialAvg (X : DistC) : Measurable (radialAvg X) :=
  measurable_circleAvg.comp (f := fun z : ℂ => (X, ‖z‖, (0 : ℂ)))
    (measurable_const.prodMk (measurable_norm.prodMk measurable_const))

lemma continuousOn_radialAvg (hg : GoodCirc X) : ContinuousOn (radialAvg X) {0}ᶜ := by
  have hc : ContinuousOn (fun z : ℂ => ((‖z‖, (0 : ℂ)) : ℝ × ℂ)) {0}ᶜ :=
    (continuous_norm.prodMk continuous_const).continuousOn
  have h := hg.comp (s := ({0}ᶜ : Set ℂ)) hc (fun z hz =>
    (⟨norm_pos_iff.2 hz, mem_univ _⟩ : ((‖z‖, (0 : ℂ)) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
  exact h

lemma measurable_coneProfile (hr : RadialGood γ α X b b') :
    Measurable (coneProfile γ α b b') :=
  hr.contA.measurable.comp (Real.measurable_log.comp measurable_norm).neg

lemma continuousOn_coneProfile (hr : RadialGood γ α X b b') :
    ContinuousOn (coneProfile γ α b b') {0}ᶜ :=
  hr.contA.comp_continuousOn ((Real.continuousOn_log.comp continuous_norm.continuousOn
    fun _ hz => norm_ne_zero_iff.2 hz).neg)

/-- the log time of a point of the punctured unit disc -/
lemma neg_log_pos {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) : 0 < -Real.log ‖w‖ := by
  have := Real.log_neg (norm_pos_iff.2 hw0) hw1; linarith

lemma radialAvg_eq_radBM (X : DistC) {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    radialAvg X w = (circleAvg X (Real.exp (-((⟨-Real.log ‖w‖, (neg_log_pos hw0 hw1).le⟩ :
      ℝ≥0) : ℝ))) 0 - circleAvg X 1 0) + circleAvg X 1 0 := by
  simp only [neg_neg, Real.exp_log (norm_pos_iff.2 hw0), sub_add_cancel]
  rfl

lemma abs_radialAvg_le (hr : RadialGood γ α X b b') {η : ℝ} (hη : 0 < η) :
    ∃ C, ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |radialAvg X w| ≤ η * -Real.log ‖w‖ + C := by
  obtain ⟨C, hC⟩ := hr.boundβ η hη
  refine ⟨C + |circleAvg X 1 0|, fun w hw0 hw1 => ?_⟩
  rw [radialAvg_eq_radBM X hw0 hw1]
  have h := hC ⟨-Real.log ‖w‖, (neg_log_pos hw0 hw1).le⟩
  change |circleAvg X (Real.exp (-(-Real.log ‖w‖))) 0 - circleAvg X 1 0| ≤
    η * (-Real.log ‖w‖) + C at h
  calc _ ≤ |circleAvg X (Real.exp (-(-Real.log ‖w‖))) 0 - circleAvg X 1 0| +
        |circleAvg X 1 0| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma coneProfile_eq (b b' : ℝ≥0 → ℝ) {w : ℂ} (hw0 : w ≠ 0) (hw1 : ‖w‖ < 1) :
    coneProfile γ α b b' w = b (-Real.log ‖w‖).toNNReal + α * -Real.log ‖w‖ := by
  rw [coneProfile, coneRadial, if_pos (neg_log_pos hw0 hw1).le]

lemma abs_coneProfile_le (hr : RadialGood γ α X b b') {η : ℝ} (hη : 0 < η) :
    ∃ C, ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 →
      |coneProfile γ α b b' w| ≤ (η + |α|) * -Real.log ‖w‖ + C ∧
        coneProfile γ α b b' w ≤ (α + η) * -Real.log ‖w‖ + C := by
  obtain ⟨C, hC⟩ := hr.boundB η hη
  refine ⟨C, fun w hw0 hw1 => ?_⟩
  have ht := neg_log_pos hw0 hw1
  have h := hC (-Real.log ‖w‖).toNNReal
  rw [Real.coe_toNNReal _ ht.le] at h
  rw [coneProfile_eq b b' hw0 hw1]
  constructor
  · calc _ ≤ |b (-Real.log ‖w‖).toNNReal| + |α * -Real.log ‖w‖| := abs_add_le _ _
      _ ≤ (η * -Real.log ‖w‖ + C) + |α| * -Real.log ‖w‖ := by
          rw [abs_mul, abs_of_pos ht]; linarith
      _ = _ := by ring
  · have := le_abs_self (b (-Real.log ‖w‖).toNNReal)
    nlinarith

end MatedCRTHarmonic.LQGCoord
